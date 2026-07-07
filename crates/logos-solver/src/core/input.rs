use std::path::{Path, PathBuf};

use logos_ir::SqlIrFrontend;
use logos_ir::ir::{Query, Schema};
use serde::{Deserialize, Serialize};

use crate::error::{Error, Result};

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct VerificationInput {
    schema: SchemaInput,
    source_query: QueryInput,
    target_query: QueryInput,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SchemaInput {
    pub path: PathBuf,
    pub sql: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct QueryInput {
    pub path: PathBuf,
    pub sql: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct VerificationIr {
    schema: Schema,
    source_query: Query,
    target_query: Query,
}

impl VerificationInput {
    pub fn read(schema: PathBuf, source: PathBuf, target: PathBuf) -> Result<Self> {
        let schema_sql = read_to_string(&schema)?;
        let source_sql = read_to_string(&source)?;
        let target_sql = read_to_string(&target)?;

        Ok(Self {
            schema: SchemaInput {
                path: schema,
                sql: schema_sql,
            },
            source_query: QueryInput {
                path: source,
                sql: source_sql,
            },
            target_query: QueryInput {
                path: target,
                sql: target_sql,
            },
        })
    }

    pub fn load_ir(&self, ir_frontend: &dyn SqlIrFrontend) -> Result<VerificationIr> {
        let mut source_ir = ir_frontend.load_sql(&self.schema.path, &self.source_query.path)?;
        let mut target_ir = ir_frontend.load_sql(&self.schema.path, &self.target_query.path)?;
        let source_query_ir = take_single_query(&self.source_query.path, &mut source_ir)?;
        let target_query_ir = take_single_query(&self.target_query.path, &mut target_ir)?;

        if source_ir.schema != target_ir.schema {
            return Err(Error::InvalidLogosIrInput(
                "source and target Calcite imports produced different schemas".to_owned(),
            ));
        }

        Ok(VerificationIr {
            schema: source_ir.schema,
            source_query: source_query_ir,
            target_query: target_query_ir,
        })
    }

    pub fn schema_sql(&self) -> &str {
        &self.schema.sql
    }

    pub fn source_sql(&self) -> &str {
        &self.source_query.sql
    }

    pub fn target_sql(&self) -> &str {
        &self.target_query.sql
    }

    pub fn stable_cache_key(&self) -> String {
        let mut hash = Fnv64::new();
        hash.write("logos-solver-verification-input-v1");
        hash.write(self.schema_sql());
        hash.write(self.source_sql());
        hash.write(self.target_sql());
        format!("{:016x}", hash.finish())
    }
}

impl VerificationIr {
    pub fn schema_ir(&self) -> &Schema {
        &self.schema
    }

    pub fn source_query_ir(&self) -> &Query {
        &self.source_query
    }

    pub fn target_query_ir(&self) -> &Query {
        &self.target_query
    }
}

struct Fnv64 {
    state: u64,
}

impl Fnv64 {
    fn new() -> Self {
        Self {
            state: 0xcbf29ce484222325,
        }
    }

    fn write(&mut self, value: &str) {
        for byte in value.as_bytes() {
            self.state ^= u64::from(*byte);
            self.state = self.state.wrapping_mul(0x100000001b3);
        }
        self.state ^= 0xff;
        self.state = self.state.wrapping_mul(0x100000001b3);
    }

    fn finish(self) -> u64 {
        self.state
    }
}

fn take_single_query(path: &Path, ir: &mut logos_ir::ir::LogosIrFile) -> Result<Query> {
    if ir.queries.len() != 1 {
        return Err(Error::InvalidLogosIrInput(format!(
            "{} must produce exactly one Logos IR query, found {}",
            path.display(),
            ir.queries.len()
        )));
    }
    Ok(ir.queries.remove(0))
}

fn read_to_string(path: &Path) -> Result<String> {
    std::fs::read_to_string(path).map_err(|source| Error::Read {
        path: path.to_owned(),
        source,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use logos_ir::ir::{LogosIrFile, RelExpr};

    #[derive(Debug, Clone)]
    struct StaticSqlIrFrontend {
        ir: LogosIrFile,
    }

    impl SqlIrFrontend for StaticSqlIrFrontend {
        fn load_sql(
            &self,
            _schema_path: &Path,
            _query_path: &Path,
        ) -> logos_ir::Result<LogosIrFile> {
            Ok(self.ir.clone())
        }
    }

    #[test]
    fn rejects_ir_files_without_exactly_one_query() {
        let mut ir = empty_ir();
        ir.queries.clear();
        let error = take_single_query(Path::new("query.sql"), &mut ir)
            .expect_err("empty query list should fail");
        assert!(format!("{error}").contains("exactly one Logos IR query"));
    }

    #[test]
    fn reads_verification_input_with_logos_ir_queries() {
        let temp = std::env::temp_dir().join(format!(
            "logos-solver-verification-input-test-{}",
            std::process::id()
        ));
        std::fs::create_dir_all(&temp).expect("create temp dir");
        let schema_path = temp.join("schema.sql");
        let source_path = temp.join("source.sql");
        let target_path = temp.join("target.sql");
        std::fs::write(&schema_path, "create table t(a int);").expect("write schema");
        std::fs::write(&source_path, "select a from t;").expect("write source");
        std::fs::write(&target_path, "select a from t;").expect("write target");

        let input =
            VerificationInput::read(schema_path, source_path, target_path).expect("read input");

        assert_eq!(input.stable_cache_key(), input.stable_cache_key());

        let ir = input
            .load_ir(&StaticSqlIrFrontend { ir: empty_ir() })
            .expect("verification IR should load");
        assert_eq!(ir.schema_ir().tables.len(), 0);
        assert_eq!(ir.source_query_ir().output.len(), 0);
        assert_eq!(ir.target_query_ir().output.len(), 0);
    }

    fn empty_ir() -> LogosIrFile {
        LogosIrFile {
            schema: Schema { tables: vec![] },
            queries: vec![Query {
                source_sql: Some("select 1".to_owned()),
                rel: RelExpr::Values {
                    tuples: logos_ir::ir::ValuesTuples::Rows { rows: vec![] },
                    output: vec![],
                },
                output: vec![],
                features: vec![],
                calcite_rel_text: None,
                calcite_rel_plan: None,
            }],
        }
    }
}
