use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

use serde_json::Value;

static NEXT_TEST_DIRECTORY: AtomicU64 = AtomicU64::new(0);

struct TestDirectory(PathBuf);

impl TestDirectory {
    fn new() -> Self {
        let sequence = NEXT_TEST_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "logos-integrity-pipeline-{}-{sequence}",
            std::process::id()
        ));
        std::fs::create_dir_all(&path).expect("create integrity pipeline test directory");
        Self(path)
    }

    fn path(&self) -> &Path {
        &self.0
    }
}

impl Drop for TestDirectory {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

#[test]
#[ignore = "runs the Java Calcite wrapper over a frozen benchmark case"]
fn authoritative_constraints_reach_every_deterministic_consumer() {
    let repo = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("workspace root");
    let case = repo.join(
        "benchmarks/core/.generated/sqlsolver/nonwetune-flat/\
         verieql-calcite__calcite-148",
    );
    let run = TestDirectory::new();

    let output = Command::new(env!("CARGO_BIN_EXE_logos-solver"))
        .current_dir(repo)
        .args([
            "check",
            "--transform-only",
            "--disable-counterexample-search",
        ])
        .arg("--schema")
        .arg(case.join("schema.sql"))
        .arg("--source")
        .arg(case.join("sql1.sql"))
        .arg("--target")
        .arg(case.join("sql2.sql"))
        .arg("--log-dir")
        .arg(run.path())
        .arg("--logos-repo-root")
        .arg(repo)
        .args([
            "--sql-default-collation",
            "C",
            "--sql-character-classification",
            "C",
            "--sql-locale-provider",
            "libc",
            "--sql-server-encoding",
            "UTF8",
            "--quiet",
        ])
        .output()
        .expect("run solver transform pipeline");
    assert!(
        output.status.success(),
        "solver failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let report = read_json(&run.path().join("report.json"));
    assert_eq!(report["outcome"], "transform_only");

    let contract = read_json(&run.path().join("input/integrity-contract.json"));
    assert_eq!(contract["caseId"], "verieql-calcite__calcite-148");
    let contract_tables = constraint_tables(&contract, "/tables");
    let dept = contract_tables.get("dept").expect("DEPT contract");
    assert_eq!(dept["primaryKey"], serde_json::json!(["deptno"]));
    assert!(
        dept["notNull"]
            .as_array()
            .is_some_and(|columns| columns.iter().any(|column| column == "deptno"))
    );

    // Query parsing receives the same authoritative contract after DDL and
    // adjacent benchmark metadata have been merged and normalized.
    let schema = read_json(&run.path().join("input/schema-ir.json"));
    assert_eq!(constraint_tables(&schema, "/tables"), contract_tables);

    let lowering = read_json(&run.path().join("proof-stage/formal-sql-lowering.json"));
    assert_eq!(
        lowering.pointer("/schema/status"),
        Some(&Value::from("lowered"))
    );
    let formal_tables = constraint_tables(&lowering, "/schema/schema/tables");
    assert_eq!(
        constraint_counts(&formal_tables),
        constraint_counts(&contract_tables)
    );
    assert_eq!(formal_tables["dept"]["primaryKey"][0]["name"], "deptno");

    let checks = read_json(&run.path().join("input/integrity-validator-checks.json"));
    assert_eq!(
        validation_counts(&checks),
        constraint_counts(&contract_tables)
    );
    let primary_key_check = checks
        .as_array()
        .and_then(|checks| {
            checks.iter().find(|check| {
                check["kind"] == "primary_key"
                    && check["table"]
                        .as_str()
                        .is_some_and(|table| table.eq_ignore_ascii_case("dept"))
            })
        })
        .expect("DEPT primary-key validator check");
    assert!(
        primary_key_check["sql"]
            .as_str()
            .is_some_and(|sql| { sql.contains("GROUP BY") && sql.contains("HAVING count(*) > 1") })
    );

    let schema_v = read_text(&run.path().join("proof-stage/formal-sql/Schema.v"));
    assert!(schema_v.contains("Definition generated_schema_constraints"));
    assert!(schema_v.contains("(Rel \"dept\")"));
    assert!(schema_v.contains("Some (Attr_int32 \"deptno\" :: nil)"));

    let summary = read_text(&run.path().join("input/integrity-contract.txt"));
    assert!(summary.contains("\"dept\": NOT NULL (\"deptno\", \"name\")"));
    assert!(summary.contains("\"dept\": PRIMARY KEY (\"deptno\")"));

    let proof_prompt = read_text(
        &run.path()
            .join("proof-stage/formal-sql/proof-agent-prompt.md"),
    );
    assert!(proof_prompt.contains("`Schema.v`"));
}

fn read_json(path: &Path) -> Value {
    serde_json::from_slice(
        &std::fs::read(path)
            .unwrap_or_else(|error| panic!("failed to read {}: {error}", path.display())),
    )
    .unwrap_or_else(|error| panic!("failed to parse {}: {error}", path.display()))
}

fn read_text(path: &Path) -> String {
    std::fs::read_to_string(path)
        .unwrap_or_else(|error| panic!("failed to read {}: {error}", path.display()))
}

fn constraint_tables(document: &Value, pointer: &str) -> BTreeMap<String, Value> {
    document
        .pointer(pointer)
        .and_then(Value::as_array)
        .expect("schema table array")
        .iter()
        .filter_map(|table| {
            let name = table
                .get("name")
                .or_else(|| table.get("relation"))?
                .as_str()?;
            let constraints = table.get("constraints")?;
            (!constraints
                .as_object()
                .is_none_or(serde_json::Map::is_empty))
            .then(|| (name.to_ascii_lowercase(), constraints.clone()))
        })
        .collect()
}

fn constraint_counts(tables: &BTreeMap<String, Value>) -> BTreeMap<&'static str, usize> {
    let mut counts = BTreeMap::from([
        ("check", 0),
        ("foreign_key", 0),
        ("not_null", 0),
        ("partial_expression_unique_index", 0),
        ("primary_key", 0),
        ("unique", 0),
    ]);
    for constraints in tables.values() {
        counts.insert(
            "not_null",
            counts["not_null"] + array_len(constraints, "notNull"),
        );
        counts.insert(
            "primary_key",
            counts["primary_key"] + usize::from(constraints.get("primaryKey").is_some()),
        );
        counts.insert(
            "unique",
            counts["unique"] + array_len(constraints, "unique"),
        );
        counts.insert(
            "foreign_key",
            counts["foreign_key"] + array_len(constraints, "foreignKeys"),
        );
        counts.insert("check", counts["check"] + array_len(constraints, "checks"));
        counts.insert(
            "partial_expression_unique_index",
            counts["partial_expression_unique_index"] + array_len(constraints, "uniqueIndexes"),
        );
    }
    counts
}

fn validation_counts(checks: &Value) -> BTreeMap<&'static str, usize> {
    let mut counts = BTreeMap::from([
        ("check", 0),
        ("foreign_key", 0),
        ("not_null", 0),
        ("partial_expression_unique_index", 0),
        ("primary_key", 0),
        ("unique", 0),
    ]);
    for check in checks.as_array().expect("validator check array") {
        let kind = check["kind"].as_str().expect("validator check kind");
        let count = counts.get_mut(kind).expect("known constraint kind");
        *count += 1;
    }
    counts
}

fn array_len(value: &Value, key: &str) -> usize {
    value.get(key).and_then(Value::as_array).map_or(0, Vec::len)
}
