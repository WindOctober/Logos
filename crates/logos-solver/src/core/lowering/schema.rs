use super::emit::{emit_rocq_create_schema, emit_rocq_schema_module};
use super::*;
use logos_ir::ir::Table;

impl LoweringContext {
    pub(super) fn lower_schema(&mut self, path: &str, schema: &Schema) -> Option<FormalSchema> {
        let tables = schema
            .tables
            .iter()
            .enumerate()
            .map(|(index, table)| self.lower_table(&format!("{path}.tables[{index}]"), table))
            .collect::<Option<Vec<_>>>()?;
        let rocq_create_schema = emit_rocq_create_schema(&tables);
        let rocq_module = emit_rocq_schema_module(&rocq_create_schema);
        Some(FormalSchema {
            tables,
            rocq_create_schema,
            rocq_module,
        })
    }

    fn lower_table(&mut self, path: &str, table: &Table) -> Option<FormalTable> {
        if table.name.is_empty() {
            self.error(
                path,
                "empty_table_name",
                "FormalSQL relation names must be non-empty.",
            );
            return None;
        }
        if !has_unique_column_names(&table.columns) {
            self.error(
                path,
                "duplicate_table_attribute",
                "FormalSQL table schema uses a finite set of attributes; duplicate column names cannot be represented soundly.",
            );
            return None;
        }
        let attributes = table
            .columns
            .iter()
            .enumerate()
            .map(|(index, column)| {
                self.lower_schema_attribute(&format!("{path}.columns[{index}]"), column)
            })
            .collect::<Option<Vec<_>>>()?;
        Some(FormalTable {
            relation: table.name.clone(),
            attributes,
        })
    }

    fn lower_schema_attribute(&mut self, path: &str, column: &Column) -> Option<FormalAttribute> {
        if column.name.is_empty() {
            self.error(
                path,
                "empty_attribute_name",
                "FormalSQL attributes must be non-empty.",
            );
            return None;
        }
        if !column.nullable {
            self.warning(
                path,
                "not_null_constraint_not_encoded",
                "FormalSQL proof-of-concept schemas type attributes but do not encode SQL NOT NULL constraints.",
            );
        }
        let ty = self.lower_attribute_type(path, column, AttributeTypeContext::Schema)?;
        Some(FormalAttribute {
            name: column.name.clone(),
            ty,
        })
    }
}
