use postgres::Transaction;

use crate::error::Result;
use crate::validation::types::{OutputColumn, OutputSchema, SchemaMismatch};

pub(super) fn describe_output_shape(
    transaction: &mut Transaction<'_>,
    query: &str,
) -> Result<OutputSchema> {
    let statement = transaction.prepare(&format!(
        "SELECT * FROM ({query}) AS _logos_shape_probe LIMIT 0"
    ))?;
    let columns = statement
        .columns()
        .iter()
        .enumerate()
        .map(|(index, column)| OutputColumn {
            ordinal: index + 1,
            name: column.name().to_owned(),
            type_oid: column.type_().oid(),
            type_name: column.type_().name().to_owned(),
        })
        .collect();
    Ok(OutputSchema { columns })
}

pub(super) fn output_mismatch(
    source: OutputSchema,
    target: OutputSchema,
) -> Option<SchemaMismatch> {
    if source.columns.len() != target.columns.len() {
        return Some(SchemaMismatch {
            reason: format!(
                "output column count differs: source has {}, target has {}",
                source.columns.len(),
                target.columns.len()
            ),
            source,
            target,
        });
    }

    for (source_column, target_column) in source.columns.iter().zip(target.columns.iter()) {
        if source_column.type_oid != target_column.type_oid {
            return Some(SchemaMismatch {
                reason: format!(
                    "output column {} type differs: source is {} (oid {}), target is {} (oid {})",
                    source_column.ordinal,
                    source_column.type_name,
                    source_column.type_oid,
                    target_column.type_name,
                    target_column.type_oid
                ),
                source,
                target,
            });
        }
    }

    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn detects_column_count_mismatch() {
        let source_schema = OutputSchema {
            columns: vec![OutputColumn {
                ordinal: 1,
                name: "?column?".to_owned(),
                type_oid: 23,
                type_name: "int4".to_owned(),
            }],
        };
        let target_schema = OutputSchema {
            columns: Vec::new(),
        };

        let mismatch = output_mismatch(source_schema, target_schema).unwrap();
        assert_eq!(
            mismatch.reason,
            "output column count differs: source has 1, target has 0"
        );
    }

    #[test]
    fn detects_column_type_mismatch() {
        let source_schema = OutputSchema {
            columns: vec![OutputColumn {
                ordinal: 1,
                name: "?column?".to_owned(),
                type_oid: 23,
                type_name: "int4".to_owned(),
            }],
        };
        let target_schema = OutputSchema {
            columns: vec![OutputColumn {
                ordinal: 1,
                name: "?column?".to_owned(),
                type_oid: 25,
                type_name: "text".to_owned(),
            }],
        };

        let mismatch = output_mismatch(source_schema, target_schema).unwrap();
        assert_eq!(
            mismatch.reason,
            "output column 1 type differs: source is int4 (oid 23), target is text (oid 25)"
        );
    }
}
