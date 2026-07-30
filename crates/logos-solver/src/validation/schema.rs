use postgres::Transaction;

use crate::core::FormalQueryError;
use crate::error::{Error, Result};
use crate::validation::types::{OutputColumn, OutputSchema, SchemaMismatch, StatementOutput};

const OUTPUT_PROBE_SAVEPOINT: &str = "logos_output_probe";

pub(super) fn describe_statement_output(
    transaction: &mut Transaction<'_>,
    query: &str,
) -> Result<StatementOutput> {
    transaction.batch_execute(&format!("SAVEPOINT {OUTPUT_PROBE_SAVEPOINT}"))?;
    match describe_output_shape(transaction, query) {
        Ok(schema) => {
            transaction.batch_execute(&format!("RELEASE SAVEPOINT {OUTPUT_PROBE_SAVEPOINT}"))?;
            Ok(StatementOutput::Success { schema })
        }
        Err(Error::Postgres(source)) => {
            transaction.batch_execute(&format!(
                "ROLLBACK TO SAVEPOINT {OUTPUT_PROBE_SAVEPOINT}; \
                 RELEASE SAVEPOINT {OUTPUT_PROBE_SAVEPOINT}"
            ))?;
            let Some(db_error) = source.as_db_error() else {
                return Err(Error::Postgres(source));
            };
            let Some(error) = formal_analysis_error(db_error.code().code()) else {
                return Err(Error::Postgres(source));
            };
            Ok(StatementOutput::AnalysisError {
                error,
                sql_state: db_error.code().code().to_owned(),
                message: db_error.message().to_owned(),
            })
        }
        Err(error) => {
            transaction.batch_execute(&format!(
                "ROLLBACK TO SAVEPOINT {OUTPUT_PROBE_SAVEPOINT}; \
                 RELEASE SAVEPOINT {OUTPUT_PROBE_SAVEPOINT}"
            ))?;
            Err(error)
        }
    }
}

fn formal_analysis_error(sql_state: &str) -> Option<FormalQueryError> {
    match sql_state {
        "42702" => Some(FormalQueryError::AmbiguousColumn),
        "42703" => Some(FormalQueryError::UndefinedColumn),
        "42883" => Some(FormalQueryError::UndefinedFunction),
        "22P02" => Some(FormalQueryError::InvalidTextRepresentation),
        _ => None,
    }
}

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
            type_modifier: column.type_modifier(),
            type_name: column.type_().name().to_owned(),
        })
        .collect();
    Ok(OutputSchema { columns })
}

#[cfg(test)]
pub(super) fn output_mismatch(
    source: OutputSchema,
    target: OutputSchema,
) -> Option<SchemaMismatch> {
    output_mismatch_at(1, source, target)
}

pub(super) fn output_program_mismatch(
    source: &[StatementOutput],
    target: &[StatementOutput],
) -> Option<SchemaMismatch> {
    if source.len() != target.len() {
        return Some(SchemaMismatch::ProgramLength {
            reason: format!(
                "query program length differs: source has {} statements, target has {}",
                source.len(),
                target.len()
            ),
            source_statement_count: source.len(),
            target_statement_count: target.len(),
        });
    }

    source.iter().cloned().zip(target.iter().cloned()).enumerate().find_map(
        |(index, (source, target))| {
            let statement = index + 1;
            match (&source, &target) {
                (
                    StatementOutput::Success {
                        schema: source_schema,
                    },
                    StatementOutput::Success {
                        schema: target_schema,
                    },
                ) => output_mismatch_at(statement, source_schema.clone(), target_schema.clone()),
                (
                    StatementOutput::AnalysisError {
                        error: source_error,
                        ..
                    },
                    StatementOutput::AnalysisError {
                        error: target_error,
                        ..
                    },
                ) if source_error == target_error => None,
                _ => Some(SchemaMismatch::StatementOutcome {
                    reason: format!(
                        "statement {statement} PostgreSQL analysis outcomes differ: source {}, target {}",
                        statement_output_label(&source),
                        statement_output_label(&target),
                    ),
                    statement,
                    source,
                    target,
                }),
            }
        },
    )
}

fn statement_output_label(output: &StatementOutput) -> String {
    match output {
        StatementOutput::Success { schema } => {
            format!("succeeds with {} output columns", schema.columns.len())
        }
        StatementOutput::AnalysisError {
            error, sql_state, ..
        } => format!("raises {error:?} (SQLSTATE {sql_state})"),
    }
}

pub(super) fn output_mismatch_at(
    statement: usize,
    source: OutputSchema,
    target: OutputSchema,
) -> Option<SchemaMismatch> {
    if source.columns.len() != target.columns.len() {
        return Some(SchemaMismatch::StatementOutput {
            reason: format!(
                "statement {statement} output column count differs: source has {}, target has {}",
                source.columns.len(),
                target.columns.len()
            ),
            statement,
            source,
            target,
        });
    }

    for (source_column, target_column) in source.columns.iter().zip(target.columns.iter()) {
        if source_column.type_oid != target_column.type_oid
            || source_column.type_modifier != target_column.type_modifier
        {
            return Some(SchemaMismatch::StatementOutput {
                reason: format!(
                    "statement {statement} output column {} type differs: source is {} (oid {}, typmod {}), target is {} (oid {}, typmod {})",
                    source_column.ordinal,
                    source_column.type_name,
                    source_column.type_oid,
                    source_column.type_modifier,
                    target_column.type_name,
                    target_column.type_oid,
                    target_column.type_modifier
                ),
                statement,
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
                type_modifier: -1,
                type_name: "int4".to_owned(),
            }],
        };
        let target_schema = OutputSchema {
            columns: Vec::new(),
        };

        let mismatch = output_mismatch(source_schema, target_schema).unwrap();
        assert_eq!(
            mismatch.reason(),
            "statement 1 output column count differs: source has 1, target has 0"
        );
    }

    #[test]
    fn detects_column_type_mismatch() {
        let source_schema = OutputSchema {
            columns: vec![OutputColumn {
                ordinal: 1,
                name: "?column?".to_owned(),
                type_oid: 23,
                type_modifier: -1,
                type_name: "int4".to_owned(),
            }],
        };
        let target_schema = OutputSchema {
            columns: vec![OutputColumn {
                ordinal: 1,
                name: "?column?".to_owned(),
                type_oid: 25,
                type_modifier: -1,
                type_name: "text".to_owned(),
            }],
        };

        let mismatch = output_mismatch(source_schema, target_schema).unwrap();
        assert_eq!(
            mismatch.reason(),
            "statement 1 output column 1 type differs: source is int4 (oid 23, typmod -1), target is text (oid 25, typmod -1)"
        );
    }

    #[test]
    fn ignores_column_label_mismatch() {
        let source_schema = OutputSchema {
            columns: vec![OutputColumn {
                ordinal: 1,
                name: "source_label".to_owned(),
                type_oid: 23,
                type_modifier: -1,
                type_name: "int4".to_owned(),
            }],
        };
        let target_schema = OutputSchema {
            columns: vec![OutputColumn {
                ordinal: 1,
                name: "target_label".to_owned(),
                type_oid: 23,
                type_modifier: -1,
                type_name: "int4".to_owned(),
            }],
        };

        assert!(output_mismatch(source_schema, target_schema).is_none());
    }

    #[test]
    fn detects_column_typmod_mismatch() {
        let source_schema = OutputSchema {
            columns: vec![OutputColumn {
                ordinal: 1,
                name: "value".to_owned(),
                type_oid: 1042,
                type_modifier: -1,
                type_name: "bpchar".to_owned(),
            }],
        };
        let target_schema = OutputSchema {
            columns: vec![OutputColumn {
                ordinal: 1,
                name: "value".to_owned(),
                type_oid: 1042,
                type_modifier: 6,
                type_name: "bpchar".to_owned(),
            }],
        };

        let mismatch = output_mismatch(source_schema, target_schema).unwrap();
        assert_eq!(
            mismatch.reason(),
            "statement 1 output column 1 type differs: source is bpchar (oid 1042, typmod -1), target is bpchar (oid 1042, typmod 6)"
        );
    }

    #[test]
    fn detects_query_program_length_mismatch() {
        let schema = OutputSchema {
            columns: Vec::new(),
        };
        let success = StatementOutput::Success { schema };
        let mismatch = output_program_mismatch(&[success.clone(), success.clone()], &[success])
            .expect("program lengths differ");

        assert_eq!(
            mismatch.reason(),
            "query program length differs: source has 2 statements, target has 1"
        );
    }

    #[test]
    fn analysis_errors_match_by_formal_sql_category() {
        let source = StatementOutput::AnalysisError {
            error: FormalQueryError::UndefinedColumn,
            sql_state: "42703".to_owned(),
            message: "column source_alias does not exist".to_owned(),
        };
        let same_category = StatementOutput::AnalysisError {
            error: FormalQueryError::UndefinedColumn,
            sql_state: "42703".to_owned(),
            message: "column target_alias does not exist".to_owned(),
        };
        assert!(output_program_mismatch(std::slice::from_ref(&source), &[same_category]).is_none());

        let different = StatementOutput::AnalysisError {
            error: FormalQueryError::UndefinedFunction,
            sql_state: "42883".to_owned(),
            message: "operator does not exist".to_owned(),
        };
        let mismatch = output_program_mismatch(&[source], &[different])
            .expect("different analysis outcomes must be observable");
        assert!(mismatch.reason().contains("analysis outcomes differ"));
    }
}
