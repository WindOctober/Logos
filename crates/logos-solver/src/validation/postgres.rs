use postgres::{Client, NoTls};

use crate::core::{SqlTimeZone, VerificationInput};
use crate::error::{Error, Result};
use crate::validation::bag_semantics::{
    bag_difference_exists_sql, diff_sample_sql, ordered_diff_sample_sql,
    ordered_difference_exists_sql, ordered_query_json_sql, query_json_sql,
};
use crate::validation::observation::{ObservationMode, classify_observation};
use crate::validation::postgres_session::{fresh_schema_name, setup_witness_schema, trim_query};
use crate::validation::schema::{describe_output_shape, output_mismatch};
use crate::validation::types::{CheckResult, WitnessCheck};

#[derive(Debug, Clone)]
pub struct PostgresValidator {
    url: String,
    statement_timeout_ms: u64,
    diff_sample_limit: usize,
    sql_time_zone: SqlTimeZone,
}

impl PostgresValidator {
    pub fn new(
        url: Option<String>,
        statement_timeout_ms: u64,
        diff_sample_limit: usize,
        sql_time_zone: SqlTimeZone,
    ) -> Result<Self> {
        let url = url
            .or_else(|| std::env::var("LOGOS_POSTGRES_URL").ok())
            .or_else(|| std::env::var("DATABASE_URL").ok())
            .ok_or(Error::MissingPostgresUrl)?;
        Ok(Self {
            url,
            statement_timeout_ms,
            diff_sample_limit,
            sql_time_zone,
        })
    }

    pub fn validate(&self, input: &VerificationInput, witness_sql: &str) -> WitnessCheck {
        let schema_name = fresh_schema_name();
        match self.try_validate(input, witness_sql, &schema_name) {
            Ok(mut validation) => {
                validation.schema_name = schema_name;
                validation
            }
            Err(error) => WitnessCheck {
                schema_name,
                warnings: Vec::new(),
                result: CheckResult::ValidationError {
                    message: format!("{error:?}"),
                },
            },
        }
    }

    fn try_validate(
        &self,
        input: &VerificationInput,
        witness_sql: &str,
        schema_name: &str,
    ) -> Result<WitnessCheck> {
        let mut client = Client::connect(&self.url, NoTls)?;
        let mut transaction = client.transaction()?;
        setup_witness_schema(
            &mut transaction,
            schema_name,
            self.statement_timeout_ms,
            &self.sql_time_zone,
            input.schema_sql(),
            witness_sql,
        )?;

        let source_query = trim_query(input.source_sql());
        let target_query = trim_query(input.target_sql());
        let observation = classify_observation(source_query, target_query);

        let source_schema = describe_output_shape(&mut transaction, source_query)?;
        let target_schema = describe_output_shape(&mut transaction, target_query)?;
        if let Some(mismatch) = output_mismatch(source_schema.clone(), target_schema) {
            transaction.rollback()?;
            return Ok(WitnessCheck {
                schema_name: String::new(),
                warnings: observation.warnings,
                result: CheckResult::OutputSchemaMismatch { mismatch },
            });
        }

        let column_count = source_schema.columns.len();
        let different_sql = match observation.mode {
            ObservationMode::Bag => bag_difference_exists_sql(source_query, target_query),
            ObservationMode::OrderedList => {
                ordered_difference_exists_sql(source_query, target_query, column_count)
            }
        };
        let different: bool = transaction.query_one(&different_sql, &[])?.get(0);
        let (source_result, target_result, diff_sample) = if different {
            match observation.mode {
                ObservationMode::Bag => (
                    Some(query_json_sql(
                        source_query,
                        self.diff_sample_limit,
                        "source",
                    )),
                    Some(query_json_sql(
                        target_query,
                        self.diff_sample_limit,
                        "target",
                    )),
                    Some(diff_sample_sql(
                        source_query,
                        target_query,
                        self.diff_sample_limit,
                    )),
                ),
                ObservationMode::OrderedList => (
                    Some(ordered_query_json_sql(
                        source_query,
                        column_count,
                        self.diff_sample_limit,
                        "source",
                    )),
                    Some(ordered_query_json_sql(
                        target_query,
                        column_count,
                        self.diff_sample_limit,
                        "target",
                    )),
                    Some(ordered_diff_sample_sql(
                        source_query,
                        target_query,
                        column_count,
                        self.diff_sample_limit,
                    )),
                ),
            }
        } else {
            (None, None, None)
        };

        let source_result = source_result
            .map(|sql| transaction.query_one(&sql, &[]).map(|row| row.get(0)))
            .transpose()?;
        let target_result = target_result
            .map(|sql| transaction.query_one(&sql, &[]).map(|row| row.get(0)))
            .transpose()?;
        let diff_sample = diff_sample
            .map(|sql| transaction.query_one(&sql, &[]).map(|row| row.get(0)))
            .transpose()?;

        transaction.rollback()?;

        let result = match (source_result, target_result, diff_sample) {
            (Some(source_result), Some(target_result), Some(diff_sample)) => {
                CheckResult::DataDifference {
                    source_result,
                    target_result,
                    diff_sample,
                }
            }
            _ => CheckResult::NoDifference,
        };

        Ok(WitnessCheck {
            schema_name: String::new(),
            warnings: observation.warnings,
            result,
        })
    }
}
