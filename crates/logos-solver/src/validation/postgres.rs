use logos_ir::integrity::IntegrityValidationCheck;
#[cfg(test)]
use postgres::SimpleQueryMessage;
#[cfg(test)]
use postgres::types::ToSql;
use postgres::types::{FromSql, Type};
use postgres::{Client, IsolationLevel, NoTls, Transaction};

#[cfg(test)]
use crate::core::ObservationCertificateReport;
use crate::core::{
    FormalAttributeType, FormalSchema, SqlEnvironment, SqlTimeZone, VerificationInput,
};
use crate::error::{Error, Result};
#[cfg(test)]
use crate::validation::bag_semantics::{
    bag_difference_exists_sql, diff_sample_sql, query_json_sql,
};
use crate::validation::determinism::reject_volatile_program;
#[cfg(test)]
use crate::validation::observation::{ObservationMode, classify_observation};
use crate::validation::postgres_session::{
    fresh_schema_name, setup_output_schema_probe, setup_witness_schema,
};
use crate::validation::schema::{describe_statement_output, output_program_mismatch};
use crate::validation::types::{
    CheckResult, FormalWitnessColumn, FormalWitnessRow, FormalWitnessSnapshot, FormalWitnessTable,
    FormalWitnessValue, OutputSchemaPreflight, OutputSchemaPreflightResult, StatementOutput,
    WitnessCheck, WitnessValidation,
};
#[cfg(test)]
use crate::validation::types::{ObservationCertificateUse, ObservationComparison, OutputSchema};

#[derive(Debug, Clone)]
pub struct PostgresValidator {
    url: String,
    statement_timeout_ms: u64,
    #[cfg(test)]
    diff_sample_limit: usize,
    sql_time_zone: SqlTimeZone,
    sql_environment: SqlEnvironment,
}

impl PostgresValidator {
    pub fn new(
        url: Option<String>,
        statement_timeout_ms: u64,
        sql_time_zone: SqlTimeZone,
        sql_environment: SqlEnvironment,
    ) -> Result<Self> {
        let url = url
            .or_else(|| std::env::var("LOGOS_POSTGRES_URL").ok())
            .or_else(|| std::env::var("DATABASE_URL").ok())
            .ok_or(Error::MissingPostgresUrl)?;
        Ok(Self {
            url,
            statement_timeout_ms,
            #[cfg(test)]
            diff_sample_limit: 20,
            sql_time_zone,
            sql_environment,
        })
    }

    #[cfg(test)]
    pub fn validate(&self, input: &VerificationInput, witness_sql: &str) -> WitnessCheck {
        self.validate_with_observation_certificates(input, witness_sql, None)
    }

    #[cfg(test)]
    pub(crate) fn validate_with_observation_certificates(
        &self,
        input: &VerificationInput,
        witness_sql: &str,
        certificates: Option<&ObservationCertificateReport>,
    ) -> WitnessCheck {
        self.validate_internal(input, witness_sql, certificates)
            .check
    }

    /// Type-check candidate DML against PostgreSQL, enforce the benchmark
    /// integrity contract, and freeze the resulting database as a complete
    /// typed FormalSQL witness. Source and target queries are deliberately not
    /// executed: only the trusted FormalSQL/Rocq selector may decide whether
    /// this database separates their possible outcomes.
    pub(crate) fn materialize_formal_witness(
        &self,
        input: &VerificationInput,
        witness_sql: &str,
        formal_schema: &FormalSchema,
    ) -> WitnessValidation {
        let schema_name = fresh_schema_name();
        match self.try_materialize_formal_witness(input, witness_sql, &schema_name, formal_schema) {
            Ok(snapshot) => {
                let row_count = snapshot.tables.iter().fold(0usize, |count, table| {
                    count.saturating_add(table.rows.len())
                });
                WitnessValidation {
                    check: WitnessCheck {
                        schema_name,
                        warnings: Vec::new(),
                        result: CheckResult::WitnessMaterialized {
                            table_count: snapshot.tables.len(),
                            row_count,
                        },
                    },
                    snapshot: Some(snapshot),
                }
            }
            Err(error) => WitnessValidation {
                check: WitnessCheck {
                    schema_name,
                    warnings: Vec::new(),
                    result: CheckResult::ValidationError {
                        message: error.to_string(),
                    },
                },
                snapshot: None,
            },
        }
    }

    #[cfg(test)]
    fn validate_internal(
        &self,
        input: &VerificationInput,
        witness_sql: &str,
        certificates: Option<&ObservationCertificateReport>,
    ) -> WitnessValidation {
        let schema_name = fresh_schema_name();
        match self.try_validate(input, witness_sql, &schema_name, certificates) {
            Ok(mut validation) => {
                validation.check.schema_name = schema_name;
                validation
            }
            Err(error) => WitnessValidation {
                check: WitnessCheck {
                    schema_name,
                    warnings: Vec::new(),
                    result: CheckResult::ValidationError {
                        message: error.to_string(),
                    },
                },
                snapshot: None,
            },
        }
    }

    pub fn preflight_output_schema(&self, input: &VerificationInput) -> OutputSchemaPreflight {
        let schema_name = fresh_schema_name();
        let result = self
            .try_preflight_output_schema(input, &schema_name)
            .unwrap_or_else(|error| OutputSchemaPreflightResult::ValidationError {
                message: error.to_string(),
            });
        OutputSchemaPreflight {
            schema_name,
            result,
        }
    }

    fn try_preflight_output_schema(
        &self,
        input: &VerificationInput,
        schema_name: &str,
    ) -> Result<OutputSchemaPreflightResult> {
        self.ensure_integrity_environment(input)?;
        let source_program = input.source_sql_program()?;
        let target_program = input.target_sql_program()?;
        let mut client = Client::connect(&self.url, NoTls)?;
        let mut transaction = begin_validation_transaction(&mut client)?;
        setup_output_schema_probe(
            &mut transaction,
            schema_name,
            self.statement_timeout_ms,
            &self.sql_time_zone,
            &self.sql_environment,
            input.schema_sql(),
        )?;
        validate_integrity_contract(
            &mut transaction,
            input.integrity_contract().validation_checks(),
        )?;

        // Describe every statement before drawing a non-equivalence conclusion.
        // A lexical program-length or early output mismatch must not hide a
        // later PostgreSQL parse/type error in either submitted program.
        let source = describe_output_program(&mut transaction, &source_program)?;
        let target = describe_output_program(&mut transaction, &target_program)?;
        let result = if let Some(mismatch) = output_program_mismatch(&source, &target) {
            OutputSchemaPreflightResult::Mismatch { mismatch }
        } else {
            reject_volatile_successful_pairs(
                &mut transaction,
                &source_program,
                &target_program,
                &source,
                &target,
            )?;
            OutputSchemaPreflightResult::Compatible { source, target }
        };
        transaction.rollback()?;
        Ok(result)
    }

    #[cfg(test)]
    fn try_validate(
        &self,
        input: &VerificationInput,
        witness_sql: &str,
        schema_name: &str,
        certificates: Option<&ObservationCertificateReport>,
    ) -> Result<WitnessValidation> {
        self.ensure_integrity_environment(input)?;
        let source_program = input.source_sql_program()?;
        let target_program = input.target_sql_program()?;
        let mut warnings = Vec::new();
        let mut rejection_messages = Vec::new();
        let mut observation_modes = Vec::with_capacity(source_program.len());
        for (index, (source_query, target_query)) in
            source_program.iter().zip(target_program.iter()).enumerate()
        {
            let statement = index + 1;
            let observation = classify_observation(source_query, target_query);
            if observation.mode == ObservationMode::Unclassifiable {
                rejection_messages.push(format!(
                    "statement {statement}: {}",
                    observation.rejection_message()
                ));
            }
            observation_modes.push(observation.mode);
            warnings.extend(observation.warnings.into_iter().map(|mut warning| {
                warning.code = format!("statement_{statement}_{}", warning.code);
                warning.message = format!("statement {statement}: {}", warning.message);
                warning
            }));
        }
        if !rejection_messages.is_empty() {
            return Ok(WitnessValidation {
                check: WitnessCheck {
                    schema_name: String::new(),
                    result: CheckResult::ValidationError {
                        message: rejection_messages.join("; "),
                    },
                    warnings,
                },
                snapshot: None,
            });
        }

        let mut client = Client::connect(&self.url, NoTls)?;
        let mut transaction = begin_validation_transaction(&mut client)?;
        setup_witness_schema(
            &mut transaction,
            schema_name,
            self.statement_timeout_ms,
            &self.sql_time_zone,
            &self.sql_environment,
            input.schema_sql(),
            witness_sql,
        )?;
        validate_integrity_contract(
            &mut transaction,
            input.integrity_contract().validation_checks(),
        )?;

        let source_outputs = describe_output_program(&mut transaction, &source_program)?;
        let target_outputs = describe_output_program(&mut transaction, &target_program)?;
        if let Some(mismatch) = output_program_mismatch(&source_outputs, &target_outputs) {
            transaction.rollback()?;
            return Ok(WitnessValidation {
                check: WitnessCheck {
                    schema_name: String::new(),
                    warnings,
                    result: CheckResult::OutputSchemaMismatch { mismatch },
                },
                snapshot: None,
            });
        }
        reject_volatile_successful_pairs(
            &mut transaction,
            &source_program,
            &target_program,
            &source_outputs,
            &target_outputs,
        )?;

        for (index, (((source_query, target_query), observation_mode), outputs)) in source_program
            .iter()
            .zip(target_program.iter())
            .zip(observation_modes)
            .zip(source_outputs.iter().zip(target_outputs.iter()))
            .enumerate()
        {
            if matches!(
                outputs,
                (
                    StatementOutput::AnalysisError { .. },
                    StatementOutput::AnalysisError { .. }
                )
            ) {
                continue;
            }
            debug_assert!(matches!(
                outputs,
                (
                    StatementOutput::Success { .. },
                    StatementOutput::Success { .. }
                )
            ));
            if observation_mode == ObservationMode::ExecutableSequence {
                // The simple-query protocol observes the submitted statements
                // directly and preserves their returned row order: no
                // row_number/window wrapper can create an order or let the
                // planner prune target expressions.  Its cells are text,
                // however, and PostgreSQL can render equal SQL values
                // differently (for example NUMERIC 1.0 and 1.00).  Reparse the
                // returned cells at their attested output types and ask
                // PostgreSQL for IS NOT DISTINCT FROM equality row by row.
                let source_rows = executable_rows(&mut transaction, source_query)?;
                let target_rows = executable_rows(&mut transaction, target_query)?;
                let output_schema = match outputs {
                    (StatementOutput::Success { schema }, StatementOutput::Success { .. }) => {
                        schema
                    }
                    _ => unreachable!("analysis-error pairs were handled above"),
                };
                if let Some(first_differing_row) = first_semantically_differing_row(
                    &mut transaction,
                    &source_rows,
                    &target_rows,
                    output_schema,
                )? {
                    let source_result =
                        sequence_sample(&source_rows, first_differing_row, self.diff_sample_limit);
                    let target_result =
                        sequence_sample(&target_rows, first_differing_row, self.diff_sample_limit);
                    let authority =
                        observation_authority(certificates, index, ObservationComparison::Sequence);
                    transaction.rollback()?;
                    return Ok(WitnessValidation {
                        check: WitnessCheck {
                            schema_name: String::new(),
                            warnings,
                            result: match authority {
                                Ok(certificate) => CheckResult::RowSequenceDifference {
                                    statement: index + 1,
                                    first_differing_row,
                                    source_result,
                                    target_result,
                                    certificate,
                                },
                                Err(reason) => CheckResult::InconclusiveObservation {
                                    statement: index + 1,
                                    comparison: ObservationComparison::Sequence,
                                    reason,
                                    source_result,
                                    target_result,
                                },
                            },
                        },
                        snapshot: None,
                    });
                }
                continue;
            }
            debug_assert_eq!(observation_mode, ObservationMode::Bag);
            let different_sql = bag_difference_exists_sql(source_query, target_query);
            let different: bool = transaction.query_one(&different_sql, &[])?.get(0);
            if !different {
                continue;
            }

            let source_result: String = transaction
                .query_one(
                    &query_json_sql(source_query, self.diff_sample_limit, "source"),
                    &[],
                )?
                .get(0);
            let target_result: String = transaction
                .query_one(
                    &query_json_sql(target_query, self.diff_sample_limit, "target"),
                    &[],
                )?
                .get(0);
            let diff_sample: String = transaction
                .query_one(
                    &diff_sample_sql(source_query, target_query, self.diff_sample_limit),
                    &[],
                )?
                .get(0);

            let authority = observation_authority(certificates, index, ObservationComparison::Bag);

            transaction.rollback()?;
            return Ok(WitnessValidation {
                check: WitnessCheck {
                    schema_name: String::new(),
                    warnings,
                    result: match authority {
                        Ok(certificate) => CheckResult::DataDifference {
                            statement: index + 1,
                            source_result,
                            target_result,
                            diff_sample,
                            certificate,
                        },
                        Err(reason) => CheckResult::InconclusiveObservation {
                            statement: index + 1,
                            comparison: ObservationComparison::Bag,
                            reason,
                            source_result,
                            target_result,
                        },
                    },
                },
                snapshot: None,
            });
        }

        transaction.rollback()?;
        Ok(WitnessValidation {
            check: WitnessCheck {
                schema_name: String::new(),
                warnings,
                result: CheckResult::NoDifference,
            },
            snapshot: None,
        })
    }

    fn try_materialize_formal_witness(
        &self,
        input: &VerificationInput,
        witness_sql: &str,
        schema_name: &str,
        formal_schema: &FormalSchema,
    ) -> Result<FormalWitnessSnapshot> {
        self.ensure_integrity_environment(input)?;
        let mut client = Client::connect(&self.url, NoTls)?;
        let mut transaction = begin_validation_transaction(&mut client)?;
        setup_witness_schema(
            &mut transaction,
            schema_name,
            self.statement_timeout_ms,
            &self.sql_time_zone,
            &self.sql_environment,
            input.schema_sql(),
            witness_sql,
        )?;
        validate_integrity_contract(
            &mut transaction,
            input.integrity_contract().validation_checks(),
        )?;
        let snapshot =
            extract_formal_witness_snapshot(&mut transaction, schema_name, formal_schema)?;
        transaction.rollback()?;
        Ok(snapshot)
    }

    fn ensure_integrity_environment(&self, input: &VerificationInput) -> Result<()> {
        input.ensure_integrity_environment()?;
        if input
            .integrity_contract()
            .requires_postgres_utf8_c_text_semantics
            && !self.sql_environment.has_postgres_utf8_c_text_semantics()
        {
            return Err(Error::InvalidSqlEnvironment(format!(
                "PostgreSQL analysis/materialization boundary for benchmark integrity contract {} requires LC_COLLATE=C, LC_CTYPE=C, locale provider libc, and server encoding UTF8; the validator is configured with LC_COLLATE={}, LC_CTYPE={}, locale provider {}, and server encoding {}",
                input
                    .integrity_contract()
                    .case_id
                    .as_deref()
                    .unwrap_or("<unknown>"),
                self.sql_environment.default_collation_label(),
                self.sql_environment.character_classification_label(),
                self.sql_environment.locale_provider_label(),
                self.sql_environment.server_encoding_label(),
            )));
        }
        Ok(())
    }
}

const FORMAL_WITNESS_SNAPSHOT_SCHEMA_VERSION: u32 = 1;

/// Preserve PostgreSQL's NUMERIC wire value without routing it through the
/// server's locale- or display-sensitive text output.
struct PostgresNumericBinary(Vec<u8>);

impl<'a> FromSql<'a> for PostgresNumericBinary {
    fn from_sql(
        _ty: &Type,
        raw: &'a [u8],
    ) -> std::result::Result<Self, Box<dyn std::error::Error + Sync + Send>> {
        Ok(Self(raw.to_vec()))
    }

    fn accepts(ty: &Type) -> bool {
        ty == &Type::NUMERIC
    }
}

macro_rules! postgres_i64_binary_type {
    ($name:ident, $postgres_type:expr) => {
        struct $name(i64);

        impl<'a> FromSql<'a> for $name {
            fn from_sql(
                _ty: &Type,
                raw: &'a [u8],
            ) -> std::result::Result<Self, Box<dyn std::error::Error + Sync + Send>> {
                let bytes: [u8; 8] = raw.try_into().map_err(|_| {
                    std::io::Error::new(
                        std::io::ErrorKind::InvalidData,
                        format!("expected 8-byte PostgreSQL value, got {} bytes", raw.len()),
                    )
                })?;
                Ok(Self(i64::from_be_bytes(bytes)))
            }

            fn accepts(ty: &Type) -> bool {
                ty == &$postgres_type
            }
        }
    };
}

postgres_i64_binary_type!(PostgresTimeBinary, Type::TIME);
postgres_i64_binary_type!(PostgresTimestampBinary, Type::TIMESTAMP);
postgres_i64_binary_type!(PostgresTimestamptzBinary, Type::TIMESTAMPTZ);

struct PostgresDateBinary(i32);

impl<'a> FromSql<'a> for PostgresDateBinary {
    fn from_sql(
        _ty: &Type,
        raw: &'a [u8],
    ) -> std::result::Result<Self, Box<dyn std::error::Error + Sync + Send>> {
        let bytes: [u8; 4] = raw.try_into().map_err(|_| {
            std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                format!("expected 4-byte PostgreSQL DATE, got {} bytes", raw.len()),
            )
        })?;
        Ok(Self(i32::from_be_bytes(bytes)))
    }

    fn accepts(ty: &Type) -> bool {
        ty == &Type::DATE
    }
}

fn extract_formal_witness_snapshot(
    transaction: &mut Transaction<'_>,
    schema_name: &str,
    formal_schema: &FormalSchema,
) -> Result<FormalWitnessSnapshot> {
    let qualified_schema = quote_postgres_identifier(schema_name)?;
    let mut tables = Vec::with_capacity(formal_schema.tables.len());

    for table in &formal_schema.tables {
        let relation = quote_postgres_identifier(&table.relation)?;
        let qualified_relation = format!("{qualified_schema}.{relation}");
        let columns = table
            .attributes
            .iter()
            .map(|attribute| FormalWitnessColumn {
                name: attribute.name.clone(),
                ty: attribute.ty,
            })
            .collect::<Vec<_>>();

        let mut rows = if table.attributes.is_empty() {
            let count: i64 = transaction
                .query_one(
                    &format!("SELECT count(*)::pg_catalog.int8 FROM {qualified_relation}"),
                    &[],
                )?
                .get(0);
            let count = usize::try_from(count).map_err(|_| {
                Error::PostgresQueryInspection(format!(
                    "zero-column relation {} has invalid row count {count}",
                    table.relation
                ))
            })?;
            vec![FormalWitnessRow { cells: Vec::new() }; count]
        } else {
            let projection = table
                .attributes
                .iter()
                .map(|attribute| quote_postgres_identifier(&attribute.name))
                .collect::<Result<Vec<_>>>()?
                .join(", ");
            let statement =
                transaction.prepare(&format!("SELECT {projection} FROM {qualified_relation}"))?;
            if statement.columns().len() != table.attributes.len() {
                return Err(Error::PostgresQueryInspection(format!(
                    "typed witness query for {} returned {} columns, expected {}",
                    table.relation,
                    statement.columns().len(),
                    table.attributes.len()
                )));
            }
            let postgres_rows = transaction.query(&statement, &[])?;
            for (attribute, column) in table.attributes.iter().zip(statement.columns()) {
                if !(formal_type_accepts_postgres_type(attribute.ty, column.type_())
                    && formal_typmod_accepts_postgres_modifier(
                        attribute.ty,
                        column.type_modifier(),
                    ))
                {
                    return Err(Error::PostgresQueryInspection(format!(
                        "typed witness column {}.{} lowered as {:?}, but PostgreSQL reports {} (OID {}, typmod {})",
                        table.relation,
                        attribute.name,
                        attribute.ty,
                        column.type_().name(),
                        column.type_().oid(),
                        column.type_modifier()
                    )));
                }
                if !postgres_rows.is_empty() && !formal_snapshot_type_supported(attribute.ty) {
                    return Err(Error::PostgresQueryInspection(format!(
                        "typed FormalSQL witness snapshots do not yet support {:?} at {}.{}",
                        attribute.ty, table.relation, attribute.name
                    )));
                }
            }
            postgres_rows
                .iter()
                .map(|row| {
                    let cells = table
                        .attributes
                        .iter()
                        .enumerate()
                        .map(|(index, attribute)| {
                            decode_formal_witness_value(row, index, attribute.ty)
                        })
                        .collect::<Result<Vec<_>>>()?;
                    Ok(FormalWitnessRow { cells })
                })
                .collect::<Result<Vec<_>>>()?
        };

        // SQL tables are bags.  PostgreSQL is free to enumerate a heap in any
        // physical order, so canonicalize only the artifact representation;
        // duplicates and therefore bag multiplicities remain intact.
        rows.sort();
        tables.push(FormalWitnessTable {
            relation: table.relation.clone(),
            columns,
            rows,
        });
    }

    Ok(FormalWitnessSnapshot {
        schema_version: FORMAL_WITNESS_SNAPSHOT_SCHEMA_VERSION,
        tables,
    })
}

fn formal_snapshot_type_supported(ty: FormalAttributeType) -> bool {
    matches!(
        ty,
        FormalAttributeType::Bool
            | FormalAttributeType::Int32
            | FormalAttributeType::Int64
            | FormalAttributeType::String { .. }
            | FormalAttributeType::Float
            | FormalAttributeType::Double
            | FormalAttributeType::Numeric
            | FormalAttributeType::Decimal { .. }
            | FormalAttributeType::Date
            | FormalAttributeType::Time
            | FormalAttributeType::Timestamp { .. }
            | FormalAttributeType::Timestamptz { .. }
    )
}

fn formal_type_accepts_postgres_type(ty: FormalAttributeType, postgres_ty: &Type) -> bool {
    match ty {
        FormalAttributeType::Bool => postgres_ty == &Type::BOOL,
        FormalAttributeType::Int32 => postgres_ty == &Type::INT4,
        FormalAttributeType::Int64 => postgres_ty == &Type::INT8,
        FormalAttributeType::String { typmod } => match typmod {
            logos_ir::ir::SqlStringType::Text => postgres_ty == &Type::TEXT,
            logos_ir::ir::SqlStringType::Varchar { .. } => postgres_ty == &Type::VARCHAR,
            logos_ir::ir::SqlStringType::Char { .. } | logos_ir::ir::SqlStringType::Bpchar => {
                postgres_ty == &Type::BPCHAR
            }
        },
        FormalAttributeType::Numeric | FormalAttributeType::Decimal { .. } => {
            postgres_ty == &Type::NUMERIC
        }
        FormalAttributeType::Float => postgres_ty == &Type::FLOAT4,
        FormalAttributeType::Double => postgres_ty == &Type::FLOAT8,
        FormalAttributeType::Date => postgres_ty == &Type::DATE,
        FormalAttributeType::Time => postgres_ty == &Type::TIME,
        FormalAttributeType::Timestamp { .. } => postgres_ty == &Type::TIMESTAMP,
        FormalAttributeType::Timestamptz { .. } => postgres_ty == &Type::TIMESTAMPTZ,
        FormalAttributeType::Z => false,
    }
}

fn formal_typmod_accepts_postgres_modifier(ty: FormalAttributeType, postgres_typmod: i32) -> bool {
    if postgres_typmod == -1
        && matches!(
            ty,
            FormalAttributeType::Time
                | FormalAttributeType::Timestamp { precision: Some(6) }
                | FormalAttributeType::Timestamptz { precision: Some(6) }
        )
    {
        // PostgreSQL records an omitted temporal typmod as -1, while the
        // lowering normalizes its effective default precision to six.
        return true;
    }
    let expected = match ty {
        FormalAttributeType::String {
            typmod:
                logos_ir::ir::SqlStringType::Varchar {
                    length: Some(length),
                },
        }
        | FormalAttributeType::String {
            typmod: logos_ir::ir::SqlStringType::Char { length },
        } => i32::try_from(length)
            .ok()
            .and_then(|length| length.checked_add(4)),
        FormalAttributeType::Decimal { precision, scale } => {
            let packed = (u64::from(precision) << 16) | u64::from(scale);
            i32::try_from(packed)
                .ok()
                .and_then(|value| value.checked_add(4))
        }
        FormalAttributeType::Timestamp {
            precision: Some(precision),
        }
        | FormalAttributeType::Timestamptz {
            precision: Some(precision),
        } => i32::try_from(precision).ok(),
        FormalAttributeType::String {
            typmod:
                logos_ir::ir::SqlStringType::Text
                | logos_ir::ir::SqlStringType::Varchar { length: None }
                | logos_ir::ir::SqlStringType::Bpchar,
        }
        | FormalAttributeType::Z
        | FormalAttributeType::Int32
        | FormalAttributeType::Int64
        | FormalAttributeType::Bool
        | FormalAttributeType::Float
        | FormalAttributeType::Double
        | FormalAttributeType::Numeric
        | FormalAttributeType::Date
        | FormalAttributeType::Timestamp { precision: None }
        | FormalAttributeType::Timestamptz { precision: None } => Some(-1),
        // FormalSQL's TIME carrier has microsecond precision but no separate
        // declaration typmod. PostgreSQL TIME and TIME(6) therefore denote
        // the two source spellings of the same represented FormalSQL type.
        FormalAttributeType::Time => Some(6),
    };
    expected == Some(postgres_typmod)
}

fn decode_formal_witness_value(
    row: &postgres::Row,
    index: usize,
    ty: FormalAttributeType,
) -> Result<FormalWitnessValue> {
    Ok(match ty {
        FormalAttributeType::Bool => row
            .try_get::<_, Option<bool>>(index)?
            .map_or(FormalWitnessValue::Null, FormalWitnessValue::Bool),
        FormalAttributeType::Int32 => row
            .try_get::<_, Option<i32>>(index)?
            .map_or(FormalWitnessValue::Null, FormalWitnessValue::Int32),
        FormalAttributeType::Int64 => row
            .try_get::<_, Option<i64>>(index)?
            .map_or(FormalWitnessValue::Null, FormalWitnessValue::Int64),
        FormalAttributeType::String { typmod } => row
            .try_get::<_, Option<String>>(index)?
            .map(|value| canonical_formal_witness_string(typmod, value))
            .map_or(FormalWitnessValue::Null, FormalWitnessValue::String),
        FormalAttributeType::Float => row
            .try_get::<_, Option<f32>>(index)?
            .map(|value| FormalWitnessValue::Float32Bits(value.to_bits()))
            .unwrap_or(FormalWitnessValue::Null),
        FormalAttributeType::Double => row
            .try_get::<_, Option<f64>>(index)?
            .map(|value| FormalWitnessValue::Float64Bits(value.to_bits()))
            .unwrap_or(FormalWitnessValue::Null),
        FormalAttributeType::Numeric | FormalAttributeType::Decimal { .. } => {
            match row.try_get::<_, Option<PostgresNumericBinary>>(index)? {
                None => FormalWitnessValue::Null,
                Some(value) => decode_postgres_numeric_binary(&value.0)?,
            }
        }
        FormalAttributeType::Date => match row.try_get::<_, Option<PostgresDateBinary>>(index)? {
            None => FormalWitnessValue::Null,
            Some(date) => FormalWitnessValue::Date(postgres_date_days(date.0)?),
        },
        FormalAttributeType::Time => match row.try_get::<_, Option<PostgresTimeBinary>>(index)? {
            None => FormalWitnessValue::Null,
            Some(time) => FormalWitnessValue::Time(postgres_time_micros(time.0)?),
        },
        FormalAttributeType::Timestamp { .. } => {
            match row.try_get::<_, Option<PostgresTimestampBinary>>(index)? {
                None => FormalWitnessValue::Null,
                Some(timestamp) => {
                    FormalWitnessValue::Timestamp(postgres_timestamp_micros(timestamp.0)?)
                }
            }
        }
        FormalAttributeType::Timestamptz { .. } => {
            match row.try_get::<_, Option<PostgresTimestamptzBinary>>(index)? {
                None => FormalWitnessValue::Null,
                Some(timestamp) => {
                    FormalWitnessValue::Timestamptz(postgres_timestamp_micros(timestamp.0)?)
                }
            }
        }
        unsupported => {
            return Err(Error::PostgresQueryInspection(format!(
                "typed FormalSQL witness snapshots do not yet support {unsupported:?}"
            )));
        }
    })
}

fn decode_postgres_numeric_binary(raw: &[u8]) -> Result<FormalWitnessValue> {
    const NUMERIC_POS: u16 = 0x0000;
    const NUMERIC_NEG: u16 = 0x4000;
    const NUMERIC_NAN: u16 = 0xC000;
    const NUMERIC_PINF: u16 = 0xD000;
    const NUMERIC_NINF: u16 = 0xF000;

    if raw.len() < 8 || (raw.len() - 8) % 2 != 0 {
        return Err(Error::PostgresQueryInspection(format!(
            "invalid PostgreSQL NUMERIC binary length {}",
            raw.len()
        )));
    }
    let read_u16 = |offset: usize| u16::from_be_bytes([raw[offset], raw[offset + 1]]);
    let ndigits = usize::from(read_u16(0));
    let weight = i16::from_be_bytes([raw[2], raw[3]]);
    let sign = read_u16(4);
    let dscale = read_u16(6);
    if raw.len() != 8 + ndigits * 2 {
        return Err(Error::PostgresQueryInspection(format!(
            "PostgreSQL NUMERIC binary declares {ndigits} digits in {} bytes",
            raw.len()
        )));
    }
    if dscale > 0x3fff {
        return Err(Error::PostgresQueryInspection(format!(
            "PostgreSQL NUMERIC binary has invalid display scale {dscale}"
        )));
    }
    match sign {
        NUMERIC_NAN | NUMERIC_PINF | NUMERIC_NINF => {
            if ndigits != 0 || weight != 0 {
                return Err(Error::PostgresQueryInspection(
                    "PostgreSQL special NUMERIC binary is not canonical".to_owned(),
                ));
            }
            return Ok(match sign {
                NUMERIC_NAN => FormalWitnessValue::NumericNaN,
                NUMERIC_PINF => FormalWitnessValue::NumericPosInfinity,
                NUMERIC_NINF => FormalWitnessValue::NumericNegInfinity,
                _ => unreachable!(),
            });
        }
        NUMERIC_POS | NUMERIC_NEG => {}
        other => {
            return Err(Error::PostgresQueryInspection(format!(
                "PostgreSQL NUMERIC binary has unknown sign 0x{other:04x}"
            )));
        }
    }

    if ndigits == 0 {
        return Ok(FormalWitnessValue::NumericFinite {
            coefficient: "0".to_owned(),
            scale: 0,
        });
    }
    let mut groups = Vec::with_capacity(ndigits);
    for index in 0..ndigits {
        let offset = 8 + index * 2;
        let digit = u16::from_be_bytes([raw[offset], raw[offset + 1]]);
        if digit >= 10_000 {
            return Err(Error::PostgresQueryInspection(format!(
                "PostgreSQL NUMERIC binary digit {digit} is outside base 10000"
            )));
        }
        groups.push(digit);
    }
    if groups[0] == 0 {
        return Err(Error::PostgresQueryInspection(
            "PostgreSQL NUMERIC binary has a non-canonical leading zero group".to_owned(),
        ));
    }

    let mut coefficient = groups[0].to_string();
    for digit in &groups[1..] {
        coefficient.push_str(&format!("{digit:04}"));
    }
    let last_group_exponent = i32::from(weight) - (ndigits as i32 - 1);
    // A negative scale is an exact, compact power-of-ten multiplier in
    // [numeric_of_scaled].  Retaining it avoids expanding a ten-byte wire
    // value such as 1e131068 into a 131 KiB Rocq decimal literal.
    let mut scale = -last_group_exponent * 4;
    while coefficient.ends_with('0') {
        coefficient.pop();
        scale -= 1;
    }
    if sign == NUMERIC_NEG {
        coefficient.insert(0, '-');
    }
    Ok(FormalWitnessValue::NumericFinite { coefficient, scale })
}

fn canonical_formal_witness_string(typmod: logos_ir::ir::SqlStringType, value: String) -> String {
    match typmod {
        // PostgreSQL CHARACTER values have blank-padded physical storage, but
        // the FormalSQL carrier stores their canonical SQL value and
        // reconstructs padding from the declared width.  This operation is
        // idempotent if the PostgreSQL driver has already removed the padding.
        logos_ir::ir::SqlStringType::Char { .. } | logos_ir::ir::SqlStringType::Bpchar => {
            value.trim_end_matches(' ').to_owned()
        }
        logos_ir::ir::SqlStringType::Text | logos_ir::ir::SqlStringType::Varchar { .. } => value,
    }
}

fn postgres_date_days(postgres_days: i32) -> Result<i32> {
    const POSTGRES_EPOCH_DAYS_FROM_UNIX: i32 = 10_957;
    const FORMAL_DATE_NEG_INFINITY: i32 = -2_440_589;
    const FORMAL_DATE_POS_INFINITY: i32 = 2_145_042_906;
    match postgres_days {
        i32::MIN => Ok(FORMAL_DATE_NEG_INFINITY),
        i32::MAX => Ok(FORMAL_DATE_POS_INFINITY),
        value => value
            .checked_add(POSTGRES_EPOCH_DAYS_FROM_UNIX)
            .filter(|value| {
                *value >= FORMAL_DATE_NEG_INFINITY + 1 && *value < FORMAL_DATE_POS_INFINITY
            })
            .ok_or_else(|| {
                Error::PostgresQueryInspection(format!(
                    "PostgreSQL DATE day count {postgres_days} is outside the FormalSQL range"
                ))
            }),
    }
}

fn postgres_time_micros(value: i64) -> Result<i64> {
    const MICROS_PER_DAY: i64 = 86_400_000_000;
    (0..=MICROS_PER_DAY)
        .contains(&value)
        .then_some(value)
        .ok_or_else(|| {
            Error::PostgresQueryInspection(format!(
                "PostgreSQL TIME value {value} is outside one civil day"
            ))
        })
}

fn postgres_timestamp_micros(postgres_micros: i64) -> Result<String> {
    const POSTGRES_EPOCH_MICROS_FROM_UNIX: i128 = 946_684_800_000_000;
    const FORMAL_TIMESTAMP_MIN: i128 = -210_866_803_200_000_000;
    const FORMAL_TIMESTAMP_END: i128 = 9_224_318_016_000_000_000;
    const FORMAL_TIMESTAMP_NEG_INFINITY: i128 = FORMAL_TIMESTAMP_MIN - 1;
    const FORMAL_TIMESTAMP_POS_INFINITY: i128 = FORMAL_TIMESTAMP_END;
    let value = match postgres_micros {
        i64::MIN => FORMAL_TIMESTAMP_NEG_INFINITY,
        i64::MAX => FORMAL_TIMESTAMP_POS_INFINITY,
        value => {
            let value = i128::from(value) + POSTGRES_EPOCH_MICROS_FROM_UNIX;
            if !(FORMAL_TIMESTAMP_MIN..FORMAL_TIMESTAMP_END).contains(&value) {
                return Err(Error::PostgresQueryInspection(format!(
                    "PostgreSQL timestamp {postgres_micros} is outside the FormalSQL range"
                )));
            }
            value
        }
    };
    Ok(value.to_string())
}

fn quote_postgres_identifier(identifier: &str) -> Result<String> {
    if identifier.contains('\0') {
        return Err(Error::PostgresQueryInspection(
            "PostgreSQL identifier contains a NUL byte".to_owned(),
        ));
    }
    Ok(format!("\"{}\"", identifier.replace('"', "\"\"")))
}

#[cfg(test)]
fn observation_authority(
    certificates: Option<&ObservationCertificateReport>,
    statement_index: usize,
    comparison: ObservationComparison,
) -> std::result::Result<ObservationCertificateUse, String> {
    let Some(certificates) = certificates else {
        return Err(
            "no host-recomputed FormalQueryExpr observation certificate was supplied; a concrete PostgreSQL execution is not a complete possible-outcome relation"
                .to_owned(),
        );
    };
    let statement = statement_index + 1;
    let Some(source) = certificates.source.get(statement_index) else {
        return Err(format!(
            "source observation analysis has no statement {statement}"
        ));
    };
    let Some(target) = certificates.target.get(statement_index) else {
        return Err(format!(
            "target observation analysis has no statement {statement}"
        ));
    };
    let (source_proven, target_proven, source_derivation, target_derivation) = match comparison {
        ObservationComparison::Bag => (
            source.success_bag_is_functional(),
            target.success_bag_is_functional(),
            source.bag_residual(),
            target.bag_residual(),
        ),
        ObservationComparison::Sequence => (
            source.success_observation_is_functional(),
            target.success_observation_is_functional(),
            source.observation_residual(),
            target.observation_residual(),
        ),
    };
    // One functional side is sufficient for a directional separation. If the
    // target is functional, the observed source success cannot match any
    // target success; source functionality gives the symmetric direction.
    if !source_proven && !target_proven {
        return Err(format!(
            "the concrete {comparison:?} difference is not authoritative because success functionality was proved on neither side (source: {source_derivation}; target: {target_derivation}); supply a one-sided uniqueness certificate or a FormalSQL outcome-separation countermodel"
        ));
    }
    Ok(ObservationCertificateUse {
        schema_version: certificates.schema_version,
        verification_input_key: certificates.verification_input_key.clone(),
        verification_input_sha256: certificates.verification_input_sha256.clone(),
        lowering_sha256: certificates.lowering_sha256.clone(),
        statement,
        comparison,
        source_derivation,
        target_derivation,
    })
}

#[cfg(test)]
type ExecutableRow = Vec<Option<String>>;

#[cfg(test)]
fn executable_rows(transaction: &mut Transaction<'_>, query: &str) -> Result<Vec<ExecutableRow>> {
    let mut rows = Vec::new();
    for message in transaction.simple_query(query)? {
        if let SimpleQueryMessage::Row(row) = message {
            rows.push(
                (0..row.len())
                    .map(|index| row.get(index).map(ToOwned::to_owned))
                    .collect(),
            );
        }
    }
    Ok(rows)
}

#[cfg(test)]
fn first_semantically_differing_row(
    transaction: &mut Transaction<'_>,
    source: &[ExecutableRow],
    target: &[ExecutableRow],
    schema: &OutputSchema,
) -> Result<Option<usize>> {
    for (index, (source_row, target_row)) in source.iter().zip(target).enumerate() {
        if !executable_rows_semantically_equal(transaction, source_row, target_row, schema)? {
            return Ok(Some(index + 1));
        }
    }
    Ok((source.len() != target.len()).then(|| source.len().min(target.len()) + 1))
}

#[cfg(test)]
fn executable_rows_semantically_equal(
    transaction: &mut Transaction<'_>,
    source: &ExecutableRow,
    target: &ExecutableRow,
    schema: &OutputSchema,
) -> Result<bool> {
    if source.len() != schema.columns.len() || target.len() != schema.columns.len() {
        return Err(Error::PostgresQueryInspection(format!(
            "ordered result row has source/target widths {}/{} but the attested output schema has {} columns",
            source.len(),
            target.len(),
            schema.columns.len()
        )));
    }
    if schema.columns.is_empty() {
        return Ok(true);
    }

    let mut predicates = Vec::with_capacity(schema.columns.len());
    for (index, column) in schema.columns.iter().enumerate() {
        let cast = postgres_builtin_value_cast(column.type_oid).ok_or_else(|| {
            Error::PostgresQueryInspection(format!(
                "ordered semantic comparison does not support PostgreSQL output type {} (OID {}) at column {}",
                column.type_name, column.type_oid, column.ordinal
            ))
        })?;
        let left = index + 1;
        let right = schema.columns.len() + index + 1;
        predicates.push(format!(
            "((${}::text)::{cast} IS NOT DISTINCT FROM (${}::text)::{cast})",
            left, right
        ));
    }
    let sql = format!("SELECT {}", predicates.join(" AND "));
    let values = source
        .iter()
        .chain(target)
        .map(|value| value.as_deref())
        .collect::<Vec<_>>();
    let parameters = values
        .iter()
        .map(|value| value as &(dyn ToSql + Sync))
        .collect::<Vec<_>>();
    Ok(transaction.query_one(&sql, &parameters)?.get(0))
}

#[cfg(test)]
fn postgres_builtin_value_cast(type_oid: u32) -> Option<&'static str> {
    // These are exactly the PostgreSQL scalar families represented by the
    // current FormalSQL TNull lowering.  OIDs are stable bootstrap OIDs; using
    // a closed mapping also prevents a schema-defined type name from entering
    // generated validator SQL.
    match type_oid {
        16 => Some("pg_catalog.bool"),
        20 => Some("pg_catalog.int8"),
        23 => Some("pg_catalog.int4"),
        25 => Some("pg_catalog.text"),
        700 => Some("pg_catalog.float4"),
        701 => Some("pg_catalog.float8"),
        1042 => Some("pg_catalog.bpchar"),
        1043 => Some("pg_catalog.varchar"),
        1082 => Some("pg_catalog.date"),
        1083 => Some("pg_catalog.time"),
        1114 => Some("pg_catalog.timestamp"),
        1184 => Some("pg_catalog.timestamptz"),
        1700 => Some("pg_catalog.numeric"),
        _ => None,
    }
}

#[cfg(test)]
fn sequence_sample(rows: &[ExecutableRow], first_differing_row: usize, limit: usize) -> String {
    let limit = limit.max(1);
    let difference_index = first_differing_row.saturating_sub(1);
    let start = difference_index.saturating_sub(limit / 2).min(rows.len());
    let end = start.saturating_add(limit).min(rows.len());
    serde_json::json!({
        "totalRows": rows.len(),
        "firstSampledRow": start + 1,
        "rows": &rows[start..end],
    })
    .to_string()
}

#[cfg(test)]
mod formal_witness_snapshot_tests {
    use super::*;
    use crate::core::{FormalAttribute, FormalTable, FormalTableConstraints};
    use logos_ir::ir::SqlStringType;

    #[test]
    fn supported_snapshot_types_have_exact_binary_postgres_types() {
        assert!(formal_type_accepts_postgres_type(
            FormalAttributeType::Bool,
            &Type::BOOL
        ));
        assert!(formal_type_accepts_postgres_type(
            FormalAttributeType::Int32,
            &Type::INT4
        ));
        assert!(formal_type_accepts_postgres_type(
            FormalAttributeType::Int64,
            &Type::INT8
        ));
        assert!(formal_type_accepts_postgres_type(
            FormalAttributeType::String {
                typmod: SqlStringType::Text,
            },
            &Type::TEXT
        ));
        assert!(formal_type_accepts_postgres_type(
            FormalAttributeType::String {
                typmod: SqlStringType::Varchar { length: Some(12) },
            },
            &Type::VARCHAR
        ));
        assert!(formal_type_accepts_postgres_type(
            FormalAttributeType::String {
                typmod: SqlStringType::Varchar { length: None },
            },
            &Type::VARCHAR
        ));
        assert!(formal_snapshot_type_supported(
            FormalAttributeType::String {
                typmod: SqlStringType::Char { length: 3 },
            }
        ));
        assert!(formal_type_accepts_postgres_type(
            FormalAttributeType::String {
                typmod: SqlStringType::Char { length: 3 },
            },
            &Type::BPCHAR
        ));
        assert!(formal_type_accepts_postgres_type(
            FormalAttributeType::String {
                typmod: SqlStringType::Bpchar,
            },
            &Type::BPCHAR
        ));
        assert!(!formal_type_accepts_postgres_type(
            FormalAttributeType::String {
                typmod: SqlStringType::Varchar { length: Some(12) },
            },
            &Type::TEXT
        ));
        assert!(formal_type_accepts_postgres_type(
            FormalAttributeType::Date,
            &Type::DATE
        ));

        assert!(!formal_type_accepts_postgres_type(
            FormalAttributeType::Int32,
            &Type::INT8
        ));
        assert!(formal_snapshot_type_supported(FormalAttributeType::Numeric));
        assert!(formal_type_accepts_postgres_type(
            FormalAttributeType::Numeric,
            &Type::NUMERIC
        ));
        assert!(formal_type_accepts_postgres_type(
            FormalAttributeType::Decimal {
                precision: 7,
                scale: 2,
            },
            &Type::NUMERIC
        ));
        assert!(formal_snapshot_type_supported(
            FormalAttributeType::Timestamp { precision: Some(6) }
        ));
        assert!(formal_type_accepts_postgres_type(
            FormalAttributeType::Float,
            &Type::FLOAT4
        ));
        assert!(formal_type_accepts_postgres_type(
            FormalAttributeType::Double,
            &Type::FLOAT8
        ));
        assert!(formal_type_accepts_postgres_type(
            FormalAttributeType::Time,
            &Type::TIME
        ));
        assert!(formal_type_accepts_postgres_type(
            FormalAttributeType::Timestamp { precision: Some(6) },
            &Type::TIMESTAMP
        ));
        assert!(formal_typmod_accepts_postgres_modifier(
            FormalAttributeType::Timestamp { precision: Some(6) },
            -1
        ));
        assert!(formal_typmod_accepts_postgres_modifier(
            FormalAttributeType::Time,
            -1
        ));
        assert!(formal_typmod_accepts_postgres_modifier(
            FormalAttributeType::Time,
            6
        ));
        assert!(!formal_typmod_accepts_postgres_modifier(
            FormalAttributeType::Time,
            3
        ));

        assert!(formal_typmod_accepts_postgres_modifier(
            FormalAttributeType::String {
                typmod: SqlStringType::Varchar { length: Some(7) },
            },
            11
        ));
        assert!(!formal_typmod_accepts_postgres_modifier(
            FormalAttributeType::String {
                typmod: SqlStringType::Varchar { length: Some(7) },
            },
            12
        ));
        assert!(formal_typmod_accepts_postgres_modifier(
            FormalAttributeType::String {
                typmod: SqlStringType::Varchar { length: None },
            },
            -1
        ));
        assert!(formal_typmod_accepts_postgres_modifier(
            FormalAttributeType::String {
                typmod: SqlStringType::Char { length: 3 },
            },
            7
        ));
        assert!(formal_typmod_accepts_postgres_modifier(
            FormalAttributeType::Decimal {
                precision: 7,
                scale: 2,
            },
            ((7_i32 << 16) | 2) + 4
        ));
        assert!(formal_typmod_accepts_postgres_modifier(
            FormalAttributeType::Numeric,
            -1
        ));
    }

    #[test]
    fn character_snapshot_values_use_formal_sql_canonical_storage() {
        assert_eq!(
            canonical_formal_witness_string(SqlStringType::Char { length: 5 }, "ab   ".to_owned()),
            "ab"
        );
        assert_eq!(
            canonical_formal_witness_string(SqlStringType::Bpchar, "ab   ".to_owned()),
            "ab"
        );
        assert_eq!(
            canonical_formal_witness_string(
                SqlStringType::Varchar { length: Some(5) },
                "ab   ".to_owned()
            ),
            "ab   "
        );
    }

    fn postgres_numeric_wire(
        ndigits: u16,
        weight: i16,
        sign: u16,
        dscale: i16,
        digits: &[u16],
    ) -> Vec<u8> {
        assert_eq!(usize::from(ndigits), digits.len());
        let mut raw = Vec::with_capacity(8 + digits.len() * 2);
        raw.extend_from_slice(&ndigits.to_be_bytes());
        raw.extend_from_slice(&weight.to_be_bytes());
        raw.extend_from_slice(&sign.to_be_bytes());
        raw.extend_from_slice(&dscale.to_be_bytes());
        for digit in digits {
            raw.extend_from_slice(&digit.to_be_bytes());
        }
        raw
    }

    #[test]
    fn numeric_snapshot_decoder_preserves_exact_decimal_values_and_specials() {
        assert_eq!(
            decode_postgres_numeric_binary(&postgres_numeric_wire(2, 0, 0x0000, 2, &[123, 4500]))
                .unwrap(),
            FormalWitnessValue::NumericFinite {
                coefficient: "12345".to_owned(),
                scale: 2,
            }
        );
        assert_eq!(
            decode_postgres_numeric_binary(&postgres_numeric_wire(1, -2, 0x4000, 5, &[1000]))
                .unwrap(),
            FormalWitnessValue::NumericFinite {
                coefficient: "-1".to_owned(),
                scale: 5,
            }
        );
        assert_eq!(
            decode_postgres_numeric_binary(&postgres_numeric_wire(1, 1, 0x0000, 0, &[1])).unwrap(),
            FormalWitnessValue::NumericFinite {
                coefficient: "1".to_owned(),
                scale: -4,
            }
        );
        assert_eq!(
            decode_postgres_numeric_binary(&postgres_numeric_wire(0, 0, 0xC000, 0, &[])).unwrap(),
            FormalWitnessValue::NumericNaN
        );
        assert_eq!(
            decode_postgres_numeric_binary(&postgres_numeric_wire(0, 0, 0xD000, 0, &[])).unwrap(),
            FormalWitnessValue::NumericPosInfinity
        );
        assert_eq!(
            decode_postgres_numeric_binary(&postgres_numeric_wire(0, 0, 0xF000, 0, &[])).unwrap(),
            FormalWitnessValue::NumericNegInfinity
        );
        assert!(decode_postgres_numeric_binary(&[0; 7]).is_err());
        assert!(
            decode_postgres_numeric_binary(&postgres_numeric_wire(1, 0, 0x0000, 0, &[10_000]))
                .is_err()
        );
        assert!(
            decode_postgres_numeric_binary(&postgres_numeric_wire(0, 0, 0x0000, 0x4000, &[]))
                .is_err()
        );
        assert!(
            decode_postgres_numeric_binary(&postgres_numeric_wire(1, 0, 0xC000, 0, &[1])).is_err()
        );
    }

    #[test]
    fn snapshot_identifier_quoting_and_date_epoch_are_canonical() {
        assert_eq!(
            quote_postgres_identifier("odd\"name").expect("quote identifier"),
            "\"odd\"\"name\""
        );
        assert!(quote_postgres_identifier("bad\0name").is_err());
        assert_eq!(postgres_date_days(-10_957).expect("encode epoch"), 0);
        assert_eq!(
            postgres_date_days(-10_958).expect("encode pre-epoch date"),
            -1
        );
        assert_eq!(postgres_date_days(i32::MIN).unwrap(), -2_440_589);
        assert_eq!(postgres_date_days(i32::MAX).unwrap(), 2_145_042_906);
        assert_eq!(
            postgres_time_micros(86_400_000_000).unwrap(),
            86_400_000_000
        );
        assert!(postgres_time_micros(86_400_000_001).is_err());
        assert_eq!(postgres_timestamp_micros(0).unwrap(), "946684800000000");
        assert_eq!(
            postgres_timestamp_micros(i64::MIN).unwrap(),
            "-210866803200000001"
        );
        assert_eq!(
            postgres_timestamp_micros(i64::MAX).unwrap(),
            "9224318016000000000"
        );
    }

    #[test]
    fn snapshot_rows_have_stable_bag_canonicalization() {
        let mut rows = [
            FormalWitnessRow {
                cells: vec![FormalWitnessValue::Int32(2)],
            },
            FormalWitnessRow {
                cells: vec![FormalWitnessValue::Null],
            },
            FormalWitnessRow {
                cells: vec![FormalWitnessValue::Int32(2)],
            },
            FormalWitnessRow {
                cells: vec![FormalWitnessValue::Int32(1)],
            },
        ];
        rows.sort();
        assert_eq!(rows[0].cells, vec![FormalWitnessValue::Null]);
        assert_eq!(rows[1].cells, vec![FormalWitnessValue::Int32(1)]);
        assert_eq!(rows[2], rows[3], "duplicate multiplicity must be retained");
    }

    #[test]
    #[ignore = "requires LOGOS_POSTGRES_URL or DATABASE_URL for a disposable PostgreSQL database"]
    fn extracts_all_formal_tables_with_typed_null_and_empty_rows() {
        let url = std::env::var("LOGOS_POSTGRES_URL")
            .or_else(|_| std::env::var("DATABASE_URL"))
            .expect("set LOGOS_POSTGRES_URL or DATABASE_URL");
        let mut client = Client::connect(&url, NoTls).expect("connect to disposable PostgreSQL");
        let mut transaction = begin_validation_transaction(&mut client).expect("begin transaction");
        let schema_name = fresh_schema_name();
        transaction
            .batch_execute(&format!(
                "CREATE SCHEMA {schema_name};\
                 CREATE TABLE {schema_name}.typed(\
                   flag boolean, n integer, wide bigint, label text, limited varchar(4),\
                   fixed char(4), amount decimal(7, 2), happened date,\
                   f32 real, f64 double precision, at time(6),\
                   ts timestamp, tstz timestamptz);\
                 CREATE TABLE {schema_name}.empty(n integer);\
                 CREATE TABLE {schema_name}.empty_unsupported(at time);\
                 INSERT INTO {schema_name}.typed VALUES\
                   (TRUE, 2, 9, 'two', 'four', 'xy', 12.30, DATE '2020-01-02',\
                    1.5, '-0', TIME '24:00:00',\
                    TIMESTAMP '2000-01-01 00:00:00',\
                    TIMESTAMPTZ '2000-01-01 00:00:00+00'),\
                   (NULL, 1, NULL, NULL, NULL, NULL, NULL, NULL,\
                    NULL, NULL, NULL, NULL, NULL);"
            ))
            .expect("create typed witness schema");
        let attribute = |name: &str, ty| FormalAttribute {
            name: name.to_owned(),
            ty,
        };
        let formal_schema = FormalSchema {
            tables: vec![
                FormalTable {
                    relation: "typed".to_owned(),
                    attributes: vec![
                        attribute("flag", FormalAttributeType::Bool),
                        attribute("n", FormalAttributeType::Int32),
                        attribute("wide", FormalAttributeType::Int64),
                        attribute(
                            "label",
                            FormalAttributeType::String {
                                typmod: SqlStringType::Text,
                            },
                        ),
                        attribute(
                            "limited",
                            FormalAttributeType::String {
                                typmod: SqlStringType::Varchar { length: Some(4) },
                            },
                        ),
                        attribute(
                            "fixed",
                            FormalAttributeType::String {
                                typmod: SqlStringType::Char { length: 4 },
                            },
                        ),
                        attribute(
                            "amount",
                            FormalAttributeType::Decimal {
                                precision: 7,
                                scale: 2,
                            },
                        ),
                        attribute("happened", FormalAttributeType::Date),
                        attribute("f32", FormalAttributeType::Float),
                        attribute("f64", FormalAttributeType::Double),
                        attribute("at", FormalAttributeType::Time),
                        attribute("ts", FormalAttributeType::Timestamp { precision: Some(6) }),
                        attribute(
                            "tstz",
                            FormalAttributeType::Timestamptz { precision: Some(6) },
                        ),
                    ],
                    constraints: FormalTableConstraints::default(),
                },
                FormalTable {
                    relation: "empty".to_owned(),
                    attributes: vec![attribute("n", FormalAttributeType::Int32)],
                    constraints: FormalTableConstraints::default(),
                },
                FormalTable {
                    relation: "empty_unsupported".to_owned(),
                    attributes: vec![attribute("at", FormalAttributeType::Time)],
                    constraints: FormalTableConstraints::default(),
                },
            ],
            rocq_module: String::new(),
        };

        let snapshot =
            extract_formal_witness_snapshot(&mut transaction, &schema_name, &formal_schema)
                .expect("extract typed snapshot");
        assert_eq!(snapshot.tables.len(), 3);
        assert_eq!(snapshot.tables[0].rows.len(), 2);
        assert!(snapshot.tables[1].rows.is_empty());
        assert!(snapshot.tables[2].rows.is_empty());
        assert!(snapshot.tables[0].rows.iter().any(|row| {
            row.cells
                == vec![
                    FormalWitnessValue::Bool(true),
                    FormalWitnessValue::Int32(2),
                    FormalWitnessValue::Int64(9),
                    FormalWitnessValue::String("two".to_owned()),
                    FormalWitnessValue::String("four".to_owned()),
                    FormalWitnessValue::String("xy".to_owned()),
                    FormalWitnessValue::NumericFinite {
                        coefficient: "123".to_owned(),
                        scale: 1,
                    },
                    FormalWitnessValue::Date(18_263),
                    FormalWitnessValue::Float32Bits(1.5_f32.to_bits()),
                    FormalWitnessValue::Float64Bits((-0.0_f64).to_bits()),
                    FormalWitnessValue::Time(86_400_000_000),
                    FormalWitnessValue::Timestamp("946684800000000".to_owned()),
                    FormalWitnessValue::Timestamptz("946684800000000".to_owned()),
                ]
        }));
        assert!(snapshot.tables[0].rows.iter().any(|row| {
            row.cells
                == vec![
                    FormalWitnessValue::Null,
                    FormalWitnessValue::Int32(1),
                    FormalWitnessValue::Null,
                    FormalWitnessValue::Null,
                    FormalWitnessValue::Null,
                    FormalWitnessValue::Null,
                    FormalWitnessValue::Null,
                    FormalWitnessValue::Null,
                    FormalWitnessValue::Null,
                    FormalWitnessValue::Null,
                    FormalWitnessValue::Null,
                    FormalWitnessValue::Null,
                    FormalWitnessValue::Null,
                ]
        }));
        transaction.rollback().expect("rollback snapshot test");
    }

    #[test]
    #[ignore = "requires LOGOS_POSTGRES_URL or DATABASE_URL for a disposable PostgreSQL database"]
    fn witness_materialization_never_executes_the_query_pair() {
        let url = std::env::var("LOGOS_POSTGRES_URL")
            .or_else(|_| std::env::var("DATABASE_URL"))
            .expect("set LOGOS_POSTGRES_URL or DATABASE_URL");
        let root =
            std::env::temp_dir().join(format!("logos-materialize-only-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&root);
        std::fs::create_dir_all(&root).expect("create materialization input");
        let schema_path = root.join("schema.sql");
        let source_path = root.join("source.sql");
        let target_path = root.join("target.sql");
        std::fs::write(&schema_path, "CREATE TABLE t(x integer);\n").expect("write schema");
        // This would raise division_by_zero if the candidate path executed the
        // source query after inserting a row.
        std::fs::write(&source_path, "SELECT 1 / 0 FROM t;\n").expect("write source");
        std::fs::write(&target_path, "SELECT x FROM t;\n").expect("write target");
        let input = VerificationInput::read_with_environment(
            schema_path,
            source_path,
            target_path,
            SqlEnvironment::postgres_utf8_c(),
        )
        .expect("read materialization input");
        let formal_schema = FormalSchema {
            tables: vec![FormalTable {
                relation: "t".to_owned(),
                attributes: vec![FormalAttribute {
                    name: "x".to_owned(),
                    ty: FormalAttributeType::Int32,
                }],
                constraints: FormalTableConstraints::default(),
            }],
            rocq_module: String::new(),
        };
        let validator = PostgresValidator::new(
            Some(url),
            10_000,
            SqlTimeZone::utc(),
            SqlEnvironment::postgres_utf8_c(),
        )
        .expect("create validator");

        let materialized = validator.materialize_formal_witness(
            &input,
            "INSERT INTO t VALUES (7);",
            &formal_schema,
        );
        assert!(matches!(
            materialized.check.result,
            CheckResult::WitnessMaterialized {
                table_count: 1,
                row_count: 1
            }
        ));
        let snapshot = materialized.snapshot.expect("typed snapshot");
        assert_eq!(
            snapshot.tables[0].rows[0].cells,
            vec![FormalWitnessValue::Int32(7)]
        );
        std::fs::remove_dir_all(root).expect("remove materialization input");
    }
}

#[cfg(test)]
mod sequence_tests {
    use super::*;
    use crate::core::{CertificateStatus, ObservationCertificateReport, StatementObservationFacts};

    static NEXT_SEQUENCE_TEST: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

    fn row(values: &[Option<&str>]) -> ExecutableRow {
        values
            .iter()
            .map(|value| value.map(ToOwned::to_owned))
            .collect()
    }

    #[test]
    fn ordered_value_comparison_has_a_closed_builtin_type_surface() {
        for oid in [
            16, 20, 23, 25, 700, 701, 1042, 1043, 1082, 1083, 1114, 1184, 1700,
        ] {
            assert!(postgres_builtin_value_cast(oid).is_some(), "OID {oid}");
        }
        assert!(postgres_builtin_value_cast(16_384).is_none());
    }

    #[test]
    fn sequence_samples_preserve_nulls_and_include_the_difference_window() {
        let rows = vec![
            row(&[Some("a")]),
            row(&[None]),
            row(&[Some("c")]),
            row(&[Some("d")]),
        ];
        let sample: serde_json::Value =
            serde_json::from_str(&sequence_sample(&rows, 3, 2)).expect("parse sequence sample");
        assert_eq!(sample["totalRows"], 4);
        assert_eq!(sample["firstSampledRow"], 2);
        assert_eq!(sample["rows"], serde_json::json!([[null], ["c"]]));
    }

    #[test]
    fn a_concrete_choice_without_functionality_authority_fails_closed() {
        let error = observation_authority(None, 0, ObservationComparison::Sequence)
            .expect_err("one execution must not authorize sequence NEQ");
        assert!(error.contains("possible-outcome relation"));
    }

    fn observation_report(
        source_observation_functional: bool,
        target_observation_functional: bool,
    ) -> ObservationCertificateReport {
        let statement = |functional: bool, side: &str| StatementObservationFacts {
            statement: 1,
            permutation_closed: false,
            success_bag_functional: CertificateStatus::Unknown {
                residual: format!("{side} bag not needed by this sequence test"),
            },
            success_observation_functional: if functional {
                CertificateStatus::Proven {
                    rule: format!("{side} sequence is functional"),
                }
            } else {
                CertificateStatus::Unknown {
                    residual: format!("{side} sequence has unresolved ties"),
                }
            },
            max_success_rows: None,
            candidate_keys: Vec::new(),
        };
        ObservationCertificateReport {
            schema_version: 1,
            verification_input_key: "input".to_owned(),
            verification_input_sha256: "input-sha256".to_owned(),
            lowering_sha256: "lowering-sha256".to_owned(),
            source: vec![statement(source_observation_functional, "source")],
            target: vec![statement(target_observation_functional, "target")],
        }
    }

    #[test]
    fn one_functional_side_authorizes_directional_sequence_separation() {
        for certificates in [
            observation_report(true, false),
            observation_report(false, true),
        ] {
            let authority =
                observation_authority(Some(&certificates), 0, ObservationComparison::Sequence)
                    .expect("either functional side is enough for directional separation");
            assert_eq!(authority.statement, 1);
            assert_eq!(authority.comparison, ObservationComparison::Sequence);
        }
    }

    #[test]
    fn zero_functional_sides_cannot_authorize_a_sequence_difference() {
        let certificates = observation_report(false, false);
        let error = observation_authority(Some(&certificates), 0, ObservationComparison::Sequence)
            .expect_err("two unresolved relations cannot authorize one sampled difference");
        assert!(error.contains("proved on neither side"));
    }

    fn ordered_input(
        label: &str,
        schema_sql: &str,
        source_sql: &str,
        target_sql: &str,
    ) -> VerificationInput {
        let sequence = NEXT_SEQUENCE_TEST.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let root = std::env::temp_dir().join(format!(
            "logos-postgres-sequence-{label}-{}-{sequence}",
            std::process::id()
        ));
        std::fs::create_dir_all(&root).expect("create ordered validator input");
        let schema = root.join("schema.sql");
        let source = root.join("source.sql");
        let target = root.join("target.sql");
        std::fs::write(&schema, schema_sql).expect("write ordered schema");
        std::fs::write(&source, source_sql).expect("write ordered source");
        std::fs::write(&target, target_sql).expect("write ordered target");
        let input = VerificationInput::read_with_environment(
            schema,
            source,
            target,
            SqlEnvironment::postgres_utf8_c(),
        )
        .expect("read ordered validator input");
        std::fs::remove_dir_all(root).expect("remove ordered validator input");
        input
    }

    #[test]
    #[ignore = "requires LOGOS_POSTGRES_URL or DATABASE_URL for a disposable PostgreSQL database"]
    fn ordered_value_comparison_uses_sql_equality_not_rendered_text() {
        let url = std::env::var("LOGOS_POSTGRES_URL")
            .or_else(|_| std::env::var("DATABASE_URL"))
            .expect("set LOGOS_POSTGRES_URL or DATABASE_URL");
        let mut client = Client::connect(&url, NoTls).expect("connect to PostgreSQL");
        let mut transaction = client.transaction().expect("begin transaction");
        let schema = OutputSchema {
            columns: vec![
                crate::validation::OutputColumn {
                    ordinal: 1,
                    name: "n".to_owned(),
                    type_oid: 1700,
                    type_modifier: -1,
                    type_name: "numeric".to_owned(),
                },
                crate::validation::OutputColumn {
                    ordinal: 2,
                    name: "f".to_owned(),
                    type_oid: 701,
                    type_modifier: -1,
                    type_name: "float8".to_owned(),
                },
            ],
        };
        let source = vec![row(&[Some("1.0"), Some("-0")])];
        let target = vec![row(&[Some("1.00"), Some("0")])];
        assert_eq!(
            first_semantically_differing_row(&mut transaction, &source, &target, &schema)
                .expect("compare typed rows"),
            None
        );
        transaction.rollback().expect("rollback comparison");
    }

    #[test]
    #[ignore = "requires LOGOS_POSTGRES_URL or DATABASE_URL for a disposable PostgreSQL database"]
    fn concrete_postgres_choices_without_formal_certificates_are_inconclusive() {
        let url = std::env::var("LOGOS_POSTGRES_URL")
            .or_else(|_| std::env::var("DATABASE_URL"))
            .expect("set LOGOS_POSTGRES_URL or DATABASE_URL");
        let validator = PostgresValidator::new(
            Some(url),
            10_000,
            SqlTimeZone::utc(),
            SqlEnvironment::postgres_utf8_c(),
        )
        .expect("create PostgreSQL validator");

        let ordered = ordered_input(
            "top-level",
            "CREATE TABLE t(x integer);",
            "SELECT x FROM t ORDER BY x;",
            "SELECT x FROM t ORDER BY x DESC;",
        );
        assert!(matches!(
            validator
                .validate(&ordered, "INSERT INTO t VALUES (1), (2);")
                .result,
            CheckResult::InconclusiveObservation {
                comparison: ObservationComparison::Sequence,
                ..
            }
        ));

        let nested = ordered_input(
            "nested-topk",
            "CREATE TABLE t(x integer);",
            "SELECT x FROM (SELECT x FROM t ORDER BY x LIMIT 1) AS s;",
            "SELECT x FROM (SELECT x FROM t ORDER BY x DESC LIMIT 1) AS s;",
        );
        assert!(matches!(
            validator
                .validate(&nested, "INSERT INTO t VALUES (1), (2);")
                .result,
            CheckResult::InconclusiveObservation {
                comparison: ObservationComparison::Bag,
                ..
            }
        ));

        let distinct_on = ordered_input(
            "distinct-on",
            "CREATE TABLE t(k integer, v integer);",
            "SELECT DISTINCT ON (k) k, v FROM t ORDER BY k, v;",
            "SELECT DISTINCT ON (k) k, v FROM t ORDER BY k, v DESC;",
        );
        assert!(matches!(
            validator
                .validate(&distinct_on, "INSERT INTO t VALUES (1, 10), (1, 20);")
                .result,
            CheckResult::InconclusiveObservation {
                comparison: ObservationComparison::Sequence,
                ..
            }
        ));
    }
}

fn validate_integrity_contract(
    transaction: &mut Transaction<'_>,
    checks: Vec<IntegrityValidationCheck>,
) -> Result<()> {
    for check in checks {
        let valid: bool = transaction.query_one(&check.sql, &[])?.get(0);
        if !valid {
            return Err(Error::InvalidCandidate(format!(
                "witness violates benchmark {} constraint on {}: {}",
                check.kind, check.table, check.description
            )));
        }
    }
    Ok(())
}

fn reject_volatile_successful_pairs(
    transaction: &mut Transaction<'_>,
    source_program: &[&str],
    target_program: &[&str],
    source_outputs: &[StatementOutput],
    target_outputs: &[StatementOutput],
) -> Result<()> {
    for (index, (((source, target), source_output), target_output)) in source_program
        .iter()
        .zip(target_program)
        .zip(source_outputs)
        .zip(target_outputs)
        .enumerate()
    {
        match (source_output, target_output) {
            (
                StatementOutput::Success {
                    schema: source_schema,
                },
                StatementOutput::Success {
                    schema: target_schema,
                },
            ) => {
                let statement = index + 1;
                reject_volatile_program(
                    transaction,
                    &format!("source_{statement}"),
                    &[*source],
                    std::slice::from_ref(source_schema),
                )?;
                reject_volatile_program(
                    transaction,
                    &format!("target_{statement}"),
                    &[*target],
                    std::slice::from_ref(target_schema),
                )?;
            }
            (StatementOutput::AnalysisError { .. }, StatementOutput::AnalysisError { .. }) => {}
            _ => {
                return Err(Error::PostgresQueryInspection(format!(
                    "statement {} reached determinism validation with mismatched analysis outcomes",
                    index + 1
                )));
            }
        }
    }
    Ok(())
}

fn describe_output_program(
    transaction: &mut Transaction<'_>,
    program: &[&str],
) -> Result<Vec<StatementOutput>> {
    program
        .iter()
        .map(|query| describe_statement_output(transaction, query))
        .collect()
}

fn begin_validation_transaction(client: &mut Client) -> Result<Transaction<'_>> {
    Ok(client
        .build_transaction()
        .isolation_level(IsolationLevel::RepeatableRead)
        .start()?)
}

#[cfg(test)]
mod integrity_tests {
    use super::*;
    use logos_ir::integrity::{
        ContractTable, SchemaIntegrityContract, parse_integrity_predicate, parse_unique_index_term,
    };
    use logos_ir::ir::{
        CheckConstraint, ForeignKeyConstraint, ForeignKeyMatch, TableConstraints, UniqueConstraint,
        UniqueIndexConstraint,
    };

    fn guarded_verification_input(environment: SqlEnvironment) -> VerificationInput {
        let nonce = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("system clock after epoch")
            .as_nanos();
        let root = std::env::temp_dir().join(format!(
            "logos-integrity-environment-validator-{}-{nonce}",
            std::process::id()
        ));
        std::fs::create_dir_all(&root).expect("create validator input directory");
        let schema = root.join("schema.sql");
        let source = root.join("source.sql");
        let target = root.join("target.sql");
        std::fs::write(&schema, "CREATE TABLE t(code text);").expect("write schema");
        std::fs::write(&source, "SELECT code FROM t;").expect("write source query");
        std::fs::write(&target, "SELECT code FROM t;").expect("write target query");
        let mut input =
            VerificationInput::read_with_environment(schema, source, target, environment)
                .expect("read validator input");
        input.integrity_contract = SchemaIntegrityContract {
            case_id: Some("validator-text-integrity-gate".to_owned()),
            requires_postgres_utf8_c_text_semantics: true,
            ..SchemaIntegrityContract::default()
        };
        std::fs::remove_dir_all(root).expect("remove validator input directory");
        input
    }

    fn disconnected_validator(environment: SqlEnvironment) -> PostgresValidator {
        PostgresValidator {
            url: "postgresql://127.0.0.1:1/logos_environment_guard_must_not_connect".to_owned(),
            statement_timeout_ms: 1,
            diff_sample_limit: 1,
            sql_time_zone: SqlTimeZone::utc(),
            sql_environment: environment,
        }
    }

    #[test]
    fn postgres_entry_points_gate_text_integrity_before_parsing_or_connecting() {
        let unspecified_input = guarded_verification_input(SqlEnvironment::default());
        let validator = disconnected_validator(SqlEnvironment::default());

        let witness = validator.validate(&unspecified_input, "");
        let CheckResult::ValidationError { message } = witness.result else {
            panic!("validator must reject an unspecified integrity environment")
        };
        assert!(
            message.contains("invalid SQL text environment"),
            "{message}"
        );
        assert!(message.contains("LC_COLLATE=C"), "{message}");
        assert!(!message.contains("connection"), "{message}");

        let preflight = validator.preflight_output_schema(&unspecified_input);
        let OutputSchemaPreflightResult::ValidationError { message } = preflight.result else {
            panic!("preflight must reject an unspecified integrity environment")
        };
        assert!(
            message.contains("invalid SQL text environment"),
            "{message}"
        );
        assert!(message.contains("LC_CTYPE=C"), "{message}");
        assert!(!message.contains("connection"), "{message}");

        let partial_environment = SqlEnvironment::try_parse("C", "unspecified", "libc", "UTF8")
            .expect("construct a partial SQL environment");
        let partial_input = guarded_verification_input(partial_environment);
        let full_validator = disconnected_validator(SqlEnvironment::postgres_utf8_c());
        let error = full_validator
            .ensure_integrity_environment(&partial_input)
            .expect_err("a partial input environment must remain fail closed");
        assert!(matches!(error, Error::InvalidSqlEnvironment(_)), "{error}");

        let full_input = guarded_verification_input(SqlEnvironment::postgres_utf8_c());
        full_validator
            .ensure_integrity_environment(&full_input)
            .expect("the complete PostgreSQL UTF8/libc/C profile must pass");
        let error = validator
            .ensure_integrity_environment(&full_input)
            .expect_err("the validator's own weaker environment must not bypass the gate");
        assert!(matches!(error, Error::InvalidSqlEnvironment(_)), "{error}");
        assert!(
            error.to_string().contains("validator is configured"),
            "{error}"
        );
    }

    fn assert_rejected(
        transaction: &mut Transaction<'_>,
        contract: &SchemaIntegrityContract,
        expected_kind: &str,
    ) {
        let error = validate_integrity_contract(transaction, contract.validation_checks())
            .expect_err("invalid snapshot must be rejected");
        assert!(matches!(error, Error::InvalidCandidate(_)), "{error}");
        assert!(error.to_string().contains(expected_kind), "{error}");
    }

    #[test]
    #[ignore = "requires LOGOS_POSTGRES_URL or DATABASE_URL for a disposable PostgreSQL database"]
    fn postgres_integrity_contract_matches_null_fk_check_and_partial_expression_semantics() {
        let url = std::env::var("LOGOS_POSTGRES_URL")
            .or_else(|_| std::env::var("DATABASE_URL"))
            .expect("set LOGOS_POSTGRES_URL or DATABASE_URL");
        let mut client = Client::connect(&url, NoTls).expect("connect to disposable PostgreSQL");
        let mut transaction = begin_validation_transaction(&mut client).expect("begin transaction");
        let schema_name = fresh_schema_name();
        transaction
            .batch_execute(&format!(
                "CREATE SCHEMA {schema_name};\
                 SET LOCAL search_path TO {schema_name}, pg_catalog;\
                 CREATE TABLE parents(id integer, region integer);\
                 CREATE TABLE items(\
                   tenant integer, region integer, code text, active boolean,\
                   category integer, archetype text);\
                 CREATE TABLE nodes(parent_category_id integer);"
            ))
            .expect("create isolated validation tables");

        let contract = SchemaIntegrityContract {
            case_id: Some("postgres-integrity-regression".to_owned()),
            source: None,
            tables: vec![
                ContractTable {
                    name: "parents".to_owned(),
                    constraints: TableConstraints {
                        not_null: vec!["id".to_owned(), "region".to_owned()],
                        primary_key: Some(vec!["id".to_owned(), "region".to_owned()]),
                        ..TableConstraints::default()
                    },
                },
                ContractTable {
                    name: "items".to_owned(),
                    constraints: TableConstraints {
                        unique: vec![UniqueConstraint {
                            name: None,
                            columns: vec!["tenant".to_owned(), "code".to_owned()],
                        }],
                        foreign_keys: vec![ForeignKeyConstraint {
                            name: None,
                            columns: vec!["tenant".to_owned(), "region".to_owned()],
                            referenced_table: "parents".to_owned(),
                            referenced_columns: vec!["id".to_owned(), "region".to_owned()],
                            match_type: ForeignKeyMatch::Simple,
                            referential_actions: Some(
                                "ON DELETE CASCADE ON UPDATE RESTRICT".to_owned(),
                            ),
                        }],
                        checks: vec![CheckConstraint {
                            name: None,
                            expression: parse_integrity_predicate(
                                "category IS NOT NULL OR archetype::text <> 'regular'::text",
                            )
                            .expect("parse CHECK"),
                            source_sql:
                                "category IS NOT NULL OR archetype::text <> 'regular'::text"
                                    .to_owned(),
                        }],
                        unique_indexes: vec![UniqueIndexConstraint {
                            name: None,
                            terms: vec![
                                parse_unique_index_term("lower(code)").expect("parse lower index"),
                            ],
                            predicate: Some(
                                parse_integrity_predicate("active IS TRUE")
                                    .expect("parse partial predicate"),
                            ),
                            predicate_sql: Some("active IS TRUE".to_owned()),
                        }],
                        ..TableConstraints::default()
                    },
                },
                ContractTable {
                    name: "nodes".to_owned(),
                    constraints: TableConstraints {
                        unique_indexes: vec![UniqueIndexConstraint {
                            name: None,
                            terms: vec![
                                parse_unique_index_term(
                                    "COALESCE(parent_category_id, '-1'::integer)",
                                )
                                .expect("parse coalesce index"),
                            ],
                            predicate: None,
                            predicate_sql: None,
                        }],
                        ..TableConstraints::default()
                    },
                },
            ],
            requires_postgres_utf8_c_text_semantics: true,
        };

        transaction
            .batch_execute(
                "INSERT INTO parents VALUES (1, 1);\
                 INSERT INTO items VALUES\
                   (1, 1, NULL, TRUE, NULL, 'other'),\
                   (1, 1, NULL, TRUE, NULL, 'other'),\
                   (NULL, 999, 'Case', FALSE, NULL, 'other'),\
                   (NULL, 999, 'case', NULL, NULL, 'other');\
                 INSERT INTO nodes VALUES (NULL), (1), (2);",
            )
            .expect("insert valid NULL-distinct and MATCH SIMPLE snapshot");
        validate_integrity_contract(&mut transaction, contract.validation_checks())
            .expect("valid snapshot must satisfy the contract");

        transaction
            .batch_execute(
                "INSERT INTO items VALUES\
                   (1, 1, 'dup', FALSE, NULL, 'other'),\
                   (1, 1, 'dup', FALSE, NULL, 'other');",
            )
            .expect("insert ordinary unique violation");
        assert_rejected(&mut transaction, &contract, "unique");
        transaction
            .execute("DELETE FROM items WHERE code = 'dup'", &[])
            .expect("remove ordinary unique violation");

        transaction
            .execute(
                "INSERT INTO items VALUES (9, 9, 'missing-parent', FALSE, NULL, 'other')",
                &[],
            )
            .expect("insert foreign-key violation");
        assert_rejected(&mut transaction, &contract, "foreign_key");
        transaction
            .execute("DELETE FROM items WHERE code = 'missing-parent'", &[])
            .expect("remove foreign-key violation");

        transaction
            .execute(
                "INSERT INTO items VALUES (NULL, NULL, 'bad-check', FALSE, NULL, 'regular')",
                &[],
            )
            .expect("insert CHECK violation");
        assert_rejected(&mut transaction, &contract, "check");
        transaction
            .execute("DELETE FROM items WHERE code = 'bad-check'", &[])
            .expect("remove CHECK violation");

        transaction
            .batch_execute(
                "INSERT INTO items VALUES\
                   (NULL, NULL, 'Mix', TRUE, NULL, 'other'),\
                   (NULL, NULL, 'mix', TRUE, NULL, 'other');",
            )
            .expect("insert partial expression uniqueness violation");
        assert_rejected(
            &mut transaction,
            &contract,
            "partial_expression_unique_index",
        );
        transaction
            .execute("DELETE FROM items WHERE lower(code) = 'mix'", &[])
            .expect("remove partial uniqueness violation");

        transaction
            .execute("INSERT INTO nodes VALUES (NULL)", &[])
            .expect("insert coalesce expression uniqueness violation");
        assert_rejected(
            &mut transaction,
            &contract,
            "partial_expression_unique_index",
        );
        transaction
            .execute("DELETE FROM nodes WHERE parent_category_id IS NULL", &[])
            .expect("remove coalesce violation rows");

        let error = validate_integrity_contract(
            &mut transaction,
            vec![IntegrityValidationCheck {
                kind: "check".to_owned(),
                table: "items".to_owned(),
                description: "evaluation error must reject the snapshot".to_owned(),
                sql: "SELECT (1 / 0) IS NULL".to_owned(),
            }],
        )
        .expect_err("PostgreSQL evaluation errors must reject candidates");
        assert!(matches!(error, Error::Postgres(_)), "{error}");
        transaction
            .rollback()
            .expect("rollback isolated regression");
    }
}
