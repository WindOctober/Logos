use std::collections::{BTreeSet, VecDeque};

use postgres::Transaction;

use crate::error::{Error, Result};
use crate::validation::types::OutputSchema;

// PostgreSQL reserves OIDs below FirstNormalObjectId for bootstrap/catalog
// objects. Schema-defined callables are rejected because PostgreSQL trusts,
// but does not verify, their declared volatility.
const FIRST_NORMAL_OBJECT_ID: u32 = 16_384;

const FUNCTION_OID_FIELDS: &[&str] = &[
    ":funcid",
    ":aggfnoid",
    ":winfnoid",
    ":opfuncid",
    ":hashfuncid",
    ":negfuncid",
    ":startInRangeFunc",
    ":endInRangeFunc",
    ":tsmhandler",
];

const OPERATOR_OID_FIELDS: &[&str] = &[":opno", ":eqop", ":sortop", ":cycle_mark_neop"];

const TYPE_OID_FIELDS: &[&str] = &[
    ":vartype",
    ":consttype",
    ":paramtype",
    ":aggtype",
    ":aggtranstype",
    ":wintype",
    ":opresulttype",
    ":msftype",
    ":refcontainertype",
    ":refelemtype",
    ":refrestype",
    ":funcresulttype",
    ":firstColType",
    ":resulttype",
    ":casetype",
    ":typeId",
    ":array_typeid",
    ":element_typeid",
    ":row_typeid",
    ":coalescetype",
    ":minmaxtype",
    ":typid",
    ":cycle_mark_type",
];

const TYPE_OID_LIST_FIELDS: &[&str] = &[":aggargtypes", ":coltypes", ":funccoltypes"];

const COLLATION_OID_FIELDS: &[&str] = &[
    ":varcollid",
    ":constcollid",
    ":paramcollid",
    ":aggcollid",
    ":wincollid",
    ":funccollid",
    ":inputcollid",
    ":opcollid",
    ":refcollid",
    ":resultcollid",
    ":collOid",
    ":casecollid",
    ":collation",
    ":array_collid",
    ":coalescecollid",
    ":minmaxcollid",
    ":cycle_mark_collation",
];

const COLLATION_OID_LIST_FIELDS: &[&str] =
    &[":colcollations", ":funccolcollations", ":ctecolcollations"];

#[derive(Debug, Default, PartialEq, Eq)]
struct QueryReferences {
    function_oids: BTreeSet<u32>,
    operator_oids: BTreeSet<u32>,
    type_oids: BTreeSet<u32>,
    collation_oids: BTreeSet<u32>,
    relation_oids: BTreeSet<u32>,
    sequence_oids: BTreeSet<u32>,
}

impl QueryReferences {
    fn extend(&mut self, other: Self) {
        self.function_oids.extend(other.function_oids);
        self.operator_oids.extend(other.operator_oids);
        self.type_oids.extend(other.type_oids);
        self.collation_oids.extend(other.collation_oids);
        self.relation_oids.extend(other.relation_oids);
        self.sequence_oids.extend(other.sequence_oids);
    }
}

/// Reject query programs whose logical result depends on PostgreSQL volatility.
/// The current FormalSQL fragment does not model volatile evaluation, so the
/// static preflight fails closed instead of delegating meaning to a plan.
pub(super) fn reject_volatile_program(
    transaction: &mut Transaction<'_>,
    side: &str,
    program: &[&str],
    schemas: &[OutputSchema],
) -> Result<()> {
    reject_program_with_volatility_policy(transaction, side, program, schemas, true)
}

fn reject_program_with_volatility_policy(
    transaction: &mut Transaction<'_>,
    side: &str,
    program: &[&str],
    schemas: &[OutputSchema],
    allow_stable: bool,
) -> Result<()> {
    if program.len() != schemas.len() {
        return Err(Error::PostgresQueryInspection(format!(
            "{side} program has {} statements but {} described schemas",
            program.len(),
            schemas.len()
        )));
    }

    for (index, (query, schema)) in program.iter().zip(schemas).enumerate() {
        reject_volatile_query(transaction, side, index + 1, query, schema, allow_stable)?;
    }
    Ok(())
}

fn reject_volatile_query(
    transaction: &mut Transaction<'_>,
    side: &str,
    statement: usize,
    query: &str,
    schema: &OutputSchema,
    allow_stable: bool,
) -> Result<()> {
    let view_name = format!("logos_determinism_{side}_{statement}");
    transaction.batch_execute(&analysis_view_sql(&view_name, query, schema))?;
    let (view_oid, rewrite_tree) = analysis_view_rewrite_tree(transaction, &view_name)?;
    let references = collect_transitive_references(transaction, view_oid, &rewrite_tree)?;

    reject_schema_defined_types(transaction, &references.type_oids)?;
    reject_schema_defined_collations(transaction, &references.collation_oids)?;

    let mut volatile_objects = Vec::new();
    for oid in references.function_oids {
        if let Some(name) = volatile_function_name(transaction, oid, allow_stable)? {
            volatile_objects.push(format!("function {name}"));
        }
    }
    for oid in references.operator_oids {
        if let Some(name) = volatile_operator_name(transaction, oid, allow_stable)? {
            volatile_objects.push(format!("operator {name}"));
        }
    }
    for oid in references.sequence_oids {
        volatile_objects.push(format!(
            "sequence read {}",
            relation_name(transaction, oid)?
        ));
    }

    volatile_objects.sort();
    volatile_objects.dedup();
    if volatile_objects.is_empty() {
        Ok(())
    } else {
        Err(Error::NonDeterministicQuery(format!(
            "{side} statement {statement} references {}",
            volatile_objects.join(", ")
        )))
    }
}

fn analysis_view_sql(view_name: &str, query: &str, schema: &OutputSchema) -> String {
    let view_name = quote_ident(view_name);
    if schema.columns.is_empty() {
        // PostgreSQL views require at least one output column. The wrapper is
        // inspection-only and keeps the zero-column query as a subquery.
        return format!(
            "CREATE TEMP VIEW {view_name} (_logos_unit) AS\n\
             SELECT 1 FROM (\n{query}\n) AS _logos_zero_column_query;"
        );
    }

    let columns = schema
        .columns
        .iter()
        .map(|column| quote_ident(&format!("c{}", column.ordinal)))
        .collect::<Vec<_>>()
        .join(", ");
    format!("CREATE TEMP VIEW {view_name} ({columns}) AS\n{query}\n;")
}

fn analysis_view_rewrite_tree(
    transaction: &mut Transaction<'_>,
    view_name: &str,
) -> Result<(u32, String)> {
    let row = transaction
        .query_opt(
            "SELECT c.oid, r.ev_action::text \
             FROM pg_catalog.pg_class AS c \
             JOIN pg_catalog.pg_rewrite AS r ON r.ev_class = c.oid \
             WHERE c.relnamespace = pg_catalog.pg_my_temp_schema() \
               AND c.relname = $1 \
               AND r.rulename = '_RETURN'",
            &[&view_name],
        )?
        .ok_or_else(|| {
            Error::PostgresQueryInspection(format!(
                "temporary analysis view {view_name:?} has no _RETURN rewrite rule"
            ))
        })?;
    Ok((row.get(0), row.get(1)))
}

fn collect_transitive_references(
    transaction: &mut Transaction<'_>,
    root_view_oid: u32,
    root_tree: &str,
) -> Result<QueryReferences> {
    let mut references = parse_query_references(root_tree)?;
    let mut pending = VecDeque::from_iter(references.relation_oids.iter().copied());
    let mut visited = BTreeSet::from([root_view_oid]);

    while let Some(relation_oid) = pending.pop_front() {
        if relation_oid == 0 || !visited.insert(relation_oid) {
            continue;
        }
        let row = transaction
            .query_opt(
                "SELECT c.relkind::text, c.relrowsecurity, \
                        n.nspname || '.' || c.relname, \
                        (SELECT r.ev_action::text \
                           FROM pg_catalog.pg_rewrite AS r \
                          WHERE r.ev_class = c.oid AND r.rulename = '_RETURN') \
                   FROM pg_catalog.pg_class AS c \
                   JOIN pg_catalog.pg_namespace AS n ON n.oid = c.relnamespace \
                  WHERE c.oid = $1",
                &[&relation_oid],
            )?
            .ok_or_else(|| {
                Error::PostgresQueryInspection(format!(
                    "analyzed query references missing relation OID {relation_oid}"
                ))
            })?;
        let relation_kind: String = row.get(0);
        let row_security: bool = row.get(1);
        let relation_name: String = row.get(2);
        let rewrite_tree: Option<String> = row.get(3);

        // Policy expressions are not embedded in a view's stored query tree.
        // Refuse them rather than silently overlooking a volatile policy.
        if row_security {
            return Err(Error::PostgresQueryInspection(format!(
                "row-level security on {relation_name} is not supported by deterministic counterexample validation"
            )));
        }
        if relation_kind == "S" {
            references.sequence_oids.insert(relation_oid);
            continue;
        }
        if relation_kind != "v" {
            continue;
        }
        let tree = rewrite_tree.ok_or_else(|| {
            Error::PostgresQueryInspection(format!(
                "referenced view {relation_name} has no _RETURN rewrite rule"
            ))
        })?;
        let nested = parse_query_references(&tree)?;
        pending.extend(nested.relation_oids.iter().copied());
        references.extend(nested);
    }

    expand_aggregate_dependencies(transaction, &mut references)?;
    Ok(references)
}

fn expand_aggregate_dependencies(
    transaction: &mut Transaction<'_>,
    references: &mut QueryReferences,
) -> Result<()> {
    let mut pending = VecDeque::from_iter(references.function_oids.iter().copied());
    let mut visited = BTreeSet::new();
    while let Some(function_oid) = pending.pop_front() {
        if !visited.insert(function_oid) {
            continue;
        }
        let function_kind = transaction
            .query_opt(
                "SELECT p.prokind::text FROM pg_catalog.pg_proc AS p WHERE p.oid = $1",
                &[&function_oid],
            )?
            .ok_or_else(|| {
                Error::PostgresQueryInspection(format!(
                    "analyzed query references missing function OID {function_oid}"
                ))
            })?
            .get::<_, String>(0);
        if function_kind != "a" {
            continue;
        }

        // CREATE AGGREGATE records the aggregate's pg_proc row as immutable
        // even when one of its execution support functions is VOLATILE. The
        // support graph, rather than only aggfnoid, defines determinism.
        let row = transaction
            .query_opt(
                "SELECT a.aggtransfn::oid, a.aggfinalfn::oid, \
                        a.aggcombinefn::oid, a.aggserialfn::oid, \
                        a.aggdeserialfn::oid, a.aggmtransfn::oid, \
                        a.aggminvtransfn::oid, a.aggmfinalfn::oid, \
                        a.aggsortop::oid \
                   FROM pg_catalog.pg_aggregate AS a \
                  WHERE a.aggfnoid = $1",
                &[&function_oid],
            )?
            .ok_or_else(|| {
                Error::PostgresQueryInspection(format!(
                    "aggregate function OID {function_oid} has no pg_aggregate row"
                ))
            })?;
        for column in 0..8 {
            let dependency: u32 = row.get(column);
            if dependency != 0 && references.function_oids.insert(dependency) {
                pending.push_back(dependency);
            }
        }
        let sort_operator: u32 = row.get(8);
        if sort_operator != 0 {
            references.operator_oids.insert(sort_operator);
        }
    }
    Ok(())
}

fn parse_query_references(tree: &str) -> Result<QueryReferences> {
    let tokens = tree.split_ascii_whitespace().collect::<Vec<_>>();
    let mut references = QueryReferences::default();
    let mut index = 0;
    while index < tokens.len() {
        let field = tokens[index];
        if FUNCTION_OID_FIELDS.contains(&field) {
            insert_scalar_oid(&tokens, index, field, &mut references.function_oids)?;
            index += 2;
        } else if OPERATOR_OID_FIELDS.contains(&field) {
            insert_scalar_oid(&tokens, index, field, &mut references.operator_oids)?;
            index += 2;
        } else if TYPE_OID_FIELDS.contains(&field) {
            insert_scalar_oid(&tokens, index, field, &mut references.type_oids)?;
            index += 2;
        } else if COLLATION_OID_FIELDS.contains(&field) {
            insert_scalar_oid(&tokens, index, field, &mut references.collation_oids)?;
            index += 2;
        } else if field == ":relid" {
            insert_scalar_oid(&tokens, index, field, &mut references.relation_oids)?;
            index += 2;
        } else if field == ":seqid" {
            insert_scalar_oid(&tokens, index, field, &mut references.sequence_oids)?;
            index += 2;
        } else if field == ":opnos" {
            index = insert_oid_list(&tokens, index, field, &mut references.operator_oids)?;
        } else if TYPE_OID_LIST_FIELDS.contains(&field) {
            index = insert_oid_list(&tokens, index, field, &mut references.type_oids)?;
        } else if COLLATION_OID_LIST_FIELDS.contains(&field) {
            index = insert_oid_list(&tokens, index, field, &mut references.collation_oids)?;
        } else {
            index += 1;
        }
    }
    Ok(references)
}

fn reject_schema_defined_types(
    transaction: &mut Transaction<'_>,
    type_oids: &BTreeSet<u32>,
) -> Result<()> {
    if let Some(oid) = type_oids
        .iter()
        .copied()
        .find(|oid| *oid >= FIRST_NORMAL_OBJECT_ID)
    {
        let name = transaction
            .query_opt(
                "SELECT n.nspname || '.' || t.typname \
                   FROM pg_catalog.pg_type AS t \
                   JOIN pg_catalog.pg_namespace AS n ON n.oid = t.typnamespace \
                  WHERE t.oid = $1",
                &[&oid],
            )?
            .ok_or_else(|| {
                Error::PostgresQueryInspection(format!(
                    "analyzed query references missing type OID {oid}"
                ))
            })?
            .get::<_, String>(0);
        Err(Error::PostgresQueryInspection(format!(
            "schema-defined type {name} has untrusted comparison and conversion support"
        )))
    } else {
        Ok(())
    }
}

fn reject_schema_defined_collations(
    transaction: &mut Transaction<'_>,
    collation_oids: &BTreeSet<u32>,
) -> Result<()> {
    if let Some(oid) = collation_oids
        .iter()
        .copied()
        .find(|oid| *oid >= FIRST_NORMAL_OBJECT_ID)
    {
        let name = transaction
            .query_opt(
                "SELECT n.nspname || '.' || c.collname \
                   FROM pg_catalog.pg_collation AS c \
                   JOIN pg_catalog.pg_namespace AS n ON n.oid = c.collnamespace \
                  WHERE c.oid = $1",
                &[&oid],
            )?
            .ok_or_else(|| {
                Error::PostgresQueryInspection(format!(
                    "analyzed query references missing collation OID {oid}"
                ))
            })?
            .get::<_, String>(0);
        Err(Error::PostgresQueryInspection(format!(
            "schema-defined collation {name} is not supported by deterministic validation"
        )))
    } else {
        Ok(())
    }
}

fn insert_scalar_oid(
    tokens: &[&str],
    index: usize,
    field: &str,
    output: &mut BTreeSet<u32>,
) -> Result<()> {
    let token = tokens.get(index + 1).ok_or_else(|| {
        Error::PostgresQueryInspection(format!("PostgreSQL rewrite tree ends after {field}"))
    })?;
    let oid = parse_oid_token(token).ok_or_else(|| {
        Error::PostgresQueryInspection(format!(
            "PostgreSQL rewrite tree has invalid {field} value {token:?}"
        ))
    })?;
    if oid != 0 {
        output.insert(oid);
    }
    Ok(())
}

fn insert_oid_list(
    tokens: &[&str],
    index: usize,
    field: &str,
    output: &mut BTreeSet<u32>,
) -> Result<usize> {
    let first = tokens.get(index + 1).ok_or_else(|| {
        Error::PostgresQueryInspection(format!("PostgreSQL rewrite tree ends after {field}"))
    })?;
    if first.trim_matches(['{', '}']) == "<>" {
        return Ok(index + 2);
    }
    if !first.starts_with('(') {
        return Err(Error::PostgresQueryInspection(format!(
            "PostgreSQL rewrite tree has invalid {field} list start {first:?}"
        )));
    }

    let mut cursor = index + 1;
    loop {
        let token = tokens.get(cursor).ok_or_else(|| {
            Error::PostgresQueryInspection(format!(
                "PostgreSQL rewrite tree has unterminated {field} list"
            ))
        })?;
        if let Some(oid) = parse_oid_token(token)
            && oid != 0
        {
            output.insert(oid);
        }
        cursor += 1;
        if token.contains(')') {
            return Ok(cursor);
        }
    }
}

fn parse_oid_token(token: &str) -> Option<u32> {
    let token = token.trim_matches(['(', ')', '{', '}']);
    (!token.is_empty() && token.bytes().all(|byte| byte.is_ascii_digit()))
        .then(|| token.parse().ok())
        .flatten()
}

fn volatile_function_name(
    transaction: &mut Transaction<'_>,
    oid: u32,
    allow_stable: bool,
) -> Result<Option<String>> {
    let row = transaction
        .query_opt(
            "SELECT p.provolatile::text, \
                    n.nspname || '.' || p.proname || '(' || \
                    pg_catalog.pg_get_function_identity_arguments(p.oid) || ')' \
               FROM pg_catalog.pg_proc AS p \
               JOIN pg_catalog.pg_namespace AS n ON n.oid = p.pronamespace \
              WHERE p.oid = $1",
            &[&oid],
        )?
        .ok_or_else(|| {
            Error::PostgresQueryInspection(format!(
                "analyzed query references missing function OID {oid}"
            ))
        })?;
    let volatility = row.get::<_, String>(0);
    let name = row.get::<_, String>(1);
    if oid >= FIRST_NORMAL_OBJECT_ID {
        return Err(Error::PostgresQueryInspection(format!(
            "schema-defined function {name} cannot be trusted from its declared volatility alone"
        )));
    }
    volatility_result(volatility, name, oid, "function", allow_stable)
}

fn volatile_operator_name(
    transaction: &mut Transaction<'_>,
    oid: u32,
    allow_stable: bool,
) -> Result<Option<String>> {
    let row = transaction
        .query_opt(
            "SELECT p.provolatile::text, \
                    n.nspname || '.' || o.oprname || ' via ' || \
                    pn.nspname || '.' || p.proname \
               FROM pg_catalog.pg_operator AS o \
               JOIN pg_catalog.pg_namespace AS n ON n.oid = o.oprnamespace \
               JOIN pg_catalog.pg_proc AS p ON p.oid = o.oprcode \
               JOIN pg_catalog.pg_namespace AS pn ON pn.oid = p.pronamespace \
              WHERE o.oid = $1",
            &[&oid],
        )?
        .ok_or_else(|| {
            Error::PostgresQueryInspection(format!(
                "analyzed query references missing or undefined operator OID {oid}"
            ))
        })?;
    let volatility = row.get::<_, String>(0);
    let name = row.get::<_, String>(1);
    if oid >= FIRST_NORMAL_OBJECT_ID {
        return Err(Error::PostgresQueryInspection(format!(
            "schema-defined operator {name} cannot be trusted from its declared volatility alone"
        )));
    }
    volatility_result(volatility, name, oid, "operator", allow_stable)
}

fn volatility_result(
    volatility: String,
    name: String,
    oid: u32,
    kind: &str,
    allow_stable: bool,
) -> Result<Option<String>> {
    match volatility.as_str() {
        "v" => Ok(Some(name)),
        "i" => Ok(None),
        "s" if allow_stable => Ok(None),
        "s" => Ok(Some(name)),
        _ => Err(Error::PostgresQueryInspection(format!(
            "{kind} OID {oid} has unknown volatility code {volatility:?}"
        ))),
    }
}

fn relation_name(transaction: &mut Transaction<'_>, oid: u32) -> Result<String> {
    Ok(transaction
        .query_opt(
            "SELECT n.nspname || '.' || c.relname \
               FROM pg_catalog.pg_class AS c \
               JOIN pg_catalog.pg_namespace AS n ON n.oid = c.relnamespace \
              WHERE c.oid = $1",
            &[&oid],
        )?
        .map(|row| row.get(0))
        .unwrap_or_else(|| format!("OID {oid}")))
}

fn quote_ident(value: &str) -> String {
    format!("\"{}\"", value.replace('"', "\"\""))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn stable_calls_are_rejected_for_cross_statement_sequence_comparison() {
        assert_eq!(
            volatility_result(
                "s".to_owned(),
                "statement_timestamp".to_owned(),
                1,
                "function",
                false
            )
            .unwrap(),
            Some("statement_timestamp".to_owned())
        );
        assert_eq!(
            volatility_result(
                "s".to_owned(),
                "statement_timestamp".to_owned(),
                1,
                "function",
                true
            )
            .unwrap(),
            None
        );
    }

    #[test]
    fn extracts_runtime_references_from_postgres_rewrite_tree() {
        let tree = "{QUERY :relid 42 :funcid 1598 :opfuncid 0 :aggfnoid 2108 \
                    :opno 97 :eqop 0 :opnos (o 521 525) :vartype 23 \
                    :aggargtypes (o 23 1700) :inputcollid 950 \
                    :funccolcollations (o 950 0) :seqid 16384}";

        let references = parse_query_references(tree).unwrap();

        assert_eq!(references.function_oids, BTreeSet::from([1598, 2108]));
        assert_eq!(references.operator_oids, BTreeSet::from([97, 521, 525]));
        assert_eq!(references.type_oids, BTreeSet::from([23, 1700]));
        assert_eq!(references.collation_oids, BTreeSet::from([950]));
        assert_eq!(references.relation_oids, BTreeSet::from([42]));
        assert_eq!(references.sequence_oids, BTreeSet::from([16384]));
    }

    #[test]
    fn accepts_empty_oid_lists_and_ignores_zero_oids() {
        let references = parse_query_references(
            "{QUERY :funcid 0 :opno 0 :vartype 0 :relid 0 :seqid 0 \
                 :inputcollid 0 :opnos <> :aggargtypes <> :colcollations <>}",
        )
        .unwrap();

        assert_eq!(references, QueryReferences::default());
    }

    #[test]
    fn rejects_malformed_scalar_oid_fields() {
        let error = parse_query_references("{QUERY :funcid not_an_oid}")
            .expect_err("malformed catalog references must fail closed");

        assert!(error.to_string().contains("invalid :funcid value"));
    }

    #[test]
    fn emits_unique_view_columns_instead_of_query_labels() {
        let schema = OutputSchema {
            columns: vec![
                crate::validation::types::OutputColumn {
                    ordinal: 1,
                    name: "duplicate".to_owned(),
                    type_oid: 23,
                    type_modifier: -1,
                    type_name: "int4".to_owned(),
                },
                crate::validation::types::OutputColumn {
                    ordinal: 2,
                    name: "duplicate".to_owned(),
                    type_oid: 23,
                    type_modifier: -1,
                    type_name: "int4".to_owned(),
                },
            ],
        };

        let sql = analysis_view_sql("probe", "SELECT 1 AS x, 2 AS x", &schema);

        assert!(sql.contains("\"probe\" (\"c1\", \"c2\")"));
        assert!(!sql.contains("duplicate"));
    }
}
