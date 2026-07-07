pub(super) fn bag_difference_exists_sql(source: &str, target: &str) -> String {
    format!(
        "SELECT EXISTS (
            SELECT * FROM ({source}) AS _logos_source
            EXCEPT ALL
            SELECT * FROM ({target}) AS _logos_target
        ) OR EXISTS (
            SELECT * FROM ({target}) AS _logos_target
            EXCEPT ALL
            SELECT * FROM ({source}) AS _logos_source
        )"
    )
}

pub(super) fn ordered_difference_exists_sql(
    source: &str,
    target: &str,
    column_count: usize,
) -> String {
    format!(
        "SELECT ({source_rows}) IS DISTINCT FROM ({target_rows})",
        source_rows = ordered_rows_json_sql(source, column_count, None),
        target_rows = ordered_rows_json_sql(target, column_count, None),
    )
}

pub(super) fn query_json_sql(query: &str, limit: usize, label: &str) -> String {
    format!(
        "SELECT COALESCE(jsonb_agg(to_jsonb(_logos_{label}) ORDER BY to_jsonb(_logos_{label})::text), '[]'::jsonb)::text
         FROM (SELECT * FROM ({query}) AS _logos_query LIMIT {limit}) AS _logos_{label}"
    )
}

pub(super) fn ordered_query_json_sql(
    query: &str,
    column_count: usize,
    limit: usize,
    label: &str,
) -> String {
    format!(
        "SELECT COALESCE(jsonb_agg(_logos_{label}._logos_row ORDER BY _logos_{label}._logos_ord), '[]'::jsonb)::text
         FROM ({rows}) AS _logos_{label}",
        rows = ordered_rows_relation_sql(query, column_count, Some(limit)),
    )
}

pub(super) fn diff_sample_sql(source: &str, target: &str, limit: usize) -> String {
    format!(
        "SELECT COALESCE(jsonb_agg(to_jsonb(_logos_diff)), '[]'::jsonb)::text
         FROM (
             (
                 SELECT 'source_minus_target' AS side, to_jsonb(_d1) AS row
                 FROM (
                     SELECT * FROM ({source}) AS _logos_source
                     EXCEPT ALL
                     SELECT * FROM ({target}) AS _logos_target
                 ) AS _d1
                 LIMIT {limit}
             )
             UNION ALL
             (
                 SELECT 'target_minus_source' AS side, to_jsonb(_d2) AS row
                 FROM (
                     SELECT * FROM ({target}) AS _logos_target
                     EXCEPT ALL
                     SELECT * FROM ({source}) AS _logos_source
                 ) AS _d2
                 LIMIT {limit}
             )
         ) AS _logos_diff"
    )
}

pub(super) fn ordered_diff_sample_sql(
    source: &str,
    target: &str,
    column_count: usize,
    limit: usize,
) -> String {
    format!(
        "SELECT COALESCE(jsonb_agg(to_jsonb(_logos_limited_diff) ORDER BY _logos_side, _logos_ord), '[]'::jsonb)::text
         FROM (
             SELECT *
             FROM (
                 SELECT 'source' AS _logos_side, source_rows._logos_ord, source_rows._logos_row
                 FROM ({source_rows}) AS source_rows
                 FULL OUTER JOIN ({target_rows}) AS target_rows
                   ON source_rows._logos_ord = target_rows._logos_ord
                 WHERE source_rows._logos_row IS DISTINCT FROM target_rows._logos_row
                 UNION ALL
                 SELECT 'target' AS _logos_side, target_rows._logos_ord, target_rows._logos_row
                 FROM ({source_rows_again}) AS source_rows
                 FULL OUTER JOIN ({target_rows_again}) AS target_rows
                   ON source_rows._logos_ord = target_rows._logos_ord
                 WHERE source_rows._logos_row IS DISTINCT FROM target_rows._logos_row
             ) AS _logos_ordered_diff
             ORDER BY _logos_side, _logos_ord
             LIMIT {limit}
         ) AS _logos_limited_diff",
        source_rows = ordered_rows_relation_sql(source, column_count, None),
        target_rows = ordered_rows_relation_sql(target, column_count, None),
        source_rows_again = ordered_rows_relation_sql(source, column_count, None),
        target_rows_again = ordered_rows_relation_sql(target, column_count, None),
    )
}

fn ordered_rows_json_sql(query: &str, column_count: usize, limit: Option<usize>) -> String {
    format!(
        "SELECT COALESCE(jsonb_agg(_logos_rows._logos_row ORDER BY _logos_rows._logos_ord), '[]'::jsonb)
         FROM ({rows}) AS _logos_rows",
        rows = ordered_rows_relation_sql(query, column_count, limit),
    )
}

fn ordered_rows_relation_sql(query: &str, column_count: usize, limit: Option<usize>) -> String {
    let columns = positional_column_aliases(column_count)
        .map(|columns| format!("({columns})"))
        .unwrap_or_default();
    let limit_clause = limit
        .map(|limit| format!(" LIMIT {limit}"))
        .unwrap_or_default();
    format!(
        "SELECT row_number() OVER () AS _logos_ord, to_jsonb(_logos_query) AS _logos_row
         FROM (SELECT * FROM ({query}) AS _logos_wrapped{limit_clause}) AS _logos_query{columns}"
    )
}

fn positional_column_aliases(column_count: usize) -> Option<String> {
    (column_count > 0).then(|| {
        (0..column_count)
            .map(|index| format!("_logos_col_{}", index + 1))
            .collect::<Vec<_>>()
            .join(", ")
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bag_difference_uses_except_all_in_both_directions() {
        let sql = bag_difference_exists_sql("select 1", "select 2");
        assert!(sql.contains("EXCEPT ALL"));
        assert!(sql.contains("select 1"));
        assert!(sql.contains("select 2"));
    }

    #[test]
    fn ordered_difference_aliases_columns_positionally() {
        let sql = ordered_difference_exists_sql("select 1 as a", "select 1 as b", 1);
        assert!(sql.contains("_logos_col_1"));
        assert!(sql.contains("IS DISTINCT FROM"));
    }

    #[test]
    fn ordered_diff_sample_limits_before_aggregation() {
        let sql = ordered_diff_sample_sql("select 1", "select 2", 1, 3);
        let limit_index = sql.find("LIMIT 3").expect("sample limit should be present");
        let aggregate_index = sql
            .find("jsonb_agg")
            .expect("diff sample should aggregate rows");
        assert!(limit_index > aggregate_index);
        assert!(sql.contains("AS _logos_limited_diff"));
    }
}
