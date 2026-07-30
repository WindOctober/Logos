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

pub(super) fn query_json_sql(query: &str, limit: usize, label: &str) -> String {
    format!(
        "SELECT COALESCE(jsonb_agg(to_jsonb(_logos_{label}) ORDER BY to_jsonb(_logos_{label})::text), '[]'::jsonb)::text
         FROM (SELECT * FROM ({query}) AS _logos_query LIMIT {limit}) AS _logos_{label}"
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
    fn generated_bag_queries_never_assign_physical_row_ordinals() {
        for sql in [
            bag_difference_exists_sql("select 1", "select 2"),
            query_json_sql("select 1", 3, "source"),
            diff_sample_sql("select 1", "select 2", 3),
        ] {
            assert!(!sql.to_ascii_lowercase().contains("row_number"));
            assert!(!sql.contains("_logos_ord"));
        }
    }
}
