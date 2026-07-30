use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use logos_ir::calcite::{CalciteFile, CalciteRel, CalciteRex};
use logos_ir::convert_raw_file;
use logos_ir::ir::{
    QueryAnalysisError, RelExpr, ScalarAst, ScalarExpr, ScalarOp, SourceAnalysisErrorProvenance,
    SqlEnvironment, SqlType,
};

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_cli_rejects_unknown_duplicate_missing_and_positional_options() {
    let repo = repo_root();
    let temp = temp_dir("closed-cli-options");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&schema, "create table t(a integer);\n").unwrap();
    fs::write(&query, "select a from t;\n").unwrap();

    let cases = [
        vec![
            "--schema".into(),
            schema.as_os_str().to_owned(),
            "--sql".into(),
            query.as_os_str().to_owned(),
            "--server-encodin".into(),
            "UTF8".into(),
        ],
        vec![
            "--schema".into(),
            schema.as_os_str().to_owned(),
            "--sql".into(),
            query.as_os_str().to_owned(),
            "--sql".into(),
            query.as_os_str().to_owned(),
        ],
        vec![
            "--schema".into(),
            schema.as_os_str().to_owned(),
            "--sql".into(),
        ],
        vec![
            "positional".into(),
            "--schema".into(),
            schema.as_os_str().to_owned(),
            "--sql".into(),
            query.as_os_str().to_owned(),
        ],
    ];
    for args in cases {
        let output = Command::new(repo.join("scripts/calcite-ir"))
            .args(args)
            .output()
            .unwrap();
        assert!(
            !output.status.success(),
            "invalid Calcite CLI arguments unexpectedly succeeded"
        );
    }
    fs::remove_dir_all(temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_attests_explicit_postgres_utf8_c_environment() {
    let repo = repo_root();
    let temp = temp_dir("postgres-utf8-c-environment");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&schema, "create table t(body text);\n").unwrap();
    fs::write(&query, "select upper(body) from t order by body;\n").unwrap();

    let output = Command::new(repo.join("scripts/calcite-ir"))
        .arg("--schema")
        .arg(&schema)
        .arg("--sql")
        .arg(&query)
        .arg("--default-collation")
        .arg("C")
        .arg("--character-classification")
        .arg("C")
        .arg("--locale-provider")
        .arg("libc")
        .arg("--server-encoding")
        .arg("UTF8")
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "calcite wrapper failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let raw: CalciteFile = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(raw.environment, SqlEnvironment::postgres_utf8_c());
    let ir = convert_raw_file(raw).unwrap();
    assert_eq!(ir.environment, SqlEnvironment::postgres_utf8_c());
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_emits_only_relroot_visible_columns_and_preserves_child_provenance() {
    fn clear_rex_source(rex: &mut CalciteRex) {
        rex.source_sql = None;
        rex.source_node_id = None;
        rex.source_text = None;
        rex.source_expansion = None;
        rex.source_kind = None;
        rex.source_operator = None;
        rex.source_window_function = None;
        rex.source_identifier_names.clear();
        rex.source_identifier_quoted.clear();
        rex.source_in_subquery_order = None;
        if let Some(reference) = rex.reference_expr.as_deref_mut() {
            clear_rex_source(reference);
        }
        for operand in &mut rex.operands {
            clear_rex_source(operand);
        }
        if let Some(window) = rex.window.as_deref_mut() {
            for key in &mut window.partition_keys {
                clear_rex_source(key);
            }
            for key in &mut window.order_keys {
                clear_rex_source(&mut key.expr);
            }
        }
    }

    fn first_typed_owned_where(
        rel: &RelExpr,
    ) -> Option<&logos_ir::ir::ScalarSourceClauseOwnership> {
        match rel {
            RelExpr::Filter {
                input, predicate, ..
            } => predicate
                .source
                .as_ref()
                .and_then(|source| source.clause_ownership.as_ref())
                .or_else(|| first_typed_owned_where(input)),
            RelExpr::Project { input, .. }
            | RelExpr::NativeHaving { input, .. }
            | RelExpr::Aggregate { input, .. }
            | RelExpr::Distinct { input, .. }
            | RelExpr::Sort { input, .. } => first_typed_owned_where(input),
            RelExpr::Join { left, right, .. } => {
                first_typed_owned_where(left).or_else(|| first_typed_owned_where(right))
            }
            RelExpr::Set { inputs, .. } => inputs.iter().find_map(first_typed_owned_where),
            RelExpr::TableScan { .. } | RelExpr::Values { .. } => None,
        }
    }

    let repo = repo_root();
    let temp = temp_dir("relroot-visible-output-project");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&schema, "create table t(a integer, b integer);\n").unwrap();
    fs::write(
        &query,
        "select a as visible_a from t where a > 0 order by b desc nulls first;\n\
         select b as out_b, a as out_a from t order by a + b;\n",
    )
    .unwrap();

    let raw = run_calcite(&repo, &schema, &query);
    assert_eq!(raw.queries.len(), 2);

    let first_root = raw.queries[0].rel.as_ref().expect("first visible root");
    assert_eq!(first_root.rel_type, "LogicalProject");
    assert_eq!(first_root.row_type.len(), 1);
    assert_eq!(first_root.row_type[0].name, "visible_a");
    assert!(
        first_root
            .project_rex
            .iter()
            .all(|rex| rex.source_sql.is_none())
    );
    let first_sort = &first_root.inputs[0];
    assert_eq!(first_sort.rel_type, "LogicalSort");
    assert_eq!(first_sort.row_type.len(), 2);
    assert_eq!(first_sort.collation[0].field_index, 1);
    let first_order = first_sort
        .source_order
        .as_ref()
        .expect("exact first ORDER BY authority");
    assert_eq!(first_order.kind, "ORDER_BY");
    assert_eq!(
        first_order.query_text,
        "select a as visible_a from t where a > 0"
    );
    assert_eq!(first_order.order_list_text, "b desc nulls first");
    assert_eq!(first_order.items.len(), 1);
    assert_eq!(first_order.items[0].item_text, "b desc nulls first");
    assert_eq!(first_order.items[0].expression_text, "b");
    assert_eq!(
        first_sort.inputs[0].project_rex[1].source_node_id,
        Some(first_order.items[0].expression_node_id.clone())
    );
    assert!(
        find_first_source_where_filter(first_root).is_some(),
        "the synthetic visible-output mask must not consume child WHERE ownership"
    );

    let second_root = raw.queries[1].rel.as_ref().expect("second visible root");
    assert_eq!(second_root.rel_type, "LogicalProject");
    assert_eq!(second_root.row_type.len(), 2);
    assert_eq!(second_root.row_type[0].name, "out_b");
    assert_eq!(second_root.row_type[1].name, "out_a");
    assert!(
        second_root
            .project_rex
            .iter()
            .all(|rex| rex.source_sql.is_none())
    );
    let second_sort = &second_root.inputs[0];
    assert_eq!(second_sort.rel_type, "LogicalSort");
    assert_eq!(second_sort.row_type.len(), 3);
    assert_eq!(second_sort.collation[0].field_index, 2);
    let second_order = second_sort
        .source_order
        .as_ref()
        .expect("exact second ORDER BY authority");
    assert_eq!(second_order.order_list_text, "a + b");
    assert_eq!(second_order.items[0].expression_text, "a + b");

    let pristine = raw.clone();
    let mut mutations = Vec::new();

    let mut missing = pristine.clone();
    missing.queries[0].rel.as_mut().unwrap().inputs[0].source_order = None;
    mutations.push(("missing sourceOrder", missing));

    let mut wrong_index = pristine.clone();
    wrong_index.queries[0].rel.as_mut().unwrap().inputs[0].collation[0].field_index = 0;
    mutations.push(("wrong field index", wrong_index));

    let mut wrong_direction = pristine.clone();
    wrong_direction.queries[0].rel.as_mut().unwrap().inputs[0].collation[0].direction =
        "ASCENDING".to_owned();
    mutations.push(("wrong direction", wrong_direction));

    let mut wrong_nulls = pristine.clone();
    wrong_nulls.queries[0].rel.as_mut().unwrap().inputs[0].collation[0].null_direction =
        Some("LAST".to_owned());
    mutations.push(("wrong NULL placement", wrong_nulls));

    let mut forged_item = pristine.clone();
    forged_item.queries[0].rel.as_mut().unwrap().inputs[0]
        .source_order
        .as_mut()
        .unwrap()
        .items[0]
        .expression_text = "a".to_owned();
    mutations.push(("forged expression text", forged_item));

    let mut borrowed_carrier = pristine.clone();
    let project = &mut borrowed_carrier.queries[0].rel.as_mut().unwrap().inputs[0].inputs[0];
    let borrowed_node_id = project.project_rex[0].source_node_id.clone();
    let borrowed_text = project.project_rex[0].source_text.clone();
    project.project_rex[1].source_node_id = borrowed_node_id;
    project.project_rex[1].source_text = borrowed_text;
    mutations.push(("borrowed hidden carrier", borrowed_carrier));

    let mut swapped_visible_mask = pristine.clone();
    let project = swapped_visible_mask.queries[1].rel.as_mut().unwrap();
    project.project_rex.swap(0, 1);
    project.row_type.swap(0, 1);
    mutations.push((
        "coherently swapped visible-output mask",
        swapped_visible_mask,
    ));

    let mut duplicated_visible_mask = pristine.clone();
    let project = duplicated_visible_mask.queries[1].rel.as_mut().unwrap();
    project.project_rex[1] = project.project_rex[0].clone();
    project.row_type[1] = project.row_type[0].clone();
    mutations.push((
        "coherently duplicated visible-output mask",
        duplicated_visible_mask,
    ));

    let mut truncated_visible_mask = pristine.clone();
    let project = truncated_visible_mask.queries[1].rel.as_mut().unwrap();
    project.project_rex.pop();
    project.row_type.pop();
    mutations.push((
        "coherently truncated visible-output mask",
        truncated_visible_mask,
    ));

    let mut empty_visible_mask = pristine.clone();
    let project = empty_visible_mask.queries[1].rel.as_mut().unwrap();
    project.project_rex.clear();
    project.row_type.clear();
    mutations.push(("zero-width visible-output mask", empty_visible_mask));

    let mut source_removed_project = pristine.clone();
    let project = &mut source_removed_project.queries[1]
        .rel
        .as_mut()
        .unwrap()
        .inputs[0]
        .inputs[0];
    assert_eq!(project.rel_type, "LogicalProject");
    project.source_query_block_id = None;
    project.source_root_query_block_id = None;
    project.source_sql = None;
    project.source_kind = None;
    project.source_operator = None;
    project.source_node_id = None;
    project.source_text = None;
    for rex in &mut project.project_rex {
        clear_rex_source(rex);
    }
    project.project_rex.swap(0, 1);
    project.row_type.swap(0, 1);
    let mut forged_row_project = source_removed_project.clone();
    let project = &mut forged_row_project.queries[1].rel.as_mut().unwrap().inputs[0].inputs[0];
    project.source_kind = Some("ROW".to_owned());
    project.source_operator = Some("ROW".to_owned());
    mutations.push((
        "coherently reordered source-erased ordinary Project",
        source_removed_project,
    ));
    mutations.push((
        "ordinary Project with forged ROW markers",
        forged_row_project,
    ));

    for (label, mutation) in mutations {
        assert!(
            convert_raw_file(mutation).is_err(),
            "accepted {label} ORDER BY mutation"
        );
    }

    let ir = convert_raw_file(raw).expect("convert visible RelRoot projections");
    let RelExpr::Project {
        input,
        exprs,
        output,
        ..
    } = &ir.queries[0].rel
    else {
        panic!("first typed root must be the visible-output Project")
    };
    assert_eq!(output.len(), 1);
    assert_eq!(output[0].name, "visible_a");
    assert!(exprs.iter().all(|expr| expr.source.is_none()));
    let RelExpr::Sort {
        collation, output, ..
    } = input.as_ref()
    else {
        panic!("first visible-output Project must retain its hidden-key Sort child")
    };
    assert_eq!(output.len(), 2);
    assert_eq!(collation[0].field_index, 1);
    assert!(first_typed_owned_where(&ir.queries[0].rel).is_some());

    let RelExpr::Project {
        input,
        exprs,
        output,
        ..
    } = &ir.queries[1].rel
    else {
        panic!("second typed root must be the visible-output Project")
    };
    assert_eq!(
        output
            .iter()
            .map(|column| column.name.as_str())
            .collect::<Vec<_>>(),
        ["out_b", "out_a"]
    );
    assert!(exprs.iter().all(|expr| expr.source.is_none()));
    let RelExpr::Sort {
        collation, output, ..
    } = input.as_ref()
    else {
        panic!("second visible-output Project must retain its hidden-key Sort child")
    };
    assert_eq!(output.len(), 3);
    assert_eq!(collation[0].field_index, 2);

    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_binds_project_aggregate_refs_to_exact_call_outputs() {
    let repo = repo_root();
    let temp = temp_dir("project-aggregate-output-lineage");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&schema, "create table t(a integer, b integer);\n").unwrap();
    fs::write(&query, "select sum(a)+1 as x, sum(b)+2 as y from t;\n").unwrap();

    let raw = run_calcite(&repo, &schema, &query);
    convert_raw_file(raw.clone()).expect("exact Aggregate outputs bind both Project expressions");

    let mut swapped = raw;
    let project = swapped.queries[0].rel.as_mut().unwrap();
    assert_eq!(project.rel_type, "LogicalProject");
    let first = &mut project.project_rex[0].operands[0];
    assert_eq!(first.source_text.as_deref(), Some("sum(a)"));
    first.index = Some(1);
    first.text = Some("$1".to_owned());
    let second = &mut project.project_rex[1].operands[0];
    assert_eq!(second.source_text.as_deref(), Some("sum(b)"));
    second.index = Some(0);
    second.text = Some("$0".to_owned());
    assert!(
        convert_raw_file(swapped).is_err(),
        "same-typed Aggregate outputs must not be positionally swapped beneath exact SUM roots"
    );

    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_order_by_alias_error_respects_postgres_identifier_casing() {
    fn one(raw: &CalciteFile, index: usize) -> CalciteFile {
        let mut one = raw.clone();
        one.queries = vec![raw.queries[index].clone()];
        one
    }

    fn rex_by_source_id_mut<'a>(
        rex: &'a mut CalciteRex,
        source_node_id: &str,
    ) -> Option<&'a mut CalciteRex> {
        if rex.source_node_id.as_deref() == Some(source_node_id) {
            return Some(rex);
        }
        if let Some(reference) = rex.reference_expr.as_deref_mut()
            && let Some(found) = rex_by_source_id_mut(reference, source_node_id)
        {
            return Some(found);
        }
        for operand in &mut rex.operands {
            if let Some(found) = rex_by_source_id_mut(operand, source_node_id) {
                return Some(found);
            }
        }
        None
    }

    fn project_rex_by_source_id_mut<'a>(
        rel: &'a mut CalciteRel,
        source_node_id: &str,
    ) -> Option<&'a mut CalciteRex> {
        for rex in &mut rel.project_rex {
            if let Some(found) = rex_by_source_id_mut(rex, source_node_id) {
                return Some(found);
            }
        }
        for input in &mut rel.inputs {
            if let Some(found) = project_rex_by_source_id_mut(input, source_node_id) {
                return Some(found);
            }
        }
        None
    }

    let repo = repo_root();
    let temp = temp_dir("order-by-alias-error-identifier-casing");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&schema, "create table t(x integer);\n").unwrap();
    fs::write(
        &query,
        "select x as Foo from t order by foo + 1;\n\
         select x as \"Foo\" from t order by \"Foo\" + 1;\n\
         select x as \"Foo\" from t order by foo + 1;\n\
         select x as \"Foo\" from t order by \"Foo\";\n\
         select x as \"Foo\" from t order by foo;\n",
    )
    .unwrap();

    let raw = run_calcite(&repo, &schema, &query);
    assert_eq!(raw.queries.len(), 5);
    for (index, output_alias) in [(0, "foo"), (1, "Foo")] {
        let marker = raw.queries[index]
            .source_analysis_error
            .as_ref()
            .unwrap_or_else(|| panic!("query {index}: missing source analysis error"));
        assert_eq!(
            marker.kind,
            "POSTGRES_ORDER_BY_ALIAS_EXPRESSION_UNDEFINED_COLUMN"
        );
        assert_eq!(marker.sql_state, "42703");
        assert_eq!(marker.output_alias, output_alias);
        assert!(raw.queries[index].error.is_none());
        assert!(raw.queries[index].rel.is_some());
        let ir = convert_raw_file(one(&raw, index))
            .unwrap_or_else(|error| panic!("query {index}: exact terminal alias error: {error}"));
        assert!(matches!(
            ir.queries[0].analysis_errors.as_slice(),
            [QueryAnalysisError::PostgresOrderByAliasExpressionUndefinedColumn {
                sql_state,
                output_alias: converted_alias,
                ..
            }] if sql_state == "42703" && converted_alias == output_alias
        ));
    }

    let reject = |label: &str, mutated: CalciteFile| {
        assert!(
            convert_raw_file(mutated).is_err(),
            "terminal ORDER-alias control accepted {label}"
        );
    };
    let marker = raw.queries[0]
        .source_analysis_error
        .as_ref()
        .expect("unquoted alias marker");
    let alias_node_id = marker.source_alias_reference_node_id.clone();

    let mut missing_marker = one(&raw, 0);
    missing_marker.queries[0].source_analysis_error = None;
    reject("a missing query-analysis marker", missing_marker);

    let mut wrong_node = one(&raw, 0);
    project_rex_by_source_id_mut(wrong_node.queries[0].rel.as_mut().unwrap(), &alias_node_id)
        .expect("terminal alias Rex")
        .source_node_id = Some("1:8-1:8".to_owned());
    reject("a forged alias-reference node", wrong_node);

    let mut wrong_text = one(&raw, 0);
    let alias =
        project_rex_by_source_id_mut(wrong_text.queries[0].rel.as_mut().unwrap(), &alias_node_id)
            .expect("terminal alias Rex");
    alias.source_text = Some("x".to_owned());
    alias.source_sql = Some("x".to_owned());
    reject("forged alias-reference text", wrong_text);

    let mut wrong_rendered_text = one(&raw, 0);
    project_rex_by_source_id_mut(
        wrong_rendered_text.queries[0].rel.as_mut().unwrap(),
        &alias_node_id,
    )
    .expect("terminal alias Rex")
    .source_sql = Some("different_alias".to_owned());
    reject("forged rendered alias text", wrong_rendered_text);

    let mut wrong_index = one(&raw, 0);
    let alias =
        project_rex_by_source_id_mut(wrong_index.queries[0].rel.as_mut().unwrap(), &alias_node_id)
            .expect("terminal alias Rex");
    alias.index = Some(1);
    alias.text = Some("$1".to_owned());
    reject("a forged generated input index", wrong_index);

    let mut wrong_type = one(&raw, 0);
    let alias =
        project_rex_by_source_id_mut(wrong_type.queries[0].rel.as_mut().unwrap(), &alias_node_id)
            .expect("terminal alias Rex");
    alias.ty = Some("BIGINT".to_owned());
    alias.full_type = Some("BIGINT".to_owned());
    reject("a forged generated type", wrong_type);

    let mut duplicate_alias = one(&raw, 0);
    let hidden_project = &mut duplicate_alias.queries[0].rel.as_mut().unwrap().inputs[0].inputs[0];
    let duplicate = hidden_project.project_rex[1].clone();
    hidden_project.project_rex.push(duplicate);
    hidden_project
        .row_type
        .push(hidden_project.row_type[1].clone());
    reject("a duplicated terminal alias expansion", duplicate_alias);

    for index in [2, 4] {
        assert!(
            raw.queries[index].source_analysis_error.is_none(),
            "query {index}: a differently cased unquoted name must not bind a quoted alias"
        );
        assert!(
            raw.queries[index].error.is_some() && raw.queries[index].rel.is_none(),
            "query {index}: Calcite must reject the unresolved name instead of producing an unmarked relation"
        );
    }
    assert!(raw.queries[3].source_analysis_error.is_none());
    assert!(raw.queries[3].error.is_none());
    assert!(raw.queries[3].rel.is_some());

    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires SQLGlot, the Java Calcite wrapper, and frozen benchmark inputs"]
fn calcite_wrappers_tpcds_rank_queries_hide_only_the_relroot_order_helper() {
    with_large_calcite_stack(|| {
        let repo = repo_root();
        let temp = temp_dir("tpcds-rank-visible-relroot");
        for query_number in ["086", "070", "036"] {
            let case = repo.join(format!(
                "benchmarks/core/.generated/sqlsolver/nonwetune-flat/tpcds-variants__query{query_number}"
            ));
            for production in [false, true] {
                for sql_name in ["sql1.sql", "sql2.sql"] {
                    let raw = if production {
                        run_calcite_sqlglot(
                            &repo,
                            &case.join("schema.sql"),
                            &case.join(sql_name),
                            &temp.join(format!("q{query_number}-{sql_name}-normalized.sql")),
                        )
                    } else {
                        run_calcite(&repo, &case.join("schema.sql"), &case.join(sql_name))
                    };
                    let label = format!(
                        "Q{query_number}/{sql_name}/{}",
                        if production { "production" } else { "direct" }
                    );
                    let root = raw.queries[0]
                        .rel
                        .as_ref()
                        .unwrap_or_else(|| panic!("{label}: missing relation"));
                    assert!(
                        raw.queries[0].source_analysis_error.is_none(),
                        "{label}: frozen PostgreSQL materialization expands nested ORDER BY aliases before Calcite"
                    );
                    assert_eq!(root.rel_type, "LogicalProject", "{label}");
                    assert_eq!(root.row_type.len(), 5, "{label}: visible arity");
                    assert!(
                        root.project_rex.iter().all(|rex| rex.source_sql.is_none()),
                        "{label}: synthetic output-mask Rex refs must have no source expression"
                    );
                    let [sort] = root.inputs.as_slice() else {
                        panic!("{label}: visible root must have one child")
                    };
                    assert_eq!(sort.rel_type, "LogicalSort", "{label}");
                    assert_eq!(sort.row_type.len(), 6, "{label}: hidden-key arity");
                    assert!(
                        sort.collation
                            .iter()
                            .all(|key| key.field_index < sort.row_type.len()),
                        "{label}: Sort key must remain bound to the six-column child"
                    );
                    assert_eq!(
                        sort.source_query_block_id, root.source_query_block_id,
                        "{label}: the hidden-key Sort must retain the root query block"
                    );
                    assert_eq!(
                        sort.source_node_id, root.source_node_id,
                        "{label}: the hidden-key Sort must retain the original root source node"
                    );
                    assert_eq!(
                        sort.source_sql, root.source_sql,
                        "{label}: the synthetic mask must not descend source context into FROM"
                    );
                    if query_number == "036" {
                        let computed = sort
                            .inputs
                            .first()
                            .unwrap_or_else(|| panic!("{label}: missing computed Project"));
                        assert_eq!(computed.rel_type, "LogicalProject", "{label}");
                        assert_eq!(computed.project_rex.len(), 6, "{label}");
                        let rank_window = computed.project_rex[4]
                            .window
                            .as_deref()
                            .unwrap_or_else(|| panic!("{label}: missing RANK window"));
                        let window_zero = rank_window.partition_keys[1]
                            .operands
                            .first()
                            .and_then(|comparison| comparison.operands.get(1))
                            .unwrap_or_else(|| panic!("{label}: missing visible window CASE zero"));
                        let hidden_zero = computed.project_rex[5]
                            .operands
                            .first()
                            .and_then(|comparison| comparison.operands.get(1))
                            .unwrap_or_else(|| {
                                panic!("{label}: missing hidden ORDER BY CASE zero")
                            });
                        for (role, zero) in [
                            ("visible window", window_zero),
                            ("hidden ORDER BY", hidden_zero),
                        ] {
                            assert_eq!(
                                zero.literal_value2.as_deref(),
                                Some("0"),
                                "{label}: {role} generated value"
                            );
                            assert_eq!(
                                zero.source_sql.as_deref(),
                                Some("0"),
                                "{label}: {role} must bind the exact source literal"
                            );
                            assert_eq!(
                                zero.source_kind.as_deref(),
                                Some("LITERAL"),
                                "{label}: {role} must not fabricate cast provenance"
                            );
                        }
                    }
                    if query_number == "086" {
                        assert!(
                            !rel_contains_literal_with_identifier_source(root),
                            "{label}: an inlined CTE literal must bind its defining source literal, not the outer projected identifier"
                        );
                    }

                    {
                        let computed = sort
                            .inputs
                            .first()
                            .unwrap_or_else(|| panic!("{label}: missing computed Project"));
                        let rank = computed
                            .project_rex
                            .get(4)
                            .unwrap_or_else(|| panic!("{label}: missing RANK projection"));
                        let rank_window = rank
                            .window
                            .as_deref()
                            .unwrap_or_else(|| panic!("{label}: missing RANK window"));
                        let partition_case = rank_window
                            .partition_keys
                            .get(1)
                            .unwrap_or_else(|| panic!("{label}: missing second partition key"));
                        assert_eq!(partition_case.kind.as_deref(), Some("CASE"), "{label}");
                        assert_eq!(partition_case.operands.len(), 3, "{label}");
                        assert!(
                            partition_case.source_text.as_deref().is_some_and(|source| {
                                source.to_ascii_uppercase().starts_with("CASE ")
                                    && !source.to_ascii_uppercase().contains(" ELSE ")
                            }),
                            "{label}: benchmark CASE must have an omitted ELSE"
                        );
                        let implicit_else = &partition_case.operands[2];
                        assert_eq!(
                            implicit_else.literal_type_name.as_deref(),
                            Some("NULL"),
                            "{label}: generated terminal CASE value"
                        );
                        assert_eq!(
                            implicit_else.literal_value.as_deref(),
                            Some("null"),
                            "{label}"
                        );
                        assert_eq!(
                            implicit_else.literal_value2.as_deref(),
                            Some("null"),
                            "{label}"
                        );
                        assert!(implicit_else.nullable, "{label}");
                        assert_eq!(implicit_else.ty, partition_case.ty, "{label}");
                        assert_eq!(implicit_else.full_type, partition_case.full_type, "{label}");
                        assert_eq!(implicit_else.precision, partition_case.precision, "{label}");
                        assert_eq!(implicit_else.scale, partition_case.scale, "{label}");
                        assert_eq!(implicit_else.charset, partition_case.charset, "{label}");
                        assert_eq!(
                            implicit_else.type_collation, partition_case.type_collation,
                            "{label}"
                        );
                        assert!(implicit_else.source_sql.is_none(), "{label}");
                        assert!(implicit_else.source_node_id.is_none(), "{label}");
                        assert!(implicit_else.source_text.is_none(), "{label}");
                        assert!(implicit_else.source_kind.is_none(), "{label}");
                        assert!(implicit_else.source_operator.is_none(), "{label}");
                        assert!(implicit_else.source_identifier_names.is_empty(), "{label}");
                        assert!(implicit_else.source_identifier_quoted.is_empty(), "{label}");
                    }

                    if query_number == "036" && sql_name == "sql1.sql" && !production {
                        fn partition_case(raw: &mut CalciteFile) -> &mut CalciteRex {
                            let rel = raw.queries[0].rel.as_mut().expect("Q036 relation");
                            let rank = first_window_rex_mut(rel, "RANK").expect("Q036 RANK window");
                            rank.window
                                .as_deref_mut()
                                .expect("Q036 window")
                                .partition_keys
                                .get_mut(1)
                                .expect("Q036 CASE partition key")
                        }
                        let reject = |role: &str, mutated: CalciteFile| {
                            assert!(
                                convert_raw_file(mutated).is_err(),
                                "Q036 forged implicit ELSE {role} must fail closed"
                            );
                        };

                        let mut wrong_value = raw.clone();
                        let terminal = &mut partition_case(&mut wrong_value).operands[2];
                        terminal.literal_value = Some("1".to_owned());
                        terminal.literal_value2 = Some("1".to_owned());
                        reject("value", wrong_value);

                        let mut wrong_type = raw.clone();
                        let terminal = &mut partition_case(&mut wrong_type).operands[2];
                        terminal.ty = Some("INTEGER".to_owned());
                        terminal.full_type = Some("INTEGER".to_owned());
                        terminal.precision = Some(10);
                        terminal.scale = Some(0);
                        reject("type", wrong_type);

                        let mut wrong_nullability = raw.clone();
                        partition_case(&mut wrong_nullability).operands[2].nullable = false;
                        reject("nullability", wrong_nullability);

                        let mut borrowed_owner = raw.clone();
                        let case = partition_case(&mut borrowed_owner);
                        let owner_node_id = case.source_node_id.clone();
                        let owner_text = case.source_text.clone();
                        let terminal = &mut case.operands[2];
                        terminal.source_sql = Some("NULL".to_owned());
                        terminal.source_node_id = owner_node_id;
                        terminal.source_text = owner_text;
                        terminal.source_kind = Some("LITERAL".to_owned());
                        reject("owner identity", borrowed_owner);

                        let mut reordered_keys = raw.clone();
                        let rank = first_window_rex_mut(
                            reordered_keys.queries[0].rel.as_mut().unwrap(),
                            "RANK",
                        )
                        .unwrap();
                        rank.window
                            .as_deref_mut()
                            .unwrap()
                            .partition_keys
                            .swap(0, 1);
                        reject("partition order", reordered_keys);
                    }

                    if query_number == "036" && sql_name == "sql2.sql" && !production {
                        fn rex_has_cte_public_output(rex: &CalciteRex, index: usize) -> bool {
                            rex.source_expansion.as_ref().is_some_and(|expansion| {
                                expansion.public_output_index == Some(index)
                            }) || rex
                                .reference_expr
                                .as_deref()
                                .is_some_and(|rex| rex_has_cte_public_output(rex, index))
                                || rex
                                    .operands
                                    .iter()
                                    .any(|rex| rex_has_cte_public_output(rex, index))
                        }
                        fn omitted_ratio_project_mut(
                            rel: &mut CalciteRel,
                        ) -> Option<&mut CalciteRel> {
                            let is_omitted_ratio = rel.rel_type == "LogicalProject"
                                && matches!(
                                    rel.inputs.as_slice(),
                                    [input] if input.rel_type == "LogicalAggregate"
                                )
                                && rel.source_input_cte_uses.as_slice().first().is_some_and(|use_| {
                                    use_.as_ref().is_some_and(|use_| {
                                        use_.definition_query_text.contains(
                                            "SUM(ss_net_profit) / SUM(ss_ext_sales_price) AS gross_margin",
                                        )
                                    })
                                })
                                && !rel
                                    .project_rex
                                    .iter()
                                    .any(|rex| rex_has_cte_public_output(rex, 2));
                            if is_omitted_ratio {
                                return Some(rel);
                            }
                            rel.inputs.iter_mut().find_map(omitted_ratio_project_mut)
                        }
                        let reject = |role: &str, mutated: CalciteFile| {
                            assert!(
                                convert_raw_file(mutated).is_err(),
                                "Q036 forged omitted CTE ratio {role} must fail closed"
                            );
                        };

                        let mut wrong_index = raw.clone();
                        let project = omitted_ratio_project_mut(
                            wrong_index.queries[0]
                                .rel
                                .as_mut()
                                .expect("Q036 target relation"),
                        )
                        .expect("Q036 omitted ratio Project");
                        assert_eq!(project.project_rex[1].index, Some(2));
                        project.project_rex[1].index = Some(3);
                        project.project_rex[1].text = Some("$3".to_owned());
                        reject("input index", wrong_index);

                        let mut wrong_type = raw.clone();
                        let project = omitted_ratio_project_mut(
                            wrong_type.queries[0]
                                .rel
                                .as_mut()
                                .expect("Q036 target relation"),
                        )
                        .expect("Q036 omitted ratio Project");
                        let aggregate = project.inputs.first_mut().expect("Q036 CTE Aggregate");
                        aggregate.row_type[2].ty = "INTEGER".to_owned();
                        aggregate.row_type[2].full_type = Some("INTEGER".to_owned());
                        aggregate.row_type[2].precision = Some(10);
                        aggregate.row_type[2].scale = Some(0);
                        aggregate.agg_call_details[0].ty = Some("INTEGER".to_owned());
                        aggregate.agg_call_details[0].full_type = Some("INTEGER".to_owned());
                        aggregate.agg_call_details[0].precision = Some(10);
                        aggregate.agg_call_details[0].scale = Some(0);
                        reject("SUM result type", wrong_type);

                        let mut wrong_expression = raw.clone();
                        let project = omitted_ratio_project_mut(
                            wrong_expression.queries[0]
                                .rel
                                .as_mut()
                                .expect("Q036 target relation"),
                        )
                        .expect("Q036 omitted ratio Project");
                        project.source_input_cte_uses[0]
                            .as_mut()
                            .expect("Q036 CTE use")
                            .definition_query_text = project.source_input_cte_uses[0]
                            .as_ref()
                            .unwrap()
                            .definition_query_text
                            .replacen(
                                "SUM(ss_net_profit) / SUM(ss_ext_sales_price)",
                                "SUM(ss_net_profit) + SUM(ss_ext_sales_price)",
                                1,
                            );
                        reject("expression", wrong_expression);

                        let mut swapped_operands = raw.clone();
                        let project = omitted_ratio_project_mut(
                            swapped_operands.queries[0]
                                .rel
                                .as_mut()
                                .expect("Q036 target relation"),
                        )
                        .expect("Q036 omitted ratio Project");
                        project.project_rex.swap(1, 2);
                        reject("swapped SUM bindings", swapped_operands);

                        let mut repeated_operand = raw.clone();
                        let project = omitted_ratio_project_mut(
                            repeated_operand.queries[0]
                                .rel
                                .as_mut()
                                .expect("Q036 target relation"),
                        )
                        .expect("Q036 omitted ratio Project");
                        project.project_rex[2] = project.project_rex[1].clone();
                        reject("repeated SUM binding", repeated_operand);
                    }
                    let ir = convert_raw_file(raw)
                        .unwrap_or_else(|error| panic!("{label}: typed conversion: {error}"));
                    let query = &ir.queries[0];
                    if query_number == "036" && sql_name == "sql2.sql" {
                        fn validate_reconstructed_ratios(rel: &RelExpr, label: &str) -> usize {
                            let mut found = 0usize;
                            match rel {
                                RelExpr::Project {
                                    input,
                                    exprs,
                                    output,
                                    ..
                                } => {
                                    if let RelExpr::Project {
                                        exprs: inner_exprs,
                                        output: inner_output,
                                        ..
                                    } = input.as_ref()
                                        && inner_output.len() == output.len() + 1
                                        && inner_output.last().map(|column| column.name.as_str())
                                            == Some("gross_margin")
                                    {
                                        assert_eq!(exprs.len(), output.len(), "{label}");
                                        assert!(
                                            exprs.iter().enumerate().all(|(index, expr)| {
                                                matches!(
                                                    expr.parsed,
                                                    ScalarAst::InputRef { index: actual }
                                                        if actual == index
                                                ) && expr.source.is_none()
                                            }),
                                            "{label}: consumer mask must be exact positional identity"
                                        );
                                        assert_eq!(
                                            &inner_output[..output.len()],
                                            output.as_slice(),
                                            "{label}: consumer-visible row must remain byte-for-byte typed"
                                        );
                                        let hidden = inner_output.last().unwrap();
                                        assert_eq!(
                                            hidden.ty,
                                            SqlType::decimal(None, None),
                                            "{label}: PostgreSQL SUM division is typmodless NUMERIC"
                                        );
                                        assert!(
                                            hidden.nullable,
                                            "{label}: nullable SUM denominator must retain NULL propagation"
                                        );
                                        let ratio = inner_exprs.last().unwrap();
                                        let ScalarAst::Call {
                                            op: ScalarOp::Divide,
                                            args,
                                            ..
                                        } = &ratio.parsed
                                        else {
                                            panic!(
                                                "{label}: hidden CTE output must remain a division"
                                            )
                                        };
                                        assert!(
                                            matches!(
                                                args.as_slice(),
                                                [ScalarAst::InputRef { index: left }, ScalarAst::InputRef { index: right }]
                                                    if left != right
                                            ),
                                            "{label}: hidden division must retain two distinct ordered SUM results"
                                        );
                                        let source = ratio
                                            .source
                                            .as_ref()
                                            .expect("reconstructed ratio source");
                                        assert_eq!(
                                            source.kind.as_deref(),
                                            Some("DIVIDE"),
                                            "{label}"
                                        );
                                        assert_eq!(
                                            source.operator.as_deref(),
                                            Some("/"),
                                            "{label}"
                                        );
                                        assert_eq!(source.operands.len(), 2, "{label}");
                                        found += 1;
                                    }
                                    found += validate_reconstructed_ratios(input, label);
                                }
                                RelExpr::Filter { input, .. }
                                | RelExpr::NativeHaving { input, .. }
                                | RelExpr::Aggregate { input, .. }
                                | RelExpr::Distinct { input, .. }
                                | RelExpr::Sort { input, .. } => {
                                    found += validate_reconstructed_ratios(input, label);
                                }
                                RelExpr::Join { left, right, .. } => {
                                    found += validate_reconstructed_ratios(left, label);
                                    found += validate_reconstructed_ratios(right, label);
                                }
                                RelExpr::Set { inputs, .. } => {
                                    found += inputs
                                        .iter()
                                        .map(|input| validate_reconstructed_ratios(input, label))
                                        .sum::<usize>();
                                }
                                RelExpr::TableScan { .. } | RelExpr::Values { .. } => {}
                            }
                            found
                        }
                        assert_eq!(
                            validate_reconstructed_ratios(&query.rel, &label),
                            2,
                            "{label}: both pruned results clones need a declarative ratio boundary"
                        );
                    }
                    assert!(
                        query.analysis_errors.iter().all(|error| !matches!(
                            error,
                            QueryAnalysisError::PostgresOrderByAliasExpressionUndefinedColumn { .. }
                        )),
                        "{label}: materialized GROUPING expression must not be relabeled as an invalid alias reference"
                    );
                    assert_eq!(query.output().len(), 5, "{label}: query output arity");
                    assert_eq!(
                        query.output()[3].ty,
                        SqlType::Integer,
                        "{label}: PostgreSQL lochierarchy is int4"
                    );
                    let RelExpr::Project {
                        input,
                        exprs,
                        output,
                        ..
                    } = &query.rel
                    else {
                        panic!("{label}: typed visible root must be Project")
                    };
                    assert_eq!(output.len(), 5, "{label}");
                    assert_eq!(output[3].ty, SqlType::Integer, "{label}");
                    assert!(exprs.iter().all(|expr| expr.source.is_none()), "{label}");
                    let RelExpr::Sort {
                        input: sort_input,
                        collation,
                        output,
                        ..
                    } = input.as_ref()
                    else {
                        panic!("{label}: typed hidden-key child must be Sort")
                    };
                    assert_eq!(output.len(), 6, "{label}");
                    assert!(
                        collation.iter().all(|key| key.field_index < output.len()),
                        "{label}: typed Sort key must remain in bounds"
                    );
                    if sql_name == "sql1.sql" {
                        let RelExpr::Project { input, output, .. } = sort_input.as_ref() else {
                            panic!("{label}: source Sort child must be its computed Project")
                        };
                        assert_eq!(output[3].ty, SqlType::Integer, "{label}");
                        let RelExpr::Aggregate { agg_calls, .. } = input.as_ref() else {
                            panic!("{label}: source computed Project must own the Aggregate")
                        };
                        assert!(
                            agg_calls.iter().all(|call| {
                                call.modifiers
                                    .source_grouping
                                    .as_ref()
                                    .is_some_and(|source| {
                                        source.kind == "ROLLUP"
                                            && source.group_indexes == [0, 1]
                                            && source.grouping_sets
                                                == [vec![0, 1], vec![0], Vec::new()]
                                    })
                            }),
                            "{label}: every aggregate call must share exact ROLLUP authority"
                        );
                    }
                }
            }
        }
        fs::remove_dir_all(&temp).unwrap();
    });
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_distinguishes_implicit_and_explicit_case_else_null() {
    fn first_case_in_rex(rex: &CalciteRex) -> Option<&CalciteRex> {
        if rex.kind.as_deref() == Some("CASE") && rex.class.as_deref() == Some("RexCall") {
            return Some(rex);
        }
        rex.operands.iter().find_map(first_case_in_rex).or_else(|| {
            rex.window.as_deref().and_then(|window| {
                window
                    .partition_keys
                    .iter()
                    .find_map(first_case_in_rex)
                    .or_else(|| {
                        window
                            .order_keys
                            .iter()
                            .find_map(|key| first_case_in_rex(&key.expr))
                    })
            })
        })
    }

    fn first_case(rel: &CalciteRel) -> Option<&CalciteRex> {
        rel_rexes(rel)
            .find_map(first_case_in_rex)
            .or_else(|| rel.inputs.iter().find_map(first_case))
    }

    let repo = repo_root();
    let temp = temp_dir("implicit-explicit-case-else-null");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&schema, "create table t(a integer, b integer);\n").unwrap();
    fs::write(
        &query,
        "SELECT CASE WHEN a = 0 THEN b END AS c FROM t;\n\
         SELECT CASE WHEN a = 0 THEN b ELSE NULL END AS c FROM t;\n\
         SELECT RANK() OVER (PARTITION BY CASE WHEN a = 0 THEN b END ORDER BY a) FROM t;\n\
         SELECT RANK() OVER (PARTITION BY CASE WHEN a = 0 THEN b ELSE NULL END ORDER BY a) FROM t;\n\
         SELECT CASE a WHEN 0 THEN b END AS c FROM t;\n\
         SELECT CASE a WHEN 0 THEN b ELSE NULL END AS c FROM t;\n\
         SELECT CAST(CASE WHEN a = 0 THEN b END AS INTEGER) AS c FROM t;\n\
         SELECT CAST(CASE WHEN a = 0 THEN b ELSE NULL END AS INTEGER) AS c FROM t;\n\
         SELECT CASE WHEN a = 0 THEN b ELSE a END AS c FROM t;\n\
         SELECT CASE WHEN a = 0 THEN b ELSE CAST(NULL AS INTEGER) END AS c FROM t;\n",
    )
    .unwrap();

    let raw = run_calcite(&repo, &schema, &query);
    assert_eq!(raw.queries.len(), 10);
    for index in [0, 2, 4, 6] {
        let case = first_case(raw.queries[index].rel.as_ref().unwrap())
            .unwrap_or_else(|| panic!("query {index}: omitted-ELSE CASE"));
        assert_eq!(case.operands.len(), 3, "query {index}");
        let terminal = &case.operands[2];
        assert_eq!(terminal.literal_type_name.as_deref(), Some("NULL"));
        assert_eq!(terminal.literal_value.as_deref(), Some("null"));
        assert_eq!(terminal.literal_value2.as_deref(), Some("null"));
        assert!(terminal.nullable);
        assert_eq!(terminal.ty, case.ty);
        assert_eq!(terminal.full_type, case.full_type);
        assert_eq!(terminal.precision, case.precision);
        assert_eq!(terminal.scale, case.scale);
        assert!(terminal.source_sql.is_none(), "query {index}");
        assert!(terminal.source_node_id.is_none(), "query {index}");
        assert!(terminal.source_text.is_none(), "query {index}");
        assert!(terminal.source_kind.is_none(), "query {index}");
        assert!(terminal.source_operator.is_none(), "query {index}");
    }
    for index in [1, 3, 5, 7] {
        let case = first_case(raw.queries[index].rel.as_ref().unwrap())
            .unwrap_or_else(|| panic!("query {index}: explicit-ELSE CASE"));
        let terminal = &case.operands[2];
        assert_eq!(terminal.literal_type_name.as_deref(), Some("NULL"));
        assert_eq!(
            terminal.source_sql.as_deref(),
            Some("NULL"),
            "query {index}"
        );
        assert_eq!(
            terminal.source_text.as_deref(),
            Some("NULL"),
            "query {index}"
        );
        assert_eq!(terminal.source_kind.as_deref(), Some("LITERAL"));
        assert_ne!(
            terminal.source_node_id, case.source_node_id,
            "query {index}"
        );
    }
    let non_null = first_case(raw.queries[8].rel.as_ref().unwrap()).unwrap();
    assert_eq!(non_null.operands[2].source_text.as_deref(), Some("a"));
    assert_eq!(
        non_null.operands[2].source_kind.as_deref(),
        Some("IDENTIFIER")
    );
    let cast_null = first_case(raw.queries[9].rel.as_ref().unwrap()).unwrap();
    assert_eq!(cast_null.operands[2].source_kind.as_deref(), Some("CAST"));
    assert_eq!(
        cast_null.operands[2].source_operator.as_deref(),
        Some("CAST")
    );
    assert!(
        cast_null.operands[2]
            .source_text
            .as_deref()
            .is_some_and(|source| source.eq_ignore_ascii_case("CAST(NULL AS INTEGER)"))
    );

    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_keeps_analysis_error_provenance_at_the_exact_scalar_node() {
    let repo = repo_root();
    let temp = temp_dir("analysis-error-scalar-provenance");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&schema, "create table projects(status integer);\n").unwrap();
    fs::write(
        &query,
        "select * from projects where status <> 'ARCHIVED';\n\
         select * from projects where status <> cast('ARCHIVED' as varchar);\n",
    )
    .unwrap();

    let raw = run_calcite(&repo, &schema, &query);
    let bare = first_condition_rex(raw.queries[0].rel.as_ref().unwrap());
    assert_eq!(bare.source_kind.as_deref(), Some("NOT_EQUALS"));
    assert_eq!(bare.source_operator.as_deref(), Some("<>"));
    assert_eq!(bare.operands[0].source_kind.as_deref(), Some("IDENTIFIER"));
    assert_eq!(bare.operands[1].source_kind.as_deref(), Some("LITERAL"));
    assert_eq!(bare.operands[1].source_sql.as_deref(), Some("'ARCHIVED'"));

    let explicitly_cast = first_condition_rex(raw.queries[1].rel.as_ref().unwrap());
    assert_eq!(explicitly_cast.source_kind.as_deref(), Some("NOT_EQUALS"));
    assert_eq!(
        explicitly_cast.operands[1].source_kind.as_deref(),
        Some("CAST")
    );
    assert_eq!(
        explicitly_cast.operands[1].source_operator.as_deref(),
        Some("CAST")
    );
    assert!(
        explicitly_cast.operands[1]
            .source_sql
            .as_deref()
            .is_some_and(|sql| sql.contains("CAST") && sql.contains("VARCHAR"))
    );
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_attests_only_bare_postgres_boolean_integer_equality_errors() {
    let repo = repo_root();
    let temp = temp_dir("postgres-boolean-integer-analysis-error");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&schema, "create table t(b boolean, i integer);\n").unwrap();
    fs::write(
        &query,
        "select * from t where b = 0;\n\
         select * from t where b = 1;\n\
         select * from t where 0 = b;\n\
         select * from t where b = false;\n\
         select * from t where b = '0';\n\
         select * from t where b = cast(0 as boolean);\n\
         select * from t where cast(b as integer) = 0;\n\
         select * from t where i = 0;\n",
    )
    .unwrap();

    let raw = run_calcite(&repo, &schema, &query);
    assert_eq!(raw.queries.len(), 8);
    let marker_count = |index: usize| {
        raw.queries[index]
            .rel
            .as_ref()
            .and_then(find_first_source_where_filter)
            .and_then(|filter| filter.source_where.as_ref())
            .map_or(0, |where_attestation| {
                where_attestation.analysis_errors.len()
            })
    };
    for index in 0..3 {
        assert_eq!(marker_count(index), 1, "positive query {index}");
        let marker =
            &find_first_source_where_filter(raw.queries[index].rel.as_ref().expect("positive rel"))
                .unwrap()
                .source_where
                .as_ref()
                .unwrap()
                .analysis_errors[0];
        assert_eq!(
            marker.kind,
            "POSTGRES_BOOLEAN_INTEGER_EQUALITY_UNDEFINED_FUNCTION"
        );
        assert!(matches!(
            (
                marker.source_literal_canonical_value.as_str(),
                marker.generated_literal_canonical_value.as_str()
            ),
            ("0", "false") | ("1", "true")
        ));
    }
    for index in 3..8 {
        assert_eq!(marker_count(index), 0, "negative query {index}");
    }

    let mut positives = raw;
    positives.queries.truncate(3);
    let ir = convert_raw_file(positives).expect("convert exact marked comparisons");
    assert_eq!(ir.queries.len(), 3);
    for (index, query) in ir.queries.iter().enumerate() {
        fn first_owned_where(rel: &RelExpr) -> Option<&logos_ir::ir::ScalarSourceClauseOwnership> {
            match rel {
                RelExpr::Filter {
                    input, predicate, ..
                } => predicate
                    .source
                    .as_ref()
                    .and_then(|source| source.clause_ownership.as_ref())
                    .or_else(|| first_owned_where(input)),
                RelExpr::Project { input, .. }
                | RelExpr::NativeHaving { input, .. }
                | RelExpr::Aggregate { input, .. }
                | RelExpr::Distinct { input, .. }
                | RelExpr::Sort { input, .. } => first_owned_where(input),
                RelExpr::Join { left, right, .. } => {
                    first_owned_where(left).or_else(|| first_owned_where(right))
                }
                RelExpr::Set { inputs, .. } => inputs.iter().find_map(first_owned_where),
                RelExpr::TableScan { .. } | RelExpr::Values { .. } => None,
            }
        }
        let ownership = first_owned_where(&query.rel).expect("typed source WHERE ownership");
        assert!(
            matches!(
            ownership.analysis_errors.as_slice(),
            [SourceAnalysisErrorProvenance::PostgresBooleanIntegerEqualityUndefinedFunction {
                ..
            }]
        ),
            "positive query {index}"
        );
    }
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_converts_wetune27_boolean_integer_errors_with_exact_branch_markers() {
    fn marker_count(rel: &RelExpr) -> usize {
        match rel {
            RelExpr::TableScan { .. } | RelExpr::Values { .. } => 0,
            RelExpr::Project { input, .. }
            | RelExpr::NativeHaving { input, .. }
            | RelExpr::Aggregate { input, .. }
            | RelExpr::Distinct { input, .. }
            | RelExpr::Sort { input, .. } => marker_count(input),
            RelExpr::Filter {
                input, predicate, ..
            } => {
                predicate
                    .source
                    .as_ref()
                    .and_then(|source| source.clause_ownership.as_ref())
                    .map_or(0, |ownership| ownership.analysis_errors.len())
                    + marker_count(input)
            }
            RelExpr::Join { left, right, .. } => marker_count(left) + marker_count(right),
            RelExpr::Set { inputs, .. } => inputs.iter().map(marker_count).sum(),
        }
    }

    with_large_calcite_stack(|| {
        let repo = repo_root();
        let case = repo.join("benchmarks/core/.generated/sqlsolver/wetune-issues/27");
        for (sql_name, expected_markers) in [("sql1.sql", 1), ("sql2.sql", 2)] {
            let raw = run_calcite(&repo, &case.join("schema.sql"), &case.join(sql_name));
            let ir = convert_raw_file(raw).expect("convert frozen wetune27 query");
            assert_eq!(ir.queries.len(), 1);
            assert_eq!(
                marker_count(&ir.queries[0].rel),
                expected_markers,
                "{sql_name}"
            );
        }
    });
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_attests_exact_two_argument_count_distinct_call() {
    let repo = repo_root();
    let temp = temp_dir("analysis-error-aggregate-provenance");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(
        &schema,
        "create table names(left_name text, right_name text);\n",
    )
    .unwrap();
    fs::write(
        &query,
        "select count(distinct left_name, right_name) from names;\n",
    )
    .unwrap();

    let raw = run_calcite(&repo, &schema, &query);
    let aggregate = first_aggregate(raw.queries[0].rel.as_ref().unwrap());
    let call = &aggregate.agg_call_details[0];
    assert_eq!(call.source_operator.as_deref(), Some("count"));
    assert_eq!(call.source_distinct, Some(true));
    assert_eq!(call.source_operands.len(), 2);
    assert_eq!(
        call.source_operands[0].source_kind.as_deref(),
        Some("IDENTIFIER")
    );
    assert_eq!(
        call.source_operands[0].source_sql.as_deref(),
        Some("left_name")
    );
    assert_eq!(
        call.source_operands[1].source_kind.as_deref(),
        Some("IDENTIFIER")
    );
    assert_eq!(
        call.source_operands[1].source_sql.as_deref(),
        Some("right_name")
    );

    let ir = convert_raw_file(raw).unwrap();
    let RelExpr::Aggregate { agg_calls, .. } = &ir.queries[0].rel else {
        panic!("expected aggregate");
    };
    assert_eq!(agg_calls[0].modifiers.source_distinct, Some(true));
    assert_eq!(
        agg_calls[0]
            .modifiers
            .source
            .as_ref()
            .unwrap()
            .operands
            .len(),
        2
    );
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_closes_exact_aggregate_operator_argument_filter_and_scope_authority() {
    let repo = repo_root();
    let temp = temp_dir("exact-aggregate-source-authority");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(
        &schema,
        "create table t(a integer, b integer, c integer);\n\
         create table outer_t(v integer);\n\
         create table inner_t(v integer);\n",
    )
    .unwrap();
    fs::write(
        &query,
        "select sum(a), count(distinct b) filter (where c = 1), \
                sum(a) filter (where c = 2) from t;\n",
    )
    .unwrap();
    let pristine = run_calcite(&repo, &schema, &query);
    convert_raw_file(pristine.clone()).expect("exact filtered aggregates must convert");

    let mut wrong_operator = pristine.clone();
    {
        let aggregate = first_aggregate_mut(wrong_operator.queries[0].rel.as_mut().unwrap());
        let call = &mut aggregate.agg_call_details[0];
        call.text = "COUNT($0)".to_owned();
        call.function = "COUNT".to_owned();
        call.kind = "COUNT".to_owned();
    }

    let mut lost_distinct = pristine.clone();
    {
        let aggregate = first_aggregate_mut(lost_distinct.queries[0].rel.as_mut().unwrap());
        let call_index = aggregate
            .agg_call_details
            .iter()
            .position(|call| call.function.eq_ignore_ascii_case("COUNT"))
            .unwrap();
        let filter = aggregate.agg_call_details[call_index].filter_arg.unwrap();
        aggregate.agg_call_details[call_index].text = format!("COUNT($1) FILTER ${filter}");
        aggregate.agg_call_details[call_index].distinct = false;
    }

    let mut swapped_argument = pristine.clone();
    {
        let aggregate = first_aggregate_mut(swapped_argument.queries[0].rel.as_mut().unwrap());
        aggregate.agg_call_details[0].text = "SUM($1)".to_owned();
        aggregate.agg_call_details[0].arg_list = vec![1];
    }

    let mut wrong_project_lineage = pristine.clone();
    {
        let aggregate = first_aggregate_mut(wrong_project_lineage.queries[0].rel.as_mut().unwrap());
        let project = &mut aggregate.inputs[0];
        assert_eq!(project.project_rex[0].source_text.as_deref(), Some("a"));
        project.project_rex[0].text = Some("$1".to_owned());
        project.project_rex[0].index = Some(1);
    }

    let mut swapped_filters = pristine.clone();
    {
        let aggregate = first_aggregate_mut(swapped_filters.queries[0].rel.as_mut().unwrap());
        let filtered = aggregate
            .agg_call_details
            .iter()
            .enumerate()
            .filter(|(_, call)| call.filter_arg.is_some_and(|index| index >= 0))
            .map(|(index, _)| index)
            .collect::<Vec<_>>();
        assert_eq!(filtered.len(), 2);
        let left_filter = aggregate.agg_call_details[filtered[0]].filter_arg.unwrap();
        let right_filter = aggregate.agg_call_details[filtered[1]].filter_arg.unwrap();
        for (call_index, filter) in [(filtered[0], right_filter), (filtered[1], left_filter)] {
            let head = aggregate.agg_call_details[call_index]
                .text
                .split_once(" FILTER ")
                .unwrap()
                .0;
            let text = format!("{head} FILTER ${filter}");
            aggregate.agg_call_details[call_index].text = text;
            aggregate.agg_call_details[call_index].filter_arg = Some(filter);
        }
    }

    let mut omitted_details = pristine;
    first_aggregate_mut(omitted_details.queries[0].rel.as_mut().unwrap())
        .agg_call_details
        .clear();

    for forged in [
        wrong_operator,
        lost_distinct,
        swapped_argument,
        wrong_project_lineage,
        swapped_filters,
        omitted_details,
    ] {
        assert!(convert_raw_file(forged).is_err());
    }

    fs::write(&query, "select sum(a), sum(b) from t;\n").unwrap();
    let mut swapped_calls = run_calcite(&repo, &schema, &query);
    {
        let aggregate = first_aggregate_mut(swapped_calls.queries[0].rel.as_mut().unwrap());
        aggregate.agg_call_details.swap(0, 1);
    }
    assert!(
        convert_raw_file(swapped_calls).is_err(),
        "complete same-operator calls may not be swapped across Aggregate output positions"
    );

    fs::write(
        &query,
        "select sum(v), sum(v) filter (where v > 0), \
                (select sum(v) from inner_t) from outer_t;\n",
    )
    .unwrap();
    let nested_pristine = run_calcite(&repo, &schema, &query);
    let (inner_call, inner_operand) = {
        let root = nested_pristine.queries[0].rel.as_ref().unwrap();
        let inner_call = root
            .project_rex
            .iter()
            .find_map(|rex| find_rex_subquery_root(rex, "LogicalAggregate"))
            .unwrap()
            .subquery_rel
            .as_deref()
            .unwrap()
            .agg_call_details[0]
            .clone();
        let inner_operand = inner_call.source_operands[0].clone();
        (inner_call, inner_operand)
    };

    let mut project_scope_borrow = nested_pristine.clone();
    {
        let aggregate = first_aggregate_mut(project_scope_borrow.queries[0].rel.as_mut().unwrap());
        let project = &mut aggregate.inputs[0].project_rex[0];
        project.source_sql = inner_operand.source_sql;
        project.source_node_id = inner_operand.source_node_id;
        project.source_text = inner_operand.source_text;
        project.source_kind = inner_operand.source_kind;
        project.source_operator = inner_operand.source_operator;
        project.source_identifier_names = inner_operand.source_identifier_names;
        project.source_identifier_quoted = inner_operand.source_identifier_quoted;
    }
    assert!(
        convert_raw_file(project_scope_borrow).is_err(),
        "an Aggregate-input Project may not borrow identical text from a nested SELECT"
    );

    let mut nested_borrow = nested_pristine;
    {
        first_aggregate_mut(nested_borrow.queries[0].rel.as_mut().unwrap()).agg_call_details[0] =
            inner_call;
    }
    assert!(
        convert_raw_file(nested_borrow).is_err(),
        "an outer Aggregate may not borrow an exact call from a nested SELECT"
    );
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_binds_same_operator_aggregates_within_their_query_block() {
    let repo = repo_root();
    let temp = temp_dir("query-block-local-aggregate-binding");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(
        &schema,
        "create table t(k integer, a integer, b integer);\n",
    )
    .unwrap();
    fs::write(
        &query,
        r#"select (select sum(b) from t) as nested_b,
                  sum(a) as outer_a, sum(b) as outer_b
           from t having sum(a) > 0;
        "#,
    )
    .unwrap();

    let raw = run_calcite(&repo, &schema, &query);
    let aggregate = first_aggregate(raw.queries[0].rel.as_ref().unwrap());
    assert_eq!(aggregate.agg_call_details.len(), 2);
    let outer_a = &aggregate.agg_call_details[0];
    let outer_b = &aggregate.agg_call_details[1];
    assert_eq!(outer_a.source_sql.as_deref(), Some("SUM(`a`)"));
    assert_eq!(outer_b.source_sql.as_deref(), Some("SUM(`b`)"));
    assert_eq!(outer_a.source_operands.len(), 1);
    assert_eq!(outer_b.source_operands.len(), 1);
    assert_eq!(outer_a.source_operands[0].source_sql.as_deref(), Some("a"));
    assert_eq!(outer_b.source_operands[0].source_sql.as_deref(), Some("b"));

    let root = raw.queries[0].rel.as_ref().unwrap();
    let having = root
        .inputs
        .first()
        .expect("final Project must contain HAVING");
    let native = having
        .source_native_having
        .as_ref()
        .expect("outer HAVING must bind only its same-block SUM(a)");
    assert_eq!(native.aggregate_call_count, 2);
    assert_eq!(native.operand_bindings.len(), 1);
    assert_eq!(native.operand_bindings[0].aggregate_output_index, 0);

    // Reverse the outer aggregate order and put the nested aggregate last.
    // Positional binding must follow the current query block, rather than the
    // first same-spelled aggregate encountered by a recursive source walk.
    fs::write(
        &query,
        r#"select sum(b) as outer_b, sum(a) as outer_a,
                  (select sum(a) from t) as nested_a
           from t having sum(b) > 0;
        "#,
    )
    .unwrap();
    let reversed = run_calcite(&repo, &schema, &query);
    let aggregate = first_aggregate(reversed.queries[0].rel.as_ref().unwrap());
    assert_eq!(aggregate.agg_call_details.len(), 2);
    assert_eq!(
        aggregate.agg_call_details[0].source_sql.as_deref(),
        Some("SUM(`b`)")
    );
    assert_eq!(
        aggregate.agg_call_details[0].source_operands[0]
            .source_sql
            .as_deref(),
        Some("b")
    );
    assert_eq!(
        aggregate.agg_call_details[1].source_sql.as_deref(),
        Some("SUM(`a`)")
    );
    assert_eq!(
        aggregate.agg_call_details[1].source_operands[0]
            .source_sql
            .as_deref(),
        Some("a")
    );
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_keeps_inlined_cte_aggregate_bindings_query_block_local() {
    with_large_calcite_stack(|| {
        let repo = repo_root();
        let temp = temp_dir("cte-query-block-local-aggregate-binding");
        let schema = temp.join("schema.sql");
        let query = temp.join("query.sql");
        fs::write(
            &schema,
            "create table t(k integer, a integer, b integer);\n",
        )
        .unwrap();
        fs::write(
            &query,
            r#"with c as (
             select k, sum(a) as total_a, sum(b) as total_b
             from t group by k having sum(a) > 0
           )
           select sum(total_b) as outer_b, sum(total_a) as outer_a
           from c having sum(total_a) > 0;
        "#,
        )
        .unwrap();

        let raw = run_calcite(&repo, &schema, &query);
        let mut aggregates = Vec::new();
        collect_aggregates(raw.queries[0].rel.as_ref().unwrap(), &mut aggregates);
        assert_eq!(
            aggregates.len(),
            2,
            "expected outer and inlined CTE aggregates"
        );

        let outer = aggregates
            .iter()
            .copied()
            .find(|aggregate| {
                aggregate.agg_call_details.iter().any(|call| {
                    call.source_operands
                        .first()
                        .and_then(|operand| operand.source_sql.as_deref())
                        == Some("total_b")
                })
            })
            .expect("outer aggregate must retain CTE-column source operands");
        assert_eq!(outer.agg_call_details.len(), 2);
        assert_eq!(
            outer.agg_call_details[0].source_sql.as_deref(),
            Some("SUM(`total_b`)")
        );
        assert_eq!(
            outer.agg_call_details[0].source_operands[0]
                .source_sql
                .as_deref(),
            Some("total_b")
        );
        assert_eq!(
            outer.agg_call_details[1].source_sql.as_deref(),
            Some("SUM(`total_a`)")
        );
        assert_eq!(
            outer.agg_call_details[1].source_operands[0]
                .source_sql
                .as_deref(),
            Some("total_a")
        );

        let inner = aggregates
            .iter()
            .copied()
            .find(|aggregate| {
                aggregate.agg_call_details.iter().any(|call| {
                    call.source_operands
                        .first()
                        .and_then(|operand| operand.source_sql.as_deref())
                        == Some("a")
                })
            })
            .expect("inlined CTE aggregate must retain base-column source operands");
        assert_eq!(inner.agg_call_details.len(), 2);
        assert_eq!(
            inner.agg_call_details[0].source_sql.as_deref(),
            Some("SUM(`a`)")
        );
        assert_eq!(
            inner.agg_call_details[0].source_operands[0]
                .source_sql
                .as_deref(),
            Some("a")
        );
        assert_eq!(
            inner.agg_call_details[1].source_sql.as_deref(),
            Some("SUM(`b`)")
        );
        assert_eq!(
            inner.agg_call_details[1].source_operands[0]
                .source_sql
                .as_deref(),
            Some("b")
        );
        convert_raw_file(raw).expect("query-local CTE aggregate bindings must convert exactly");

        fs::remove_dir_all(&temp).unwrap();
    });
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_closes_parenthesized_scalar_cte_aggregate_lineage() {
    with_large_calcite_stack(|| {
        let repo = repo_root();
        let temp = temp_dir("parenthesized-scalar-cte-aggregate-lineage");
        let schema = temp.join("schema.sql");
        let query = temp.join("query.sql");
        fs::write(&schema, "create table t(k integer, v integer);\n").unwrap();
        fs::write(
            &query,
            r#"with c(k, total) as (
             select k, max(v) from t group by k
           )
           select x.k from c as x
           where x.total = (select max(total) from c);
        "#,
        )
        .unwrap();

        let pristine = run_calcite(&repo, &schema, &query);
        let scalar = find_first_scalar_subquery(pristine.queries[0].rel.as_ref().unwrap())
            .expect("scalar CTE aggregate subquery");
        let nested = scalar
            .subquery_rel
            .as_deref()
            .expect("scalar relational tree");
        assert_eq!(nested.rel_type, "LogicalAggregate");
        let [carrier] = nested.inputs.as_slice() else {
            panic!("scalar Aggregate must have one Project carrier")
        };
        assert_eq!(carrier.rel_type, "LogicalProject");
        let [rex] = carrier.project_rex.as_slice() else {
            panic!("scalar Aggregate carrier must expose one CTE output")
        };
        assert_eq!(rex.index, Some(1));
        let expansion = rex
            .source_expansion
            .as_ref()
            .expect("explicit CTE output expansion");
        assert_eq!(expansion.kind, "DIRECT_CTE_EXPLICIT_COLUMN");
        assert_ne!(
            nested.source_query_block_id.as_deref(),
            Some(expansion.outer_select_node_id.as_str()),
            "the regression requires Calcite's SELECT span to exclude the scalar parentheses"
        );
        convert_raw_file(pristine.clone()).expect("exact parenthesized CTE aggregate lineage");

        let mut swapped = pristine;
        let scalar = find_first_scalar_subquery_mut(swapped.queries[0].rel.as_mut().unwrap())
            .expect("mutable scalar CTE aggregate subquery");
        let carrier = &mut scalar.subquery_rel.as_deref_mut().unwrap().inputs[0];
        assert_eq!(
            carrier.inputs[0].row_type[0].ty,
            carrier.inputs[0].row_type[1].ty
        );
        carrier.project_rex[0].index = Some(0);
        carrier.project_rex[0].text = Some("$0".to_owned());
        assert!(
            convert_raw_file(swapped).is_err(),
            "a same-typed CTE group key cannot replace the exact aggregate output"
        );

        fs::remove_dir_all(&temp).unwrap();
    });
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_closes_select_list_subquery_derived_expression_carrier() {
    with_large_calcite_stack(|| {
        let repo = repo_root();
        let temp = temp_dir("select-list-subquery-derived-expression-carrier");
        let schema = temp.join("schema.sql");
        let query = temp.join("query.sql");
        fs::write(&schema, "create table t(a integer, b integer);\n").unwrap();
        fs::write(
            &query,
            r#"select a,
                  case when true then cast(b as integer) else null end in
                    (select b_alias
                       from (select a,
                                    case when true then cast(b as integer) else null end
                                      as b_alias
                               from t) as d
                      where a < 20) as matched
             from t;
        "#,
        )
        .unwrap();

        let pristine = run_calcite(&repo, &schema, &query);
        let in_subquery = find_first_in_subquery(pristine.queries[0].rel.as_ref().unwrap())
            .expect("SELECT-list IN subquery");
        let nested = in_subquery
            .subquery_rel
            .as_deref()
            .expect("SELECT-list IN relational tree");
        assert_eq!(nested.rel_type, "LogicalProject");
        let [carrier] = nested.project_rex.as_slice() else {
            panic!("nested SELECT must expose one derived output")
        };
        assert_eq!(carrier.index, Some(1));
        assert_eq!(
            carrier
                .source_expansion
                .as_ref()
                .map(|expansion| expansion.kind.as_str()),
            Some("DIRECT_DERIVED_OUTPUT_ALIAS")
        );
        convert_raw_file(pristine.clone()).expect("exact SELECT-list subquery carrier");

        let mut swapped = pristine.clone();
        let in_subquery = find_first_in_subquery_mut(swapped.queries[0].rel.as_mut().unwrap())
            .expect("mutable SELECT-list IN subquery");
        let nested = in_subquery.subquery_rel.as_deref_mut().unwrap();
        assert_eq!(
            nested.inputs[0].row_type[0].ty,
            nested.inputs[0].row_type[1].ty
        );
        nested.project_rex[0].index = Some(0);
        nested.project_rex[0].text = Some("$0".to_owned());
        assert!(
            convert_raw_file(swapped).is_err(),
            "a same-typed derived input cannot replace the exact CASE output"
        );

        fs::remove_dir_all(&temp).unwrap();
    });
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_closes_hidden_having_group_derived_projection() {
    fn derived_public_project(rel: &CalciteRel) -> Option<&CalciteRel> {
        let owns_hidden_group = rel.rel_type == "LogicalProject"
            && rel.project_rex.len() == 2
            && rel.project_rex.iter().all(|rex| {
                rex.source_expansion.as_ref().is_some_and(|expansion| {
                    matches!(
                        expansion.kind.as_str(),
                        "DIRECT_DERIVED_OUTPUT_ALIAS" | "DIRECT_DERIVED_PASSTHROUGH"
                    ) && expansion
                        .inner_select_text
                        .to_ascii_lowercase()
                        .contains("group by")
                })
            });
        if owns_hidden_group {
            return Some(rel);
        }
        rel.inputs.iter().find_map(derived_public_project)
    }

    fn derived_public_project_mut(rel: &mut CalciteRel) -> Option<&mut CalciteRel> {
        let owns_hidden_group = rel.rel_type == "LogicalProject"
            && rel.project_rex.len() == 2
            && rel.project_rex.iter().all(|rex| {
                rex.source_expansion.as_ref().is_some_and(|expansion| {
                    matches!(
                        expansion.kind.as_str(),
                        "DIRECT_DERIVED_OUTPUT_ALIAS" | "DIRECT_DERIVED_PASSTHROUGH"
                    ) && expansion
                        .inner_select_text
                        .to_ascii_lowercase()
                        .contains("group by")
                })
            });
        if owns_hidden_group {
            return Some(rel);
        }
        rel.inputs.iter_mut().find_map(derived_public_project_mut)
    }

    with_large_calcite_stack(|| {
        let repo = repo_root();
        let temp = temp_dir("hidden-having-group-derived-projection");
        let schema = temp.join("schema.sql");
        let query = temp.join("query.sql");
        fs::write(
            &schema,
            "create table t(dept integer, hidden integer, v integer);\n",
        )
        .unwrap();
        fs::write(
            &query,
            r#"select d, sum(total)
                 from (select dept as d, count(v) as total
                         from t
                        group by dept, hidden
                       having hidden >= 0) as q
                group by d;
            "#,
        )
        .unwrap();

        let pristine = run_calcite(&repo, &schema, &query);
        let project = derived_public_project(pristine.queries[0].rel.as_ref().unwrap())
            .expect("public Project over hidden HAVING group key");
        assert_eq!(project.project_rex[0].index, Some(0));
        assert_eq!(project.project_rex[1].index, Some(2));
        assert_eq!(
            project.project_rex[0]
                .source_expansion
                .as_ref()
                .map(|expansion| expansion.reference_text.as_str()),
            Some("d")
        );
        convert_raw_file(pristine.clone())
            .expect("hidden HAVING group output must remain internal to its Aggregate");

        let mut swapped = pristine;
        let project = derived_public_project_mut(swapped.queries[0].rel.as_mut().unwrap()).unwrap();
        assert_eq!(
            project.inputs[0].row_type[0].ty,
            project.inputs[0].row_type[1].ty
        );
        project.project_rex[0].index = Some(1);
        project.project_rex[0].text = Some("$1".to_owned());
        assert!(
            convert_raw_file(swapped).is_err(),
            "a same-typed hidden HAVING group key cannot replace the public derived output"
        );

        fs::remove_dir_all(&temp).unwrap();
    });
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_overrides_attested_fixed_numeric_stddev_samp_result() {
    let repo = repo_root();
    let temp = temp_dir("numeric-7-2-stddev-samp");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&schema, "create table measurements(amount decimal(7,2));\n").unwrap();
    fs::write(
        &query,
        "select stddev_samp(amount) as spread from measurements;\n",
    )
    .unwrap();

    let raw = run_calcite(&repo, &schema, &query);
    let aggregate = first_aggregate(raw.queries[0].rel.as_ref().unwrap());
    let call = &aggregate.agg_call_details[0];
    assert_eq!(call.ty.as_deref(), Some("DECIMAL"));
    assert_eq!(call.precision, Some(7));
    assert_eq!(call.scale, Some(2));
    assert_eq!(call.source_kind.as_deref(), Some("OTHER_FUNCTION"));
    assert_eq!(call.source_operator.as_deref(), Some("stddev_samp"));
    assert_eq!(call.source_text.as_deref(), Some("stddev_samp(amount)"));
    assert!(call.source_node_id.is_some());
    assert_eq!(call.source_distinct, Some(false));
    assert_eq!(call.source_operands.len(), 1);
    assert_eq!(
        call.source_operands[0].source_kind.as_deref(),
        Some("IDENTIFIER")
    );
    assert_eq!(
        call.source_operands[0].source_sql.as_deref(),
        Some("amount")
    );
    assert_eq!(
        call.source_operands[0].source_text.as_deref(),
        Some("amount")
    );
    assert!(call.source_operands[0].source_node_id.is_some());

    let ir = convert_raw_file(raw).unwrap();
    let (agg_calls, output) = first_ir_aggregate(&ir.queries[0].rel);
    assert_eq!(agg_calls[0].modifiers.source_distinct, Some(false));
    let source = agg_calls[0]
        .modifiers
        .source
        .as_ref()
        .expect("aggregate keeps exact source binding");
    assert_eq!(source.text.as_deref(), Some("stddev_samp(amount)"));
    assert!(source.node_id.is_some());
    assert_eq!(
        source.operands[0]
            .as_ref()
            .and_then(|operand| operand.text.as_deref()),
        Some("amount")
    );
    assert_eq!(output[0].ty, SqlType::decimal(None, None));
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_preserves_character_typmods_end_to_end() {
    let repo = repo_root();
    let temp = temp_dir("character-typmods");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(
        &schema,
        "create table t(c char(4), v varchar(7), body text, b bpchar);\n",
    )
    .unwrap();
    fs::write(&query, "select c, v, body, b from t;\n").unwrap();

    let ir = convert_raw_file(run_calcite(&repo, &schema, &query)).unwrap();
    assert_eq!(ir.schema.tables[0].columns[0].ty, SqlType::character(4));
    assert_eq!(ir.schema.tables[0].columns[1].ty, SqlType::varchar(Some(7)));
    assert_eq!(ir.schema.tables[0].columns[2].ty, SqlType::text());
    assert_eq!(ir.schema.tables[0].columns[3].ty, SqlType::bpchar());

    let RelExpr::Project { input, output, .. } = &ir.queries[0].rel else {
        panic!("expected project");
    };
    assert_eq!(output, &ir.schema.tables[0].columns);
    let RelExpr::TableScan {
        output: scan_output,
        ..
    } = input.as_ref()
    else {
        panic!("expected table scan");
    };
    assert_eq!(scan_output, &ir.schema.tables[0].columns);
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_closes_character_coalesce_empty_literal_carrier() {
    fn find_zero_width_character_literal(rex: &CalciteRex) -> Option<&CalciteRex> {
        (rex.kind.as_deref() == Some("LITERAL")
            && rex.class.as_deref() == Some("RexLiteral")
            && rex.full_type.as_deref() == Some("CHAR(0) NOT NULL"))
        .then_some(rex)
        .or_else(|| {
            rex.operands
                .iter()
                .find_map(find_zero_width_character_literal)
        })
    }

    let repo = repo_root();
    let temp = temp_dir("character-coalesce-empty-carrier");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&schema, "create table t(c char(30));\n").unwrap();
    fs::write(&query, "select coalesce(c, '') as coalesced from t;\n").unwrap();

    let raw = run_calcite(&repo, &schema, &query);
    let project = raw.queries[0].rel.as_ref().unwrap_or_else(|| {
        panic!(
            "Calcite did not produce a project: {:?}",
            raw.queries[0].error
        )
    });
    let carrier = project
        .project_rex
        .iter()
        .find_map(find_zero_width_character_literal)
        .expect("Calcite empty-string CHAR(0) carrier");
    assert_eq!(carrier.ty.as_deref(), Some("CHAR"));
    assert!(!carrier.nullable);
    assert_eq!(carrier.precision, Some(0));
    assert_eq!(carrier.scale, Some(i32::MIN));
    assert_eq!(carrier.literal_value.as_deref(), Some("_ISO-8859-1''"));
    assert_eq!(carrier.literal_value_as_string.as_deref(), Some(""));
    assert_eq!(carrier.literal_value2.as_deref(), Some(""));

    let ir = convert_raw_file(raw).expect("convert exact character COALESCE carrier");
    assert_eq!(ir.queries[0].output()[0].ty, SqlType::bpchar());
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_preserves_numeric_schema_defaults_and_typmods() {
    let repo = repo_root();
    let temp = temp_dir("numeric-schema-typmods");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(
        &schema,
        "create table t(unbounded numeric, default_scale numeric(7), fixed numeric(7,2));\n",
    )
    .unwrap();
    fs::write(&query, "select unbounded, default_scale, fixed from t;\n").unwrap();

    let raw = run_calcite(&repo, &schema, &query);
    assert!(
        raw.schema[0].columns[0]
            .scale
            .is_some_and(|scale| scale < 0)
    );
    assert!(
        raw.schema[0].columns[1]
            .scale
            .is_some_and(|scale| scale < 0)
    );
    let ir = convert_raw_file(raw).unwrap();
    let expected = [
        SqlType::decimal(None, None),
        SqlType::decimal(Some(7), Some(0)),
        SqlType::decimal(Some(7), Some(2)),
    ];
    assert_eq!(
        ir.schema.tables[0]
            .columns
            .iter()
            .map(|column| column.ty.clone())
            .collect::<Vec<_>>(),
        expected
    );
    let RelExpr::Project { output, .. } = &ir.queries[0].rel else {
        panic!("expected project");
    };
    assert_eq!(
        output
            .iter()
            .map(|column| column.ty.clone())
            .collect::<Vec<_>>(),
        expected
    );
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_preserves_timestamp_schema_defaults_and_timezone_family() {
    let repo = repo_root();
    let temp = temp_dir("timestamp-schema-typmods");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(
        &schema,
        "create table t(ts timestamp, ts3 timestamp(3), tz timestamptz, tz3 timestamptz(3));\n",
    )
    .unwrap();
    fs::write(&query, "select ts, ts3, tz, tz3 from t;\n").unwrap();

    let ir = convert_raw_file(run_calcite(&repo, &schema, &query)).unwrap();
    let expected = [
        SqlType::timestamp(Some(6)),
        SqlType::timestamp(Some(3)),
        SqlType::timestamptz(Some(6)),
        SqlType::timestamptz(Some(3)),
    ];
    assert_eq!(
        ir.schema.tables[0]
            .columns
            .iter()
            .map(|column| column.ty.clone())
            .collect::<Vec<_>>(),
        expected
    );
    let RelExpr::Project { input, output, .. } = &ir.queries[0].rel else {
        panic!("expected project");
    };
    assert_eq!(
        output
            .iter()
            .map(|column| column.ty.clone())
            .collect::<Vec<_>>(),
        expected
    );
    let RelExpr::TableScan { output, .. } = input.as_ref() else {
        panic!("expected table scan");
    };
    assert_eq!(
        output
            .iter()
            .map(|column| column.ty.clone())
            .collect::<Vec<_>>(),
        expected
    );
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_rejects_schema_defaults_even_with_protected_delimiters() {
    let repo = repo_root();
    let temp = temp_dir("schema-quoted-default-delimiters");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(
        &schema,
        "create table t (a text default '(', b integer, c text default $tag$),($tag$);\n",
    )
    .unwrap();
    fs::write(&query, "select a from t;\n").unwrap();

    let diagnostic = run_calcite_failure(&repo, &schema, &query);
    assert!(diagnostic.contains("unsupported or malformed column-constraint tail"));
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_rejects_unconsumed_comment_statement_with_protected_create_text() {
    let repo = repo_root();
    let temp = temp_dir("schema-create-table-comment-literal");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(
        &schema,
        "create table t(a integer);\n\
         comment on table t is 'create table fake (x integer)';\n",
    )
    .unwrap();
    fs::write(&query, "select a from t;\n").unwrap();

    let diagnostic = run_calcite_failure(&repo, &schema, &query);
    assert!(diagnostic.contains("unsupported or unconsumed schema statement"));
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_dollar_tag_inside_identifier_is_not_a_dollar_quote() {
    let repo = repo_root();
    let temp = temp_dir("schema-dollar-tag-identifiers");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&schema, "create table t(a integer, b$tag$qux integer);\n").unwrap();
    fs::write(&query, "select a from t;\n").unwrap();

    let ir = convert_raw_file(run_calcite(&repo, &schema, &query)).unwrap();
    assert_eq!(ir.schema.tables.len(), 1);
    assert_eq!(ir.schema.tables[0].columns.len(), 2);
    assert_eq!(ir.schema.tables[0].columns[0].name, "a");
    assert_eq!(ir.schema.tables[0].columns[1].name, "b$tag$qux");
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_rejects_non_ascii_dollar_tag_before_schema_tokenization() {
    let repo = repo_root();
    let temp = temp_dir("schema-non-ascii-dollar-tag");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(
        &schema,
        "create table t(a text default $é$),($é$, b integer);\n",
    )
    .unwrap();
    fs::write(&query, "select a from t;\n").unwrap();

    let output = Command::new(repo.join("scripts/calcite-ir"))
        .arg("--schema")
        .arg(&schema)
        .arg("--sql")
        .arg(&query)
        .output()
        .unwrap();
    assert!(!output.status.success());
    let diagnostic = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        diagnostic.contains("non-ASCII PostgreSQL dollar-quote tags are not supported"),
        "unexpected error: {diagnostic}"
    );
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_rejects_unconsumed_comment_statements_with_escape_strings() {
    let repo = repo_root();
    let temp = temp_dir("schema-standard-conforming-backslash");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(
        &schema,
        "create table t(a integer);\n\
         comment on table t is 'x\\';\n\
         create table u(z integer); -- '\n\
         comment on table u is E'escaped\\\' quote';\n",
    )
    .unwrap();
    fs::write(&query, "select z from u;\n").unwrap();

    let diagnostic = run_calcite_failure(&repo, &schema, &query);
    assert!(diagnostic.contains("unsupported or unconsumed schema statement"));
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_preserves_string_literal_and_typed_null_outputs() {
    let repo = repo_root();
    let temp = temp_dir("string-literal-outputs");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&schema, "create table t(id integer);\n").unwrap();
    fs::write(
        &query,
        "select 'a' as bare, cast('abcd' as varchar(2)) as narrowed, cast(null as varchar(2)) as null_v, cast(null as char(4)) as null_c from t;\n",
    )
    .unwrap();

    let ir = convert_raw_file(run_calcite(&repo, &schema, &query)).unwrap();
    assert_eq!(
        ir.queries[0]
            .output()
            .iter()
            .map(|column| column.ty.clone())
            .collect::<Vec<_>>(),
        vec![
            SqlType::text(),
            SqlType::varchar(Some(2)),
            SqlType::varchar(Some(2)),
            SqlType::character(4),
        ]
    );
    let RelExpr::Project { exprs, .. } = &ir.queries[0].rel else {
        panic!("expected project");
    };
    assert!(matches!(
        &exprs[0].parsed,
        ScalarAst::Literal { raw } if raw == "'a'"
    ));
    for (expr, expected) in exprs[1..]
        .iter()
        .zip(["VARCHAR(2)", "VARCHAR(2)", "CHAR(4)"])
    {
        assert!(matches!(
            &expr.parsed,
            ScalarAst::TypeAnnotation { expr, ty }
                if ty == expected && matches!(expr.as_ref(), ScalarAst::Call { op: ScalarOp::Cast, .. })
        ));
    }
    assert!(matches!(
        &exprs[2].parsed,
        ScalarAst::TypeAnnotation { expr, .. }
            if matches!(
                expr.as_ref(),
                ScalarAst::Call { args, .. }
                    if matches!(
                        args.as_slice(),
                        [ScalarAst::TypeAnnotation { expr, ty }]
                            if ty == "TEXT"
                                && matches!(expr.as_ref(), ScalarAst::Literal { raw } if raw == "NULL")
                    )
            )
    ));
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_keeps_no_from_values_input_synthetic() {
    let repo = repo_root();
    let temp = temp_dir("no-from-values-provenance");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&schema, "create table t(id integer);\n").unwrap();
    fs::write(&query, "select cast('a' as char(2)) as x;\n").unwrap();

    let raw = run_calcite(&repo, &schema, &query);
    let project = raw.queries[0].rel.as_ref().unwrap();
    let values = project
        .inputs
        .first()
        .expect("project must retain its dummy input");
    let dummy = &values
        .tuples
        .as_ref()
        .expect("no-FROM SELECT must use a synthetic VALUES row")[0][0];
    assert_eq!(dummy.text.as_deref(), Some("0"));
    assert!(dummy.source_sql.is_none());

    let ir = convert_raw_file(raw).unwrap();
    let RelExpr::Project { input, output, .. } = &ir.queries[0].rel else {
        panic!("expected project");
    };
    assert_eq!(output[0].ty, SqlType::character(2));
    let RelExpr::Values { rows, output } = input.as_ref() else {
        panic!("expected synthetic values input");
    };
    assert_eq!(output[0].ty, SqlType::Integer);
    assert!(matches!(
        &rows[0][0].parsed,
        ScalarAst::TypeAnnotation { expr, ty }
            if ty == "INTEGER"
                && matches!(expr.as_ref(), ScalarAst::Literal { raw } if raw == "0")
    ));
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_recovers_case_string_typmods() {
    let repo = repo_root();
    let temp = temp_dir("case-string-typmods");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&schema, "create table t(flag boolean);\n").unwrap();
    fs::write(
        &query,
        "select case when flag then cast('a' as char(2)) else null end as x from t;\n\
         select case when flag then cast('a' as char(2)) else cast(null as char(2)) end as x from t;\n\
         select case when flag then cast('a' as varchar(2)) else null end as x from t;\n\
         select case when flag then cast('a' as varchar(2)) else cast(null as varchar(2)) end as x from t;\n",
    )
    .unwrap();

    let ir = convert_raw_file(run_calcite(&repo, &schema, &query)).unwrap();
    assert_eq!(ir.queries[0].output()[0].ty, SqlType::bpchar());
    assert_eq!(ir.queries[1].output()[0].ty, SqlType::character(2));
    assert_eq!(ir.queries[2].output()[0].ty, SqlType::varchar(None));
    assert_eq!(ir.queries[3].output()[0].ty, SqlType::varchar(Some(2)));

    let RelExpr::Project {
        exprs: source_exprs,
        ..
    } = &ir.queries[0].rel
    else {
        panic!("expected source project");
    };
    let ScalarAst::Call {
        op: ScalarOp::Case,
        args: source_args,
        ..
    } = &source_exprs[0].parsed
    else {
        panic!("expected source CASE");
    };
    assert!(matches!(source_args.last(), Some(ScalarAst::Literal { raw }) if raw == "NULL"));

    let RelExpr::Project {
        exprs: target_exprs,
        ..
    } = &ir.queries[1].rel
    else {
        panic!("expected target project");
    };
    let ScalarAst::Call {
        op: ScalarOp::Case,
        args: target_args,
        ..
    } = &target_exprs[0].parsed
    else {
        panic!("expected target CASE");
    };
    assert!(matches!(
        target_args.last(),
        Some(ScalarAst::TypeAnnotation { ty, .. }) if ty == "CHAR(2)"
    ));
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_recovers_postgres_numeric_case_branch_dscales() {
    let repo = repo_root();
    let temp = temp_dir("numeric-case-branch-dscales");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&schema, "create table emp(id integer);\n").unwrap();
    fs::write(
        &query,
        "select case when false then 2.1 else 1 end as newcol from emp;\n",
    )
    .unwrap();

    let raw = run_calcite(&repo, &schema, &query);
    let ir = convert_raw_file(raw.clone()).unwrap();
    assert_eq!(ir.queries[0].output()[0].ty, SqlType::decimal(None, None));
    let RelExpr::Project { exprs, .. } = &ir.queries[0].rel else {
        panic!("expected CASE project");
    };
    let ScalarAst::Call {
        op: ScalarOp::Case,
        args,
        ..
    } = &exprs[0].parsed
    else {
        panic!("expected CASE expression");
    };
    assert!(matches!(
        &args[1],
        ScalarAst::TypeAnnotation { expr, ty }
            if ty == "NUMERIC"
                && matches!(expr.as_ref(), ScalarAst::Literal { raw } if raw == "2.1")
    ));
    assert!(matches!(
        &args[2],
        ScalarAst::TypeAnnotation { expr, ty }
            if ty == "NUMERIC"
                && matches!(
                    expr.as_ref(),
                    ScalarAst::Call { op: ScalarOp::Cast, args, .. }
                        if matches!(
                            args.as_slice(),
                            [ScalarAst::TypeAnnotation { expr, ty }]
                                if ty == "INTEGER"
                                    && matches!(expr.as_ref(), ScalarAst::Literal { raw } if raw == "1")
                        )
                )
    ));
    let exact_case = exprs[0].parsed.clone();

    fn case_rex(raw: &mut logos_ir::calcite::CalciteFile) -> &mut logos_ir::calcite::CalciteRex {
        &mut raw.queries[0].rel.as_mut().expect("project").project_rex[0]
    }
    let mut parent_drift = raw.clone();
    case_rex(&mut parent_drift).source_sql = Some("CASE WHEN FALSE THEN 2.1 ELSE 2 END".to_owned());
    let parent_drift = convert_raw_file(parent_drift).expect("exact CASE text overrides sourceSql");
    let RelExpr::Project { exprs, .. } = &parent_drift.queries[0].rel else {
        panic!("expected CASE project after rendered parent drift");
    };
    assert_eq!(exprs[0].parsed, exact_case);

    let mut child_drift = raw.clone();
    case_rex(&mut child_drift).operands[2].source_sql = Some("2".to_owned());
    let child_drift = convert_raw_file(child_drift).expect("exact branch text overrides sourceSql");
    let RelExpr::Project { exprs, .. } = &child_drift.queries[0].rel else {
        panic!("expected CASE project after rendered branch drift");
    };
    assert_eq!(exprs[0].parsed, exact_case);

    let mut exact_text_drift = raw.clone();
    case_rex(&mut exact_text_drift).operands[2].source_text = Some("2".to_owned());
    assert!(convert_raw_file(exact_text_drift).is_err());

    let mut payload_drift = raw;
    case_rex(&mut payload_drift).operands[2].literal_value2 = Some("11".to_owned());
    assert!(convert_raw_file(payload_drift).is_err());
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_exact_scalar_text_overrides_well_formed_rendered_semantic_drift() {
    fn drift_rendered_source(rex: &mut CalciteRex, exact_text: &str, rendered: &str) -> usize {
        let mut changed = 0;
        if rex.source_text.as_deref() == Some(exact_text) {
            rex.source_sql = Some(rendered.to_owned());
            changed += 1;
        }
        for operand in &mut rex.operands {
            changed += drift_rendered_source(operand, exact_text, rendered);
        }
        changed
    }

    fn exact_descendant_mut<'a>(rex: &'a mut CalciteRex, text: &str) -> &'a mut CalciteRex {
        if rex.source_text.as_deref() == Some(text) {
            return rex;
        }
        for operand in &mut rex.operands {
            if operand.source_text.as_deref() == Some(text) {
                return operand;
            }
            if operand
                .operands
                .iter()
                .any(|descendant| descendant.source_text.as_deref() == Some(text))
            {
                return exact_descendant_mut(operand, text);
            }
        }
        panic!("missing exact scalar descendant {text:?}");
    }

    let repo = repo_root();
    let temp = temp_dir("exact-source-rendered-scalar-drift");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(
        &schema,
        "create table t(a integer, n numeric(10,2), flag boolean, b boolean);\n",
    )
    .unwrap();
    fs::write(
        &query,
        "select cast(n as numeric(3,1)) as x from t;\n\
         select coalesce(n, 0.00) as x from t;\n\
         select 'a ' as x from t;\n\
         select cast('1970-01-01 00:00:01.123456' as timestamp(6)) as x from t;\n\
         select a + a as x from t;\n\
         select * from t where b = false;\n",
    )
    .unwrap();

    let raw = run_calcite(&repo, &schema, &query);
    assert_eq!(raw.queries.len(), 6);
    for (index, query) in raw.queries.iter().enumerate() {
        convert_raw_file(CalciteFile {
            environment: raw.environment,
            schema: raw.schema.clone(),
            queries: vec![query.clone()],
        })
        .unwrap_or_else(|error| panic!("exact scalar fixture {index}: {error}"));
    }
    let exact = convert_raw_file(raw.clone()).expect("convert exact scalar fixtures");

    let exact_texts = [
        "cast(n as numeric(3,1))",
        "coalesce(n, 0.00)",
        "'a '",
        "cast('1970-01-01 00:00:01.123456' as timestamp(6))",
    ];
    for (index, expected) in exact_texts.into_iter().enumerate() {
        assert_eq!(
            raw.queries[index].rel.as_ref().unwrap().project_rex[0]
                .source_text
                .as_deref(),
            Some(expected),
            "query {index} exact root"
        );
    }

    let plus = &raw.queries[4].rel.as_ref().unwrap().project_rex[0];
    assert_eq!(plus.operands.len(), 2);
    assert_eq!(plus.operands[0].source_text.as_deref(), Some("a"));
    assert_eq!(plus.operands[1].source_text.as_deref(), Some("a"));
    assert_eq!(plus.operands[0].source_sql, plus.operands[1].source_sql);
    assert_ne!(
        plus.operands[0].source_node_id, plus.operands[1].source_node_id,
        "lexically identical identifiers must retain distinct exact positions"
    );

    let boolean_filter = find_first_source_where_filter(raw.queries[5].rel.as_ref().unwrap())
        .expect("Boolean WHERE ownership");
    assert!(
        boolean_filter
            .source_where
            .as_ref()
            .unwrap()
            .analysis_errors
            .is_empty(),
        "the exact Boolean literal must not acquire an integer-comparison error marker"
    );

    let mut rendered_cases = Vec::new();

    let mut cast_typmod = raw.clone();
    assert!(
        drift_rendered_source(
            &mut cast_typmod.queries[0].rel.as_mut().unwrap().project_rex[0],
            "cast(n as numeric(3,1))",
            "CAST(`n` AS NUMERIC(30,10))",
        ) > 0
    );
    rendered_cases.push(("cast typmod", 0, cast_typmod));

    let mut coalesce_scale = raw.clone();
    let coalesce = &mut coalesce_scale.queries[1].rel.as_mut().unwrap().project_rex[0];
    assert!(drift_rendered_source(coalesce, "coalesce(n, 0.00)", "COALESCE(`n`, 0)") > 0);
    assert!(drift_rendered_source(coalesce, "0.00", "0") > 0);
    rendered_cases.push(("COALESCE fallback scale", 1, coalesce_scale));

    let mut trailing_space = raw.clone();
    assert!(
        drift_rendered_source(
            &mut trailing_space.queries[2].rel.as_mut().unwrap().project_rex[0],
            "'a '",
            "'a'",
        ) > 0
    );
    rendered_cases.push(("character trailing space", 2, trailing_space));

    let mut timestamp_fraction = raw.clone();
    let timestamp = &mut timestamp_fraction.queries[3]
        .rel
        .as_mut()
        .unwrap()
        .project_rex[0];
    assert!(
        drift_rendered_source(
            timestamp,
            "cast('1970-01-01 00:00:01.123456' as timestamp(6))",
            "CAST('1970-01-01 00:00:01.123' AS TIMESTAMP(3))",
        ) > 0
    );
    assert!(
        drift_rendered_source(
            timestamp,
            "'1970-01-01 00:00:01.123456'",
            "'1970-01-01 00:00:01.123'",
        ) > 0
    );
    rendered_cases.push(("timestamp fraction", 3, timestamp_fraction));

    let mut boolean_literal = raw.clone();
    let boolean_filter = find_first_source_where_filter_mut(
        boolean_literal.queries[5]
            .rel
            .as_mut()
            .expect("Boolean relation"),
    )
    .expect("Boolean WHERE ownership");
    let condition = boolean_filter
        .condition_rex
        .as_mut()
        .expect("Boolean WHERE Rex");
    assert!(drift_rendered_source(condition, "b = false", "`b` = 0") > 0);
    assert!(drift_rendered_source(condition, "false", "0") > 0);
    boolean_filter
        .source_where
        .as_mut()
        .unwrap()
        .source_condition_sql = "`b` = 0".to_owned();
    rendered_cases.push(("Boolean false versus integer zero", 5, boolean_literal));

    let mut failures = Vec::new();
    for (label, query_index, rendered) in rendered_cases {
        match convert_raw_file(rendered) {
            Ok(rendered) => {
                if rendered.queries[query_index].output() != exact.queries[query_index].output() {
                    failures.push(format!("{label}: rendered drift changed output typing"));
                }
                if ir_scalar_asts(&rendered.queries[query_index].rel)
                    != ir_scalar_asts(&exact.queries[query_index].rel)
                {
                    failures.push(format!("{label}: rendered drift changed scalar semantics"));
                }
            }
            Err(error) => failures.push(format!("{label}: {error}")),
        }
    }
    assert!(
        failures.is_empty(),
        "exact source text did not override rendered SQL drift:\n{}",
        failures.join("\n")
    );

    let mut forged_exact_text = raw.clone();
    let coalesce = &mut forged_exact_text.queries[1]
        .rel
        .as_mut()
        .unwrap()
        .project_rex[0];
    exact_descendant_mut(coalesce, "0.00").source_text = Some("0".to_owned());
    assert!(
        convert_raw_file(forged_exact_text).is_err(),
        "changed exact text must not validate against its original source span"
    );

    let mut borrowed_identifier_span = raw;
    let plus = &mut borrowed_identifier_span.queries[4]
        .rel
        .as_mut()
        .unwrap()
        .project_rex[0];
    let right_node = plus.operands[1].source_node_id.clone();
    plus.operands[0].source_node_id = right_node;
    assert!(
        convert_raw_file(borrowed_identifier_span).is_err(),
        "same rendered identifier text must not authorize a different exact source position"
    );

    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_closes_project_order_operator_and_contextual_cast_authority() {
    let repo = repo_root();
    let temp = temp_dir("project-order-operator-cast-authority");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(
        &schema,
        "create table t(a integer, b integer, d double precision);\n",
    )
    .unwrap();
    fs::write(
        &query,
        "select a, b from t;\n\
         select a + b from t;\n\
         select d from t where d = 88.0;\n\
         select cast(a as double precision) from t \
           order by cast(a as double precision) offset 1 rows;\n",
    )
    .unwrap();

    let raw = run_calcite(&repo, &schema, &query);
    convert_raw_file(raw.clone()).expect("pristine ordered Projects and comparison coercion");

    let double_sort = raw.queries[3]
        .rel
        .as_ref()
        .expect("explicit DOUBLE PRECISION query");
    assert_eq!(double_sort.rel_type, "LogicalSort");
    let double_project = &double_sort.inputs[0];
    assert_eq!(double_project.rel_type, "LogicalProject");
    let double_cast = &double_project.project_rex[0];
    assert_eq!(double_cast.source_kind.as_deref(), Some("CAST"));
    assert_eq!(
        double_cast.source_text.as_deref(),
        Some("cast(a as double precision)")
    );
    assert_eq!(
        double_cast.operands[0].source_kind.as_deref(),
        Some("IDENTIFIER")
    );
    assert_eq!(double_cast.operands[0].source_text.as_deref(), Some("a"));
    assert_eq!(
        double_cast.operands[0].source_identifier_names,
        ["a".to_owned()]
    );

    let mut inherited_cast_source = raw.clone();
    let cast = &mut inherited_cast_source.queries[3]
        .rel
        .as_mut()
        .unwrap()
        .inputs[0]
        .project_rex[0];
    let inherited = cast.clone();
    let operand = &mut cast.operands[0];
    operand.source_sql = inherited.source_sql;
    operand.source_node_id = inherited.source_node_id;
    operand.source_text = inherited.source_text;
    operand.source_kind = inherited.source_kind;
    operand.source_operator = inherited.source_operator;
    operand.source_identifier_names.clear();
    operand.source_identifier_quoted.clear();
    assert!(
        matches!(
            convert_raw_file(inherited_cast_source),
            Err(logos_ir::Error::InvalidRelSourceProvenance(_))
        ),
        "a CAST root cannot replace its generated identifier operand's exact lineage"
    );

    let mut wrong_cast_input = raw.clone();
    let operand =
        &mut wrong_cast_input.queries[3].rel.as_mut().unwrap().inputs[0].project_rex[0].operands[0];
    operand.index = Some(1);
    operand.text = Some("$1".to_owned());
    assert!(
        matches!(
            convert_raw_file(wrong_cast_input),
            Err(logos_ir::Error::InvalidRelSourceProvenance(_))
        ),
        "the exact CAST identifier cannot authorize a different same-typed input position"
    );

    let mut swapped = raw.clone();
    swapped.queries[0]
        .rel
        .as_mut()
        .expect("two-item Project")
        .project_rex
        .swap(0, 1);
    assert!(
        convert_raw_file(swapped).is_err(),
        "complete exact SELECT nodes cannot be swapped between output positions"
    );

    let mut omitted_query_block = raw.clone();
    omitted_query_block.queries[0]
        .rel
        .as_mut()
        .expect("source-associated Project")
        .source_query_block_id = None;
    assert!(
        convert_raw_file(omitted_query_block).is_err(),
        "exact Project nodes cannot bypass item ordering by omitting the query block"
    );

    let mut mismatched_operator = raw.clone();
    let plus = &mut mismatched_operator.queries[1]
        .rel
        .as_mut()
        .expect("PLUS Project")
        .project_rex[0];
    plus.kind = Some("TIMES".to_owned());
    plus.op_kind = Some("TIMES".to_owned());
    plus.operator = Some("*".to_owned());
    plus.text = Some("*($0, $1)".to_owned());
    assert!(
        convert_raw_file(mismatched_operator).is_err(),
        "exact source a+b cannot authorize a generated multiplication"
    );

    let mut project_cast = raw;
    let project = project_cast.queries[0]
        .rel
        .as_mut()
        .expect("Project for forged cast");
    let leaf = project.project_rex[0].clone();
    let cast = &mut project.project_rex[0];
    cast.kind = Some("CAST".to_owned());
    cast.class = Some("RexCall".to_owned());
    cast.op_kind = Some("CAST".to_owned());
    cast.operator = Some("CAST".to_owned());
    cast.text = Some("CAST($0):BIGINT".to_owned());
    cast.ty = Some("BIGINT".to_owned());
    cast.full_type = Some("BIGINT".to_owned());
    cast.precision = Some(19);
    cast.scale = Some(0);
    cast.index = None;
    cast.operands = vec![leaf];
    assert!(
        convert_raw_file(project_cast).is_err(),
        "a comparison-only implicit-cast rule cannot authorize a Project-root INTEGER-to-BIGINT cast"
    );

    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_recovers_postgres_values_string_typmods() {
    let repo = repo_root();
    let temp = temp_dir("values-string-typmods");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&schema, "create table t(id integer);\n").unwrap();
    fs::write(
        &query,
        "values ('a'), ('bb'), (null);\n\
         values (cast('a' as varchar(2))), (cast('b' as varchar(2)));\n\
         values ('a'), (cast('b' as varchar(2)));\n\
         values ('a '), ('bb');\n",
    )
    .unwrap();

    let raw = run_calcite(&repo, &schema, &query);
    assert_eq!(raw.queries.len(), 4);
    let values = raw.queries[0].rel.as_ref().expect("bare VALUES relation");
    assert_eq!(values.source_query_block_id, values.source_node_id);
    assert_eq!(values.source_root_query_block_id, values.source_node_id);
    assert_eq!(
        values.source_text.as_deref(),
        Some("values ('a'), ('bb'), (null)")
    );
    let first = &values.tuples.as_ref().expect("bare VALUES tuples")[0][0];
    assert_eq!(first.text.as_deref(), Some("'a '"));
    assert_eq!(first.source_sql.as_deref(), Some("'a'"));
    assert_eq!(first.source_text.as_deref(), Some("'a'"));
    assert_eq!(first.source_kind.as_deref(), Some("LITERAL"));
    assert_eq!(first.literal_value2.as_deref(), Some("a "));

    let ir = convert_raw_file(raw.clone()).unwrap();
    assert_eq!(ir.queries.len(), 4);
    assert_eq!(ir.queries[0].output()[0].ty, SqlType::text());
    let RelExpr::Values { rows, .. } = &ir.queries[0].rel else {
        panic!("expected VALUES");
    };
    assert!(matches!(&rows[0][0].parsed, ScalarAst::Literal { raw } if raw == "'a'"));
    assert!(matches!(&rows[1][0].parsed, ScalarAst::Literal { raw } if raw == "'bb'"));
    assert_eq!(ir.queries[1].output()[0].ty, SqlType::varchar(Some(2)));
    assert_eq!(ir.queries[2].output()[0].ty, SqlType::varchar(None));
    assert_eq!(ir.queries[3].output()[0].ty, SqlType::text());
    let RelExpr::Values { rows, .. } = &ir.queries[3].rel else {
        panic!("expected trailing-space VALUES");
    };
    assert!(matches!(&rows[0][0].parsed, ScalarAst::Literal { raw } if raw == "'a '"));

    let mut rendered_cell_drift = raw.clone();
    rendered_cell_drift.queries[0]
        .rel
        .as_mut()
        .unwrap()
        .tuples
        .as_mut()
        .unwrap()[0][0]
        .source_sql = Some("'c'".to_owned());
    let rendered_cell_drift =
        convert_raw_file(rendered_cell_drift).expect("exact VALUES cell overrides sourceSql");
    let RelExpr::Values { rows, .. } = &rendered_cell_drift.queries[0].rel else {
        panic!("expected VALUES after rendered cell drift");
    };
    assert!(matches!(&rows[0][0].parsed, ScalarAst::Literal { raw } if raw == "'a'"));

    let mut forged_exact_text = raw.clone();
    forged_exact_text.queries[0]
        .rel
        .as_mut()
        .unwrap()
        .tuples
        .as_mut()
        .unwrap()[0][0]
        .source_text = Some("'c'".to_owned());
    assert!(convert_raw_file(forged_exact_text).is_err());

    let mut borrowed_cell_span = raw.clone();
    let second_span = borrowed_cell_span.queries[0]
        .rel
        .as_ref()
        .unwrap()
        .tuples
        .as_ref()
        .unwrap()[1][0]
        .source_node_id
        .clone();
    borrowed_cell_span.queries[0]
        .rel
        .as_mut()
        .unwrap()
        .tuples
        .as_mut()
        .unwrap()[0][0]
        .source_node_id = second_span;
    assert!(convert_raw_file(borrowed_cell_span).is_err());

    let mut swapped_exact_cells = raw.clone();
    swapped_exact_cells.queries[0]
        .rel
        .as_mut()
        .unwrap()
        .tuples
        .as_mut()
        .unwrap()
        .swap(0, 1);
    assert!(
        convert_raw_file(swapped_exact_cells).is_err(),
        "complete exact VALUES cells cannot be swapped between source positions"
    );

    let mut rendered_parent_drift = raw;
    rendered_parent_drift.queries[0]
        .rel
        .as_mut()
        .unwrap()
        .source_sql = Some("VALUES ROW('diagnostic only')".to_owned());
    let exact = convert_raw_file(rendered_parent_drift).unwrap();
    let RelExpr::Values { rows, .. } = &exact.queries[0].rel else {
        panic!("expected exact VALUES after rendered-source drift");
    };
    assert!(matches!(&rows[0][0].parsed, ScalarAst::Literal { raw } if raw == "'a'"));
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_recovers_mixed_numeric_values_zero_dscale() {
    let repo = repo_root();
    let temp = temp_dir("values-numeric-zero-dscale");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&schema, "create table t(id integer);\n").unwrap();
    fs::write(&query, "values (0), (2.1);\n").unwrap();

    let raw = run_calcite(&repo, &schema, &query);
    let values = raw.queries[0].rel.as_ref().expect("numeric VALUES");
    let rows = values.tuples.as_ref().expect("numeric VALUES tuples");
    assert_eq!(rows[0][0].source_sql.as_deref(), Some("0"));
    assert_eq!(rows[0][0].text.as_deref(), Some("0.0:DECIMAL(11, 1)"));
    assert_eq!(rows[0][0].scale, Some(1));

    let ir = convert_raw_file(raw.clone()).unwrap();
    let RelExpr::Values { rows, output } = &ir.queries[0].rel else {
        panic!("expected converted numeric VALUES");
    };
    assert_eq!(output[0].ty, SqlType::decimal(None, None));
    assert!(matches!(
        &rows[0][0].parsed,
        ScalarAst::TypeAnnotation { expr, ty }
            if ty == "NUMERIC"
                && matches!(
                    expr.as_ref(),
                    ScalarAst::Call { op: ScalarOp::Cast, args, .. }
                        if matches!(
                            args.as_slice(),
                            [ScalarAst::TypeAnnotation { expr, ty }]
                                if ty == "INTEGER"
                                    && matches!(expr.as_ref(), ScalarAst::Literal { raw } if raw == "0")
                        )
                )
    ));
    assert!(matches!(
        &rows[1][0].parsed,
        ScalarAst::TypeAnnotation { expr, ty }
            if ty == "NUMERIC"
                && matches!(expr.as_ref(), ScalarAst::Literal { raw } if raw == "2.1")
    ));

    let exact_zero = rows[0][0].parsed.clone();
    let mut rendered_source_drift = raw.clone();
    rendered_source_drift.queries[0]
        .rel
        .as_mut()
        .unwrap()
        .tuples
        .as_mut()
        .unwrap()[0][0]
        .source_sql = Some("1".to_owned());
    let rendered_source_drift = convert_raw_file(rendered_source_drift)
        .expect("exact numeric VALUES cell overrides sourceSql");
    let RelExpr::Values { rows, .. } = &rendered_source_drift.queries[0].rel else {
        panic!("expected numeric VALUES after rendered-source drift");
    };
    assert_eq!(rows[0][0].parsed, exact_zero);

    let mut exact_text_drift = raw.clone();
    exact_text_drift.queries[0]
        .rel
        .as_mut()
        .unwrap()
        .tuples
        .as_mut()
        .unwrap()[0][0]
        .source_text = Some("1".to_owned());
    assert!(convert_raw_file(exact_text_drift).is_err());

    let mut forged_payload = raw;
    forged_payload.queries[0]
        .rel
        .as_mut()
        .unwrap()
        .tuples
        .as_mut()
        .unwrap()[0][0]
        .literal_value2 = Some("1".to_owned());
    assert!(convert_raw_file(forged_payload).is_err());
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_models_ordered_character_values_common_types() {
    let repo = repo_root();
    let temp = temp_dir("values-mixed-character-common-type");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&schema, "create table t(id integer);\n").unwrap();
    fs::write(
        &query,
        "values (cast('a' as char(2))), (cast('b' as varchar(2)));\n\
         values (cast('a' as varchar(2))), (cast('b' as char(2)));\n\
         select cast('a' as char(2)) as x union all select null;\n\
         select null as x union all select cast('a' as char(2));\n",
    )
    .unwrap();

    let raw = run_calcite(&repo, &schema, &query);
    assert_eq!(raw.queries.len(), 4);
    for (query_index, branch_index, source_cast, source_literal) in [
        (0, 0, "CAST('a' AS CHAR(2))", "'a'"),
        (1, 1, "CAST('b' AS CHAR(2))", "'b'"),
    ] {
        let union = raw.queries[query_index]
            .rel
            .as_ref()
            .expect("mixed character VALUES union");
        assert_eq!(union.rel_type, "LogicalUnion");
        assert_eq!(union.all, Some(true));
        let outer = &union.inputs[branch_index].project_rex[0];
        assert_eq!(outer.kind.as_deref(), Some("CAST"));
        assert_eq!(outer.ty.as_deref(), Some("VARCHAR"));
        assert_eq!(outer.source_sql.as_deref(), Some(source_cast));
        assert_eq!(outer.source_kind.as_deref(), Some("CAST"));
        let explicit = &outer.operands[0];
        assert_eq!(explicit.kind.as_deref(), Some("CAST"));
        assert_eq!(explicit.ty.as_deref(), Some("CHAR"));
        assert_eq!(explicit.source_sql.as_deref(), Some(source_cast));
        assert_eq!(
            explicit.operands[0].source_sql.as_deref(),
            Some(source_literal)
        );
        assert_eq!(explicit.operands[0].source_kind.as_deref(), Some("LITERAL"));
    }

    let ir = convert_raw_file(raw.clone()).unwrap();
    assert_eq!(ir.queries[0].output()[0].ty, SqlType::bpchar());
    assert_eq!(ir.queries[1].output()[0].ty, SqlType::varchar(None));
    assert_eq!(ir.queries[2].output()[0].ty, SqlType::bpchar());
    assert_eq!(ir.queries[3].output()[0].ty, SqlType::bpchar());
    let exact_semantics = ir_scalar_asts(&ir.queries[0].rel);

    type RelMutation = (&'static str, fn(&mut logos_ir::calcite::CalciteRel));
    let values_expansion_mutations: [RelMutation; 4] = [
        ("source kind", |rel: &mut logos_ir::calcite::CalciteRel| {
            rel.source_kind = Some("SELECT".to_owned());
        }),
        (
            "source operator",
            |rel: &mut logos_ir::calcite::CalciteRel| {
                rel.source_operator = Some("UNION".to_owned());
            },
        ),
        ("row count", |rel: &mut logos_ir::calcite::CalciteRel| {
            rel.inputs.pop();
        }),
        (
            "set quantifier",
            |rel: &mut logos_ir::calcite::CalciteRel| {
                rel.all = Some(false);
            },
        ),
    ];
    for (label, mutate) in values_expansion_mutations {
        let mut forged = raw.clone();
        mutate(forged.queries[0].rel.as_mut().unwrap());
        assert!(
            convert_raw_file(forged).is_err(),
            "forged mixed-character VALUES {label} must fail closed"
        );
    }

    let exact_parent_source = raw.queries[0]
        .rel
        .as_ref()
        .and_then(|rel| rel.source_sql.as_deref())
        .expect("mixed character VALUES parent source");
    let parent_drifts = [
        (
            "parent cell type",
            exact_parent_source.replacen("CAST('a' AS CHAR(2))", "CAST('a' AS VARCHAR(2))", 1),
        ),
        (
            "parent cell value",
            exact_parent_source.replacen("CAST('a' AS CHAR(2))", "CAST('z' AS CHAR(2))", 1),
        ),
        (
            "parent cell expression",
            exact_parent_source.replacen("CAST('a' AS CHAR(2))", "CAST('a' AS CHAR(2)) || ''", 1),
        ),
    ];
    for (label, parent_source) in parent_drifts {
        assert_ne!(
            parent_source, exact_parent_source,
            "missing fixture for {label}"
        );
        let mut forged_parent = raw.clone();
        forged_parent.queries[0].rel.as_mut().unwrap().source_sql = Some(parent_source);
        let converted = convert_raw_file(forged_parent).unwrap_or_else(|error| {
            panic!("{label}: exact source must override sourceSql: {error}")
        });
        assert_eq!(
            ir_scalar_asts(&converted.queries[0].rel),
            exact_semantics,
            "{label} changed declarative scalar semantics"
        );
    }

    let mut rendered_cast_drift = raw.clone();
    rendered_cast_drift.queries[0].rel.as_mut().unwrap().inputs[0].project_rex[0].source_sql =
        Some("CAST('a' AS VARCHAR(2))".to_owned());
    let converted =
        convert_raw_file(rendered_cast_drift).expect("exact cast typmod overrides sourceSql");
    assert_eq!(ir_scalar_asts(&converted.queries[0].rel), exact_semantics);

    let mut exact_cast_drift = raw;
    exact_cast_drift.queries[0].rel.as_mut().unwrap().inputs[0].project_rex[0].source_text =
        Some("cast('a' as varchar(2))".to_owned());
    assert!(convert_raw_file(exact_cast_drift).is_err());
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_retains_fractional_numeric_to_integer_casts() {
    let repo = repo_root();
    let temp = temp_dir("folded-fractional-numeric-to-integer-casts");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&schema, "create table t(id integer);\n").unwrap();
    fs::write(
        &query,
        "select cast(1.9 as integer) as positive, \
                cast(-1.9 as integer) as negative from t;\n\
         select cast(1 as integer) as one, \
                cast(10 as integer) as ten, \
                cast(null as integer) as null_integer, \
                cast(null as boolean) as null_boolean from t;\n",
    )
    .unwrap();

    let raw = run_calcite(&repo, &schema, &query);
    assert_eq!(raw.queries.len(), 2);
    let project = raw.queries[0].rel.as_ref().expect("project root");
    assert_eq!(project.project_rex.len(), 2);
    for (rex, source, operand) in [
        (&project.project_rex[0], "CAST(1.9 AS INTEGER)", "1.9"),
        (&project.project_rex[1], "CAST(-1.9 AS INTEGER)", "-1.9"),
    ] {
        assert_eq!(rex.class.as_deref(), Some("RexCall"));
        assert_eq!(rex.kind.as_deref(), Some("CAST"));
        assert_eq!(rex.source_sql.as_deref(), Some(source));
        assert_eq!(rex.source_kind.as_deref(), Some("CAST"));
        assert_eq!(rex.source_operator.as_deref(), Some("CAST"));
        assert_eq!(rex.operands.len(), 1);
        assert_eq!(rex.operands[0].class.as_deref(), Some("RexLiteral"));
        assert_eq!(rex.operands[0].source_sql.as_deref(), Some(operand));
        assert_eq!(rex.operands[0].source_kind.as_deref(), Some("LITERAL"));
    }

    let fractional = convert_raw_file(CalciteFile {
        environment: raw.environment,
        schema: raw.schema.clone(),
        queries: vec![raw.queries[0].clone()],
    })
    .expect("explicit fractional numeric casts must remain semantic operations");
    let RelExpr::Project { exprs, output, .. } = &fractional.queries[0].rel else {
        panic!("fractional numeric casts must remain in a Project")
    };
    assert!(exprs.iter().all(|expr| scalar_contains_cast(&expr.parsed)));
    assert!(output.iter().all(|column| column.ty == SqlType::Integer));

    let safe_project = raw.queries[1].rel.as_ref().expect("safe project root");
    for (rex, source, value) in [
        (&safe_project.project_rex[0], "CAST(1 AS INTEGER)", "1"),
        (&safe_project.project_rex[1], "CAST(10 AS INTEGER)", "10"),
    ] {
        assert_eq!(rex.class.as_deref(), Some("RexLiteral"));
        assert_eq!(rex.text.as_deref(), Some(value));
        assert_eq!(rex.literal_value.as_deref(), Some(value));
        assert_eq!(rex.literal_value2.as_deref(), Some(value));
        assert_eq!(rex.source_sql.as_deref(), Some(source));
    }
    for (rex, source) in [
        (&safe_project.project_rex[2], "CAST(NULL AS INTEGER)"),
        (&safe_project.project_rex[3], "CAST(NULL AS BOOLEAN)"),
    ] {
        assert_eq!(rex.class.as_deref(), Some("RexLiteral"));
        assert_eq!(rex.literal_type_name.as_deref(), Some("NULL"));
        assert_eq!(rex.source_sql.as_deref(), Some(source));
    }
    let safe = convert_raw_file(CalciteFile {
        environment: raw.environment,
        schema: raw.schema.clone(),
        queries: vec![raw.queries[1].clone()],
    })
    .unwrap();
    assert_eq!(safe.queries[0].output()[0].ty, SqlType::Integer);
    assert_eq!(safe.queries[0].output()[1].ty, SqlType::Integer);
    assert_eq!(safe.queries[0].output()[2].ty, SqlType::Integer);
    assert_eq!(safe.queries[0].output()[3].ty, SqlType::Boolean);
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_preserves_set_type_resolution_association() {
    let repo = repo_root();
    let temp = temp_dir("set-character-common-type-association");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&schema, "create table t(id integer);\n").unwrap();
    fs::write(
        &query,
        "select null as x union all select null union all select cast('a' as char(2));\n\
         select null as x union all select cast('a' as char(2)) union all select null;\n\
         select null as x union all (select null union all select cast('a' as char(2)));\n",
    )
    .unwrap();

    let ir = convert_raw_file(run_calcite(&repo, &schema, &query)).unwrap();
    assert_eq!(ir.queries[0].output()[0].ty, SqlType::text());
    assert_eq!(ir.queries[1].output()[0].ty, SqlType::bpchar());
    assert_eq!(ir.queries[2].output()[0].ty, SqlType::bpchar());
    assert!(matches!(
        &ir.queries[0].rel,
        RelExpr::Set { inputs, .. } if matches!(inputs.first(), Some(RelExpr::Set { .. }))
    ));
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_rejects_rewritten_nullif_string_typing() {
    let repo = repo_root();
    let temp = temp_dir("rewritten-nullif-string-typing");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&schema, "create table t(c text);\n").unwrap();
    fs::write(
        &query,
        "select nullif(c, cast('x' as varchar)) as x from t;\n\
         select cast(nullif(c, cast('x' as varchar)) as varchar) as x from t;\n",
    )
    .unwrap();

    let raw = run_calcite(&repo, &schema, &query);
    let nullif = &raw.queries[0].rel.as_ref().unwrap().project_rex[0];
    assert_eq!(
        nullif.source_sql.as_deref(),
        Some("NULLIF(`c`, CAST('x' AS VARCHAR))")
    );
    assert!(
        nullif
            .source_operator
            .as_deref()
            .is_some_and(|operator| operator.eq_ignore_ascii_case("NULLIF"))
    );
    assert!(nullif.operands[1].source_sql.is_none());
    let casted_nullif = &raw.queries[1].rel.as_ref().unwrap().project_rex[0];
    assert_eq!(casted_nullif.kind.as_deref(), Some("CAST"));
    assert_eq!(casted_nullif.operands.len(), 1);
    assert!(casted_nullif.operands[0].operands[1].source_sql.is_none());

    for query in &raw.queries {
        let error = convert_raw_file(CalciteFile {
            environment: raw.environment,
            schema: raw.schema.clone(),
            queries: vec![query.clone()],
        })
        .unwrap_err();
        assert!(
            error.to_string().contains("NULLIF")
                || error
                    .to_string()
                    .contains("collapsed an observable VARCHAR CAST"),
            "unexpected error: {error}"
        );
    }
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_keeps_unknown_character_comparison_literals_unconstrained() {
    let repo = repo_root();
    let temp = temp_dir("unknown-character-comparison-literals");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&schema, "create table t(c char(2), v varchar(2));\n").unwrap();
    fs::write(
        &query,
        "select c from t where c = 'abc';\n\
         select v from t where v = 'abc';\n",
    )
    .unwrap();

    let ir = convert_raw_file(run_calcite(&repo, &schema, &query)).unwrap();
    for query in &ir.queries {
        let predicate = outer_filter_predicate(&query.rel);
        assert!(matches!(
            &predicate.parsed,
            ScalarAst::Call { args, .. }
                if matches!(args.as_slice(), [ScalarAst::InputRef { .. }, ScalarAst::Literal { raw }] if raw == "'abc'")
        ));
    }
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_only_recovers_exact_integer_numeric_literals_in_double_comparisons() {
    let repo = repo_root();
    let temp = temp_dir("exact-numeric-literal-double-comparison");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&schema, "create table measurements(score float);\n").unwrap();
    fs::write(
        &query,
        "select score from measurements where score <= 88.0;\n\
         select score from measurements where score <= 88.1;\n\
         select score from measurements where score <= 9007199254740993.0;\n",
    )
    .unwrap();

    let raw = run_calcite(&repo, &schema, &query);
    for (index, source) in ["88.0", "88.1", "9007199254740993.0"]
        .into_iter()
        .enumerate()
    {
        let comparison = first_condition_rex(raw.queries[index].rel.as_ref().unwrap());
        let rhs = &comparison.operands[1];
        assert_eq!(rhs.source_kind.as_deref(), Some("LITERAL"));
        assert_eq!(rhs.source_sql.as_deref(), Some(source));
        let [literal] = rhs.operands.as_slice() else {
            panic!("Calcite implicit DOUBLE coercion must retain one literal operand");
        };
        assert_eq!(literal.source_kind.as_deref(), Some("LITERAL"));
        assert_eq!(literal.source_sql.as_deref(), Some(source));
    }

    let ir = convert_raw_file(raw).unwrap();
    let positive = outer_filter_predicate(&ir.queries[0].rel);
    assert!(matches!(
        &positive.parsed,
        ScalarAst::Call { args, .. }
            if matches!(
                args.as_slice(),
                [ScalarAst::InputRef { .. }, ScalarAst::TypeAnnotation { expr, ty }]
                    if ty == "DOUBLE"
                        && matches!(expr.as_ref(), ScalarAst::Literal { raw } if raw == "88")
            )
    ));
    for query in &ir.queries[1..] {
        assert!(
            scalar_contains_cast(&outer_filter_predicate(&query.rel).parsed),
            "non-integral or out-of-range NUMERIC literals must retain their coercion boundary"
        );
    }
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_keeps_nested_filter_cast_provenance_at_its_query_level() {
    let repo = repo_root();
    let temp = temp_dir("nested-filter-cast-provenance");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(
        &schema,
        "create table t(c char(4), v varchar(2), n integer);\n",
    )
    .unwrap();
    fs::write(
        &query,
        "select c from (select c, v, n from t where cast(c as varchar(2)) = v) s where c = v;\n\
         select c from (select c, v, n from t where cast(c as varchar(2)) = v) s where cast(c as varchar(2)) = v;\n",
    )
    .unwrap();

    let ir = convert_raw_file(run_calcite(&repo, &schema, &query)).unwrap();
    assert_eq!(ir.queries.len(), 2);
    let source = outer_filter_predicate(&ir.queries[0].rel);
    let target = outer_filter_predicate(&ir.queries[1].rel);
    assert!(matches!(
        &source.parsed,
        ScalarAst::Call { args, .. }
            if matches!(args.as_slice(), [ScalarAst::InputRef { .. }, ScalarAst::InputRef { .. }])
    ));
    assert!(matches!(
        &target.parsed,
        ScalarAst::Call { args, .. }
            if matches!(args.first(), Some(ScalarAst::TypeAnnotation { ty, .. }) if ty == "VARCHAR(2)")
    ));
    assert_ne!(source.parsed, target.parsed);
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_keeps_cartesian_sources_as_logical_joins() {
    fn raw_join(rel: &CalciteRel) -> Option<&CalciteRel> {
        if rel.rel_type == "LogicalJoin" {
            return Some(rel);
        }
        rel.inputs.iter().find_map(raw_join)
    }

    fn raw_join_mut(rel: &mut CalciteRel) -> Option<&mut CalciteRel> {
        if rel.rel_type == "LogicalJoin" {
            return Some(rel);
        }
        rel.inputs.iter_mut().find_map(raw_join_mut)
    }

    fn collect_join_types(rel: &RelExpr, join_types: &mut Vec<logos_ir::ir::JoinType>) {
        match rel {
            RelExpr::Join {
                left,
                right,
                join_type,
                ..
            } => {
                join_types.push(*join_type);
                collect_join_types(left, join_types);
                collect_join_types(right, join_types);
            }
            RelExpr::Project { input, .. }
            | RelExpr::Filter { input, .. }
            | RelExpr::NativeHaving { input, .. }
            | RelExpr::Aggregate { input, .. }
            | RelExpr::Distinct { input, .. }
            | RelExpr::Sort { input, .. } => collect_join_types(input, join_types),
            RelExpr::Set { inputs, .. } => {
                for input in inputs {
                    collect_join_types(input, join_types);
                }
            }
            RelExpr::TableScan { .. } | RelExpr::Values { .. } => {}
        }
    }

    let repo = repo_root();
    let temp = temp_dir("logical-cartesian-joins");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(
        &schema,
        "create table a(id integer);\ncreate table b(id integer);\ncreate table c(id integer);\ncreate table d(id integer);\n",
    )
    .unwrap();
    fs::write(
        &query,
        "select a.id, b.id from a cross join b;\n\
         select a.id, b.id from a, b;\n\
         select a.id, b.id from a left join b on true;\n\
         select a.id, b.id, c.id from a cross join b inner join c on true;\n\
         select a.id, b.id, c.id, d.id from (a cross join b) cross join (c cross join d);\n",
    )
    .unwrap();

    let raw = run_calcite(&repo, &schema, &query);
    assert_eq!(raw.queries.len(), 5);
    for (index, (expected, syntax, syntax_text)) in [
        ("INNER", "CROSS", "CROSS JOIN"),
        ("INNER", "COMMA", ","),
        ("LEFT", "LEFT", "LEFT JOIN"),
    ]
    .into_iter()
    .enumerate()
    {
        let join = raw_join(raw.queries[index].rel.as_ref().expect("logical relation"))
            .expect("source join must remain a LogicalJoin");
        assert_eq!(join.rel_type, "LogicalJoin");
        assert_eq!(join.join_type.as_deref(), Some(expected));
        assert_eq!(join.source_join_type.as_deref(), Some(expected));
        assert_eq!(join.source_join_syntax.as_deref(), Some(syntax));
        assert!(
            join.source_join_syntax_text
                .as_deref()
                .is_some_and(|text| text.eq_ignore_ascii_case(syntax_text))
        );
        assert!(join.source_join_syntax_node_id.is_some());
        assert_eq!(join.inputs.len(), 2);
    }

    let baseline = convert_raw_file(raw.clone()).expect("convert exact logical joins");

    let mut rendered_drift = raw.clone();
    raw_join_mut(rendered_drift.queries[0].rel.as_mut().unwrap())
        .unwrap()
        .source_sql = Some("SELECT * FROM a INNER JOIN b ON TRUE".to_owned());
    let rendered = convert_raw_file(rendered_drift)
        .expect("rendered join SQL is diagnostic beside exact syntax identity");
    assert_eq!(
        ir_scalar_asts(&rendered.queries[0].rel),
        ir_scalar_asts(&baseline.queries[0].rel)
    );

    let mut forged_syntax = raw.clone();
    raw_join_mut(forged_syntax.queries[0].rel.as_mut().unwrap())
        .unwrap()
        .source_join_syntax = Some("INNER".to_owned());
    assert!(matches!(
        convert_raw_file(forged_syntax),
        Err(logos_ir::Error::InvalidRelSourceProvenance(_))
    ));

    let mut forged_text = raw.clone();
    raw_join_mut(forged_text.queries[0].rel.as_mut().unwrap())
        .unwrap()
        .source_join_syntax_text = Some("INNER JOIN".to_owned());
    assert!(matches!(
        convert_raw_file(forged_text),
        Err(logos_ir::Error::InvalidRelSourceProvenance(_))
    ));

    let mut omitted_syntax = raw.clone();
    let join = raw_join_mut(omitted_syntax.queries[0].rel.as_mut().unwrap()).unwrap();
    join.source_kind = None;
    join.source_join_syntax = None;
    join.source_join_syntax_node_id = None;
    join.source_join_syntax_text = None;
    assert!(matches!(
        convert_raw_file(omitted_syntax),
        Err(logos_ir::Error::InvalidRelSourceProvenance(_))
    ));

    let mut omitted_all_join_authority = raw.clone();
    let join = raw_join_mut(omitted_all_join_authority.queries[0].rel.as_mut().unwrap()).unwrap();
    join.source_sql = None;
    join.source_node_id = None;
    join.source_text = None;
    join.source_kind = None;
    join.source_operator = None;
    join.source_join_type = None;
    join.source_join_syntax = None;
    join.source_join_syntax_node_id = None;
    join.source_join_syntax_text = None;
    assert!(matches!(
        convert_raw_file(omitted_all_join_authority),
        Err(logos_ir::Error::InvalidRelSourceProvenance(_))
    ));

    let mut borrowed_syntax = raw.clone();
    let outer = raw_join(
        borrowed_syntax.queries[3]
            .rel
            .as_ref()
            .expect("multi-join relation"),
    )
    .unwrap();
    let inner = outer.inputs.iter().find_map(raw_join).unwrap();
    let borrowed = (
        inner.source_join_syntax.clone(),
        inner.source_join_syntax_node_id.clone(),
        inner.source_join_syntax_text.clone(),
    );
    let outer = raw_join_mut(borrowed_syntax.queries[3].rel.as_mut().unwrap()).unwrap();
    outer.source_join_syntax = borrowed.0;
    outer.source_join_syntax_node_id = borrowed.1;
    outer.source_join_syntax_text = borrowed.2;
    assert!(matches!(
        convert_raw_file(borrowed_syntax),
        Err(logos_ir::Error::InvalidRelSourceProvenance(_))
    ));

    let mut sibling_reuse = raw.clone();
    let outer = raw_join_mut(sibling_reuse.queries[4].rel.as_mut().unwrap()).unwrap();
    let left_join_index = outer
        .inputs
        .iter()
        .position(|input| input.rel_type == "LogicalJoin")
        .expect("left sibling Join");
    let right_join_index = outer
        .inputs
        .iter()
        .rposition(|input| input.rel_type == "LogicalJoin")
        .expect("right sibling Join");
    assert_ne!(left_join_index, right_join_index);
    let borrowed = {
        let left = &outer.inputs[left_join_index];
        (
            left.source_join_syntax.clone(),
            left.source_join_syntax_node_id.clone(),
            left.source_join_syntax_text.clone(),
        )
    };
    let right = &mut outer.inputs[right_join_index];
    right.source_join_syntax = borrowed.0;
    right.source_join_syntax_node_id = borrowed.1;
    right.source_join_syntax_text = borrowed.2;
    assert!(matches!(
        convert_raw_file(sibling_reuse),
        Err(logos_ir::Error::InvalidRelSourceProvenance(_))
    ));

    let ir = baseline;
    for (index, expected) in [
        logos_ir::ir::JoinType::Inner,
        logos_ir::ir::JoinType::Inner,
        logos_ir::ir::JoinType::Left,
    ]
    .into_iter()
    .enumerate()
    {
        let mut join_types = Vec::new();
        collect_join_types(&ir.queries[index].rel, &mut join_types);
        assert_eq!(join_types, [expected]);
    }
    let mut nested_join_types = Vec::new();
    collect_join_types(&ir.queries[3].rel, &mut nested_join_types);
    assert_eq!(
        nested_join_types,
        [logos_ir::ir::JoinType::Inner, logos_ir::ir::JoinType::Inner]
    );
    let mut parenthesized_join_types = Vec::new();
    collect_join_types(&ir.queries[4].rel, &mut parenthesized_join_types);
    assert_eq!(
        parenthesized_join_types,
        [
            logos_ir::ir::JoinType::Inner,
            logos_ir::ir::JoinType::Inner,
            logos_ir::ir::JoinType::Inner,
        ]
    );

    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_keeps_complete_values_alias_join_extents() {
    fn raw_join(rel: &CalciteRel) -> Option<&CalciteRel> {
        (rel.rel_type == "LogicalJoin")
            .then_some(rel)
            .or_else(|| rel.inputs.iter().find_map(raw_join))
    }

    fn raw_join_mut(rel: &mut CalciteRel) -> Option<&mut CalciteRel> {
        if rel.rel_type == "LogicalJoin" {
            return Some(rel);
        }
        rel.inputs.iter_mut().find_map(raw_join_mut)
    }

    let repo = repo_root();
    let temp = temp_dir("complete-values-alias-join-extent");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&schema, "create table emp(deptno integer, mgr integer);\n").unwrap();
    fs::write(
        &query,
        "select emp.deptno, max(emp.mgr) from emp, (values (4)) as t (four) \
         group by t.four, emp.deptno;\n",
    )
    .unwrap();

    let raw = run_calcite(&repo, &schema, &query);
    let join = raw_join(raw.queries[0].rel.as_ref().expect("VALUES join relation"))
        .expect("VALUES comma join");
    let source_join = join.source_join.as_ref().expect("exact join authority");
    assert_eq!(
        source_join.right_text.to_ascii_lowercase(),
        "(values (4)) as t (four)"
    );
    convert_raw_file(raw.clone()).expect("convert exact VALUES alias namespace");

    let mut truncated = raw;
    let source_join = raw_join_mut(truncated.queries[0].rel.as_mut().unwrap())
        .unwrap()
        .source_join
        .as_mut()
        .unwrap();
    source_join.right_text = source_join.right_text[1..].to_owned();
    assert!(
        convert_raw_file(truncated).is_err(),
        "a VALUES alias extent missing its opening parenthesis must fail closed"
    );

    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_keeps_source_provenance_through_cte_predicate_rewrites() {
    let repo = repo_root();
    let temp = temp_dir("cte-string-predicate-provenance");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&schema, "create table t(c char(4), n integer);\n").unwrap();
    fs::write(
        &query,
        "with x as (select c from t where n between 1 and 2 and c in ('a', 'b')) \
         select c from x;\n",
    )
    .unwrap();

    convert_raw_file(run_calcite(&repo, &schema, &query)).unwrap();
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_keeps_outer_where_separate_from_nested_having() {
    let repo = repo_root();
    let temp = temp_dir("nested-where-having-provenance");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(
        &schema,
        "create table t(unused integer, k integer, v integer, tail integer);\n",
    )
    .unwrap();
    fs::write(
        &query,
        "select q.k, q.s from (select k, sum(v) as s from t group by k having k = 1) as q \
         where q.s > 0;\n",
    )
    .unwrap();

    fn count_clauses(rel: &RelExpr, having: &mut usize, filter: &mut usize) {
        match rel {
            RelExpr::NativeHaving { input, .. } => {
                *having += 1;
                count_clauses(input, having, filter);
            }
            RelExpr::Filter { input, .. } => {
                *filter += 1;
                count_clauses(input, having, filter);
            }
            RelExpr::Project { input, .. }
            | RelExpr::Aggregate { input, .. }
            | RelExpr::Distinct { input, .. }
            | RelExpr::Sort { input, .. } => count_clauses(input, having, filter),
            RelExpr::Join { left, right, .. } => {
                count_clauses(left, having, filter);
                count_clauses(right, having, filter);
            }
            RelExpr::Set { inputs, .. } => {
                for input in inputs {
                    count_clauses(input, having, filter);
                }
            }
            RelExpr::TableScan { .. } | RelExpr::Values { .. } => {}
        }
    }

    let raw = run_calcite(&repo, &schema, &query);
    let ir = convert_raw_file(raw).unwrap();
    let mut having = 0;
    let mut filter = 0;
    count_clauses(&ir.queries[0].rel, &mut having, &mut filter);
    assert_eq!(having, 1, "inner query must retain one HAVING");
    assert_eq!(filter, 1, "outer query must retain one ordinary WHERE");
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_keeps_quoted_and_unquoted_project_aliases_distinct() {
    let repo = repo_root();
    let temp = temp_dir("quoted-project-alias-identity");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&schema, "create table t(v varchar(9));\n").unwrap();
    fs::write(
        &query,
        "select \"X\", x from (\
           select cast(v as varchar(3)) as \"X\", cast(v as varchar(7)) as x from t\
         ) s;\n",
    )
    .unwrap();

    let ir = convert_raw_file(run_calcite(&repo, &schema, &query)).unwrap();
    let RelExpr::Project { exprs, output, .. } = &ir.queries[0].rel else {
        panic!("expected flattened project");
    };
    assert_eq!(output[0].ty, SqlType::varchar(Some(3)));
    assert_eq!(output[1].ty, SqlType::varchar(Some(7)));
    assert!(matches!(
        &exprs[0].parsed,
        ScalarAst::TypeAnnotation { ty, .. } if ty == "VARCHAR(3)"
    ));
    assert!(matches!(
        &exprs[1].parsed,
        ScalarAst::TypeAnnotation { ty, .. } if ty == "VARCHAR(7)"
    ));
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_keeps_quoted_and_unquoted_cte_names_distinct() {
    let repo = repo_root();
    let temp = temp_dir("quoted-cte-identity");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&schema, "create table t(v varchar(9));\n").unwrap();
    fs::write(
        &query,
        "with x as (select cast(v as varchar(2)) as payload from t),\
              \"X\" as (select cast(v as varchar(5)) as payload from t)\
         select payload from x;\n\
         with x as (select cast(v as varchar(2)) as payload from t),\
              \"X\" as (select cast(v as varchar(5)) as payload from t)\
         select payload from \"X\";\n",
    )
    .unwrap();

    let raw = run_calcite_json(&repo, &schema, &query);
    let queries = raw["queries"].as_array().expect("queries array");
    assert_eq!(queries.len(), 2);
    for (query, expected_length) in queries.iter().zip([2, 5]) {
        assert!(query.get("error").is_none());
        let child_source = query["rel"]["inputs"][0]["sourceSql"]
            .as_str()
            .expect("inlined CTE input source");
        assert!(
            child_source.contains(&format!("VARCHAR({expected_length})")),
            "wrong CTE provenance for expected VARCHAR({expected_length}): {child_source}"
        );
        let other_length = if expected_length == 2 { 5 } else { 2 };
        assert!(!child_source.contains(&format!("VARCHAR({other_length})")));
    }
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_preserves_cte_scope_inside_in_subquery_literal_recovery() {
    let repo = repo_root();
    let temp = temp_dir("cte-in-subquery-literal-recovery");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(
        &schema,
        "create table items(item_id integer, category char(50));\n",
    )
    .unwrap();
    fs::write(
        &query,
        "with selected as (select item_id from items where category in ('Books', 'Shoes')) \
         select item_id from items where item_id in (select item_id from selected);\n",
    )
    .unwrap();

    let raw = run_calcite(&repo, &schema, &query);
    assert!(raw.queries[0].error.is_none());
    let ir = convert_raw_file(raw).unwrap_or_else(|error| {
        panic!(
            "an inlined CTE below an IN subquery must retain the exact source literal/cast origin: {error}"
        )
    });
    assert_eq!(ir.queries.len(), 1);

    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_nested_cte_shadowing_uses_inner_cast_provenance() {
    let repo = repo_root();
    let temp = temp_dir("nested-cte-shadowing");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&schema, "create table t(v varchar(9));\n").unwrap();
    fs::write(
        &query,
        "with x as (select v from t where cast(v as varchar(2)) = v),\
              y as (with x as (select v from t where cast(v as varchar(5)) = v)\
                    select v from x)\
         select v from y;\n",
    )
    .unwrap();

    let raw = run_calcite(&repo, &schema, &query);
    let filter =
        find_first_filter(raw.queries[0].rel.as_ref().unwrap()).expect("surviving inner CTE WHERE");
    let predicate = filter.condition_rex.as_ref().expect("inner CTE predicate");
    assert_eq!(
        predicate.source_text.as_deref(),
        Some("cast(v as varchar(5)) = v")
    );
    assert!(find_rex_by_source_sql(predicate, "CAST(`v` AS VARCHAR(5))").is_some());
    assert!(
        !predicate
            .source_text
            .as_deref()
            .is_some_and(|source| source.contains("varchar(2)"))
    );

    let error = convert_raw_file(raw).expect_err(
        "the independently present but unused outer CTE SELECT remains conservatively rejected",
    );
    assert!(matches!(
        error,
        logos_ir::Error::InvalidRelSourceProvenance(message)
            if message.contains("source SELECT at byte 11 has no owned logical query-block subtree")
    ));
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_derived_with_switches_to_inner_cte_provenance() {
    let repo = repo_root();
    let temp = temp_dir("derived-with-cte-provenance");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&schema, "create table t(v varchar(9));\n").unwrap();
    fs::write(
        &query,
        "select v \
         from (with x as (\
                 select v from t where cast(v as varchar(5)) = v\
               ) select v from x) s \
         where cast(v as varchar(2)) = v;\n",
    )
    .unwrap();

    let ir = convert_raw_file(run_calcite(&repo, &schema, &query)).unwrap();
    let RelExpr::Project { input, .. } = &ir.queries[0].rel else {
        panic!("expected outer project");
    };
    let RelExpr::Filter {
        predicate: outer,
        input,
        ..
    } = input.as_ref()
    else {
        panic!("expected outer filter");
    };
    let RelExpr::Project { input, .. } = input.as_ref() else {
        panic!("expected derived WITH project");
    };
    let RelExpr::Filter {
        predicate: inner, ..
    } = input.as_ref()
    else {
        panic!("expected inner WITH filter");
    };
    assert!(scalar_contains_annotation(&outer.parsed, "VARCHAR(2)"));
    assert!(!scalar_contains_annotation(&outer.parsed, "VARCHAR(5)"));
    assert!(scalar_contains_annotation(&inner.parsed, "VARCHAR(5)"));
    assert!(!scalar_contains_annotation(&inner.parsed, "VARCHAR(2)"));
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_scalar_minus_is_not_used_as_in_subquery_source() {
    let repo = repo_root();
    let temp = temp_dir("scalar-minus-subquery-source");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&schema, "create table t(a integer);\n").unwrap();
    fs::write(
        &query,
        "select a from t \
         where a - 1 in (\
           with x as (select a from t) select a from x\
         );\n\
         select a from t \
         where a in (select a from t except select a from t);\n",
    )
    .unwrap();

    let raw = run_calcite_json(&repo, &schema, &query);
    let subquery = &raw["queries"][0]["rel"]["inputs"][0]["conditionRex"];
    assert_eq!(subquery["class"].as_str(), Some("RexSubQuery"));
    let source = subquery["subqueryRel"]["sourceSql"]
        .as_str()
        .expect("IN subquery relation source");
    assert!(source.starts_with("WITH "), "{source}");
    assert!(source.contains("SELECT `a`"), "{source}");
    assert!(source.contains("FROM `x`"), "{source}");
    assert!(!source.contains("`a` - 1"), "{source}");

    let set_subquery = &raw["queries"][1]["rel"]["inputs"][0]["conditionRex"];
    assert_eq!(set_subquery["class"].as_str(), Some("RexSubQuery"));
    let set_source = set_subquery["subqueryRel"]["sourceSql"]
        .as_str()
        .expect("EXCEPT subquery relation source");
    assert!(set_source.contains("EXCEPT"), "{set_source}");
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_binds_project_correlation_to_pre_projection_row() {
    let repo = repo_root();
    let temp = temp_dir("project-correlation-input-row");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(
        &schema,
        "create table emp(empno integer, job text, sal integer);\n\
         create table dept(deptno integer, name text);\n",
    )
    .unwrap();
    fs::write(
        &query,
        "select sal, empno not in (\
           select deptno from dept where emp.job = name\
         ) from emp;\n",
    )
    .unwrap();

    let ir = convert_raw_file(run_calcite(&repo, &schema, &query)).unwrap();
    let RelExpr::Project {
        input,
        correlations,
        output,
        ..
    } = &ir.queries[0].rel
    else {
        panic!("expected correlated outer project");
    };
    assert_eq!(output.len(), 2);
    assert_eq!(input.output().len(), 3);
    assert_eq!(correlations.len(), 1);
    assert_eq!(correlations[0].output, input.output());
    assert_eq!(correlations[0].output[1].name, "job");
    assert_eq!(correlations[0].output[1].ty, SqlType::text());
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_cte_body_does_not_see_later_sibling_over_base_relation() {
    let repo = repo_root();
    let temp = temp_dir("cte-later-sibling-visibility");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(
        &schema,
        "create table later(v varchar(9));\ncreate table t(v varchar(9));\n",
    )
    .unwrap();
    fs::write(
        &query,
        "with early as (select v from later),\
              later as (select cast(v as varchar(7)) as v from t)\
         select v from early;\n",
    )
    .unwrap();

    let raw = run_calcite_json(&repo, &schema, &query);
    let child = &raw["queries"][0]["rel"]["inputs"][0];
    assert_eq!(child["type"].as_str(), Some("LogicalTableScan"));
    assert_eq!(
        child["table"]
            .as_array()
            .and_then(|parts| parts.last())
            .and_then(|part| part.as_str()),
        Some("later")
    );
    let child_source = child["sourceSql"]
        .as_str()
        .expect("base-relation source provenance");
    assert!(child_source.contains("FROM `later`"), "{child_source}");
    assert!(!child_source.contains("VARCHAR(7)"), "{child_source}");
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_aligns_rewritten_character_expression_provenance() {
    let repo = repo_root();
    let temp = temp_dir("rewritten-character-expression-provenance");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(
        &schema,
        "create table t(c char(9), v varchar(9), n integer);\n",
    )
    .unwrap();
    fs::write(
        &query,
        "select c from t where c in ('a', 'a') and c not like 'b%';\n\
         select sum(case when c = 'Sunday' then n else 0 end) from t;\n\
         select c from t where cast(c as varchar(1)) = 'Manager';\n\
         select count(*) filter (where c = 'CLERK') from t;\n",
    )
    .unwrap();

    let ir = convert_raw_file(run_calcite(&repo, &schema, &query)).unwrap();
    assert_eq!(ir.queries.len(), 4);
    let predicate = outer_filter_predicate(&ir.queries[2].rel);
    assert!(scalar_contains_annotation(&predicate.parsed, "VARCHAR(1)"));
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_rejects_multiply_referenced_cte_without_shared_query_binding() {
    let repo = repo_root();
    let temp = temp_dir("multiply-referenced-cte-boundary");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&schema, "create table t(c char(9));\n").unwrap();
    fs::write(
        &query,
        "with channels as (select 'store' as channel from t union all select 'catalog' from t)\n\
         select channel from channels;\n",
    )
    .unwrap();
    let single_use = convert_raw_file(run_calcite(&repo, &schema, &query))
        .expect("one lexical CTE reference remains exactly inlineable");
    assert_eq!(single_use.queries.len(), 1);

    fs::write(
        &query,
        "with channels as (select 'store' as channel from t union all select 'catalog' from t)\n\
         select channel from channels union all select channel from channels;\n",
    )
    .unwrap();

    let error = convert_raw_file(run_calcite(&repo, &schema, &query)).unwrap_err();
    assert!(matches!(
        error,
        logos_ir::Error::InvalidRelSourceProvenance(message)
            if message.contains("multiply referenced lexical CTE \"channels\"")
                && message.contains("native shared-query binding")
                && message.contains("independent RelExpr clones would replay")
    ));
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_uses_postgres_sum_integer_result_type() {
    let repo = repo_root();
    let temp = temp_dir("postgres-sum-integer-type");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&schema, "create table t(n integer, flag boolean);\n").unwrap();
    fs::write(
        &query,
        "select sum(n) as direct, \
         sum(case when flag then n else 0 end) as conditional from t;\n",
    )
    .unwrap();

    let raw = run_calcite(&repo, &schema, &query);
    let raw_aggregate = raw.queries[0].rel.as_ref().expect("expected query rel");
    assert_eq!(raw_aggregate.rel_type, "LogicalAggregate");
    assert_eq!(raw_aggregate.row_type.len(), 2);
    assert!(
        raw_aggregate
            .row_type
            .iter()
            .all(|field| field.ty == "BIGINT" && field.nullable)
    );
    assert_eq!(raw_aggregate.agg_call_details.len(), 2);
    assert!(raw_aggregate.agg_call_details.iter().all(|call| {
        call.function.eq_ignore_ascii_case("SUM") && call.ty.as_deref() == Some("BIGINT")
    }));
    let raw_project = raw_aggregate
        .inputs
        .first()
        .expect("SUM(CASE ...) must have an aggregate-input project");
    assert_eq!(raw_project.rel_type, "LogicalProject");
    assert_eq!(raw_project.row_type.len(), 2);
    assert!(
        raw_project
            .row_type
            .iter()
            .all(|field| field.ty == "INTEGER")
    );

    let ir = convert_raw_file(raw).unwrap();
    assert_eq!(ir.queries[0].output().len(), 2);
    assert!(
        ir.queries[0]
            .output()
            .iter()
            .all(|column| column.ty == SqlType::BigInt && column.nullable)
    );
    let RelExpr::Aggregate {
        input,
        agg_calls,
        output,
        ..
    } = &ir.queries[0].rel
    else {
        panic!("expected converted aggregate");
    };
    assert_eq!(output.as_slice(), ir.queries[0].output());
    assert_eq!(agg_calls.len(), 2);
    assert!(
        agg_calls
            .iter()
            .all(|call| call.function.eq_ignore_ascii_case("SUM"))
    );
    let RelExpr::Project {
        output: project_output,
        ..
    } = input.as_ref()
    else {
        panic!("expected aggregate-input project");
    };
    assert!(
        project_output
            .iter()
            .all(|column| column.ty == SqlType::Integer)
    );
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_preserves_proved_nonnull_grouped_postgres_sum() {
    let repo = repo_root();
    let temp = temp_dir("postgres-grouped-nonnull-sum");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&schema, "create table t(k integer, n bigint);\n").unwrap();
    fs::write(&query, "select k, sum(coalesce(n, 0)) from t group by k;\n").unwrap();

    let raw = run_calcite(&repo, &schema, &query);
    let aggregate = first_aggregate(raw.queries[0].rel.as_ref().unwrap());
    assert!(
        aggregate
            .group_sets
            .as_deref()
            .is_some_and(|sets| sets == [vec![0]])
    );
    assert!(
        !aggregate.row_type[1].nullable,
        "Calcite should retain the source COALESCE/nonempty-group proof"
    );
    let mut null_fallback = raw.clone();
    {
        let aggregate = first_aggregate_mut(null_fallback.queries[0].rel.as_mut().unwrap());
        let fallback = &mut aggregate.inputs[0].project_rex[1].operands[2];
        fallback.text = Some("null:NULL".to_owned());
        fallback.literal_type_name = Some("NULL".to_owned());
        fallback.literal_value = Some("null".to_owned());
        fallback.literal_value2 = Some("null".to_owned());
    }
    assert!(convert_raw_file(null_fallback).is_err());

    let mut numeric_fallback = raw.clone();
    {
        let aggregate = first_aggregate_mut(numeric_fallback.queries[0].rel.as_mut().unwrap());
        let fallback = &mut aggregate.inputs[0].project_rex[1].operands[2];
        fallback.ty = Some("DECIMAL".to_owned());
        fallback.full_type = Some("DECIMAL".to_owned());
        fallback.precision = Some(-1);
        fallback.scale = Some(-1);
    }
    assert!(convert_raw_file(numeric_fallback).is_err());

    let mut borrowed_source_role = raw.clone();
    {
        let aggregate = first_aggregate_mut(borrowed_source_role.queries[0].rel.as_mut().unwrap());
        let case = &mut aggregate.inputs[0].project_rex[1];
        let borrowed_node_id = case.operands[1].source_node_id.clone();
        let borrowed_text = case.operands[1].source_text.clone();
        case.operands[2].source_node_id = borrowed_node_id;
        case.operands[2].source_text = borrowed_text;
    }
    assert!(convert_raw_file(borrowed_source_role).is_err());

    let mut wrong_condition_input = raw.clone();
    {
        let aggregate = first_aggregate_mut(wrong_condition_input.queries[0].rel.as_mut().unwrap());
        aggregate.inputs[0].project_rex[1].operands[0].operands[0].index = Some(0);
    }
    assert!(convert_raw_file(wrong_condition_input).is_err());

    let converted = convert_raw_file(raw).expect("proved grouped SUM must convert");
    let (_, output) = first_ir_aggregate(&converted.queries[0].rel);
    assert_eq!(output[1].ty, SqlType::decimal(None, None));
    assert!(!output[1].nullable);

    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_repairs_source_attested_postgres_avg_integer_result_type() {
    let repo = repo_root();
    let temp = temp_dir("postgres-avg-integer-type");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&schema, "create table t(n integer);\n").unwrap();
    fs::write(&query, "select avg(n) from t;\n").unwrap();

    let raw = run_calcite(&repo, &schema, &query);
    let aggregate = raw.queries[0].rel.as_ref().unwrap();
    assert_eq!(
        aggregate.agg_call_details[0].source_sql.as_deref(),
        Some("AVG(`n`)")
    );
    let mut mismatched_call_type = raw.clone();
    first_aggregate_mut(mismatched_call_type.queries[0].rel.as_mut().unwrap()).agg_call_details
        [0]
    .ty = Some("BIGINT".to_owned());
    assert!(matches!(
        convert_raw_file(mismatched_call_type),
        Err(logos_ir::Error::InvalidRelSourceProvenance(_))
    ));

    let mut coherent_wrong_family = raw.clone();
    {
        let aggregate = first_aggregate_mut(coherent_wrong_family.queries[0].rel.as_mut().unwrap());
        let output = &mut aggregate.row_type[0];
        output.ty = "DOUBLE".to_owned();
        output.full_type = Some("DOUBLE".to_owned());
        output.precision = Some(15);
        output.scale = Some(i32::MIN);
        let call = &mut aggregate.agg_call_details[0];
        call.ty = Some(output.ty.clone());
        call.full_type = output.full_type.clone();
        call.precision = output.precision;
        call.scale = output.scale;
        call.charset = output.charset.clone();
        call.type_collation = output.type_collation.clone();
    }
    assert!(matches!(
        convert_raw_file(coherent_wrong_family),
        Err(logos_ir::Error::InvalidRelSourceProvenance(_))
    ));

    let ir = convert_raw_file(raw).unwrap();
    assert_eq!(ir.queries[0].output()[0].ty, SqlType::decimal(None, None));
    assert!(ir.queries[0].output()[0].nullable);
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and frozen benchmark inputs"]
fn calcite_wrapper_applies_postgres_integer_statistical_aggregate_type_family() {
    let repo = repo_root();
    let case = repo.join(
        "benchmarks/core/.generated/sqlsolver/nonwetune-flat/\
         verieql-calcite__calcite-276",
    );
    let raw = run_calcite(&repo, &case.join("schema.sql"), &case.join("sql1.sql"));
    let aggregate = first_aggregate(raw.queries[0].rel.as_ref().unwrap());
    assert!(aggregate.agg_call_details.iter().all(|call| {
        call.ty.as_deref() == Some("INTEGER") && call.full_type.as_deref() == Some("INTEGER")
    }));

    let converted = convert_raw_file(raw).expect("PostgreSQL statistical type family");
    let (_, output) = first_ir_aggregate(&converted.queries[0].rel);
    assert_eq!(output.len(), 6);
    assert!(
        output[1..]
            .iter()
            .all(|column| column.ty == SqlType::decimal(None, None) && column.nullable)
    );
}

#[test]
#[ignore = "requires the Java Calcite wrapper and frozen benchmark inputs"]
fn calcite_wrapper_closes_inlined_cte_definitions_under_aggregate_arguments() {
    fn inlined_results_project_mut(rel: &mut CalciteRel) -> Option<&mut CalciteRel> {
        let is_results_project = rel.rel_type == "LogicalProject"
            && rel.source_input_cte_uses.iter().flatten().any(|use_| {
                use_.definition_name_text.eq_ignore_ascii_case("results")
                    && use_
                        .definition_query_text
                        .contains("CAST(cs_quantity AS DECIMAL(12, 2)) AS agg1")
            });
        if is_results_project {
            return Some(rel);
        }
        rel.inputs.iter_mut().find_map(inlined_results_project_mut)
    }

    with_large_calcite_stack(|| {
        let repo = repo_root();
        let case = repo.join(
            "benchmarks/core/.generated/sqlsolver/nonwetune-flat/\
             tpcds-variants__query018",
        );
        let raw = run_calcite(&repo, &case.join("schema.sql"), &case.join("sql2.sql"));
        convert_raw_file(raw.clone()).expect("exact inlined CTE definitions must convert");

        let mut swapped_definitions = raw.clone();
        {
            let project =
                inlined_results_project_mut(swapped_definitions.queries[0].rel.as_mut().unwrap())
                    .expect("inlined results Project");
            let quantity = project
                .project_rex
                .iter()
                .position(|rex| {
                    rex.source_text.as_deref() == Some("CAST(cs_quantity AS DECIMAL(12, 2))")
                })
                .expect("quantity definition");
            let list_price = project
                .project_rex
                .iter()
                .position(|rex| {
                    rex.source_text.as_deref() == Some("CAST(cs_list_price AS DECIMAL(12, 2))")
                })
                .expect("list-price definition");
            project.project_rex.swap(quantity, list_price);
        }
        assert!(convert_raw_file(swapped_definitions).is_err());

        let mut wrong_same_typed_input = raw;
        {
            let project = inlined_results_project_mut(
                wrong_same_typed_input.queries[0].rel.as_mut().unwrap(),
            )
            .expect("inlined results Project");
            let quantity = project
                .project_rex
                .iter_mut()
                .find(|rex| {
                    rex.source_text.as_deref() == Some("CAST(cs_quantity AS DECIMAL(12, 2))")
                })
                .expect("quantity definition");
            // c_birth_year is also nullable INTEGER, so only exact source/name
            // lineage—not a convenient type mismatch—can reject this mutation.
            quantity.operands[0].index = Some(65);
        }
        assert!(convert_raw_file(wrong_same_typed_input).is_err());
    });
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_retries_postgres_safe_reserved_aliases() {
    let repo = repo_root();
    let temp = temp_dir("postgres-safe-reserved-aliases");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&schema, "create table t(n integer);\n").unwrap();
    fs::write(
        &query,
        "with q as (select sum(n) as returns from t) select returns from q;\n\
         select 1 as one from t;\n",
    )
    .unwrap();

    let raw = run_calcite(&repo, &schema, &query);
    assert_eq!(raw.queries.len(), 2);
    assert_eq!(
        raw.queries[0].sql,
        "with q as (select sum(n) as returns from t) select returns from q"
    );
    assert_eq!(raw.queries[1].sql, "select 1 as one from t");
    let ir = convert_raw_file(raw).unwrap();
    assert_eq!(ir.queries.len(), 2);
    assert_eq!(
        ir.queries[0].output()[0].name.to_ascii_lowercase(),
        "returns"
    );
    assert_eq!(ir.queries[0].output()[0].ty, SqlType::BigInt);
    assert_eq!(ir.queries[1].output()[0].name.to_ascii_lowercase(), "one");
    assert_eq!(ir.queries[1].output()[0].ty, SqlType::Integer);
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_maps_private_parser_rewrites_to_exact_original_spans() {
    fn one_line_span(statement: &str, start: usize, text: &str) -> String {
        let start_column = statement[..start].chars().count() + 1;
        let end_column = start_column + text.chars().count() - 1;
        format!("1:{start_column}-1:{end_column}")
    }

    let repo = repo_root();
    let temp = temp_dir("postgres-private-parser-source-map");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(
        &schema,
        "create table t(returns integer, one integer, tail integer);\n",
    )
    .unwrap();
    // The parser copy replaces the vertical tab, reports tabs and the astral
    // character in Calcite's UTF-16 reader coordinates, and inserts eight
    // quotes around four reserved-word occurrences. Exact provenance must
    // still use the original statement's Unicode-scalar positions and bytes.
    let statement = "/* 😀 */ SELECT\u{000b}returns,\tone,\treturns,\tone,\ttail\r\nFROM t";
    fs::write(&query, format!("{statement};\r\n")).unwrap();

    let raw = run_calcite(&repo, &schema, &query);
    assert_eq!(raw.queries[0].sql, statement);
    assert!(raw.queries[0].error.is_none(), "{:#?}", raw.queries[0]);
    let project = raw.queries[0].rel.as_ref().expect("mapped project");
    assert_eq!(project.rel_type, "LogicalProject");
    assert_eq!(
        project.source_text.as_deref(),
        Some(&statement[statement.find("SELECT").unwrap()..]),
        "the multiline relational span must preserve CRLF and vertical-tab bytes"
    );
    assert_eq!(project.project_rex.len(), 5);

    let expected_text = ["returns", "one", "returns", "one", "tail"];
    let mut search_from = 0;
    let mut expected_ids = Vec::new();
    for (rex, expected) in project.project_rex.iter().zip(expected_text) {
        let relative = statement[search_from..]
            .find(expected)
            .unwrap_or_else(|| panic!("missing {expected:?} after byte {search_from}"));
        let start = search_from + relative;
        expected_ids.push(one_line_span(statement, start, expected));
        assert_eq!(rex.source_text.as_deref(), Some(expected));
        assert_eq!(
            rex.source_identifier_quoted,
            [false],
            "private parser quotes must not rewrite original PostgreSQL quotedness"
        );
        assert_eq!(
            rex.source_node_id.as_deref(),
            expected_ids.last().map(String::as_str)
        );
        search_from = start + expected.len();
    }
    assert_eq!(
        expected_ids
            .iter()
            .collect::<std::collections::HashSet<_>>()
            .len(),
        expected_ids.len(),
        "repeated identifiers must retain distinct source spans"
    );
    convert_raw_file(raw.clone()).expect("convert exact mapped parser-copy spans");

    let mut forged_private_quote = raw.clone();
    forged_private_quote.queries[0]
        .rel
        .as_mut()
        .unwrap()
        .project_rex[0]
        .source_identifier_quoted[0] = true;
    assert!(
        convert_raw_file(forged_private_quote).is_err(),
        "a private parser quote must not become original PostgreSQL quotedness"
    );

    let mut drifted = raw;
    drifted.queries[0].rel.as_mut().unwrap().project_rex[4].source_node_id =
        Some(expected_ids[0].clone());
    assert!(
        convert_raw_file(drifted).is_err(),
        "an exact-text leaf must not borrow an unrelated mapped span"
    );

    fs::write(&query, "select \"returns\" from t;\n").unwrap();
    let explicitly_quoted = run_calcite(&repo, &schema, &query);
    let quoted_rex = &explicitly_quoted.queries[0]
        .rel
        .as_ref()
        .unwrap()
        .project_rex[0];
    assert_eq!(quoted_rex.source_text.as_deref(), Some("\"returns\""));
    assert_eq!(quoted_rex.source_identifier_names, ["returns"]);
    assert_eq!(quoted_rex.source_identifier_quoted, [true]);
    let mut forged_unquoted = explicitly_quoted.clone();
    forged_unquoted.queries[0].rel.as_mut().unwrap().project_rex[0].source_identifier_quoted[0] =
        false;
    assert!(
        convert_raw_file(forged_unquoted).is_err(),
        "an original quoted identifier must not be downgraded to an unquoted name"
    );
    convert_raw_file(explicitly_quoted).expect("convert original quoted identifier metadata");

    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and frozen benchmark inputs"]
fn calcite_wrapper_maps_all_tpcds_q005_q080_reserved_identifier_retries() {
    with_large_calcite_stack(|| {
        let repo = repo_root();
        for query_number in ["005", "080"] {
            let case = repo.join(format!(
                "benchmarks/core/.generated/sqlsolver/nonwetune-flat/\
                 tpcds-variants__query{query_number}"
            ));
            for sql in ["sql1.sql", "sql2.sql"] {
                let raw = run_calcite(&repo, &case.join("schema.sql"), &case.join(sql));
                assert!(
                    raw.queries[0].error.is_none(),
                    "Q{query_number}/{sql}: {:#?}",
                    raw.queries[0]
                );
                convert_raw_file(raw).unwrap_or_else(|error| {
                    panic!("Q{query_number}/{sql}: mapped conversion failed: {error}")
                });
            }
        }
    });
}

#[test]
#[ignore = "requires the Java Calcite wrapper and frozen benchmark inputs"]
fn calcite_wrapper_q080_order_names_and_indexes_are_exact_source_bound() {
    fn sort_mut(rel: &mut CalciteRel) -> Option<&mut CalciteRel> {
        if rel.rel_type == "LogicalSort" {
            return Some(rel);
        }
        rel.inputs.iter_mut().find_map(sort_mut)
    }

    fn later_item_use(rel: &CalciteRel) -> Option<&logos_ir::calcite::CalciteSourceCteUse> {
        rel.source_input_cte_uses
            .iter()
            .flatten()
            .chain(
                rel.source_join
                    .iter()
                    .flat_map(|join| join.left_cte_use.iter().chain(join.right_cte_use.iter())),
            )
            .find(|use_| use_.reference_scope_kind == "LATER_ITEM")
            .or_else(|| rel.inputs.iter().find_map(later_item_use))
    }

    with_large_calcite_stack(|| {
        let repo = repo_root();
        let case = repo
            .join("benchmarks/core/.generated/sqlsolver/nonwetune-flat/tpcds-variants__query080");
        let raw = run_calcite(&repo, &case.join("schema.sql"), &case.join("sql2.sql"));
        let project = &raw.queries[0].rel.as_ref().unwrap().inputs[0];
        assert_eq!(
            project.project_rex[3].source_text.as_deref(),
            Some("returns")
        );
        assert_eq!(project.project_rex[3].source_identifier_quoted, [false]);
        let later = later_item_use(raw.queries[0].rel.as_ref().unwrap())
            .expect("Q080 ordered CTE dependency");
        assert!(later.definition_item_text.contains(" AS ("));
        assert!(
            !later
                .definition_list_text
                .to_ascii_lowercase()
                .starts_with("with")
        );
        assert!(
            later
                .definition_with_text
                .to_ascii_lowercase()
                .starts_with("with ")
        );
        assert!(later.reference_scope_text.contains(" AS ("));
        assert!(later.reference_scope_text.contains(&later.reference_text));
        convert_raw_file(raw.clone()).expect("Q080 exact set-output ORDER BY");

        let mut name_drift = raw.clone();
        let sort = sort_mut(name_drift.queries[0].rel.as_mut().unwrap()).unwrap();
        sort.row_type[0].name = "forged_channel".to_owned();
        sort.inputs[0].row_type[0].name = "forged_channel".to_owned();
        assert!(
            convert_raw_file(name_drift).is_err(),
            "Q080 accepted a coherent generated set-output name mutation"
        );

        let mut index_drift = raw;
        let sort = sort_mut(index_drift.queries[0].rel.as_mut().unwrap()).unwrap();
        sort.collation[0].field_index = 1;
        assert!(
            convert_raw_file(index_drift).is_err(),
            "Q080 accepted a generated Sort-index mutation"
        );
    });
}

#[test]
#[ignore = "requires the Java Calcite wrapper and frozen benchmark inputs"]
fn calcite_wrapper_emits_only_exact_nonrecursive_lexical_cte_extents() {
    fn collect_uses<'a>(
        rel: &'a CalciteRel,
        uses: &mut Vec<&'a logos_ir::calcite::CalciteSourceCteUse>,
    ) {
        uses.extend(rel.source_input_cte_uses.iter().flatten());
        if let Some(join) = rel.source_join.as_ref() {
            uses.extend(join.left_cte_use.iter());
            uses.extend(join.right_cte_use.iter());
        }
        for input in &rel.inputs {
            collect_uses(input, uses);
        }
    }

    fn corrupt_web_cte(rel: &mut CalciteRel, scope: bool) -> bool {
        for use_ in rel.source_input_cte_uses.iter_mut().flatten() {
            if use_.definition_name_text.eq_ignore_ascii_case("web_v1") {
                if scope {
                    use_.reference_scope_node_id = use_.definition_name_node_id.clone();
                    use_.reference_scope_text = use_.definition_name_text.clone();
                } else {
                    use_.definition_item_node_id = use_.definition_name_node_id.clone();
                    use_.definition_item_text = use_.definition_name_text.clone();
                }
                return true;
            }
        }
        if let Some(join) = rel.source_join.as_mut() {
            for use_ in [&mut join.left_cte_use, &mut join.right_cte_use]
                .into_iter()
                .filter_map(Option::as_mut)
            {
                if use_.definition_name_text.eq_ignore_ascii_case("web_v1") {
                    if scope {
                        use_.reference_scope_node_id = use_.definition_name_node_id.clone();
                        use_.reference_scope_text = use_.definition_name_text.clone();
                    } else {
                        use_.definition_item_node_id = use_.definition_name_node_id.clone();
                        use_.definition_item_text = use_.definition_name_text.clone();
                    }
                    return true;
                }
            }
        }
        rel.inputs
            .iter_mut()
            .any(|input| corrupt_web_cte(input, scope))
    }

    with_large_calcite_stack(|| {
        let repo = repo_root();
        let case = repo
            .join("benchmarks/core/.generated/sqlsolver/nonwetune-flat/tpcds-variants__query051");
        let raw = run_calcite_postgres_c(&repo, &case.join("schema.sql"), &case.join("sql1.sql"));
        assert!(raw.queries[0].error.is_none(), "{:#?}", raw.queries[0]);
        let mut uses = Vec::new();
        collect_uses(raw.queries[0].rel.as_ref().unwrap(), &mut uses);
        let web = uses
            .iter()
            .copied()
            .find(|use_| {
                use_.reference_scope_kind == "BODY"
                    && use_.definition_name_text.eq_ignore_ascii_case("web_v1")
            })
            .expect("web_v1 CTE referenced from the WITH body");
        assert!(web.definition_item_text.starts_with("web_v1 AS ("));
        assert!(web.definition_item_text.ends_with(')'));
        assert!(web.definition_list_text.starts_with("web_v1 AS ("));
        assert!(
            !web.definition_list_text
                .to_ascii_lowercase()
                .starts_with("with")
        );
        assert!(web.definition_list_text.contains("), store_v1 AS ("));
        assert!(web.definition_with_text.starts_with("WITH web_v1 AS ("));
        assert!(
            web.definition_with_text
                .ends_with(&web.definition_body_text)
        );
        assert_eq!(web.reference_scope_text, web.definition_body_text);
        convert_raw_file(raw.clone()).expect("pristine q051 exact CTE extents must convert");

        let mut truncated_item = raw.clone();
        assert!(corrupt_web_cte(
            truncated_item.queries[0].rel.as_mut().unwrap(),
            false
        ));
        assert!(matches!(
            convert_raw_file(truncated_item),
            Err(logos_ir::Error::InvalidRelSourceProvenance(_))
        ));

        let mut truncated_scope = raw;
        assert!(corrupt_web_cte(
            truncated_scope.queries[0].rel.as_mut().unwrap(),
            true
        ));
        assert!(matches!(
            convert_raw_file(truncated_scope),
            Err(logos_ir::Error::InvalidRelSourceProvenance(_))
        ));
    });
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_closes_unaliased_derived_outputs_before_outer_window() {
    fn composed_project(rel: &CalciteRel) -> Option<&CalciteRel> {
        let is_composed = rel.rel_type == "LogicalProject"
            && rel.project_rex.len() == 3
            && rel.project_rex[..2].iter().all(|rex| {
                rex.source_expansion.as_ref().is_some_and(|expansion| {
                    matches!(
                        expansion.kind.as_str(),
                        "DIRECT_DERIVED_OUTPUT_ALIAS" | "DIRECT_DERIVED_PASSTHROUGH"
                    )
                })
            })
            && rel.project_rex[2]
                .source_window_function
                .as_deref()
                .is_some_and(|function| function.eq_ignore_ascii_case("row_number"));
        if is_composed {
            return Some(rel);
        }
        rel.inputs.iter().find_map(composed_project)
    }

    fn composed_project_mut(rel: &mut CalciteRel) -> Option<&mut CalciteRel> {
        let is_composed = rel.rel_type == "LogicalProject"
            && rel.project_rex.len() == 3
            && rel.project_rex[..2]
                .iter()
                .all(|rex| rex.source_expansion.is_some())
            && rel.project_rex[2]
                .source_window_function
                .as_deref()
                .is_some_and(|function| function.eq_ignore_ascii_case("row_number"));
        if is_composed {
            return Some(rel);
        }
        rel.inputs.iter_mut().find_map(composed_project_mut)
    }

    with_large_calcite_stack(|| {
        let repo = repo_root();
        let temp = temp_dir("unaliased-derived-outer-window");
        let schema = temp.join("schema.sql");
        let query = temp.join("query.sql");
        fs::write(&schema, "create table t(a integer, b integer);\n").unwrap();
        fs::write(
            &query,
            "select x, y, row_number() over (order by x) as rn \
             from (select a + b as x, a as y from t);\n",
        )
        .unwrap();

        let pristine = run_calcite_postgres_c(&repo, &schema, &query);
        let project = composed_project(pristine.queries[0].rel.as_ref().unwrap())
            .expect("outer Project composed directly over an unaliased derived SELECT");
        assert_eq!(project.row_type[0].ty, project.row_type[1].ty);
        for rex in &project.project_rex[..2] {
            let expansion = rex.source_expansion.as_ref().unwrap();
            assert!(
                expansion
                    .outer_from_text
                    .strip_prefix(&expansion.inner_select_text)
                    .is_some_and(|suffix| suffix.trim() == ")"),
                "the unaliased relation extent must be exactly the inner SELECT plus its closing parenthesis"
            );
        }
        convert_raw_file(pristine.clone())
            .expect("exact unaliased derived outputs followed by ROW_NUMBER must convert");

        let mut reordered = pristine.clone();
        composed_project_mut(reordered.queries[0].rel.as_mut().unwrap())
            .unwrap()
            .project_rex
            .swap(0, 1);
        assert!(
            convert_raw_file(reordered).is_err(),
            "same-typed derived outputs cannot exchange their exact outer SELECT roles"
        );

        let mut missing = pristine;
        composed_project_mut(missing.queries[0].rel.as_mut().unwrap())
            .unwrap()
            .project_rex[0]
            .source_expansion = None;
        assert!(
            convert_raw_file(missing).is_err(),
            "every collapsed inner output must retain its exact declarative expansion"
        );

        fs::remove_dir_all(&temp).unwrap();
    });
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_binds_explicit_cte_names_by_exact_definition_position() {
    let repo = repo_root();
    let temp = temp_dir("exact-cte-public-output-position");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&schema, "create table t(a integer, b integer);\n").unwrap();
    fs::write(
        &query,
        "with x(k, total) as (select a, max(b) from t group by a) select total from x;\n",
    )
    .unwrap();

    let raw = run_calcite(&repo, &schema, &query);
    convert_raw_file(raw.clone()).expect("convert exact column-list CTE namespace");

    let mut wrong_declared_position = raw;
    let root = wrong_declared_position.queries[0].rel.as_mut().unwrap();
    let project = if root.rel_type == "LogicalProject" {
        root
    } else {
        root.inputs
            .iter_mut()
            .find(|input| input.rel_type == "LogicalProject")
            .expect("explicit-column-list consumer Project")
    };
    let total = project
        .project_rex
        .iter_mut()
        .find(|rex| {
            rex.source_expansion.as_ref().is_some_and(|expansion| {
                expansion.kind == "DIRECT_CTE_EXPLICIT_COLUMN"
                    && expansion.reference_text == "total"
                    && expansion.public_output_index == Some(1)
            })
        })
        .expect("total CTE output reference");
    total.index = Some(0);
    total.text = Some("$0".to_owned());
    assert!(
        convert_raw_file(wrong_declared_position).is_err(),
        "an explicit CTE output name bound to the wrong generated ordinal"
    );

    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_preserves_postgres_quoted_identifier_identity() {
    let repo = repo_root();
    let temp = temp_dir("postgres-quoted-identifiers");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(
        &schema,
        "create table foo(a integer); create table \"Foo Bar\"(\"A B\" integer);\n",
    )
    .unwrap();

    fs::write(&query, "select * from \"Foo\";\n").unwrap();
    let raw = run_calcite(&repo, &schema, &query);
    let error = raw.queries[0]
        .error
        .as_deref()
        .expect("quoted Foo must not resolve the unquoted PostgreSQL name foo");
    assert!(error.contains("not found"), "{error}");

    fs::write(&query, "select \"A B\" from \"Foo Bar\";\n").unwrap();
    let ir = convert_raw_file(run_calcite(&repo, &schema, &query)).unwrap();
    assert_eq!(ir.schema.tables[0].name, "foo");
    assert_eq!(ir.schema.tables[1].name, "Foo Bar");
    assert_eq!(ir.schema.tables[1].columns[0].name, "A B");
    assert_eq!(ir.queries[0].output()[0].name, "A B");
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_rejects_duplicate_postgres_relation_identity() {
    let repo = repo_root();
    let temp = temp_dir("postgres-duplicate-identifiers");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&query, "select 1;\n").unwrap();

    for schema_sql in [
        "create table Foo(a integer); create table foo(b integer);\n",
        "create table foo(a integer); create table \"foo\"(b integer);\n",
    ] {
        fs::write(&schema, schema_sql).unwrap();
        let output = Command::new(repo.join("scripts/calcite-ir"))
            .arg("--schema")
            .arg(&schema)
            .arg("--sql")
            .arg(&query)
            .output()
            .unwrap();
        assert!(!output.status.success());
        let message = format!(
            "{}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(
            message.contains("duplicate PostgreSQL relation identity"),
            "{message}"
        );
    }

    fs::write(
        &schema,
        "create table foo(a integer); create table \"Foo\"(b integer);\n",
    )
    .unwrap();
    let ir = convert_raw_file(run_calcite(&repo, &schema, &query)).unwrap();
    assert_eq!(ir.schema.tables[0].name, "foo");
    assert_eq!(ir.schema.tables[1].name, "Foo");
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_preserves_distinct_on_parse_exception() {
    let repo = repo_root();
    let temp = temp_dir("distinct-on-exception");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&schema, "create table t(id integer);\n").unwrap();
    fs::write(
        &query,
        "select * from (select distinct on (id) id from t) as q;\n",
    )
    .unwrap();

    let raw = run_calcite(&repo, &schema, &query);
    let error = raw.queries[0]
        .error
        .as_deref()
        .expect("DISTINCT ON must retain the Calcite parse exception");
    assert!(error.contains("SqlParseException"), "{error}");
    assert!(
        error.contains("Encountered \"on\"") || error.contains("keyword 'ON'"),
        "{error}"
    );
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_splits_only_postgres_top_level_semicolons() {
    let repo = repo_root();
    let temp = temp_dir("postgres-statement-splitter");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&schema, "create table t(id integer);\n").unwrap();
    fs::write(
        &query,
        "select ';' as literal;\n\
         -- ; select 999\n\
         /* ordinary block ; inner text ; end */ select 2;\n\
         -- comment-only ;\n\
         ;\n\
         select $tag$not;split$tag$;\n\
         select 4;\n",
    )
    .unwrap();

    let raw = run_calcite(&repo, &schema, &query);
    assert_eq!(raw.queries.len(), 4);
    assert_eq!(raw.queries[0].sql, "select ';' as literal");
    assert!(raw.queries[1].sql.ends_with("select 2"));
    assert!(raw.queries[1].sql.contains("select 999"));
    assert_eq!(raw.queries[2].sql, "select $tag$not;split$tag$");
    assert_eq!(raw.queries[3].sql, "select 4");
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_rejects_nested_postgres_query_block_comments_before_calcite() {
    let repo = repo_root();
    let temp = temp_dir("postgres-nested-query-block-comment");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&schema, "CREATE TABLE t(a int);\n").unwrap();
    fs::write(
        &query,
        "SELECT\u{000b}1 /* outer /* inner */ + 1 -- outer */;",
    )
    .unwrap();

    let diagnostics = run_calcite_failure(&repo, &schema, &query);
    assert!(
        diagnostics.contains(
            "nested PostgreSQL block comments are not supported by the Calcite query frontend"
        ),
        "audit counterexample was not rejected before Calcite:\n{diagnostics}"
    );
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_nested_comment_guard_ignores_protected_delimiter_text() {
    let repo = repo_root();
    let temp = temp_dir("postgres-protected-nested-comment-delimiters");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    let protected_name = "/* outer /* inner */";
    fs::write(
        &schema,
        format!("CREATE TABLE t(\"{protected_name}\" int);\n"),
    )
    .unwrap();
    fs::write(
        &query,
        format!(
            "SELECT 'prefix'' /* outer /* inner */ suffix' AS ordinary;\n\
             SELECT E'prefix\\' /* outer /* inner */ suffix' AS escaped;\n\
             SELECT \"{protected_name}\" FROM t;\n\
             SELECT $tag$/* outer /* inner */$tag$;\n\
             -- /* outer /* inner */ protected by line comment\n\
             SELECT 1;\n\
             SELECT `/* outer /* inner */`;\n\
             SELECT [/* outer /* inner */];\n\
             SELECT 2 /* one ordinary block comment */;\n"
        ),
    )
    .unwrap();

    let raw = run_calcite(&repo, &schema, &query);
    assert_eq!(raw.queries.len(), 8);
    for index in [0, 2, 4, 7] {
        assert!(
            raw.queries[index].error.is_none() && raw.queries[index].rel.is_some(),
            "protected query {index}: {:#?}",
            raw.queries[index]
        );
    }
    assert_eq!(
        raw.queries[2].rel.as_ref().unwrap().row_type[0].name,
        protected_name
    );
    assert!(raw.queries.iter().all(|query| {
        query.sql.contains("/* outer /* inner */") || query.sql.contains("SELECT 2")
    }));
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_rejects_non_postgres_sql_text_characters_before_tokenization() {
    let repo = repo_root();
    let temp = temp_dir("postgres-sql-text-characters");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&query, "SELECT 1;\n").unwrap();

    for (label, schema_sql, expected) in [
        (
            "em-space-between-column-and-type",
            "CREATE TABLE t(a\u{2003}int);",
            "U+2003",
        ),
        (
            "en-space-between-keywords",
            "CREATE\u{2002}TABLE t(a int);",
            "U+2002",
        ),
        (
            "ogham-space-before-relation",
            "CREATE TABLE\u{1680}t(a int);",
            "U+1680",
        ),
        (
            "line-separator-after-entry",
            "CREATE TABLE t(a int\u{2028});",
            "U+2028",
        ),
        (
            "no-break-space-before-type",
            "CREATE TABLE t(a\u{00a0}int);",
            "U+00A0",
        ),
        (
            "nul-at-entry-start",
            "CREATE TABLE t(\0a int);",
            "must not contain NUL",
        ),
        (
            "control-0001-at-entry-start",
            "CREATE TABLE t(\u{0001}a int);",
            "U+0001",
        ),
        (
            "control-001c-at-entry-start",
            "CREATE TABLE t(\u{001c}a int);",
            "U+001C",
        ),
        (
            "control-001f-at-entry-end",
            "CREATE TABLE t(a int\u{001f});",
            "U+001F",
        ),
        (
            "c1-control-inside-quoted-identifier",
            "CREATE TABLE \"a\u{0085}b\"(a int);",
            "U+0085",
        ),
        (
            "format-inside-quoted-identifier",
            "CREATE TABLE \"a\u{200b}b\"(a int);",
            "U+200B",
        ),
        (
            "format-inside-comment",
            "-- hidden \u{feff}\nCREATE TABLE t(a int);",
            "U+FEFF",
        ),
    ] {
        fs::write(&schema, schema_sql).unwrap();
        let diagnostics = run_calcite_failure(&repo, &schema, &query);
        assert!(
            diagnostics.contains("PostgreSQL schema SQL text") && diagnostics.contains(expected),
            "{label}: expected {expected:?}\noutput:\n{diagnostics}"
        );
    }

    fs::write(&schema, "CREATE TABLE t(a int);\n").unwrap();
    for (label, query_sql, expected) in [
        ("em-space-only-statement", "\u{2003};", "U+2003"),
        ("c0-only-statement", "\u{0001};", "U+0001"),
        ("em-space-inside-select", "SELECT\u{2003}1;", "U+2003"),
        (
            "nul-inside-line-comment",
            "-- hidden \0\nSELECT 1;",
            "must not contain NUL",
        ),
        ("c1-control-inside-string", "SELECT 'a\u{0085}b';", "U+0085"),
        (
            "format-inside-block-comment",
            "/* hidden \u{2060} */ SELECT 1;",
            "U+2060",
        ),
    ] {
        fs::write(&query, query_sql).unwrap();
        let diagnostics = run_calcite_failure(&repo, &schema, &query);
        assert!(
            diagnostics.contains("PostgreSQL query SQL text") && diagnostics.contains(expected),
            "{label}: expected {expected:?}\noutput:\n{diagnostics}"
        );
    }

    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_accepts_exact_postgres_sql_whitespace_and_quoted_unicode_letters() {
    let repo = repo_root();
    let temp = temp_dir("postgres-six-sql-whitespace-characters");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");

    for (label, whitespace) in [
        ("space", ' '),
        ("tab", '\t'),
        ("line-feed", '\n'),
        ("carriage-return", '\r'),
        ("form-feed", '\u{000c}'),
        ("vertical-tab", '\u{000b}'),
    ] {
        fs::write(
            &schema,
            format!(
                "CREATE{whitespace}TABLE{whitespace}\"表\"{whitespace}(\
                 {whitespace}\"列\"{whitespace}INTEGER{whitespace}){whitespace};{whitespace}"
            ),
        )
        .unwrap();
        fs::write(
            &query,
            format!(
                "{whitespace}SELECT{whitespace}\"列\"{whitespace}FROM\
                 {whitespace}\"表\"{whitespace};{whitespace}"
            ),
        )
        .unwrap();

        let raw = run_calcite(&repo, &schema, &query);
        assert_eq!(raw.schema.len(), 1, "{label}");
        assert_eq!(raw.schema[0].name, "表", "{label}");
        assert_eq!(raw.schema[0].columns[0].name, "列", "{label}");
        assert_eq!(raw.queries.len(), 1, "{label}");
        assert!(
            raw.queries[0].sql.contains(whitespace),
            "{label}: original PostgreSQL whitespace must remain in JSON"
        );
        assert!(
            raw.queries[0].error.is_none(),
            "{label}: {:#?}",
            raw.queries[0]
        );
        assert!(raw.queries[0].rel.is_some(), "{label}");
        let project = raw.queries[0].rel.as_ref().unwrap();
        assert_eq!(project.project_rex[0].source_identifier_quoted, [true]);
        if label == "carriage-return" {
            assert_eq!(
                project.project_rex[0].source_node_id.as_deref(),
                Some("1:8-1:10"),
                "lone CR is a Calcite line break but remains one original-coordinate scalar"
            );
            assert_eq!(
                project.inputs[0]
                    .source_table
                    .as_ref()
                    .unwrap()
                    .table_node_id,
                "1:17-1:19"
            );
        }
        convert_raw_file(raw).unwrap_or_else(|error| {
            panic!("{label}: exact quoted-Unicode conversion failed: {error}")
        });
    }

    fs::write(
        &schema,
        "CREATE\r\nTABLE\r\n\"表\"\r\n(\"列\"\r\nINTEGER);\r\n",
    )
    .unwrap();
    fs::write(&query, "SELECT\r\n\"列\"\r\nFROM\r\n\"表\";\r\n").unwrap();
    let crlf = run_calcite(&repo, &schema, &query);
    assert!(crlf.queries[0].error.is_none(), "{:#?}", crlf.queries[0]);
    let project = crlf.queries[0].rel.as_ref().unwrap();
    assert_eq!(
        project.project_rex[0].source_node_id.as_deref(),
        Some("2:1-2:3")
    );
    assert_eq!(project.project_rex[0].source_identifier_quoted, [true]);
    assert_eq!(
        project.inputs[0]
            .source_table
            .as_ref()
            .unwrap()
            .table_node_id,
        "4:1-4:3",
        "CRLF must advance exactly one Calcite parser line"
    );
    convert_raw_file(crlf).expect("convert exact CRLF quoted-Unicode source spans");

    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_preserves_protected_vertical_tab_content() {
    let repo = repo_root();
    let temp = temp_dir("postgres-protected-vertical-tab");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    let table_name = "表\u{000b}名";
    let column_name = "列\u{000b}名";
    let literal = "x\u{000b}y";
    fs::write(
        &schema,
        format!("CREATE TABLE \"{table_name}\"(\"{column_name}\" TEXT);\n"),
    )
    .unwrap();
    let statement = format!(
        "-- line\u{000b}comment\nSELECT \"{column_name}\", '{literal}' AS payload \
         FROM \"{table_name}\" /* block\u{000b}comment */"
    );
    fs::write(&query, format!("{statement};\n")).unwrap();

    let raw = run_calcite(&repo, &schema, &query);
    assert_eq!(raw.schema[0].name, table_name);
    assert_eq!(raw.schema[0].columns[0].name, column_name);
    assert_eq!(raw.queries[0].sql, statement);
    assert!(raw.queries[0].error.is_none(), "{:#?}", raw.queries[0]);
    let rel = raw.queries[0].rel.as_ref().expect("protected-VT relation");
    assert_eq!(rel.row_type[0].name, column_name);
    assert_eq!(rel.project_rex[0].source_sql.as_deref(), Some(column_name));
    assert_eq!(
        rel.project_rex[1].source_sql.as_deref(),
        Some(format!("'{literal}'").as_str())
    );
    assert_eq!(
        rel.project_rex[1].literal_value_as_string.as_deref(),
        Some(literal)
    );

    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_distinguishes_where_and_having_provenance() {
    let repo = repo_root();
    let temp = temp_dir("where-having-provenance");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(
        &schema,
        "create table t(c char(10), n integer, v integer);\n",
    )
    .unwrap();
    fs::write(
        &query,
        "select n, sum(v) from t where c = 'outer' group by n \
         having sum(v) > (select sum(v) from t where c = 'inner');\n",
    )
    .unwrap();

    let raw = run_calcite(&repo, &schema, &query);
    let having = raw.queries[0].rel.as_ref().expect("rel");
    assert_eq!(having.source_clause.as_deref(), Some("HAVING"));
    assert!(
        having.source_where.is_none(),
        "HAVING scalar provenance must not carry WHERE clause ownership"
    );
    let native = having
        .source_native_having
        .as_ref()
        .expect("aggregate/subquery HAVING must have exact native attestation");
    assert_eq!(native.kind, "DECLARATIVE_HAVING");
    assert_eq!(native.aggregate_output_arity, 2);
    assert_eq!(native.aggregate_call_count, 1);
    assert_eq!(native.operand_bindings.len(), 1);
    assert_eq!(native.operand_bindings[0].path, "$.0");
    assert_eq!(native.operand_bindings[0].aggregate_output_index, 1);
    let condition = having.condition_rex.as_ref().expect("HAVING Rex");
    let aggregate_operand = &condition.operands[0];
    assert_eq!(
        native.source_condition_sql,
        condition.source_sql.as_deref().unwrap()
    );
    assert_eq!(
        native.generated_condition_sql,
        condition.text.as_deref().unwrap()
    );
    assert_eq!(
        native.operand_bindings[0].source_sql,
        aggregate_operand.source_sql.as_deref().unwrap()
    );
    assert_eq!(
        native.operand_bindings[0].source_kind,
        aggregate_operand.source_kind.as_deref().unwrap()
    );
    assert_eq!(
        native.operand_bindings[0].source_operator.as_deref(),
        aggregate_operand.source_operator.as_deref()
    );
    assert_eq!(
        having.source_query_block_id,
        having.inputs[0].source_query_block_id
    );
    let aggregate_input_project = &having.inputs[0].inputs[0];
    let where_filter = &aggregate_input_project.inputs[0];
    assert_eq!(where_filter.source_clause.as_deref(), Some("WHERE"));
    let source_where = where_filter
        .source_where
        .as_ref()
        .expect("direct outer WHERE must carry exact operator-local ownership");
    assert_eq!(source_where.kind, "WHERE");
    assert_eq!(
        source_where.query_block_id,
        having.source_query_block_id.as_deref().unwrap()
    );
    assert_eq!(
        source_where.source_condition_sql,
        where_filter
            .condition_rex
            .as_ref()
            .unwrap()
            .source_sql
            .as_deref()
            .unwrap()
    );
    assert_eq!(
        source_where.source_condition_node_id, "1:31-1:41",
        "the ownership id must be the independently parsed WHERE predicate span"
    );
    assert_eq!(
        where_filter.source_query_block_id,
        having.source_query_block_id
    );
    let expected_where_sql = where_filter
        .condition_rex
        .as_ref()
        .and_then(|condition| condition.source_text.clone())
        .expect("exact WHERE condition text");

    let ir = convert_raw_file(raw).unwrap();
    let RelExpr::NativeHaving { input, .. } = &ir.queries[0].rel else {
        panic!("source-attested aggregate/subquery HAVING must retain native identity");
    };
    let RelExpr::Aggregate { input, .. } = input.as_ref() else {
        panic!("source HAVING Filter must retain its immediate Aggregate");
    };
    let RelExpr::Project { input, .. } = input.as_ref() else {
        panic!("expected aggregate-input project");
    };
    let RelExpr::Filter { predicate, .. } = input.as_ref() else {
        panic!("expected source WHERE Filter");
    };
    let ownership = predicate
        .source
        .as_ref()
        .and_then(|source| source.clause_ownership.as_ref())
        .expect("converted WHERE root must retain validated ownership");
    assert_eq!(ownership.kind, logos_ir::ir::SourceClauseKind::Where);
    assert_eq!(ownership.source_sql, expected_where_sql);
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and frozen benchmark inputs"]
fn calcite_wrapper_emits_cross_checked_tpch_date_literal_payloads() {
    let repo = repo_root();
    let case = repo.join("benchmarks/core/.generated/sqlsolver/nonwetune-flat/rbot-tpch__query1");
    let schema = case.join("schema.sql");

    for query_name in ["sql1.sql", "sql2.sql"] {
        let raw = run_calcite(&repo, &schema, &case.join(query_name));
        let filter = find_first_source_where_filter(
            raw.queries[0]
                .rel
                .as_ref()
                .expect("TPCH1 must produce a relation"),
        )
        .expect("TPCH1 WHERE must carry exact source ownership");
        let date = find_rex_by_source_sql(
            filter.condition_rex.as_ref().expect("TPCH1 condition"),
            "DATE '1998-12-01'",
        )
        .expect("TPCH1 condition must retain its source DATE literal");
        assert_eq!(date.literal_type_name.as_deref(), Some("DATE"));
        assert_eq!(date.date_literal.as_deref(), Some("1998-12-01"));
        assert_eq!(date.literal_value2.as_deref(), Some("10561"));
        convert_raw_file(raw)
            .unwrap_or_else(|error| panic!("{query_name}: date authority rejected: {error}"));
    }
}

#[test]
#[ignore = "requires the Java Calcite wrapper and frozen benchmark inputs"]
fn calcite_wrapper_preserves_calcite393_typed_date_identity_cast() {
    let repo = repo_root();
    let case = repo
        .join("benchmarks/core/.generated/sqlsolver/nonwetune-flat/verieql-calcite__calcite-393");
    let schema = case.join("schema.sql");

    for query_name in ["sql1.sql", "sql2.sql"] {
        let raw = run_calcite(&repo, &schema, &case.join(query_name));
        if query_name == "sql1.sql" {
            let mut swapped_null_roles = raw.clone();
            let rewrite = find_rel_rex_by_source_kind_mut(
                swapped_null_roles.queries[0].rel.as_mut().unwrap(),
                "IS_NOT_DISTINCT_FROM",
            )
            .expect("Calcite393 exact IS NOT DISTINCT FROM rewrite");
            rewrite.operands[0].operands.swap(0, 1);
            assert!(matches!(
                convert_raw_file(swapped_null_roles),
                Err(logos_ir::Error::InvalidRelSourceProvenance(message))
                    if message.contains("IS NOT DISTINCT FROM")
            ));

            let mut forged_equality_nullability = raw.clone();
            let rewrite = find_rel_rex_by_source_kind_mut(
                forged_equality_nullability.queries[0].rel.as_mut().unwrap(),
                "IS_NOT_DISTINCT_FROM",
            )
            .expect("Calcite393 exact IS NOT DISTINCT FROM rewrite");
            rewrite.operands[1].operands[0].nullable = false;
            rewrite.operands[1].operands[0].full_type = Some("BOOLEAN NOT NULL".to_owned());
            assert!(matches!(
                convert_raw_file(forged_equality_nullability),
                Err(logos_ir::Error::InvalidRelSourceProvenance(message))
                    if message.contains("IS NOT DISTINCT FROM")
            ));

            let mut forged_internal_source_role = raw.clone();
            let rewrite = find_rel_rex_by_source_kind_mut(
                forged_internal_source_role.queries[0].rel.as_mut().unwrap(),
                "IS_NOT_DISTINCT_FROM",
            )
            .expect("Calcite393 exact IS NOT DISTINCT FROM rewrite");
            rewrite.operands[0].source_kind = Some("AND".to_owned());
            rewrite.operands[0].source_operator = Some("AND".to_owned());
            assert!(matches!(
                convert_raw_file(forged_internal_source_role),
                Err(logos_ir::Error::InvalidRelSourceProvenance(message))
                    if message.contains("IS NOT DISTINCT FROM")
            ));
        }
        if query_name == "sql2.sql" {
            let project = raw.queries[0]
                .rel
                .as_ref()
                .expect("Calcite393 target relation");
            let literal = &project.project_rex[0];
            assert_eq!(
                literal.source_sql.as_deref(),
                Some("CAST(DATE '2020-12-11' AS DATE)")
            );
            assert_eq!(literal.source_kind.as_deref(), Some("CAST"));
            assert_eq!(literal.source_operator.as_deref(), Some("CAST"));
            assert_eq!(literal.date_literal.as_deref(), Some("2020-12-11"));
            assert_eq!(literal.text.as_deref(), Some("2020-12-11"));
            assert_eq!(literal.literal_value2.as_deref(), Some("18607"));
        }
        convert_raw_file(raw)
            .unwrap_or_else(|error| panic!("{query_name}: DATE identity cast rejected: {error}"));
    }
}

#[test]
#[ignore = "requires the Java Calcite wrapper and frozen benchmark inputs"]
fn calcite_wrapper_binds_tpch2_nested_comma_join_source_envelopes() {
    fn count_comma_joins(rel: &CalciteRel) -> usize {
        usize::from(
            rel.rel_type == "LogicalJoin"
                && rel.source_kind.as_deref() == Some("JOIN")
                && rel.source_operator.as_deref() == Some("COMMA-JOIN"),
        ) + rel.inputs.iter().map(count_comma_joins).sum::<usize>()
    }

    with_large_calcite_stack(|| {
        let repo = repo_root();
        let case =
            repo.join("benchmarks/core/.generated/sqlsolver/nonwetune-flat/rbot-tpch__query2");
        let schema = case.join("schema.sql");
        for query_name in ["sql1.sql", "sql2.sql"] {
            let raw = run_calcite(&repo, &schema, &case.join(query_name));
            let filter = find_first_source_where_filter(
                raw.queries[0]
                    .rel
                    .as_ref()
                    .expect("TPCH2 must produce a relation"),
            )
            .expect("TPCH2 outer WHERE must carry source ownership");
            assert_eq!(filter.variables_set, ["$cor0"]);
            let scalar = find_rex_subquery_root(
                filter.condition_rex.as_ref().expect("TPCH2 condition"),
                "LogicalAggregate",
            )
            .expect("TPCH2 must retain its correlated scalar aggregate");
            let nested = scalar.subquery_rel.as_deref().unwrap();
            assert_eq!(count_comma_joins(nested), 3);
            assert!(nested.variables_set.is_empty());
            convert_raw_file(raw).unwrap_or_else(|error| {
                panic!("{query_name}: nested join authority rejected: {error}")
            });
        }
    });
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_rejects_mixed_comma_outer_join_precedence_drift() {
    let repo = repo_root();
    let temp = temp_dir("mixed-comma-outer-join-precedence");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(
        &schema,
        "create table a(id integer);\n\
         create table b(id integer);\n\
         create table c(id integer);\n",
    )
    .unwrap();
    fs::write(
        &query,
        "select * from a, b full join c on b.id = c.id;\n\
         select * from a left join b on a.id = b.id, c;\n",
    )
    .unwrap();

    let raw = run_calcite(&repo, &schema, &query);
    assert_eq!(raw.queries.len(), 2);

    let mut calcite_misassociated = raw.clone();
    calcite_misassociated.queries.truncate(1);
    assert!(matches!(
        convert_raw_file(calcite_misassociated),
        Err(logos_ir::Error::InvalidRelSourceProvenance(message))
            if message.contains("association disagrees")
    ));

    let mut comma_root = raw;
    comma_root.queries.remove(0);
    convert_raw_file(comma_root)
        .expect("a qualified join followed by a FROM-list comma has the same root in PostgreSQL");
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and frozen benchmark inputs"]
fn calcite_wrapper_withholds_wetune32_outer_where_over_local_subquery_binder() {
    fn collect_rex_filters<'a>(rex: &'a CalciteRex, filters: &mut Vec<&'a CalciteRel>) {
        if let Some(subquery) = rex.subquery_rel.as_deref() {
            collect_rel_filters(subquery, filters);
        }
        for operand in &rex.operands {
            collect_rex_filters(operand, filters);
        }
    }

    fn collect_rel_filters<'a>(rel: &'a CalciteRel, filters: &mut Vec<&'a CalciteRel>) {
        if rel.rel_type == "LogicalFilter" {
            filters.push(rel);
        }
        for rex in rel
            .project_rex
            .iter()
            .chain(rel.condition_rex.iter())
            .chain(rel.fetch_rex.iter())
            .chain(rel.offset_rex.iter())
        {
            collect_rex_filters(rex, filters);
        }
        for input in &rel.inputs {
            collect_rel_filters(input, filters);
        }
    }

    let repo = repo_root();
    let case = repo.join("benchmarks/core/.generated/sqlsolver/wetune-issues/32");
    for query_name in ["sql1.sql", "sql2.sql"] {
        let raw = run_calcite(&repo, &case.join("schema.sql"), &case.join(query_name));
        let root = raw.queries[0]
            .rel
            .as_ref()
            .unwrap_or_else(|| panic!("{query_name}: expected a relational tree"));
        let mut filters = Vec::new();
        collect_rel_filters(root, &mut filters);

        if query_name == "sql1.sql" {
            let outer = find_first_filter(root).expect("wetune-32 source outer Filter");
            assert!(outer.variables_set.is_empty());
            assert_eq!(outer.source_clause.as_deref(), Some("WHERE"));
            assert!(
                outer.source_where.is_some(),
                "the exact outer WHERE remains independently owned when its subquery introduces a local correlation"
            );
            let local_owner = filters
                .iter()
                .copied()
                .find(|filter| !filter.variables_set.is_empty())
                .expect("wetune-32 source nested local correlation owner");
            assert_eq!(local_owner.variables_set, ["$cor0"]);
            assert_eq!(
                local_owner
                    .source_where
                    .as_ref()
                    .map(|source| source.variables_set.as_slice()),
                Some(local_owner.variables_set.as_slice()),
                "attesting the enclosing WHERE must preserve the locally owned WHERE"
            );
        }

        convert_raw_file(raw).unwrap_or_else(|error| {
            panic!("{query_name}: local binder conversion failed: {error}")
        });
    }
}

#[test]
#[ignore = "requires SQLGlot, the Java Calcite wrapper, and frozen benchmark inputs"]
fn calcite_wrapper_reconstructs_wetune46_in_subquery_order() {
    with_large_calcite_stack(|| {
        fn marker_rex(rex: &CalciteRex) -> Option<&CalciteRex> {
            if rex.source_in_subquery_order.is_some() {
                return Some(rex);
            }
            for operand in &rex.operands {
                if let Some(found) = marker_rex(operand) {
                    return Some(found);
                }
            }
            rex.subquery_rel.as_deref().and_then(marker_rel)
        }

        fn marker_rel(rel: &CalciteRel) -> Option<&CalciteRex> {
            for rex in rel.project_rex.iter().chain(rel.condition_rex.iter()) {
                if let Some(found) = marker_rex(rex) {
                    return Some(found);
                }
            }
            rel.inputs.iter().find_map(marker_rel)
        }

        fn typed_ordered_subquery(ast: &ScalarAst) -> Option<&RelExpr> {
            match ast {
                ScalarAst::RelSubquery { rel }
                    if matches!(
                        rel.as_ref(),
                        RelExpr::Project { input, exprs, .. }
                            if matches!(exprs.as_slice(), [ScalarExpr {
                                parsed: ScalarAst::InputRef { index: 0 },
                                ..
                            }]) && matches!(input.as_ref(), RelExpr::Sort { .. })
                    ) =>
                {
                    Some(rel)
                }
                ScalarAst::RelSubquery { rel } => typed_ordered_subquery_rel(rel),
                ScalarAst::Call { args, .. } => args.iter().find_map(typed_ordered_subquery),
                ScalarAst::TypeAnnotation { expr, .. } => typed_ordered_subquery(expr),
                _ => None,
            }
        }

        fn typed_ordered_subquery_rel(rel: &RelExpr) -> Option<&RelExpr> {
            match rel {
                RelExpr::Project { input, exprs, .. } => exprs
                    .iter()
                    .find_map(|expr| typed_ordered_subquery(&expr.parsed))
                    .or_else(|| typed_ordered_subquery_rel(input)),
                RelExpr::Filter {
                    input, predicate, ..
                }
                | RelExpr::NativeHaving {
                    input, predicate, ..
                } => typed_ordered_subquery(&predicate.parsed)
                    .or_else(|| typed_ordered_subquery_rel(input)),
                RelExpr::Join {
                    left,
                    right,
                    condition,
                    ..
                } => typed_ordered_subquery(&condition.parsed)
                    .or_else(|| typed_ordered_subquery_rel(left))
                    .or_else(|| typed_ordered_subquery_rel(right)),
                RelExpr::Aggregate { input, .. }
                | RelExpr::Distinct { input, .. }
                | RelExpr::Sort { input, .. } => typed_ordered_subquery_rel(input),
                RelExpr::Set { inputs, .. } => inputs.iter().find_map(typed_ordered_subquery_rel),
                RelExpr::TableScan { .. } | RelExpr::Values { .. } => None,
            }
        }

        let repo = repo_root();
        let case = repo.join("benchmarks/core/.generated/sqlsolver/wetune-issues/46");
        let temp = temp_dir("wetune46-lost-in-order");
        for production in [false, true] {
            let raw = if production {
                run_calcite_sqlglot(
                    &repo,
                    &case.join("schema.sql"),
                    &case.join("sql1.sql"),
                    &temp.join("sql1.normalized.sql"),
                )
            } else {
                run_calcite(&repo, &case.join("schema.sql"), &case.join("sql1.sql"))
            };
            let rex = marker_rel(raw.queries[0].rel.as_ref().expect("wetune46 relation"))
                .expect("wetune46 IN subquery must carry lost-order evidence");
            let marker = rex.source_in_subquery_order.as_ref().unwrap();
            assert_eq!(marker.kind, "POSTGRES_IN_SUBQUERY_LOST_ORDER_BY");
            assert_eq!(marker.query_block_id, marker.select_node_id);
            assert_eq!(marker.project_input_index, 0);
            assert_eq!(marker.project_base_field_name, "id");
            assert_eq!(marker.order_field_index, 1);
            assert_eq!(marker.order_base_field_name, "title");
            assert_eq!(marker.direction, "ASCENDING");
            assert_eq!(marker.null_direction, "LAST");
            let generated = rex.subquery_rel.as_deref().unwrap();
            assert_eq!(generated.source_kind.as_deref(), Some("SELECT"));
            assert_eq!(
                generated.source_node_id,
                Some(marker.select_node_id.clone())
            );

            let ir = convert_raw_file(raw).unwrap_or_else(|error| {
                panic!(
                    "{} wetune46 conversion rejected reconstructed order: {error}",
                    if production { "production" } else { "direct" }
                )
            });
            let ordered = typed_ordered_subquery_rel(&ir.queries[0].rel)
                .expect("typed wetune46 IN subquery must retain its source order");
            let RelExpr::Project { input, output, .. } = ordered else {
                unreachable!("finder requires Project")
            };
            assert_eq!(output.len(), 1);
            assert_eq!(output[0].name, "id");
            let RelExpr::Sort {
                input,
                collation,
                fetch,
                offset,
                output,
            } = input.as_ref()
            else {
                unreachable!("finder requires Sort")
            };
            assert!(fetch.is_none() && offset.is_none());
            assert_eq!(collation.len(), 1);
            assert_eq!(collation[0].field_index, 1);
            assert_eq!(
                collation[0].direction,
                logos_ir::ir::SortDirection::Ascending
            );
            assert_eq!(
                collation[0].null_direction,
                Some(logos_ir::ir::SortNullDirection::Last)
            );
            assert_eq!(output.len(), 12);
            assert_eq!(output[1].name, "title");
            assert!(matches!(input.as_ref(), RelExpr::Filter { input, .. }
            if matches!(input.as_ref(), RelExpr::TableScan { table, .. }
                if table.as_slice() == ["labels"])));
        }
        fs::remove_dir_all(&temp).unwrap();
    });
}

#[test]
#[ignore = "requires the Java Calcite wrapper and frozen benchmark inputs"]
fn calcite_wrapper_rejects_wetune46_lost_order_attestation_drift() {
    with_large_calcite_stack(|| {
        fn marker_rex_mut(rex: &mut CalciteRex) -> Option<&mut CalciteRex> {
            if rex.source_in_subquery_order.is_some() {
                return Some(rex);
            }
            for operand in &mut rex.operands {
                if let Some(found) = marker_rex_mut(operand) {
                    return Some(found);
                }
            }
            rex.subquery_rel.as_deref_mut().and_then(marker_rel_mut)
        }

        fn marker_rel_mut(rel: &mut CalciteRel) -> Option<&mut CalciteRex> {
            for rex in &mut rel.project_rex {
                if let Some(found) = marker_rex_mut(rex) {
                    return Some(found);
                }
            }
            if let Some(condition) = rel.condition_rex.as_mut()
                && let Some(found) = marker_rex_mut(condition)
            {
                return Some(found);
            }
            for input in &mut rel.inputs {
                if let Some(found) = marker_rel_mut(input) {
                    return Some(found);
                }
            }
            None
        }

        fn assert_rejected(raw: CalciteFile, label: &str) {
            assert!(
                matches!(
                    convert_raw_file(raw),
                    Err(logos_ir::Error::InvalidRelSourceProvenance(_))
                ),
                "{label} must fail closed"
            );
        }

        let repo = repo_root();
        let case = repo.join("benchmarks/core/.generated/sqlsolver/wetune-issues/46");
        let raw = run_calcite(&repo, &case.join("schema.sql"), &case.join("sql1.sql"));
        let baseline = convert_raw_file(raw.clone()).expect("pristine wetune46 conversion");

        let mut missing = raw.clone();
        marker_rel_mut(missing.queries[0].rel.as_mut().unwrap())
            .unwrap()
            .source_in_subquery_order = None;
        assert_rejected(missing, "removed marker");

        let mut key = raw.clone();
        marker_rel_mut(key.queries[0].rel.as_mut().unwrap())
            .unwrap()
            .source_in_subquery_order
            .as_mut()
            .unwrap()
            .order_field_index = 0;
        assert_rejected(key, "forged key index");

        let mut direction = raw.clone();
        marker_rel_mut(direction.queries[0].rel.as_mut().unwrap())
            .unwrap()
            .source_in_subquery_order
            .as_mut()
            .unwrap()
            .direction = "DESCENDING".to_owned();
        assert_rejected(direction, "forged direction");

        let mut rendered = raw.clone();
        let rendered_marker = marker_rel_mut(rendered.queries[0].rel.as_mut().unwrap())
            .unwrap()
            .source_in_subquery_order
            .as_mut()
            .unwrap();
        rendered_marker.source_order_by_sql.push_str(" LIMIT 1");
        rendered_marker.source_order_item_sql = "labels.id DESC".to_owned();
        rendered_marker.source_relation_sql = "other_table".to_owned();
        let rendered_ir = convert_raw_file(rendered)
            .expect("rendered lost-order SQL is diagnostic beside exact text");
        assert_eq!(
            ir_scalar_asts(&rendered_ir.queries[0].rel),
            ir_scalar_asts(&baseline.queries[0].rel)
        );

        let mut exact_order_item = raw.clone();
        marker_rel_mut(exact_order_item.queries[0].rel.as_mut().unwrap())
            .unwrap()
            .source_in_subquery_order
            .as_mut()
            .unwrap()
            .order_item_text = "labels.id".to_owned();
        assert_rejected(exact_order_item, "forged exact order item");

        let mut exact_relation = raw.clone();
        marker_rel_mut(exact_relation.queries[0].rel.as_mut().unwrap())
            .unwrap()
            .source_in_subquery_order
            .as_mut()
            .unwrap()
            .source_relation_text = "projects".to_owned();
        assert_rejected(exact_relation, "forged exact relation");

        let mut exact_direction = raw.clone();
        marker_rel_mut(exact_direction.queries[0].rel.as_mut().unwrap())
            .unwrap()
            .source_in_subquery_order
            .as_mut()
            .unwrap()
            .order_by_text = "DESC".to_owned();
        assert_rejected(exact_direction, "forged exact order direction token");

        let mut stale_root_project_order = raw.clone();
        let stale_collation = stale_root_project_order.queries[0]
            .rel
            .as_ref()
            .and_then(|rel| rel.collation.first())
            .cloned()
            .expect("wetune46 outer Sort collation");
        let rex =
            marker_rel_mut(stale_root_project_order.queries[0].rel.as_mut().unwrap()).unwrap();
        rex.source_in_subquery_order = None;
        let subquery = rex.subquery_rel.as_deref_mut().unwrap();
        subquery.source_kind = Some("ORDER_BY".to_owned());
        subquery.source_sql = Some(format!(
            "{}\nORDER BY `labels`.`title`",
            subquery.source_sql.as_deref().unwrap()
        ));
        subquery.collation = vec![stale_collation];
        assert_eq!(subquery.rel_type, "LogicalProject");
        assert_rejected(
            stale_root_project_order,
            "stale root Project collation without source binding",
        );

        let mut span = raw;
        marker_rel_mut(span.queries[0].rel.as_mut().unwrap())
            .unwrap()
            .source_in_subquery_order
            .as_mut()
            .unwrap()
            .order_item_node_id = "1:1-1:1".to_owned();
        assert_rejected(span, "forged order-item identity");

        let temp = temp_dir("wetune46-coherent-borrowed-asc");
        let query = temp.join("sql1.sql");
        let source = fs::read_to_string(case.join("sql1.sql")).unwrap();
        let outer_desc = source.rfind("DESC").expect("outer DESC token");
        let mut asc_source = source;
        asc_source.replace_range(outer_desc..outer_desc + 4, "ASC");
        fs::write(&query, &asc_source).unwrap();
        let mut coherent_borrow = run_calcite(&repo, &case.join("schema.sql"), &query);
        let outer_asc = asc_source.rfind("ASC").expect("borrowed outer ASC token");
        let marker = marker_rel_mut(coherent_borrow.queries[0].rel.as_mut().unwrap())
            .unwrap()
            .source_in_subquery_order
            .as_mut()
            .unwrap();
        marker.order_by_node_id = format!("1:{}-1:{}", outer_asc + 1, outer_asc + 3);
        marker.order_by_text = "ASC".to_owned();
        assert_rejected(
            coherent_borrow,
            "coherent exact ASC token borrowed from the outer ORDER BY",
        );
        fs::remove_dir_all(&temp).unwrap();
    });
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_rejects_or_withholds_risky_in_subquery_order_attestation() {
    with_large_calcite_stack(|| {
        fn ordered_rex(rex: &CalciteRex) -> Option<&CalciteRex> {
            if rex
                .source_sql
                .as_deref()
                .is_some_and(|source| source.contains("ORDER BY"))
                && rex.subquery_rel.is_some()
            {
                return Some(rex);
            }
            for operand in &rex.operands {
                if let Some(found) = ordered_rex(operand) {
                    return Some(found);
                }
            }
            rex.subquery_rel.as_deref().and_then(ordered_rel)
        }

        fn ordered_rel(rel: &CalciteRel) -> Option<&CalciteRex> {
            for rex in rel.project_rex.iter().chain(rel.condition_rex.iter()) {
                if let Some(found) = ordered_rex(rex) {
                    return Some(found);
                }
            }
            rel.inputs.iter().find_map(ordered_rel)
        }

        let repo = repo_root();
        let temp = temp_dir("risky-in-subquery-orders");
        let schema = temp.join("schema.sql");
        let query = temp.join("query.sql");
        fs::write(
            &schema,
            "create table labels(id integer, title varchar(255));\n",
        )
        .unwrap();
        let cases = [
            (
                "limit",
                "select id from labels where id in (select id from labels order by title limit 1);\n",
            ),
            (
                "offset",
                "select id from labels where id in (select id from labels order by title offset 1);\n",
            ),
            (
                "runtime-error",
                "select id from labels where id in (select id from labels order by id / (id - id));\n",
            ),
            (
                "srf",
                "select id from labels where id in (select id from labels order by generate_series(1, 0));\n",
            ),
            (
                "window",
                "select id from labels where id in (select id from labels order by row_number() over (order by id));\n",
            ),
            (
                "collate",
                "select id from labels where id in (select id from labels order by title collate \"C\");\n",
            ),
        ];
        for (label, sql) in cases {
            fs::write(&query, sql).unwrap();
            let raw = run_calcite(&repo, &schema, &query);
            let Some(root) = raw.queries[0].rel.as_ref() else {
                assert!(raw.queries[0].error.is_some(), "{label}: missing rel/error");
                continue;
            };
            let ordered = ordered_rel(root)
                .unwrap_or_else(|| panic!("{label}: expected ordered RexSubQuery source"));
            assert!(
                ordered.source_in_subquery_order.is_none(),
                "{label}: risky order must never receive the frozen q46 marker"
            );
            let subquery = ordered.subquery_rel.as_deref().unwrap();
            let source_claims_order = subquery.source_kind.as_deref() == Some("ORDER_BY")
                && subquery
                    .source_sql
                    .as_deref()
                    .is_some_and(|source| source.contains("\nORDER BY "));
            if source_claims_order {
                assert!(
                    matches!(
                        convert_raw_file(raw),
                        Err(logos_ir::Error::InvalidRelSourceProvenance(_))
                    ),
                    "{label}: a lost, unmarked source order must fail closed"
                );
            }
        }
        fs::remove_dir_all(&temp).unwrap();
    });
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_closes_every_table_scan_row_against_the_source_schema() {
    let repo = repo_root();
    let temp = temp_dir("table-scan-schema-row-closure");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(
        &schema,
        "create table t(a integer, b bigint, c varchar(10));\n",
    )
    .unwrap();
    fs::write(&query, "select a from t where b > 0; select b, a from t;\n").unwrap();

    let raw = run_calcite(&repo, &schema, &query);
    assert!(
        find_first_source_where_filter(raw.queries[0].rel.as_ref().unwrap()).is_some(),
        "the first statement must exercise the outer WHERE input path"
    );
    convert_raw_file(raw.clone()).unwrap();

    let mut reordered_where_scan = raw.clone();
    find_rel_type_mut(
        reordered_where_scan.queries[0].rel.as_mut().unwrap(),
        "LogicalTableScan",
    )
    .unwrap()
    .row_type
    .swap(0, 1);

    let mut renamed_plain_scan = raw.clone();
    find_rel_type_mut(
        renamed_plain_scan.queries[1].rel.as_mut().unwrap(),
        "LogicalTableScan",
    )
    .unwrap()
    .row_type[0]
        .name = "forged_a".to_owned();

    let mut retyped_plain_scan = raw.clone();
    let field = &mut find_rel_type_mut(
        retyped_plain_scan.queries[1].rel.as_mut().unwrap(),
        "LogicalTableScan",
    )
    .unwrap()
    .row_type[0];
    field.ty = "BOOLEAN".to_owned();
    field.full_type = Some("BOOLEAN".to_owned());
    field.precision = Some(1);
    field.scale = None;

    let mut renullable_plain_scan = raw;
    let field = &mut find_rel_type_mut(
        renullable_plain_scan.queries[1].rel.as_mut().unwrap(),
        "LogicalTableScan",
    )
    .unwrap()
    .row_type[0];
    field.nullable = !field.nullable;

    for forged in [
        reordered_where_scan,
        renamed_plain_scan,
        retyped_plain_scan,
        renullable_plain_scan,
    ] {
        assert!(matches!(
            convert_raw_file(forged),
            Err(logos_ir::Error::InvalidRelSourceProvenance(_))
        ));
    }
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_attests_where_ownership_per_operator_and_correlation_scope() {
    fn collect_rex_filters<'a>(rex: &'a CalciteRex, filters: &mut Vec<&'a CalciteRel>) {
        if let Some(subquery) = rex.subquery_rel.as_deref() {
            collect_rel_filters(subquery, filters);
        }
        if let Some(reference) = rex.reference_expr.as_deref() {
            collect_rex_filters(reference, filters);
        }
        for operand in &rex.operands {
            collect_rex_filters(operand, filters);
        }
    }

    fn collect_rel_filters<'a>(rel: &'a CalciteRel, filters: &mut Vec<&'a CalciteRel>) {
        if rel.rel_type == "LogicalFilter" {
            filters.push(rel);
        }
        for rex in rel
            .project_rex
            .iter()
            .chain(rel.condition_rex.iter())
            .chain(rel.fetch_rex.iter())
            .chain(rel.offset_rex.iter())
        {
            collect_rex_filters(rex, filters);
        }
        for input in &rel.inputs {
            collect_rel_filters(input, filters);
        }
    }

    let repo = repo_root();
    let temp = temp_dir("operator-local-where-ownership");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&schema, "create table t(k integer, v integer);\n").unwrap();
    fs::write(
        &query,
        r#"select outer_t.k from t outer_t
           where outer_t.v > (
             select avg(inner_t.v) from t inner_t
             where inner_t.k = outer_t.k
           );
           select q.k from (
             select k, v from t where v > 0
           ) q where q.k > 0;
           select k, sum(v) from t group by k having sum(v) > 0;
        "#,
    )
    .unwrap();

    let raw = run_calcite(&repo, &schema, &query);
    let mut correlated_filters = Vec::new();
    collect_rel_filters(
        raw.queries[0].rel.as_ref().expect("correlated query rel"),
        &mut correlated_filters,
    );
    assert_eq!(correlated_filters.len(), 2);
    let outer = correlated_filters
        .iter()
        .copied()
        .find(|filter| !filter.variables_set.is_empty())
        .expect("outer WHERE owns the subquery correlation");
    let inner = correlated_filters
        .iter()
        .copied()
        .find(|filter| filter.variables_set.is_empty())
        .expect("inner WHERE uses an inherited correlation");
    let outer_where = outer
        .source_where
        .as_ref()
        .expect("outer correlated WHERE must be independently attested");
    assert!(
        inner.source_where.is_none(),
        "a nested Filter using a free outer correlation must not claim a second local WHERE owner"
    );
    assert_eq!(outer_where.variables_set, outer.variables_set);
    let outer_condition = outer.condition_rex.as_ref().unwrap();
    assert_eq!(
        outer_condition.source_sql.as_deref(),
        Some(outer_where.source_condition_sql.as_str())
    );
    assert_eq!(
        outer_condition.source_kind.as_deref(),
        Some(outer_where.source_condition_kind.as_str())
    );
    assert_eq!(
        outer_condition.source_operator,
        outer_where.source_condition_operator
    );
    let inner_condition = inner.condition_rex.as_ref().unwrap();
    assert!(inner_condition.source_sql.is_some());
    assert_eq!(inner.source_clause.as_deref(), Some("WHERE"));

    let mut flattened_filters = Vec::new();
    collect_rel_filters(
        raw.queries[1].rel.as_ref().expect("flattened query rel"),
        &mut flattened_filters,
    );
    assert_eq!(flattened_filters.len(), 2);
    assert_eq!(
        flattened_filters
            .iter()
            .filter(|filter| filter.source_where.is_some())
            .count(),
        1,
        "only the direct inner table Filter has closed base-field lineage; the outer derived-table Filter must fail closed"
    );

    let mut having_filters = Vec::new();
    collect_rel_filters(
        raw.queries[2].rel.as_ref().expect("HAVING query rel"),
        &mut having_filters,
    );
    assert!(having_filters.iter().any(|filter| {
        filter.source_clause.as_deref() == Some("HAVING") && filter.source_where.is_none()
    }));

    let ir = convert_raw_file(raw).unwrap();
    assert_eq!(ir.queries.len(), 3);
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_where_identifier_binding_preserves_postgres_quoted_case() {
    let repo = repo_root();
    let temp = temp_dir("where-quoted-identifier-case");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(
        &schema,
        "create table t(\"CaseKey\" integer, casekey integer);\n",
    )
    .unwrap();
    fs::write(
        &query,
        "select \"d2\".\"CaseKey\" from t as \"d2\" \
           where \"d2\".\"CaseKey\" = 1; \
         select d2.casekey from t as d2 where D2.CASEKEY = 1;\n",
    )
    .unwrap();

    let raw = run_calcite(&repo, &schema, &query);
    let quoted = find_first_source_where_filter(raw.queries[0].rel.as_ref().unwrap()).unwrap();
    let quoted_rex = &quoted.condition_rex.as_ref().unwrap().operands[0];
    assert_eq!(quoted_rex.source_identifier_names, ["d2", "CaseKey"]);
    assert_eq!(quoted_rex.source_identifier_quoted, [true, true]);
    assert_eq!(quoted_rex.index, Some(0));
    let unquoted = find_first_source_where_filter(raw.queries[1].rel.as_ref().unwrap()).unwrap();
    let unquoted_rex = &unquoted.condition_rex.as_ref().unwrap().operands[0];
    assert_eq!(unquoted_rex.source_identifier_names, ["d2", "casekey"]);
    assert_eq!(unquoted_rex.source_identifier_quoted, [false, false]);
    assert_eq!(unquoted_rex.index, Some(1));
    convert_raw_file(raw.clone()).unwrap();

    let mut swapped_index = raw.clone();
    let filter =
        find_first_source_where_filter_mut(swapped_index.queries[0].rel.as_mut().unwrap()).unwrap();
    filter.condition_rex.as_mut().unwrap().operands[0].index = Some(1);

    let mut forged_case = raw.clone();
    let filter =
        find_first_source_where_filter_mut(forged_case.queries[0].rel.as_mut().unwrap()).unwrap();
    let identifier = &mut filter.condition_rex.as_mut().unwrap().operands[0];
    *identifier.source_identifier_names.last_mut().unwrap() = "casekey".to_owned();
    *identifier.source_identifier_quoted.last_mut().unwrap() = true;
    identifier.source_sql = Some("\"d2\".\"casekey\"".to_owned());

    let mut missing_quotedness = raw;
    find_first_source_where_filter_mut(missing_quotedness.queries[0].rel.as_mut().unwrap())
        .unwrap()
        .condition_rex
        .as_mut()
        .unwrap()
        .operands[0]
        .source_identifier_quoted
        .clear();

    for forged in [swapped_index, forged_case, missing_quotedness] {
        assert!(matches!(
            convert_raw_file(forged),
            Err(logos_ir::Error::InvalidRelSourceProvenance(_))
        ));
    }

    let wrong_case_query = temp.join("wrong-case.sql");
    fs::write(
        &wrong_case_query,
        "select d2.casekey from t as \"D2\" where d2.casekey = 1;\n",
    )
    .unwrap();
    let wrong_case = run_calcite(&repo, &schema, &wrong_case_query);
    assert!(wrong_case.queries[0].rel.is_none());
    assert!(
        wrong_case.queries[0]
            .error
            .as_deref()
            .is_some_and(|error| error.contains("d2")),
        "quoted \"D2\" must never bind unquoted d2: {:?}",
        wrong_case.queries[0].error
    );
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_where_correlation_field_binds_source_index_and_type() {
    let repo = repo_root();
    let temp = temp_dir("where-correlated-field-binding");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(
        &schema,
        "create table outer_t(\"CaseKey\" integer, other integer); \
         create table inner_t(fk integer);\n",
    )
    .unwrap();
    fs::write(
        &query,
        "select o.\"CaseKey\" from outer_t o where exists ( \
           select 1 from inner_t i where i.fk = o.\"CaseKey\" \
         );\n",
    )
    .unwrap();

    let raw = run_calcite(&repo, &schema, &query);
    let mut inspected = raw.clone();
    let field = find_rel_field_access_mut(inspected.queries[0].rel.as_mut().unwrap()).unwrap();
    assert_eq!(field.field_name.as_deref(), Some("CaseKey"));
    assert_eq!(field.field_index, Some(0));
    assert_eq!(field.ty.as_deref(), Some("INTEGER"));
    assert_eq!(field.source_identifier_names, ["o", "CaseKey"]);
    assert_eq!(field.source_identifier_quoted, [false, true]);
    assert_eq!(
        field
            .reference_expr
            .as_ref()
            .unwrap()
            .correlation_name
            .as_deref(),
        Some("$cor0")
    );
    convert_raw_file(raw.clone()).unwrap();

    let mut wrong_index = raw.clone();
    find_rel_field_access_mut(wrong_index.queries[0].rel.as_mut().unwrap())
        .unwrap()
        .field_index = Some(1);
    let mut wrong_source_case = raw.clone();
    find_rel_field_access_mut(wrong_source_case.queries[0].rel.as_mut().unwrap())
        .unwrap()
        .source_identifier_names[1] = "casekey".to_owned();
    let mut wrong_type = raw.clone();
    let field = find_rel_field_access_mut(wrong_type.queries[0].rel.as_mut().unwrap()).unwrap();
    field.ty = Some("BIGINT".to_owned());
    field.precision = Some(19);
    let mut wrong_correlation = raw.clone();
    let reference = find_rel_field_access_mut(wrong_correlation.queries[0].rel.as_mut().unwrap())
        .unwrap()
        .reference_expr
        .as_mut()
        .unwrap();
    reference.correlation_id = Some(1);
    reference.correlation_name = Some("$cor1".to_owned());
    reference.text = Some("$cor1".to_owned());
    let mut ambiguous_owner_name = raw.clone();
    {
        let filter = find_first_source_where_filter_mut(
            ambiguous_owner_name.queries[0].rel.as_mut().unwrap(),
        )
        .unwrap();
        filter.row_type[1].name = "CaseKey".to_owned();
        filter.inputs[0].row_type[1].name = "CaseKey".to_owned();
        find_rex_field_access_mut(filter.condition_rex.as_mut().unwrap())
            .unwrap()
            .field_index = Some(1);
    }
    let mut missing_source_identity = raw;
    find_rel_field_access_mut(missing_source_identity.queries[0].rel.as_mut().unwrap())
        .unwrap()
        .source_identifier_names
        .clear();

    for forged in [
        wrong_index,
        wrong_source_case,
        wrong_type,
        wrong_correlation,
        ambiguous_owner_name,
        missing_source_identity,
    ] {
        assert!(matches!(
            convert_raw_file(forged),
            Err(logos_ir::Error::InvalidRelSourceProvenance(_))
        ));
    }
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and frozen benchmark inputs"]
fn calcite_wrapper_converts_both_q010_families_with_exact_repeated_aggregate_roles() {
    fn find_ordered_where(rel: &CalciteRel) -> Option<&CalciteRel> {
        if rel.rel_type == "LogicalFilter"
            && rel.source_kind.as_deref() == Some("ORDER_BY")
            && rel.source_where.is_some()
        {
            return Some(rel);
        }
        for rex in rel.project_rex.iter().chain(rel.condition_rex.iter()) {
            if let Some(subquery) = rex.subquery_rel.as_deref()
                && let Some(found) = find_ordered_where(subquery)
            {
                return Some(found);
            }
        }
        rel.inputs.iter().find_map(find_ordered_where)
    }

    fn borrow_repeated_aggregate_source_from_sibling(rel: &mut CalciteRel) -> bool {
        if rel.rel_type == "LogicalProject"
            && rel
                .inputs
                .first()
                .is_some_and(|input| input.rel_type == "LogicalAggregate")
        {
            let mut pair = None;
            for right in 0..rel.project_rex.len() {
                let candidate = &rel.project_rex[right];
                if candidate.class.as_deref() != Some("RexInputRef")
                    || candidate.source_kind.as_deref() == Some("IDENTIFIER")
                    || candidate.source_node_id.is_none()
                    || candidate.source_text.is_none()
                {
                    continue;
                }
                for left in 0..right {
                    let earlier = &rel.project_rex[left];
                    if earlier.class.as_deref() == Some("RexInputRef")
                        && earlier.index == candidate.index
                        && earlier.source_kind == candidate.source_kind
                        && earlier.source_operator == candidate.source_operator
                        && earlier.source_text == candidate.source_text
                        && earlier.source_node_id != candidate.source_node_id
                    {
                        pair = Some((left, right));
                        break;
                    }
                }
                if pair.is_some() {
                    break;
                }
            }
            if let Some((left, right)) = pair {
                let borrowed_id = rel.project_rex[left].source_node_id.clone();
                let borrowed_text = rel.project_rex[left].source_text.clone();
                let borrowed_sql = rel.project_rex[left].source_sql.clone();
                rel.project_rex[right].source_node_id = borrowed_id;
                rel.project_rex[right].source_text = borrowed_text;
                rel.project_rex[right].source_sql = borrowed_sql;
                return true;
            }
        }
        rel.inputs
            .iter_mut()
            .any(borrow_repeated_aggregate_source_from_sibling)
    }

    with_large_calcite_stack(|| {
        let repo = repo_root();
        let temp = temp_dir("dsb10-direct-and-production");
        for case_name in ["rbot-dsb__query010", "tpcds-variants__query010"] {
            let case = repo.join(format!(
                "benchmarks/core/.generated/sqlsolver/nonwetune-flat/{case_name}"
            ));
            for (query_name, rbot_expected) in [
                ("sql1.sql", Some(("1:1-1:1884", "1:311-1:1726"))),
                ("sql2.sql", Some(("1:1-1:1871", "1:311-1:1713"))),
            ] {
                for production in [false, true] {
                    let normalized_path =
                        temp.join(format!("{case_name}-{query_name}.normalized.sql"));
                    let raw = if production {
                        run_calcite_sqlglot(
                            &repo,
                            &case.join("schema.sql"),
                            &case.join(query_name),
                            &normalized_path,
                        )
                    } else {
                        run_calcite(&repo, &case.join("schema.sql"), &case.join(query_name))
                    };
                    let label = format!(
                        "{case_name}/{query_name}/{}",
                        if production { "production" } else { "direct" }
                    );
                    if production {
                        let normalized = fs::read_to_string(&normalized_path)
                            .unwrap_or_else(|error| panic!("{label}: normalized SQL: {error}"));
                        if case_name == "rbot-dsb__query010" {
                            assert!(normalized.contains("COUNT(*) \"cnt1\""), "{label}");
                            assert!(!normalized.contains("COUNT(*) AS \"cnt1\""), "{label}");
                            assert!(normalized.contains("FROM \"customer\" \"c\""), "{label}");
                            assert!(
                                !normalized.contains("FROM \"customer\" AS \"c\""),
                                "{label}"
                            );
                        } else {
                            assert!(normalized.contains("COUNT(*) AS \"cnt1\""), "{label}");
                            assert!(normalized.contains("FROM \"customer\" AS \"c\""), "{label}");
                        }
                    }
                    let filter = find_ordered_where(
                        raw.queries[0]
                            .rel
                            .as_ref()
                            .unwrap_or_else(|| panic!("{label}: relation")),
                    );
                    if !production
                        && case_name == "rbot-dsb__query010"
                        && let Some(expected) = rbot_expected
                    {
                        let source_where = filter
                            .and_then(|filter| filter.source_where.as_ref())
                            .unwrap_or_else(|| panic!("{label}: outer WHERE beneath ORDER BY"));
                        assert_eq!(source_where.query_block_id, expected.0, "{label}");
                        assert_eq!(source_where.source_condition_node_id, expected.1, "{label}");
                    }
                    if let Some(source_where) =
                        filter.and_then(|filter| filter.source_where.as_ref())
                    {
                        assert!(!source_where.owner_node_id.is_empty(), "{label}");
                    }

                    if !production {
                        let mut borrowed = raw.clone();
                        assert!(
                            borrow_repeated_aggregate_source_from_sibling(
                                borrowed.queries[0].rel.as_mut().unwrap()
                            ),
                            "{label}: find two repeated exact Aggregate consumers"
                        );
                        assert!(
                            convert_raw_file(borrowed).is_err(),
                            "{label}: a repeated Aggregate consumer cannot borrow its sibling SELECT-item source role"
                        );
                    }
                    convert_raw_file(raw)
                        .unwrap_or_else(|error| panic!("{label} conversion failed: {error}"));
                }
            }
        }
        fs::remove_dir_all(&temp).unwrap();
    });
}

#[test]
#[ignore = "requires the Java Calcite wrapper and frozen benchmark inputs"]
fn calcite_wrapper_converts_dsb50_duplicate_alias_where_bindings() {
    with_large_calcite_stack(|| {
        let repo = repo_root();
        let case =
            repo.join("benchmarks/core/.generated/sqlsolver/nonwetune-flat/rbot-dsb__query050");
        for query_name in ["sql1.sql", "sql2.sql"] {
            let raw = run_calcite(&repo, &case.join("schema.sql"), &case.join(query_name));
            let filter = raw.queries[0]
                .rel
                .as_ref()
                .and_then(find_first_source_where_filter)
                .expect("DSB50 source WHERE");
            let source_where = filter.source_where.as_ref().unwrap();
            let d2_year = source_where
                .input_bindings
                .iter()
                .find(|binding| binding.source_sql == "d2.d_year")
                .expect("d2.d_year binding");
            assert_eq!(d2_year.input_index, 106);
            assert_eq!(d2_year.source_relation_sql, "`date_dim` AS `d2`");
            assert_eq!(d2_year.base_table, ["date_dim"]);
            assert_eq!(d2_year.base_field_name, "d_year");
            assert_eq!(d2_year.generated_field_name, "d_year0");
            let mut reordered = raw.clone();
            find_first_source_where_filter_mut(reordered.queries[0].rel.as_mut().unwrap())
                .unwrap()
                .source_where
                .as_mut()
                .unwrap()
                .input_bindings
                .swap(0, 1);
            assert!(matches!(
                convert_raw_file(reordered),
                Err(logos_ir::Error::InvalidRelSourceProvenance(_))
            ));
            convert_raw_file(raw).unwrap();
        }
    });
}

#[test]
#[ignore = "requires SQLGlot, the Java Calcite wrapper, and frozen benchmark inputs"]
fn calcite_wrapper_sqlglot_preserves_dsb50_aliases_and_where_authority() {
    with_large_calcite_stack(|| {
        let repo = repo_root();
        let case =
            repo.join("benchmarks/core/.generated/sqlsolver/nonwetune-flat/rbot-dsb__query050");
        let temp = temp_dir("dsb50-sqlglot-production-path");
        for query_name in ["sql1.sql", "sql2.sql"] {
            let normalized = temp.join(format!("{query_name}.normalized.sql"));
            let raw = run_calcite_sqlglot(
                &repo,
                &case.join("schema.sql"),
                &case.join(query_name),
                &normalized,
            );
            let normalized_sql = fs::read_to_string(&normalized).unwrap();
            for alias in ["31-60 days", "61-90 days", "91-120 days"] {
                assert!(
                    normalized_sql.contains(format!("AS \"{alias}\"").as_str()),
                    "SQLGlot changed quoted output alias {alias}: {normalized_sql}"
                );
            }
            assert!(!normalized_sql.contains("AS \"31-INTERVAL"));

            let filter = raw.queries[0]
                .rel
                .as_ref()
                .and_then(find_first_source_where_filter)
                .expect("normalized DSB50 source WHERE");
            let d2_year = filter
                .source_where
                .as_ref()
                .unwrap()
                .input_bindings
                .iter()
                .find(|binding| binding.source_sql == "d2.d_year")
                .expect("normalized d2.d_year binding");
            assert_eq!(d2_year.input_index, 106);
            assert_eq!(d2_year.base_field_name, "d_year");
            let d2_year_rex =
                find_rex_by_source_sql(filter.condition_rex.as_ref().unwrap(), "d2.d_year")
                    .expect("normalized d2.d_year Rex source");
            assert_eq!(d2_year_rex.source_identifier_names, ["d2", "d_year"]);
            assert_eq!(d2_year_rex.source_identifier_quoted, [true, true]);
            convert_raw_file(raw).unwrap();
        }
        fs::remove_dir_all(&temp).unwrap();
    });
}

#[test]
#[ignore = "requires SQLGlot and the Java Calcite wrapper"]
fn calcite_wrapper_sqlglot_folds_only_unquoted_postgres_identifiers() {
    fn first_scan(rel: &RelExpr) -> &[String] {
        match rel {
            RelExpr::TableScan { table, .. } => table,
            RelExpr::Project { input, .. }
            | RelExpr::Filter { input, .. }
            | RelExpr::NativeHaving { input, .. }
            | RelExpr::Aggregate { input, .. }
            | RelExpr::Distinct { input, .. }
            | RelExpr::Sort { input, .. } => first_scan(input),
            RelExpr::Join { left, .. } => first_scan(left),
            RelExpr::Set { inputs, .. } => first_scan(&inputs[0]),
            RelExpr::Values { .. } => panic!("expected a table scan"),
        }
    }

    let repo = repo_root();
    let temp = temp_dir("sqlglot-postgres-identifier-folding");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    let normalized = temp.join("normalized.sql");
    fs::write(
        &schema,
        "CREATE TABLE DEPT (NAME text);\n\
         CREATE TABLE \"DEPT\" (\"NAME\" text);\n",
    )
    .unwrap();
    fs::write(
        &query,
        "SELECT NAME FROM DEPT;\n\
         SELECT \"NAME\" FROM \"DEPT\";\n\
         SELECT \"NAME\" FROM DEPT;\n\
         SELECT NAME FROM \"DEPT\";\n",
    )
    .unwrap();

    let raw = run_calcite_sqlglot(&repo, &schema, &query, &normalized);
    assert_eq!(
        raw.schema
            .iter()
            .map(|table| table.name.as_str())
            .collect::<Vec<_>>(),
        ["dept", "DEPT"]
    );
    assert!(raw.queries[0].error.is_none());
    assert!(raw.queries[1].error.is_none());
    assert!(raw.queries[2].error.is_some());
    assert!(raw.queries[3].error.is_some());
    assert!(raw.queries[0].sql.contains("\"dept\""));
    assert!(raw.queries[1].sql.contains("\"DEPT\""));

    let mut valid = raw.clone();
    valid.queries.truncate(2);
    let ir = convert_raw_file(valid).unwrap();
    assert_eq!(first_scan(&ir.queries[0].rel), ["dept"]);
    assert_eq!(first_scan(&ir.queries[1].rel), ["DEPT"]);

    let normalized_sql = fs::read_to_string(&normalized).unwrap();
    assert!(normalized_sql.contains("SELECT \"name\" FROM \"dept\""));
    assert!(normalized_sql.contains("SELECT \"NAME\" FROM \"DEPT\""));
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires SQLGlot, the Java Calcite wrapper, and frozen benchmark inputs"]
fn calcite_wrapper_sqlglot_folds_calcite148_postgres_identifiers() {
    let repo = repo_root();
    let case = repo.join(
        "benchmarks/core/.generated/sqlsolver/nonwetune-flat/\
         verieql-calcite__calcite-148",
    );
    let temp = temp_dir("sqlglot-calcite148-identifier-folding");

    for query_name in ["sql1.sql", "sql2.sql"] {
        let direct = run_calcite(&repo, &case.join("schema.sql"), &case.join(query_name));
        assert!(direct.queries[0].error.is_none(), "direct {query_name}");
        convert_raw_file(direct).unwrap_or_else(|error| {
            panic!("direct calcite-148 {query_name} conversion failed: {error}")
        });

        let normalized = temp.join(format!("{query_name}.normalized.sql"));
        let raw = run_calcite_sqlglot(
            &repo,
            &case.join("schema.sql"),
            &case.join(query_name),
            &normalized,
        );
        assert!(
            raw.queries[0].error.is_none(),
            "{query_name}: {:?}",
            raw.queries[0].error
        );
        let dept = raw
            .schema
            .iter()
            .find(|table| table.name == "dept")
            .expect("canonical calcite-148 dept table");
        assert_eq!(
            dept.columns
                .iter()
                .map(|column| column.name.as_str())
                .collect::<Vec<_>>(),
            ["deptno", "name"]
        );
        let normalized_sql = fs::read_to_string(&normalized).unwrap();
        assert!(normalized_sql.contains("\"dept\""), "{query_name}");
        assert!(!normalized_sql.contains("\"DEPT\""), "{query_name}");
        convert_raw_file(raw)
            .unwrap_or_else(|error| panic!("calcite-148 {query_name} conversion failed: {error}"));
    }
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires SQLGlot and the Java Calcite wrapper"]
fn calcite_wrapper_sqlglot_default_preserves_postgres_asc_nulls_last() {
    let repo = repo_root();
    let temp = temp_dir("sqlglot-default-postgres-null-ordering");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    let normalized = temp.join("normalized.sql");
    let report = temp.join("report.json");
    fs::write(&schema, "create table t(a integer);\n").unwrap();
    fs::write(&query, "select a from t order by a;\n").unwrap();

    let output = Command::new(repo.join("scripts/calcite-ir-sqlglot"))
        .arg("--schema")
        .arg(&schema)
        .arg("--sql")
        .arg(&query)
        .arg("--normalized-output")
        .arg(&normalized)
        .arg("--report")
        .arg(&report)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "default SQLGlot/Calcite wrapper failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let raw: CalciteFile = serde_json::from_slice(&output.stdout).unwrap();
    let sort = raw.queries[0].rel.as_ref().unwrap();
    assert_eq!(sort.rel_type, "LogicalSort");
    assert_eq!(sort.collation[0].direction, "ASCENDING");
    assert_eq!(sort.collation[0].null_direction.as_deref(), Some("LAST"));
    let normalized_sql = fs::read_to_string(&normalized).unwrap();
    assert!(!normalized_sql.contains("NULLS FIRST"));
    let report: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(&report).unwrap()).unwrap();
    assert_eq!(report["readDialect"], "postgres");
    convert_raw_file(raw).unwrap();
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_closes_order_by_ordinals_aliases_expressions_and_item_order() {
    fn sort(rel: &CalciteRel) -> &CalciteRel {
        if rel.rel_type == "LogicalSort" {
            return rel;
        }
        rel.inputs
            .iter()
            .find_map(|input| {
                (input.rel_type == "LogicalSort")
                    .then_some(input)
                    .or_else(|| {
                        input
                            .inputs
                            .iter()
                            .find(|child| child.rel_type == "LogicalSort")
                    })
            })
            .expect("query Sort")
    }

    let repo = repo_root();
    let temp = temp_dir("exact-source-order-by-forms");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(
        &schema,
        "create table t(a integer, b integer, c integer);\n",
    )
    .unwrap();
    fs::write(
        &query,
        "select a, b from t order by 2 desc;\n\
         select a out_a, b from t order by out_a;\n\
         select a + b as total from t order by a + b nulls first;\n\
         select a from t order by b, c desc nulls last;\n\
         select p.* from t p order by p.b desc nulls last;\n",
    )
    .unwrap();

    let raw = run_calcite(&repo, &schema, &query);
    assert_eq!(raw.queries.len(), 5);
    let forms = raw
        .queries
        .iter()
        .map(|query| sort(query.rel.as_ref().unwrap()))
        .collect::<Vec<_>>();
    assert_eq!(forms[0].collation[0].field_index, 1);
    assert_eq!(
        forms[0].source_order.as_ref().unwrap().items[0].item_text,
        "2 desc"
    );
    assert_eq!(forms[1].collation[0].field_index, 0);
    assert_eq!(
        forms[1].source_order.as_ref().unwrap().items[0].expression_text,
        "out_a"
    );
    assert_eq!(forms[2].collation[0].field_index, 0);
    assert_eq!(
        forms[2].source_order.as_ref().unwrap().items[0].expression_text,
        "a + b"
    );
    assert_eq!(
        forms[3]
            .source_order
            .as_ref()
            .unwrap()
            .items
            .iter()
            .map(|item| item.item_text.as_str())
            .collect::<Vec<_>>(),
        ["b", "c desc nulls last"]
    );
    assert_eq!(forms[3].collation[0].field_index, 1);
    assert_eq!(forms[3].collation[1].field_index, 2);
    assert_eq!(forms[4].collation[0].field_index, 1);
    assert_eq!(
        forms[4].source_order.as_ref().unwrap().items[0].expression_text,
        "p.b"
    );

    let mut qualified_wildcard_drift = raw.clone();
    let root = qualified_wildcard_drift.queries[4].rel.as_mut().unwrap();
    let sort = if root.rel_type == "LogicalSort" {
        root
    } else {
        &mut root.inputs[0]
    };
    sort.collation[0].field_index = 0;
    assert!(
        convert_raw_file(qualified_wildcard_drift).is_err(),
        "accepted a qualified-wildcard ORDER BY field-index drift"
    );

    let mut swapped = raw.clone();
    let root = swapped.queries[3].rel.as_mut().unwrap();
    let sort = if root.rel_type == "LogicalSort" {
        root
    } else {
        &mut root.inputs[0]
    };
    sort.source_order.as_mut().unwrap().items.swap(0, 1);
    assert!(
        convert_raw_file(swapped).is_err(),
        "accepted reordered exact ORDER BY item identities"
    );

    let mut truncated = raw.clone();
    let root = truncated.queries[3].rel.as_mut().unwrap();
    let sort = if root.rel_type == "LogicalSort" {
        root
    } else {
        &mut root.inputs[0]
    };
    sort.collation.truncate(1);
    let authority = sort.source_order.as_mut().unwrap();
    authority.items.truncate(1);
    authority.order_list_node_id = authority.items[0].item_node_id.clone();
    authority.order_list_text = authority.items[0].item_text.clone();
    assert!(
        convert_raw_file(truncated).is_err(),
        "accepted a coherently truncated source ORDER BY list"
    );

    convert_raw_file(raw).expect("convert exact ORDER BY forms");
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_closes_ordered_query_identity_across_with_prefix_and_body() {
    let repo = repo_root();
    let temp = temp_dir("exact-source-order-by-with-query");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&schema, "create table t(a integer, b integer);\n").unwrap();
    fs::write(
        &query,
        "with c as (select a, b from t) select a from c order by b desc;\n",
    )
    .unwrap();

    let raw = run_calcite(&repo, &schema, &query);
    let root = raw.queries[0].rel.as_ref().expect("WITH relation");
    let sort = if root.rel_type == "LogicalSort" {
        root
    } else {
        root.inputs
            .iter()
            .find(|input| input.rel_type == "LogicalSort")
            .expect("WITH Sort")
    };
    let order = sort
        .source_order
        .as_ref()
        .expect("WITH source ORDER BY authority");
    assert_eq!(
        order.query_text,
        "with c as (select a, b from t) select a from c"
    );
    assert_eq!(order.order_list_text, "b desc");
    assert_eq!(order.items[0].expression_text, "b");
    assert!(
        order.query_node_id.starts_with("1:1-"),
        "WITH authority must start at the WITH prefix"
    );
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and frozen benchmark inputs"]
fn calcite_wrapper_closes_tpch22_nested_where_relations_and_correlations() {
    with_large_calcite_stack(|| {
        let repo = repo_root();
        let case =
            repo.join("benchmarks/core/.generated/sqlsolver/nonwetune-flat/rbot-tpch__query22");
        let mut pristine = None;
        for query_name in ["sql1.sql", "sql2.sql"] {
            let raw = run_calcite(&repo, &case.join("schema.sql"), &case.join(query_name));
            let filter = raw.queries[0]
                .rel
                .as_ref()
                .and_then(find_first_source_where_filter)
                .expect("TPCH22 source WHERE");
            let scalar =
                find_rex_subquery_root(filter.condition_rex.as_ref().unwrap(), "LogicalAggregate")
                    .expect("TPCH22 AVG scalar subquery");
            assert!(scalar.subquery_rel.is_some());
            convert_raw_file(raw.clone()).unwrap();
            pristine.get_or_insert(raw);
        }
        let pristine = pristine.unwrap();

        let mut forged_aggregate = pristine.clone();
        let scalar = find_rex_subquery_root_mut(
            find_first_source_where_filter_mut(forged_aggregate.queries[0].rel.as_mut().unwrap())
                .unwrap()
                .condition_rex
                .as_mut()
                .unwrap(),
            "LogicalAggregate",
        )
        .unwrap();
        let aggregate = scalar.subquery_rel.as_deref_mut().unwrap();
        aggregate.agg_call_details[0].text = "SUM($0)".to_owned();
        aggregate.agg_call_details[0].function = "SUM".to_owned();

        let mut forged_predicate = pristine.clone();
        let scalar = find_rex_subquery_root_mut(
            find_first_source_where_filter_mut(forged_predicate.queries[0].rel.as_mut().unwrap())
                .unwrap()
                .condition_rex
                .as_mut()
                .unwrap(),
            "LogicalAggregate",
        )
        .unwrap();
        let inner_filter =
            find_rel_type_mut(scalar.subquery_rel.as_deref_mut().unwrap(), "LogicalFilter")
                .unwrap();
        inner_filter
            .condition_rex
            .as_mut()
            .unwrap()
            .operands
            .clear();

        let mut forged_table = pristine;
        let scalar = find_rex_subquery_root_mut(
            find_first_source_where_filter_mut(forged_table.queries[0].rel.as_mut().unwrap())
                .unwrap()
                .condition_rex
                .as_mut()
                .unwrap(),
            "LogicalAggregate",
        )
        .unwrap();
        let table = find_rel_type_mut(
            scalar.subquery_rel.as_deref_mut().unwrap(),
            "LogicalTableScan",
        )
        .unwrap();
        table.table = vec!["orders".to_owned()];

        let mut forged_result_type =
            run_calcite(&repo, &case.join("schema.sql"), &case.join("sql1.sql"));
        let scalar = find_rex_subquery_root_mut(
            find_first_source_where_filter_mut(forged_result_type.queries[0].rel.as_mut().unwrap())
                .unwrap()
                .condition_rex
                .as_mut()
                .unwrap(),
            "LogicalAggregate",
        )
        .unwrap();
        scalar.ty = Some("DOUBLE".to_owned());
        scalar.precision = Some(15);
        scalar.scale = None;
        let aggregate = scalar.subquery_rel.as_deref_mut().unwrap();
        aggregate.row_type[0].ty = "DOUBLE".to_owned();
        aggregate.row_type[0].precision = Some(15);
        aggregate.row_type[0].scale = None;
        aggregate.agg_call_details[0].ty = Some("DOUBLE".to_owned());
        aggregate.agg_call_details[0].full_type = Some("DOUBLE".to_owned());
        aggregate.agg_call_details[0].precision = Some(15);
        aggregate.agg_call_details[0].scale = None;

        let mut ambiguous_aggregate_name =
            run_calcite(&repo, &case.join("schema.sql"), &case.join("sql1.sql"));
        let scalar = find_rex_subquery_root_mut(
            find_first_source_where_filter_mut(
                ambiguous_aggregate_name.queries[0].rel.as_mut().unwrap(),
            )
            .unwrap()
            .condition_rex
            .as_mut()
            .unwrap(),
            "LogicalAggregate",
        )
        .unwrap();
        let aggregate = scalar.subquery_rel.as_deref_mut().unwrap();
        let project = find_rel_type_mut(&mut aggregate.inputs[0], "LogicalProject").unwrap();
        project.row_type.push(project.row_type[0].clone());
        project.project_rex.push(project.project_rex[0].clone());
        aggregate.agg_call_details[0].text = "AVG($1)".to_owned();
        aggregate.agg_call_details[0].arg_list = vec![1];

        for (label, forged) in [
            ("aggregate function", forged_aggregate),
            ("nested predicate", forged_predicate),
            ("nested table", forged_table),
            ("aggregate result type", forged_result_type),
        ] {
            assert!(convert_raw_file(forged).is_err(), "accepted {label} drift");
        }
        // The final mutation adds an internal Project carrier that is exactly
        // the same c_acctbal expression and redirects AVG to that duplicate.
        // It changes no declarative row, NULL, bag, error, or aggregate value,
        // so accepting it avoids making source fidelity depend on one
        // generated carrier shape.
        convert_raw_file(ambiguous_aggregate_name)
            .expect("an identical duplicate aggregate carrier is declaratively inert");
    });
}

#[test]
#[ignore = "requires the Java Calcite wrapper and frozen benchmark inputs"]
fn calcite_wrapper_closes_tpch11_nested_aggregate_output_lineage() {
    fn first_subquery_rex_mut(rex: &mut CalciteRex) -> Option<&mut CalciteRex> {
        if rex.class.as_deref() == Some("RexSubQuery") {
            return Some(rex);
        }
        rex.operands.iter_mut().find_map(first_subquery_rex_mut)
    }

    fn first_subquery_rel_mut(rel: &mut CalciteRel) -> Option<&mut CalciteRex> {
        for rex in rel
            .project_rex
            .iter_mut()
            .chain(rel.condition_rex.iter_mut())
        {
            if let Some(found) = first_subquery_rex_mut(rex) {
                return Some(found);
            }
        }
        rel.inputs.iter_mut().find_map(first_subquery_rel_mut)
    }

    with_large_calcite_stack(|| {
        let repo = repo_root();
        let case =
            repo.join("benchmarks/core/.generated/sqlsolver/nonwetune-flat/rbot-tpch__query11");
        let raw = run_calcite(&repo, &case.join("schema.sql"), &case.join("sql1.sql"));
        convert_raw_file(raw.clone()).expect("convert TPCH11 exact nested aggregate output");

        let mut forged_project_role = raw.clone();
        let subquery = first_subquery_rel_mut(forged_project_role.queries[0].rel.as_mut().unwrap())
            .expect("TPCH11 scalar subquery");
        let project = subquery.subquery_rel.as_deref_mut().unwrap();
        assert_eq!(project.rel_type, "LogicalProject");
        let aggregate_ref = &mut project.project_rex[0].operands[0];
        assert_eq!(aggregate_ref.source_operator.as_deref(), Some("sum"));
        aggregate_ref.source_operator = Some("max".to_owned());
        assert!(
            convert_raw_file(forged_project_role).is_err(),
            "a post-Aggregate input reference borrowed a different source call"
        );

        let mut forged_argument_tree = raw;
        let subquery =
            first_subquery_rel_mut(forged_argument_tree.queries[0].rel.as_mut().unwrap())
                .expect("TPCH11 scalar subquery");
        let aggregate = &mut subquery.subquery_rel.as_deref_mut().unwrap().inputs[0];
        assert_eq!(aggregate.rel_type, "LogicalAggregate");
        aggregate.agg_call_details[0].source_operands[0].source_operator = Some("+".to_owned());
        assert!(
            convert_raw_file(forged_argument_tree).is_err(),
            "an Aggregate source argument tree drifted from its exact input Project expression"
        );
    });
}

#[test]
#[ignore = "requires the Java Calcite wrapper"]
fn calcite_wrapper_nested_where_binds_exact_group_indexes_and_join_type() {
    let repo = repo_root();
    let temp = temp_dir("nested-where-group-and-join-binding");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(
        &schema,
        "create table l(l_a integer, l_b integer, l_c integer); \
         create table r(r_a integer, r_b integer);\n",
    )
    .unwrap();
    fs::write(
        &query,
        "select o.l_a from l o where exists ( \
           select i.l_a from l i group by i.l_a, i.l_b \
         ); \
         select o.l_a from l o where exists ( \
           select 1 from l i inner join r j on i.l_a = j.r_a \
         );\n",
    )
    .unwrap();

    let raw = run_calcite(&repo, &schema, &query);
    assert_eq!(raw.queries.len(), 2);
    convert_raw_file(raw.clone()).unwrap();

    let mut swapped_group_indexes = raw.clone();
    let aggregate = find_rex_subquery_root_mut(
        find_first_source_where_filter_mut(swapped_group_indexes.queries[0].rel.as_mut().unwrap())
            .unwrap()
            .condition_rex
            .as_mut()
            .unwrap(),
        "LogicalAggregate",
    )
    .unwrap();
    let rel = aggregate.subquery_rel.as_deref_mut().unwrap();
    assert_eq!(rel.source_group_indexes, [0, 1]);
    rel.group_set = Some(vec![1, 2]);
    rel.group_sets = Some(vec![vec![1, 2]]);

    let mut changed_join_type = raw;
    let join = find_rex_subquery_root_mut(
        find_first_source_where_filter_mut(changed_join_type.queries[1].rel.as_mut().unwrap())
            .unwrap()
            .condition_rex
            .as_mut()
            .unwrap(),
        "LogicalJoin",
    )
    .unwrap();
    let rel = join.subquery_rel.as_deref_mut().unwrap();
    assert_eq!(rel.source_join_type.as_deref(), Some("INNER"));
    rel.join_type = Some("LEFT".to_owned());
    let left_arity = rel.inputs[0].row_type.len();
    for field in &mut rel.row_type[left_arity..] {
        field.nullable = true;
    }

    for forged in [swapped_group_indexes, changed_join_type] {
        assert!(matches!(
            convert_raw_file(forged),
            Err(logos_ir::Error::InvalidRelSourceProvenance(_))
        ));
    }
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper"]
fn calcite_wrapper_nested_where_rejects_untyped_set_values_and_duplicate_base_names() {
    let repo = repo_root();
    let temp = temp_dir("nested-where-conservative-closures");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(
        &schema,
        "create table t(a integer); \
         create table left_t(id integer); \
         create table right_t(id integer);\n",
    )
    .unwrap();
    fs::write(
        &query,
        "select a from t where exists ( \
           select a from t union select a from t \
         ); \
         select a from t where a in (values (1), (2)); \
         select l.id from left_t l where exists ( \
           select 1 from left_t x inner join right_t y on x.id = y.id \
         );\n",
    )
    .unwrap();

    let raw = run_calcite(&repo, &schema, &query);
    assert_eq!(raw.queries.len(), 3);
    let one = |index: usize| CalciteFile {
        environment: raw.environment,
        schema: raw.schema.clone(),
        queries: vec![raw.queries[index].clone()],
    };
    for index in [0, 2] {
        let query = &raw.queries[index];
        let filter = find_first_filter(query.rel.as_ref().expect("conservative query rel"))
            .expect("outer WHERE Filter");
        assert_eq!(filter.source_clause.as_deref(), Some("WHERE"));
        assert!(
            filter.source_where.is_some(),
            "query {index} exact WHERE authority"
        );
    }
    let rejected_values = &raw.queries[1];
    assert!(
        rejected_values.rel.is_none(),
        "source VALUES without ordered-cell attestation must not expose a relation"
    );
    assert_eq!(
        rejected_values.error.as_deref(),
        Some(
            "java.lang.UnsupportedOperationException: source subquery does not align with its generated relational tree"
        )
    );
    convert_raw_file(one(0)).expect("typed UNION subquery has exact common typing");
    assert!(matches!(
        convert_raw_file(one(1)),
        Err(logos_ir::Error::CalciteQueryError(_))
    ));
    convert_raw_file(one(2))
        .expect("qualified join identifiers disambiguate duplicate base-column names");
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires SQLGlot, the Java Calcite wrapper, and frozen benchmark inputs"]
fn calcite_wrapper_tpch18_in_subquery_keeps_outer_clause_and_subquery_authority() {
    let repo = repo_root();
    let case = repo.join("benchmarks/core/.generated/sqlsolver/nonwetune-flat/rbot-tpch__query18");
    let temp = temp_dir("tpch18-direct-and-production");
    for query_name in ["sql1.sql", "sql2.sql"] {
        for production in [false, true] {
            let raw = if production {
                run_calcite_sqlglot(
                    &repo,
                    &case.join("schema.sql"),
                    &case.join(query_name),
                    &temp.join(format!("{query_name}.normalized.sql")),
                )
            } else {
                run_calcite(&repo, &case.join("schema.sql"), &case.join(query_name))
            };
            let outer = raw.queries[0]
                .rel
                .as_ref()
                .and_then(find_first_filter)
                .filter(|filter| filter.source_clause.as_deref() == Some("WHERE"))
                .expect("TPCH18 outer logical WHERE filter");
            assert_eq!(outer.source_clause.as_deref(), Some("WHERE"));
            let in_subquery =
                find_rex_subquery_root(outer.condition_rex.as_ref().unwrap(), "LogicalProject")
                    .expect("TPCH18 IN subquery");
            assert!(in_subquery.subquery_rel.is_some());
            convert_raw_file(raw).unwrap_or_else(|error| {
                panic!(
                    "{} {query_name} TPCH18 conversion failed: {error}",
                    if production { "production" } else { "direct" }
                )
            });
        }
    }
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and frozen benchmark inputs"]
fn calcite_wrapper_attests_dsb27_grouping_and_overrides_only_exact_source_binding() {
    with_large_calcite_stack(|| {
        let repo = repo_root();
        let case =
            repo.join("benchmarks/core/.generated/sqlsolver/nonwetune-flat/rbot-dsb__query027");
        let schema = case.join("schema.sql");
        let mut pristine = None;
        for query_name in ["sql1.sql", "sql2.sql"] {
            let raw = run_calcite(&repo, &schema, &case.join(query_name));
            let aggregate = first_aggregate(raw.queries[0].rel.as_ref().expect("DSB27 rel"));
            let grouping = &aggregate.agg_call_details[0];
            assert_eq!(grouping.text, "GROUPING($1)");
            assert_eq!(grouping.function, "GROUPING");
            assert_eq!(grouping.kind, "GROUPING");
            assert_eq!(grouping.arg_list, [1]);
            assert_eq!(grouping.ty.as_deref(), Some("BIGINT"));
            assert_eq!(grouping.full_type.as_deref(), Some("BIGINT NOT NULL"));
            assert_eq!(grouping.source_sql.as_deref(), Some("GROUPING(`s_state`)"));
            assert_eq!(grouping.source_kind.as_deref(), Some("OTHER_FUNCTION"));
            assert_eq!(grouping.source_operator.as_deref(), Some("grouping"));
            assert_eq!(grouping.source_distinct, Some(false));
            assert_eq!(grouping.source_operands.len(), 1);
            assert_eq!(
                grouping.source_operands[0].source_sql.as_deref(),
                Some("s_state")
            );
            assert_eq!(
                grouping.source_operands[0].source_kind.as_deref(),
                Some("IDENTIFIER")
            );
            assert!(
                aggregate.agg_call_details[1..]
                    .iter()
                    .all(|call| call.source_sql.is_some()),
                "same-block GROUPING alignment must not discard sibling AVG provenance"
            );

            let ir = convert_raw_file(raw.clone()).unwrap();
            let (calls, output) = first_ir_aggregate(&ir.queries[0].rel);
            assert_eq!(output[2].ty, SqlType::Integer);
            assert!(!output[2].nullable);
            assert_eq!(ir.queries[0].output()[2].ty, SqlType::Integer);
            assert_eq!(calls.len(), 5);
            assert!(
                calls[1..]
                    .iter()
                    .all(|call| call.function.eq_ignore_ascii_case("AVG"))
            );
            let postgres_numeric = SqlType::Decimal {
                precision: None,
                scale: None,
            };
            for (index, column) in output.iter().enumerate().take(7).skip(3) {
                assert_eq!(
                    column.ty,
                    postgres_numeric,
                    "DSB27 Aggregate agg{} must use PostgreSQL's unconstrained NUMERIC AVG result",
                    index - 2
                );
                assert_eq!(
                    ir.queries[0].output()[index].ty,
                    postgres_numeric,
                    "DSB27 projected agg{} must retain the unconstrained NUMERIC result",
                    index - 2
                );
            }
            let source = calls[0]
                .modifiers
                .source
                .as_ref()
                .expect("GROUPING source authority");
            assert_eq!(source.sql.as_deref(), Some("GROUPING(`s_state`)"));
            assert_eq!(source.operands.len(), 1);
            assert_eq!(
                source.operands[0].as_ref().unwrap().sql.as_deref(),
                Some("s_state")
            );
            pristine.get_or_insert(raw);
        }

        let pristine = pristine.unwrap();
        let grouping_type = |raw: CalciteFile| {
            let ir = convert_raw_file(raw).unwrap();
            first_ir_aggregate(&ir.queries[0].rel).1[2].ty.clone()
        };

        let mut missing = pristine.clone();
        let grouping =
            &mut first_aggregate_mut(missing.queries[0].rel.as_mut().unwrap()).agg_call_details[0];
        grouping.source_sql = None;
        grouping.source_node_id = None;
        grouping.source_text = None;
        grouping.source_kind = None;
        grouping.source_operator = None;
        grouping.source_distinct = None;
        grouping.source_operands.clear();
        assert!(convert_raw_file(missing).is_err());

        let mut forged_source = pristine.clone();
        first_aggregate_mut(forged_source.queries[0].rel.as_mut().unwrap()).agg_call_details[0]
            .source_operator = Some("avg".to_owned());
        assert!(convert_raw_file(forged_source).is_err());

        let mut forged_argument = pristine.clone();
        first_aggregate_mut(forged_argument.queries[0].rel.as_mut().unwrap()).agg_call_details[0]
            .source_operands[0]
            .source_sql = Some("i_item_id".to_owned());
        assert_eq!(
            grouping_type(forged_argument),
            SqlType::Integer,
            "rendered aggregate-operand sourceSql is diagnostic only"
        );

        let mut forged_exact_argument = pristine.clone();
        first_aggregate_mut(forged_exact_argument.queries[0].rel.as_mut().unwrap())
            .agg_call_details[0]
            .source_operands[0]
            .source_text = Some("i_item_id".to_owned());
        assert!(convert_raw_file(forged_exact_argument).is_err());

        let mut forged_index = pristine.clone();
        first_aggregate_mut(forged_index.queries[0].rel.as_mut().unwrap()).agg_call_details[0]
            .arg_list = vec![0];
        assert!(convert_raw_file(forged_index).is_err());

        let mut forged_type = pristine.clone();
        let grouping = &mut first_aggregate_mut(forged_type.queries[0].rel.as_mut().unwrap())
            .agg_call_details[0];
        grouping.ty = Some("INTEGER".to_owned());
        grouping.full_type = Some("INTEGER NOT NULL".to_owned());
        grouping.precision = Some(10);
        assert!(convert_raw_file(forged_type).is_err());

        let mut reordered = pristine;
        first_aggregate_mut(reordered.queries[0].rel.as_mut().unwrap())
            .agg_call_details
            .swap(0, 1);
        assert!(convert_raw_file(reordered).is_err());
    });
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_rejects_nested_grouping_without_complete_subquery_alignment() {
    let repo = repo_root();
    let temp = temp_dir("nested-grouping-query-block");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(
        &schema,
        "create table outer_t(k integer); create table inner_t(j integer);\n",
    )
    .unwrap();
    fs::write(
        &query,
        "select (select grouping(j) from inner_t group by rollup(j) limit 1) as inner_g, \
                grouping(k) as outer_g from outer_t group by rollup(k);\n",
    )
    .unwrap();

    let raw = run_calcite(&repo, &schema, &query);
    assert!(raw.queries[0].rel.is_none());
    assert!(raw.queries[0].error.as_deref().is_some_and(|error| {
        error.contains("source subquery does not align with its generated relational tree")
    }));
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_grouping_argument_order_is_positional_and_typed() {
    let repo = repo_root();
    let temp = temp_dir("multi-argument-grouping-order");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&schema, "create table t(a integer, b bigint);\n").unwrap();
    fs::write(
        &query,
        "select grouping(a, b) as g from t group by rollup(a, b);\n",
    )
    .unwrap();

    let raw = run_calcite(&repo, &schema, &query);
    let aggregate = first_aggregate(raw.queries[0].rel.as_ref().unwrap());
    let grouping = &aggregate.agg_call_details[0];
    assert_eq!(grouping.text, "GROUPING($0, $1)");
    assert_eq!(grouping.arg_list, [0, 1]);
    assert_eq!(grouping.source_operands.len(), 2);
    assert_eq!(grouping.source_operands[0].source_sql.as_deref(), Some("a"));
    assert_eq!(grouping.source_operands[1].source_sql.as_deref(), Some("b"));
    let source_grouping = aggregate
        .source_grouping
        .as_ref()
        .expect("ROLLUP source authority");
    assert_eq!(
        aggregate.source_root_query_block_id.as_deref(),
        Some(source_grouping.query_block_id.as_str())
    );
    assert_eq!(source_grouping.kind, "ROLLUP");
    assert_eq!(source_grouping.group_indexes, [0, 1]);
    assert_eq!(
        source_grouping.grouping_sets,
        [vec![0, 1], vec![0], Vec::new()]
    );
    assert_eq!(source_grouping.source_operand_indexes, [vec![0, 1]]);
    assert_eq!(source_grouping.source_operands.len(), 1);
    assert_eq!(source_grouping.source_operands[0].len(), 2);
    assert_eq!(
        source_grouping.source_operands[0][0].source_text.as_deref(),
        Some("a")
    );
    assert_eq!(
        source_grouping.source_operands[0][1].source_text.as_deref(),
        Some("b")
    );
    assert!(!source_grouping.source_has_where);
    assert!(!source_grouping.source_has_having);

    let converted = convert_raw_file(raw.clone()).unwrap();
    assert_eq!(
        first_ir_aggregate(&converted.queries[0].rel).1[2].ty,
        SqlType::Integer
    );
    let (calls, _) = first_ir_aggregate(&converted.queries[0].rel);
    assert_eq!(
        calls[0]
            .modifiers
            .source_grouping
            .as_ref()
            .unwrap()
            .grouping_sets,
        [vec![0, 1], vec![0], Vec::new()]
    );

    let mut missing_grouping_authority = raw.clone();
    first_aggregate_mut(missing_grouping_authority.queries[0].rel.as_mut().unwrap())
        .source_grouping = None;
    assert!(matches!(
        convert_raw_file(missing_grouping_authority),
        Err(logos_ir::Error::InvalidRelSourceProvenance(_))
    ));

    let mut reordered_sets = raw.clone();
    first_aggregate_mut(reordered_sets.queries[0].rel.as_mut().unwrap())
        .source_grouping
        .as_mut()
        .unwrap()
        .grouping_sets
        .swap(0, 1);
    assert!(matches!(
        convert_raw_file(reordered_sets),
        Err(logos_ir::Error::InvalidRelSourceProvenance(_))
    ));

    for clause in ["WHERE", "HAVING"] {
        let mut forged_parent_clause = raw.clone();
        let marker = first_aggregate_mut(forged_parent_clause.queries[0].rel.as_mut().unwrap())
            .source_grouping
            .as_mut()
            .unwrap();
        match clause {
            "WHERE" => marker.source_has_where = true,
            "HAVING" => marker.source_has_having = true,
            _ => unreachable!(),
        }
        assert!(matches!(
            convert_raw_file(forged_parent_clause),
            Err(logos_ir::Error::InvalidRelSourceProvenance(_))
        ));
    }

    fs::write(
        &query,
        "select cast(grouping(a) + grouping(b) as bigint) as g \
           from t group by rollup(a, b);\n\
         select cast(grouping(a) as bigint) + grouping(b) as g \
           from t group by rollup(a, b);\n",
    )
    .unwrap();
    let explicit_casts = run_calcite(&repo, &schema, &query);
    assert_eq!(explicit_casts.queries.len(), 2);
    // simplify=false retains the two explicit casts at their exact source
    // positions. This preserves the first query's int4 addition-before-cast
    // runtime-error boundary and the second query's cast-before-addition
    // boundary instead of relying on Calcite's BIGINT Rex result metadata.
    for (index, query) in explicit_casts.queries.iter().enumerate() {
        let converted = convert_raw_file(CalciteFile {
            environment: explicit_casts.environment,
            schema: explicit_casts.schema.clone(),
            queries: vec![query.clone()],
        })
        .unwrap_or_else(|error| panic!("explicit GROUPING cast {index}: {error}"));
        let RelExpr::Project { exprs, .. } = &converted.queries[0].rel else {
            panic!("explicit GROUPING cast {index}: Project")
        };
        match index {
            0 => assert!(matches!(
                &exprs[0].parsed,
                ScalarAst::TypeAnnotation { expr, ty }
                    if ty == "BIGINT"
                        && matches!(
                            expr.as_ref(),
                            ScalarAst::Call { op: ScalarOp::Cast, args, .. }
                                if matches!(
                                    args.as_slice(),
                                    [ScalarAst::Call { op: ScalarOp::Plus, .. }]
                                )
                        )
            )),
            1 => assert!(matches!(
                &exprs[0].parsed,
                ScalarAst::Call { op: ScalarOp::Plus, args, .. }
                    if matches!(
                        args.first(),
                        Some(ScalarAst::TypeAnnotation { expr, ty })
                            if ty == "BIGINT"
                                && matches!(
                                    expr.as_ref(),
                                    ScalarAst::Call { op: ScalarOp::Cast, .. }
                                )
                    )
            )),
            _ => unreachable!(),
        }
    }

    fs::write(
        &query,
        "select grouping(a, b) as g, count(*) as n from t \
         where a is not null group by rollup(a, b) having count(*) >= 0;\n",
    )
    .unwrap();
    let restricted_raw = run_calcite(&repo, &schema, &query);
    let restricted_marker = first_aggregate(restricted_raw.queries[0].rel.as_ref().unwrap())
        .source_grouping
        .as_ref()
        .unwrap();
    assert!(restricted_marker.source_has_where);
    assert!(restricted_marker.source_has_having);
    for clause in ["WHERE", "HAVING"] {
        let mut forged_unrestricted = restricted_raw.clone();
        let marker = first_aggregate_mut(forged_unrestricted.queries[0].rel.as_mut().unwrap())
            .source_grouping
            .as_mut()
            .unwrap();
        match clause {
            "WHERE" => marker.source_has_where = false,
            "HAVING" => marker.source_has_having = false,
            _ => unreachable!(),
        }
        assert!(matches!(
            convert_raw_file(forged_unrestricted),
            Err(logos_ir::Error::InvalidRelSourceProvenance(_))
        ));
    }

    let mut reordered_source = raw.clone();
    first_aggregate_mut(reordered_source.queries[0].rel.as_mut().unwrap())
        .source_grouping
        .as_mut()
        .unwrap()
        .source_operands
        .first_mut()
        .unwrap()
        .swap(0, 1);
    assert!(matches!(
        convert_raw_file(reordered_source),
        Err(logos_ir::Error::InvalidRelSourceProvenance(_))
    ));

    let mut reordered_rex_indexes = raw;
    first_aggregate_mut(reordered_rex_indexes.queries[0].rel.as_mut().unwrap()).agg_call_details[0]
        .arg_list
        .swap(0, 1);
    assert!(convert_raw_file(reordered_rex_indexes).is_err());
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_binds_ordinary_group_by_operands_to_exact_generated_indexes() {
    let repo = repo_root();
    let temp = temp_dir("ordinary-group-by-source-authority");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&schema, "create table t(a integer, b bigint);\n").unwrap();
    fs::write(&query, "select a, b, sum(a) from t group by a, b;\n").unwrap();

    let raw = run_calcite(&repo, &schema, &query);
    let aggregate = first_aggregate(raw.queries[0].rel.as_ref().unwrap());
    let grouping = aggregate
        .source_grouping
        .as_ref()
        .expect("ordinary GROUP BY exact source authority");
    assert_eq!(grouping.kind, "GROUP_BY");
    assert_eq!(grouping.group_indexes, [0, 1]);
    assert_eq!(grouping.grouping_sets, [vec![0, 1]]);
    assert_eq!(grouping.source_operand_indexes, [vec![0, 1]]);
    assert_eq!(grouping.source_operands.len(), 1);
    assert_eq!(grouping.source_operands[0].len(), 2);
    convert_raw_file(raw.clone()).expect("ordinary exact GROUP BY conversion");

    let mut missing = raw.clone();
    first_aggregate_mut(missing.queries[0].rel.as_mut().unwrap()).source_grouping = None;
    assert!(matches!(
        convert_raw_file(missing),
        Err(logos_ir::Error::InvalidRelSourceProvenance(_))
    ));

    let mut swapped_indexes = raw.clone();
    first_aggregate_mut(swapped_indexes.queries[0].rel.as_mut().unwrap())
        .source_grouping
        .as_mut()
        .unwrap()
        .source_operand_indexes[0]
        .swap(0, 1);
    assert!(matches!(
        convert_raw_file(swapped_indexes),
        Err(logos_ir::Error::InvalidRelSourceProvenance(_))
    ));

    let mut wrong_group_output_type = raw.clone();
    {
        let aggregate =
            first_aggregate_mut(wrong_group_output_type.queries[0].rel.as_mut().unwrap());
        aggregate.row_type[0].ty = "BIGINT".to_owned();
        aggregate.row_type[0].full_type = Some("BIGINT".to_owned());
        aggregate.row_type[0].precision = Some(19);
        aggregate.row_type[0].scale = Some(0);
    }
    assert!(matches!(
        convert_raw_file(wrong_group_output_type),
        Err(logos_ir::Error::InvalidRelSourceProvenance(_))
    ));

    let mut borrowed_select_operand = raw;
    let root = borrowed_select_operand.queries[0].rel.as_mut().unwrap();
    let aggregate = first_aggregate_mut(root);
    let select_a = aggregate.agg_call_details[0].source_operands[0].clone();
    let operand = &mut aggregate.source_grouping.as_mut().unwrap().source_operands[0][0];
    operand.source_node_id = select_a.source_node_id;
    operand.source_text = select_a.source_text;
    assert!(matches!(
        convert_raw_file(borrowed_select_operand),
        Err(logos_ir::Error::InvalidRelSourceProvenance(_))
    ));

    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_binds_grouping_through_join_collision_labels() {
    fn joined_group(rel: &CalciteRel) -> Option<&CalciteRel> {
        if rel.rel_type == "LogicalAggregate"
            && rel
                .inputs
                .first()
                .is_some_and(|input| input.rel_type == "LogicalJoin")
            && rel.source_grouping.is_some()
        {
            return Some(rel);
        }
        rel.inputs.iter().find_map(joined_group)
    }

    fn joined_group_mut(rel: &mut CalciteRel) -> Option<&mut CalciteRel> {
        if rel.rel_type == "LogicalAggregate"
            && rel
                .inputs
                .first()
                .is_some_and(|input| input.rel_type == "LogicalJoin")
            && rel.source_grouping.is_some()
        {
            return Some(rel);
        }
        rel.inputs.iter_mut().find_map(joined_group_mut)
    }

    with_large_calcite_stack(|| {
        let repo = repo_root();
        let temp = temp_dir("grouping-through-join-collision-labels");
        let schema = temp.join("schema.sql");
        let query = temp.join("query.sql");
        fs::write(&schema, "create table employee(mgr integer);\n").unwrap();
        fs::write(
            &query,
            r#"select l.mgr, r.mgr as right_mgr
                 from (select mgr from employee group by mgr) as l
                 full join (select mgr from employee group by mgr) as r
                   on l.mgr = r.mgr
                group by l.mgr, r.mgr;
            "#,
        )
        .unwrap();

        let pristine = run_calcite(&repo, &schema, &query);
        let aggregate = joined_group(pristine.queries[0].rel.as_ref().unwrap())
            .expect("outer group over FULL JOIN");
        let input = &aggregate.inputs[0];
        assert_eq!(input.row_type.len(), 2);
        assert_eq!(input.row_type[0].name, "mgr");
        assert_eq!(input.row_type[1].name, "mgr0");
        assert_eq!(input.row_type[0].ty, input.row_type[1].ty);
        let grouping = aggregate.source_grouping.as_ref().unwrap();
        assert_eq!(grouping.source_operand_indexes, [vec![0, 1]]);
        assert_eq!(
            grouping.source_operands[0][0].source_identifier_names,
            ["l", "mgr"]
        );
        assert_eq!(
            grouping.source_operands[0][1].source_identifier_names,
            ["r", "mgr"]
        );
        convert_raw_file(pristine.clone())
            .expect("qualified grouping names must resolve through synthetic join labels");

        let mut wrong_side = pristine;
        joined_group_mut(wrong_side.queries[0].rel.as_mut().unwrap())
            .unwrap()
            .source_grouping
            .as_mut()
            .unwrap()
            .source_operand_indexes[0][1] = 0;
        assert!(
            convert_raw_file(wrong_side).is_err(),
            "the right qualified grouping operand cannot bind the left same-typed join field"
        );

        fs::remove_dir_all(&temp).unwrap();
    });
}

#[test]
#[ignore = "requires SQLGlot and the Java Calcite wrapper"]
fn calcite_wrappers_reject_explicit_row_grouping_expression_before_ast_erasure() {
    let repo = repo_root();
    let temp = temp_dir("explicit-row-grouping-expression");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&schema, "create table t(a integer, b integer);\n").unwrap();
    fs::write(
        &query,
        "select a, b, count(*) from t \
         group by grouping sets ((row(a, b)), ());\n\
         select a, count(*) from t group by row(a);\n\
         select a, count(*) from t group by rollup(row(a));\n",
    )
    .unwrap();

    for production in [false, true] {
        let raw = if production {
            run_calcite_sqlglot(&repo, &schema, &query, &temp.join("normalized.sql"))
        } else {
            run_calcite(&repo, &schema, &query)
        };
        assert_eq!(raw.queries.len(), 3);
        for (index, query) in raw.queries.iter().enumerate() {
            let error = query.error.as_deref().unwrap_or_else(|| {
                panic!(
                    "{} accepted explicit ROW grouping statement {index}",
                    if production { "production" } else { "direct" }
                )
            });
            assert!(
                error.contains("UnsupportedOperationException")
                    && error.contains("explicit ROW grouping expressions"),
                "{error}"
            );
        }
    }
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper"]
fn calcite_wrapper_rejects_forged_derived_grouping_root_identity() {
    let repo = repo_root();
    let temp = temp_dir("derived-grouping-root-identity");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&schema, "create table t(a integer, b integer);\n").unwrap();
    fs::write(
        &query,
        "select a, b, n from (\
           select a, b, count(*) as n from t \
           group by grouping sets ((a, b), (a), ())\
         ) as grouped where a = 1 order by a nulls first limit 1;\n",
    )
    .unwrap();

    let raw = run_calcite(&repo, &schema, &query);
    let aggregate = first_aggregate(raw.queries[0].rel.as_ref().unwrap());
    let marker = aggregate.source_grouping.as_ref().unwrap();
    assert_ne!(
        aggregate.source_root_query_block_id.as_deref(),
        Some(marker.query_block_id.as_str())
    );
    convert_raw_file(raw.clone()).unwrap();

    let mut forged = raw;
    let aggregate = first_aggregate_mut(forged.queries[0].rel.as_mut().unwrap());
    aggregate.source_root_query_block_id = Some(
        aggregate
            .source_grouping
            .as_ref()
            .unwrap()
            .query_block_id
            .clone(),
    );
    assert!(matches!(
        convert_raw_file(forged),
        Err(logos_ir::Error::InvalidRelSourceProvenance(_))
    ));
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_binds_all_having_forms_declaratively() {
    fn source_having_mut(rel: &mut CalciteRel) -> Option<&mut CalciteRel> {
        if rel.rel_type == "LogicalFilter" && rel.source_clause.as_deref() == Some("HAVING") {
            return Some(rel);
        }
        rel.inputs.iter_mut().find_map(source_having_mut)
    }

    fn rex_at_path<'a>(root: &'a CalciteRex, path: &str) -> &'a CalciteRex {
        assert!(path == "$" || path.starts_with("$."));
        path.strip_prefix("$.")
            .map(|suffix| {
                suffix.split('.').fold(root, |rex, index| {
                    &rex.operands[index.parse::<usize>().unwrap()]
                })
            })
            .unwrap_or(root)
    }

    fn assert_declarative_bindings(
        rel: &CalciteRel,
        expected: &[(&str, usize, &str, &str, Option<&str>)],
    ) {
        let having = find_first_filter(rel).expect("source HAVING Filter");
        assert_eq!(having.source_clause.as_deref(), Some("HAVING"));
        assert_eq!(having.rel_type, "LogicalFilter");
        assert_eq!(having.inputs.len(), 1);
        assert_eq!(having.inputs[0].rel_type, "LogicalAggregate");
        assert_eq!(
            having.source_query_block_id,
            having.inputs[0].source_query_block_id
        );

        let condition = having.condition_rex.as_ref().expect("HAVING Rex");
        let attestation = having
            .source_native_having
            .as_ref()
            .expect("declarative HAVING attestation");
        assert_eq!(attestation.kind, "DECLARATIVE_HAVING");
        assert_eq!(
            attestation.query_block_id,
            having.source_query_block_id.as_deref().unwrap()
        );
        assert_eq!(
            attestation.source_condition_sql,
            condition.source_sql.as_deref().unwrap()
        );
        assert_eq!(
            attestation.generated_condition_sql,
            condition.text.as_deref().unwrap()
        );
        assert_eq!(attestation.aggregate_output_arity, having.row_type.len());
        assert_eq!(
            attestation.aggregate_call_count,
            having.inputs[0].agg_call_details.len()
        );
        assert_eq!(attestation.operand_bindings.len(), expected.len());

        for (binding, (path, output_index, source_sql, source_kind, source_operator)) in
            attestation.operand_bindings.iter().zip(expected)
        {
            assert_eq!(binding.path, *path);
            assert_eq!(binding.aggregate_output_index, *output_index);
            assert_eq!(binding.source_sql, *source_sql);
            assert_eq!(binding.source_kind, *source_kind);
            assert_eq!(binding.source_operator.as_deref(), *source_operator);

            let rex = rex_at_path(condition, path);
            assert_eq!(rex.class.as_deref(), Some("RexInputRef"));
            assert_eq!(rex.index, Some(*output_index));
            assert_eq!(rex.source_sql.as_deref(), Some(*source_sql));
            assert_eq!(rex.source_kind.as_deref(), Some(*source_kind));
            assert_eq!(rex.source_operator.as_deref(), *source_operator);
        }
    }

    fn count_ir_clauses(rel: &RelExpr) -> (usize, usize) {
        match rel {
            RelExpr::NativeHaving { input, .. } => {
                let (having, filter) = count_ir_clauses(input);
                (having + 1, filter)
            }
            RelExpr::Filter { input, .. } => {
                let (having, filter) = count_ir_clauses(input);
                (having, filter + 1)
            }
            RelExpr::Project { input, .. }
            | RelExpr::Aggregate { input, .. }
            | RelExpr::Distinct { input, .. }
            | RelExpr::Sort { input, .. } => count_ir_clauses(input),
            RelExpr::Join { left, right, .. } => {
                let left = count_ir_clauses(left);
                let right = count_ir_clauses(right);
                (left.0 + right.0, left.1 + right.1)
            }
            RelExpr::Set { inputs, .. } => inputs
                .iter()
                .map(count_ir_clauses)
                .fold((0, 0), |sum, count| (sum.0 + count.0, sum.1 + count.1)),
            RelExpr::TableScan { .. } | RelExpr::Values { .. } => (0, 0),
        }
    }

    let repo = repo_root();
    let temp = temp_dir("declarative-having-bindings");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(
        &schema,
        "create table t(a integer, b integer, v integer);\n\
         create table dept(deptno integer, name text);\n",
    )
    .unwrap();
    fs::write(
        &query,
        "select a, sum(v) from t group by a, b having b = 100;\n\
         select name as c1 from dept where name > 'b' group by name \
           having name > 'c' and (count(*) > 30 or name < 'z');\n\
         select name, deptno, count(*) from dept \
           group by grouping sets ((name, deptno), name) having name = 'Charlie';\n",
    )
    .unwrap();

    let raw = run_calcite(&repo, &schema, &query);
    assert_eq!(raw.queries.len(), 3);
    assert_declarative_bindings(
        raw.queries[0].rel.as_ref().expect("ordinary HAVING"),
        &[("$.0", 1, "b", "IDENTIFIER", None)],
    );
    assert_declarative_bindings(
        raw.queries[1].rel.as_ref().expect("mixed HAVING"),
        &[
            ("$.0.0", 0, "name", "IDENTIFIER", None),
            ("$.1.0.0", 1, "COUNT(*)", "OTHER_FUNCTION", Some("count")),
            ("$.1.1.0", 0, "name", "IDENTIFIER", None),
        ],
    );
    assert_declarative_bindings(
        raw.queries[2].rel.as_ref().expect("grouping-sets HAVING"),
        &[("$.0", 0, "name", "IDENTIFIER", None)],
    );
    assert_eq!(
        raw.queries[1].rel.as_ref().unwrap().project_rex[0]
            .source_node_id
            .as_deref(),
        Some("1:8-1:11"),
        "the post-HAVING output must retain its SELECT-item role"
    );

    let mut borrowed_group_role = raw.clone();
    borrowed_group_role.queries[1]
        .rel
        .as_mut()
        .unwrap()
        .project_rex[0]
        .source_node_id = Some("1:55-1:58".to_owned());
    assert!(
        convert_raw_file(borrowed_group_role).is_err(),
        "a post-HAVING output borrowed the same-spelled GROUP BY occurrence"
    );

    let mut forged_index = raw.clone();
    let forged_filter = source_having_mut(
        forged_index.queries[0]
            .rel
            .as_mut()
            .expect("forged ordinary HAVING"),
    )
    .expect("forged source HAVING Filter");
    forged_filter
        .condition_rex
        .as_mut()
        .expect("forged HAVING condition")
        .operands[0]
        .index = Some(0);
    forged_filter
        .source_native_having
        .as_mut()
        .expect("forged HAVING attestation")
        .operand_bindings[0]
        .aggregate_output_index = 0;
    assert!(matches!(
        convert_raw_file(forged_index),
        Err(logos_ir::Error::InvalidRelSourceProvenance(_))
    ));

    let ir = convert_raw_file(raw).expect("convert declarative HAVING forms");
    assert_eq!(count_ir_clauses(&ir.queries[0].rel), (1, 0));
    assert_eq!(
        count_ir_clauses(&ir.queries[1].rel),
        (1, 1),
        "the source WHERE must remain an ordinary Filter"
    );
    assert_eq!(count_ir_clauses(&ir.queries[2].rel), (1, 0));
    let (calls, _) = first_ir_aggregate(&ir.queries[2].rel);
    assert_eq!(calls.len(), 1);

    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_closes_expanded_coalesce_having_bindings() {
    fn source_having(rel: &CalciteRel) -> Option<&CalciteRel> {
        if rel.rel_type == "LogicalFilter" && rel.source_clause.as_deref() == Some("HAVING") {
            return Some(rel);
        }
        rel.inputs.iter().find_map(source_having)
    }

    fn source_having_mut(rel: &mut CalciteRel) -> Option<&mut CalciteRel> {
        if rel.rel_type == "LogicalFilter" && rel.source_clause.as_deref() == Some("HAVING") {
            return Some(rel);
        }
        rel.inputs.iter_mut().find_map(source_having_mut)
    }

    fn coalesce_case_mut(having: &mut CalciteRel) -> &mut CalciteRex {
        let condition = having.condition_rex.as_mut().unwrap();
        condition
            .operands
            .iter_mut()
            .find(|rex| {
                rex.kind.as_deref() == Some("CASE")
                    && rex
                        .source_operator
                        .as_deref()
                        .is_some_and(|operator| operator.eq_ignore_ascii_case("COALESCE"))
            })
            .expect("expanded COALESCE CASE")
    }

    fn direct_input_leaf_mut(rex: &mut CalciteRex) -> &mut CalciteRex {
        let mut current = rex;
        while current.kind.as_deref() == Some("CAST") && current.operands.len() == 1 {
            current = &mut current.operands[0];
        }
        current
    }

    let repo = repo_root();
    let temp = temp_dir("expanded-coalesce-having-bindings");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(
        &schema,
        "create table t(a decimal(19,2), v decimal(19,2));\n",
    )
    .unwrap();
    fs::write(
        &query,
        "select a, sum(v) from t group by a \
         having coalesce(sum(v), 0) > (select sum(v) from t);\n",
    )
    .unwrap();

    let pristine = run_calcite_postgres_c(&repo, &schema, &query);
    let having = source_having(pristine.queries[0].rel.as_ref().unwrap()).unwrap();
    let attestation = having
        .source_native_having
        .as_ref()
        .expect("expanded COALESCE HAVING must be declaratively attested");
    assert_eq!(
        attestation
            .operand_bindings
            .iter()
            .map(|binding| binding.path.as_str())
            .collect::<Vec<_>>(),
        ["$.0.0.0", "$.0.1.0"]
    );
    assert!(
        attestation
            .operand_bindings
            .iter()
            .all(|binding| binding.aggregate_output_index == 1)
    );
    convert_raw_file(pristine.clone()).expect("convert exact COALESCE HAVING normalization");

    // Forge a coherent same-typed shift of both tested/returned leaves and
    // both native bindings from the SUM output to the group key.  Shape and
    // type equality alone must not authorize the wrong semantic output.
    let mut wrong_leaf = pristine.clone();
    let having = source_having_mut(wrong_leaf.queries[0].rel.as_mut().unwrap()).unwrap();
    {
        let case = coalesce_case_mut(having);
        let tested = &mut case.operands[0].operands[0];
        tested.index = Some(0);
        tested.text = Some("$0".to_owned());
        let returned = direct_input_leaf_mut(&mut case.operands[1]);
        returned.index = Some(0);
        returned.text = Some("$0".to_owned());
    }
    for binding in &mut having
        .source_native_having
        .as_mut()
        .unwrap()
        .operand_bindings
    {
        binding.aggregate_output_index = 0;
    }

    let mut wrong_arm_order = pristine.clone();
    coalesce_case_mut(source_having_mut(wrong_arm_order.queries[0].rel.as_mut().unwrap()).unwrap())
        .operands
        .swap(1, 2);

    let mut wrong_fallback = pristine.clone();
    let case = coalesce_case_mut(
        source_having_mut(wrong_fallback.queries[0].rel.as_mut().unwrap()).unwrap(),
    );
    case.operands[2] = case.operands[1].clone();

    let mut wrong_call = pristine.clone();
    coalesce_case_mut(source_having_mut(wrong_call.queries[0].rel.as_mut().unwrap()).unwrap())
        .source_operator = Some("NULLIF".to_owned());

    let mut duplicate_binding_path = pristine.clone();
    let having =
        source_having_mut(duplicate_binding_path.queries[0].rel.as_mut().unwrap()).unwrap();
    let first_path = having
        .source_native_having
        .as_ref()
        .unwrap()
        .operand_bindings[0]
        .path
        .clone();
    having
        .source_native_having
        .as_mut()
        .unwrap()
        .operand_bindings[1]
        .path = first_path;

    let nested_query_block = find_first_scalar_subquery(pristine.queries[0].rel.as_ref().unwrap())
        .unwrap()
        .subquery_rel
        .as_ref()
        .unwrap()
        .source_query_block_id
        .clone()
        .unwrap();
    let mut borrowed_block = pristine.clone();
    source_having_mut(borrowed_block.queries[0].rel.as_mut().unwrap())
        .unwrap()
        .source_native_having
        .as_mut()
        .unwrap()
        .query_block_id = nested_query_block;

    for (label, mutation) in [
        ("wrong tested/returned leaf", wrong_leaf),
        ("wrong CASE arm order", wrong_arm_order),
        ("wrong fallback", wrong_fallback),
        ("wrong COALESCE call", wrong_call),
        ("duplicate binding path", duplicate_binding_path),
        ("borrowed nested query block", borrowed_block),
    ] {
        assert!(
            convert_raw_file(mutation).is_err(),
            "accepted expanded COALESCE HAVING {label} mutation"
        );
    }

    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_keeps_declarative_having_through_inlined_cte_aggregate() {
    fn collect_direct_aggregate_filters<'a>(
        rel: &'a CalciteRel,
        filters: &mut Vec<&'a CalciteRel>,
    ) {
        if rel.rel_type == "LogicalFilter"
            && rel.source_clause.as_deref() == Some("HAVING")
            && rel
                .inputs
                .first()
                .is_some_and(|input| input.rel_type == "LogicalAggregate")
        {
            filters.push(rel);
        }
        for input in &rel.inputs {
            collect_direct_aggregate_filters(input, filters);
        }
    }

    fn count_native_having(rel: &RelExpr) -> usize {
        match rel {
            RelExpr::NativeHaving { input, .. } => 1 + count_native_having(input),
            RelExpr::Project { input, .. }
            | RelExpr::Filter { input, .. }
            | RelExpr::Aggregate { input, .. }
            | RelExpr::Distinct { input, .. }
            | RelExpr::Sort { input, .. } => count_native_having(input),
            RelExpr::Join { left, right, .. } => {
                count_native_having(left) + count_native_having(right)
            }
            RelExpr::Set { inputs, .. } => inputs.iter().map(count_native_having).sum(),
            RelExpr::TableScan { .. } | RelExpr::Values { .. } => 0,
        }
    }

    with_large_calcite_stack(|| {
        let repo = repo_root();
        let temp = temp_dir("declarative-having-inlined-cte");
        let schema = temp.join("schema.sql");
        let query = temp.join("query.sql");
        fs::write(
            &schema,
            "create table t(k integer, j integer, v integer);\n",
        )
        .unwrap();
        fs::write(
            &query,
            r#"with results as (
             select k, j, sum(s) as total from (
               select k, j, sum(v) as s from t group by k, j
                 having sum(v) > (select sum(v) from t)
               union all
               select k, j, sum(v) as s from t group by k, j
                 having sum(v) > (select sum(v) from t)
             ) y group by k, j
           )
           select k, j, total from results
           union
           select k, null as j, sum(total) from results group by k;
            "#,
        )
        .unwrap();

        let raw = run_calcite(&repo, &schema, &query);
        let mut filters = Vec::new();
        let rel = raw.queries[0]
            .rel
            .as_ref()
            .unwrap_or_else(|| panic!("Calcite failed: {:?}", raw.queries[0].error));
        collect_direct_aggregate_filters(rel, &mut filters);
        assert!(
            filters.len() >= 4,
            "each inlined CTE copy must retain both source HAVING filters"
        );
        for filter in &filters {
            let attestation = filter
                .source_native_having
                .as_ref()
                .expect("inlined source HAVING attestation");
            assert_eq!(attestation.kind, "DECLARATIVE_HAVING");
            assert_eq!(
                filter.source_query_block_id,
                filter.inputs[0].source_query_block_id
            );
        }

        let expected = filters.len();
        let ir = convert_raw_file(raw).expect("convert inlined declarative HAVING");
        assert_eq!(count_native_having(&ir.queries[0].rel), expected);
        fs::remove_dir_all(&temp).unwrap();
    });
}

#[test]
#[ignore = "requires the Java Calcite wrapper"]
fn calcite_wrapper_closes_transformed_native_having_source_edges() {
    let repo = repo_root();
    let temp = temp_dir("native-having-source-edges");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&schema, "create table t(a integer, v integer);\n").unwrap();
    fs::write(
        &query,
        "select a from t group by a having a in (1, 2);\n\
         select a from t group by a having a between 1 and 2;\n\
         select a from t group by a having case a when 1 then true \
           when 2 then false else true end;\n\
         select a from t group by a having cast(a > 0 as boolean) is true;\n\
         select a, sum(v) from t group by a \
           having sum(v) > (select sum(v) from t);\n",
    )
    .unwrap();

    let raw = run_calcite(&repo, &schema, &query);
    assert_eq!(raw.queries.len(), 5);
    for (index, query) in raw.queries.iter().enumerate() {
        let rel = query
            .rel
            .as_ref()
            .unwrap_or_else(|| panic!("transformed HAVING {index}: {:?}", query.error));
        let having = find_first_filter(rel).expect("source HAVING Filter");
        assert_eq!(having.source_clause.as_deref(), Some("HAVING"));
        assert!(
            having.source_native_having.is_some(),
            "transformed HAVING {index} must retain declarative source authority"
        );
        let mut one = raw.clone();
        one.queries = vec![query.clone()];
        convert_raw_file(one)
            .unwrap_or_else(|error| panic!("convert transformed native HAVING {index}: {error}"));
    }
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_erases_exact_numeric_coalesce_cast_carriers() {
    fn coalesce_rex_mut(rex: &mut CalciteRex) -> Option<&mut CalciteRex> {
        if rex.kind.as_deref() == Some("CASE")
            && rex
                .source_operator
                .as_deref()
                .is_some_and(|operator| operator.eq_ignore_ascii_case("COALESCE"))
        {
            return Some(rex);
        }
        rex.operands.iter_mut().find_map(coalesce_rex_mut)
    }

    fn coalesce_rel_mut(rel: &mut CalciteRel) -> Option<&mut CalciteRex> {
        for rex in &mut rel.project_rex {
            if let Some(found) = coalesce_rex_mut(rex) {
                return Some(found);
            }
        }
        if let Some(rex) = &mut rel.condition_rex
            && let Some(found) = coalesce_rex_mut(rex)
        {
            return Some(found);
        }
        rel.inputs.iter_mut().find_map(coalesce_rel_mut)
    }

    fn ir_coalesce(rel: &RelExpr) -> Option<&logos_ir::ir::ScalarExpr> {
        match rel {
            RelExpr::Project { input, exprs, .. } => exprs
                .iter()
                .find(|expr| {
                    expr.source
                        .as_ref()
                        .and_then(|source| source.operator.as_deref())
                        .is_some_and(|operator| operator.eq_ignore_ascii_case("COALESCE"))
                })
                .or_else(|| ir_coalesce(input)),
            RelExpr::Filter { input, .. }
            | RelExpr::NativeHaving { input, .. }
            | RelExpr::Aggregate { input, .. }
            | RelExpr::Distinct { input, .. }
            | RelExpr::Sort { input, .. } => ir_coalesce(input),
            RelExpr::Join { left, right, .. } => ir_coalesce(left).or_else(|| ir_coalesce(right)),
            RelExpr::Set { inputs, .. } => inputs.iter().find_map(ir_coalesce),
            RelExpr::TableScan { .. } | RelExpr::Values { .. } => None,
        }
    }

    let repo = repo_root();
    let temp = temp_dir("numeric-coalesce-cast-carriers");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&schema, "create table t(k integer, amount decimal(7,2));\n").unwrap();
    fs::write(
        &query,
        "select coalesce(amount, 0) as n from t where amount > 50;\n\
         select k, sum(coalesce(amount, 0)) as n from t group by k \
           having sum(coalesce(amount, 0)) > 0;\n",
    )
    .unwrap();

    let mut raw = run_calcite(&repo, &schema, &query);
    let coalesce =
        coalesce_rel_mut(raw.queries[0].rel.as_mut().unwrap()).expect("generated numeric COALESCE");
    assert!(matches!(coalesce.operands.as_slice(), [_, returned, _]
        if returned.kind.as_deref() == Some("CAST")
            && returned.operands.first().is_some_and(|inner| inner.kind.as_deref() == Some("CAST"))));

    let mut forged = raw.clone();
    let returned = &mut coalesce_rel_mut(forged.queries[0].rel.as_mut().unwrap())
        .unwrap()
        .operands[1];
    returned.precision = Some(returned.precision.unwrap() + 1);
    assert!(matches!(
        convert_raw_file(forged),
        Err(logos_ir::Error::InvalidRelSourceProvenance(_))
            | Err(logos_ir::Error::InvalidScalar(_))
    ));

    let ir = convert_raw_file(raw).expect("convert exact numeric COALESCE carriers");
    assert_eq!(ir.queries.len(), 2);
    for query in &ir.queries {
        assert_eq!(
            query.output().last().unwrap().ty,
            SqlType::decimal(None, None)
        );
        let expr = ir_coalesce(&query.rel).expect("source-bound logical COALESCE");
        assert!(matches!(&expr.parsed,
            ScalarAst::Call { op: ScalarOp::Case, args, .. }
                if matches!(args.as_slice(), [_, ScalarAst::InputRef { .. }, _])));
    }
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_keeps_derived_group_key_where_as_an_ordinary_filter() {
    let repo = repo_root();
    let temp = temp_dir("derived-group-key-where-filter");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(
        &schema,
        "create table dept(deptno integer, name integer);\n",
    )
    .unwrap();
    fs::write(
        &query,
        "select t2.dname, t2.cnt from (\
           select dept0.name as dname, count(*) as cnt from dept as dept0 \
           group by dept0.name\
         ) as t2 where t2.dname = 10;\n",
    )
    .unwrap();

    let raw = run_calcite(&repo, &schema, &query);
    let filter = find_first_filter(raw.queries[0].rel.as_ref().expect("derived WHERE relation"))
        .expect("source WHERE Filter");
    assert_eq!(filter.rel_type, "LogicalFilter");
    assert_eq!(filter.source_clause.as_deref(), Some("WHERE"));
    assert!(filter.source_native_having.is_none());

    let ir = convert_raw_file(raw).expect("convert derived group-key WHERE");
    let RelExpr::Project { input, .. } = &ir.queries[0].rel else {
        panic!("expected output Project");
    };
    assert!(
        matches!(input.as_ref(), RelExpr::Filter { .. }),
        "a derived-table WHERE must remain a logical Filter"
    );

    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_removes_validator_string_cast_in_mixed_comparison() {
    let repo = repo_root();
    let temp = temp_dir("mixed-string-comparison");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&schema, "create table t(c char(2), v varchar(2));\n").unwrap();
    fs::write(&query, "select c from t where c = v;\n").unwrap();

    let ir = convert_raw_file(run_calcite(&repo, &schema, &query)).unwrap();
    let RelExpr::Project { input, .. } = &ir.queries[0].rel else {
        panic!("expected project");
    };
    let RelExpr::Filter { predicate, .. } = input.as_ref() else {
        panic!("expected filter");
    };
    assert!(matches!(
        &predicate.parsed,
        ScalarAst::Call { op: ScalarOp::Eq, args, .. }
            if matches!(args.as_slice(), [ScalarAst::InputRef { index: 0 }, ScalarAst::InputRef { index: 1 }])
    ));
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_attests_complementary_text_order_and_rejects_collate() {
    let repo = repo_root();
    let temp = temp_dir("complementary-text-order");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&schema, "create table t(s text);\n").unwrap();
    fs::write(&query, "select s from t where s < 'x' or s > 'x';\n").unwrap();

    let ir = convert_raw_file(run_calcite(&repo, &schema, &query)).unwrap();
    let RelExpr::Project { input, .. } = &ir.queries[0].rel else {
        panic!("expected project")
    };
    let RelExpr::Filter { predicate, .. } = input.as_ref() else {
        panic!("expected filter")
    };
    let ScalarAst::Call {
        op: ScalarOp::Or,
        args,
        ..
    } = &predicate.parsed
    else {
        panic!("expected complementary OR")
    };
    assert!(matches!(
        args.as_slice(),
        [
            ScalarAst::Call { op: ScalarOp::Lt, args: left, .. },
            ScalarAst::Call { op: ScalarOp::Gt, args: right, .. }
        ] if matches!(left.as_slice(), [ScalarAst::InputRef { index: 0 }, ScalarAst::Literal { raw }] if raw == "'x'")
            && matches!(right.as_slice(), [ScalarAst::InputRef { index: 0 }, ScalarAst::Literal { raw }] if raw == "'x'")
    ));

    fs::write(
        &query,
        "select s from t where s collate \"C\" < 'x' or s collate \"C\" > 'x';\n",
    )
    .unwrap();
    let collated = run_calcite(&repo, &schema, &query);
    assert!(
        collated.queries[0]
            .error
            .as_deref()
            .is_some_and(|error| error.contains("SqlParseException") && error.contains("collate")),
        "query-level COLLATE must fail before complementary-order lowering"
    );

    fs::write(&query, "select s collate \"de_DE\" from t;\n").unwrap();
    let non_default_projection = run_calcite(&repo, &schema, &query);
    assert!(
        non_default_projection.queries[0]
            .error
            .as_deref()
            .is_some_and(|error| {
                error.to_ascii_lowercase().contains("collate")
                    && (error.contains("SqlParseException")
                        || error.contains("expression-level COLLATE is not modeled"))
            }),
        "non-default projection COLLATE must fail before Rex conversion"
    );
    assert!(non_default_projection.queries[0].rel.is_none());

    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_rejects_explicit_schema_collation() {
    let repo = repo_root();
    let temp = temp_dir("explicit-collation");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&query, "select v from t;\n").unwrap();

    for declaration in [
        "v varchar(4) collate \"und-x-icu\"",
        "v text default E'x\\'y' collate \"C\"",
        "v text default $tag$($tag$ collate \"C\"",
    ] {
        fs::write(&schema, format!("create table t({declaration});\n")).unwrap();
        let diagnostic = run_calcite_failure(&repo, &schema, &query);
        assert!(
            diagnostic.contains("unsupported or malformed column-constraint tail"),
            "explicit schema constraint was not rejected for {declaration:?}: {diagnostic}"
        );
    }
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_preserves_submillisecond_timestamp_cast() {
    let repo = repo_root();
    let temp = std::env::temp_dir().join(format!(
        "logos-ir-calcite-wrapper-e2e-{}",
        std::process::id()
    ));
    if temp.exists() {
        fs::remove_dir_all(&temp).unwrap();
    }
    fs::create_dir_all(&temp).unwrap();
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&schema, "create table R(id int);\n").unwrap();
    fs::write(
        &query,
        "select cast('1970-01-01 00:00:01.123456' as timestamp(6)) as ts from R;\n",
    )
    .unwrap();

    let output = Command::new(repo.join("scripts/calcite-ir"))
        .arg("--schema")
        .arg(&schema)
        .arg("--sql")
        .arg(&query)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "calcite wrapper failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let calcite: CalciteFile = serde_json::from_slice(&output.stdout).unwrap();
    let ir = convert_raw_file(calcite).unwrap();
    let RelExpr::Project { exprs, .. } = &ir.queries[0].rel else {
        panic!("expected top-level project");
    };
    assert_eq!(
        exprs[0].parsed,
        ScalarAst::TypeAnnotation {
            expr: Box::new(ScalarAst::Call {
                operator: "CAST".to_owned(),
                op: ScalarOp::Cast,
                args: vec![ScalarAst::Literal {
                    raw: "'1970-01-01 00:00:01.123456'".to_owned()
                }]
            }),
            ty: "TIMESTAMP(6)".to_owned()
        }
    );
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_keeps_ambiguous_timestamp_inputs_on_the_source_cast_path() {
    let repo = repo_root();
    let temp = temp_dir("ambiguous-timestamp-input");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&schema, "create table t(id integer);\n").unwrap();

    fs::write(
        &query,
        "select timestamp '1970-01-01 00:00:00.123456' as ts from t;\n",
    )
    .unwrap();
    let exact = convert_raw_file(run_calcite(&repo, &schema, &query)).unwrap();
    let RelExpr::Project { exprs, .. } = &exact.queries[0].rel else {
        panic!("expected exact direct TIMESTAMP project");
    };
    assert!(matches!(
        &exprs[0].parsed,
        ScalarAst::TypeAnnotation { expr, ty }
            if ty == "TIMESTAMP(6)"
                && matches!(
                    expr.as_ref(),
                    ScalarAst::Literal { raw }
                        if raw == "1970-01-01 00:00:00.123456"
                )
    ));

    fs::write(
        &query,
        "select timestamp '01-02-03 00:00:00' as ts from t;\n",
    )
    .unwrap();
    let ambiguous_direct = convert_raw_file(run_calcite(&repo, &schema, &query)).unwrap_err();
    assert!(
        ambiguous_direct
            .to_string()
            .contains("not one exact independently parsed SQL literal"),
        "{ambiguous_direct}"
    );

    fs::write(
        &query,
        "select cast('01-02-03 00:00:00' as timestamp(6)) as ts from t;\n",
    )
    .unwrap();
    let explicit = convert_raw_file(run_calcite(&repo, &schema, &query)).unwrap();
    let RelExpr::Project { exprs, .. } = &explicit.queries[0].rel else {
        panic!("expected explicit TIMESTAMP CAST project");
    };
    assert!(matches!(
        &exprs[0].parsed,
        ScalarAst::TypeAnnotation { expr, ty }
            if ty == "TIMESTAMP(6)"
                && matches!(
                    expr.as_ref(),
                    ScalarAst::Call { op: ScalarOp::Cast, args, .. }
                        if matches!(
                            args.as_slice(),
                            [ScalarAst::Literal { raw }]
                                if raw == "'01-02-03 00:00:00'"
                        )
                )
    ));

    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_preserves_int8_to_integer_narrowing_cast() {
    let repo = repo_root();
    let temp = std::env::temp_dir().join(format!(
        "logos-ir-calcite-wrapper-int8-e2e-{}",
        std::process::id()
    ));
    if temp.exists() {
        fs::remove_dir_all(&temp).unwrap();
    }
    fs::create_dir_all(&temp).unwrap();
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&schema, "create table t(b int8);\n").unwrap();
    fs::write(&query, "select cast(b as integer) as b from t;\n").unwrap();

    let output = Command::new(repo.join("scripts/calcite-ir"))
        .arg("--schema")
        .arg(&schema)
        .arg("--sql")
        .arg(&query)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "calcite wrapper failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let calcite: CalciteFile = serde_json::from_slice(&output.stdout).unwrap();
    let ir = convert_raw_file(calcite).unwrap();
    let RelExpr::Project {
        input,
        exprs,
        output,
        ..
    } = &ir.queries[0].rel
    else {
        panic!("expected top-level project");
    };
    let RelExpr::TableScan {
        output: scan_output,
        ..
    } = input.as_ref()
    else {
        panic!("expected project over table scan");
    };
    assert_eq!(scan_output[0].ty, SqlType::BigInt);
    assert_eq!(output[0].ty, SqlType::Integer);
    assert_eq!(
        exprs[0].parsed,
        ScalarAst::TypeAnnotation {
            expr: Box::new(ScalarAst::Call {
                operator: "CAST".to_owned(),
                op: ScalarOp::Cast,
                args: vec![ScalarAst::InputRef { index: 0 }],
            }),
            ty: "INTEGER".to_owned(),
        }
    );
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_preserves_flattened_varchar_typmod() {
    let repo = repo_root();
    let temp = temp_dir("flattened-varchar");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&schema, "create table t(v varchar(4));\n").unwrap();
    fs::write(
        &query,
        "select x from (select cast(v as varchar(2)) as x from t) s;\n",
    )
    .unwrap();

    let calcite = run_calcite(&repo, &schema, &query);
    let ir = convert_raw_file(calcite).unwrap();
    let RelExpr::Project { exprs, .. } = &ir.queries[0].rel else {
        panic!("expected flattened project");
    };
    assert!(matches!(
        &exprs[0].parsed,
        ScalarAst::TypeAnnotation { ty, .. } if ty == "VARCHAR(2)"
    ));
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_rejects_unsupported_schema_default_expression() {
    let repo = repo_root();
    let temp = temp_dir("schema-default");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&schema, "create table t(v varchar default chr(65));\n").unwrap();
    fs::write(&query, "select cast(v as varchar(65)) as x from t;\n").unwrap();

    let diagnostic = run_calcite_failure(&repo, &schema, &query);
    assert!(diagnostic.contains("unsupported or malformed column-constraint tail"));
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_transports_postgres_create_table_constraints_separately() {
    let repo = repo_root();
    let temp = temp_dir("postgres-table-constraints");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(
        &schema,
        "create table tenant_scope (\n\
           id int,\n\
           region int,\n\
           alias text,\n\
           constraint tenant_scope_pk primary key (id, region),\n\
           constraint tenant_scope_alias unique (alias, region)\n\
         );\n\
         create table \"Order\" (\n\
           \"Tenant\" int constraint tenant_nn not null,\n\
           region int not null,\n\
           id int,\n\
           note text,\n\
           email text,\n\
           active boolean,\n\
           parent_category_id int,\n\
           post_action_type_id int,\n\
           constraint \"UniqueNote\" unique (note, \"Tenant\"),\n\
           constraint \"OrderPk\" primary key (id, \"Tenant\"),\n\
           constraint \"OrderCheck\" check (((note)::text <> ''::text) OR active),\n\
           constraint \"OrderTenantFk\" foreign key (\"Tenant\", region)\n\
             references tenant_scope (id, region) match simple\n\
             on delete cascade on update cascade\n\
         );\n\
         create unique index order_email_active_idx on \"Order\"\n\
           (lower((email)::text) varchar_pattern_ops, id DESC)\n\
           where (active AND (post_action_type_id = ANY (ARRAY[3, 4, 7, 8])));\n\
         create unique index order_parent_note_idx on public.\"Order\"\n\
           (COALESCE(parent_category_id, '-1'::integer), note);\n\
         create table inline_key (\n\
           \"Id\" int constraint \"InlinePk\" primary key,\n\
           payload text constraint payload_nn not null\n\
         );\n\
         create table empty_table ();\n",
    )
    .unwrap();
    fs::write(
        &query,
        "select \"Tenant\", id from \"Order\";\n\
         select id, region from tenant_scope;\n\
         select \"Id\", payload from inline_key;\n",
    )
    .unwrap();

    let raw = run_calcite(&repo, &schema, &query);
    assert_eq!(raw.schema.len(), 4);
    assert_eq!(raw.schema[0].name, "tenant_scope");
    assert_eq!(raw.schema[0].constraints.not_null, ["id", "region"]);
    assert_eq!(
        raw.schema[0].constraints.primary_key.as_ref().unwrap(),
        &vec!["id".to_owned(), "region".to_owned()]
    );
    assert_eq!(raw.schema[0].constraints.unique.len(), 1);
    assert_eq!(
        raw.schema[0].constraints.unique[0].name.as_deref(),
        Some("tenant_scope_alias")
    );
    assert_eq!(
        raw.schema[0].constraints.unique[0].columns,
        ["alias", "region"]
    );

    assert_eq!(raw.schema[1].name, "Order");
    assert_eq!(
        raw.schema[1].constraints.not_null,
        ["Tenant", "region", "id"]
    );
    assert_eq!(
        raw.schema[1].constraints.primary_key.as_ref().unwrap(),
        &vec!["id".to_owned(), "Tenant".to_owned()]
    );
    assert_eq!(raw.schema[1].constraints.unique.len(), 1);
    assert_eq!(
        raw.schema[1].constraints.unique[0].columns,
        ["note", "Tenant"]
    );
    assert_eq!(raw.schema[1].constraints.foreign_keys.len(), 1);
    let raw_foreign = &raw.schema[1].constraints.foreign_keys[0];
    assert_eq!(raw_foreign.name.as_deref(), Some("OrderTenantFk"));
    assert_eq!(raw_foreign.columns, ["Tenant", "region"]);
    assert_eq!(raw_foreign.referenced_table, "tenant_scope");
    assert_eq!(raw_foreign.referenced_columns, ["id", "region"]);
    assert_eq!(
        raw_foreign.match_type,
        logos_ir::ir::ForeignKeyMatch::Simple
    );
    assert_eq!(
        raw_foreign.referential_actions.as_deref(),
        Some("ON DELETE CASCADE ON UPDATE CASCADE")
    );
    assert_eq!(raw.schema[1].constraints.checks.len(), 1);
    assert_eq!(
        raw.schema[1].constraints.checks[0].expression,
        "((note)::text <> ''::text) OR active"
    );
    assert_eq!(raw.schema[1].constraints.unique_indexes.len(), 2);
    assert_eq!(
        raw.schema[1].constraints.unique_indexes[0].terms,
        ["lower((email)::text) varchar_pattern_ops", "id DESC"]
    );
    assert_eq!(
        raw.schema[1].constraints.unique_indexes[0]
            .predicate
            .as_deref(),
        Some("(active AND (post_action_type_id = ANY (ARRAY[3, 4, 7, 8])))")
    );
    assert_eq!(
        raw.schema[1].constraints.unique_indexes[1].terms,
        ["COALESCE(parent_category_id, '-1'::integer)", "note"]
    );
    assert!(
        raw.schema[1].constraints.unique_indexes[1]
            .predicate
            .is_none()
    );

    assert_eq!(raw.schema[2].name, "inline_key");
    assert_eq!(raw.schema[2].constraints.not_null, ["Id", "payload"]);
    assert_eq!(
        raw.schema[2].constraints.primary_key.as_ref().unwrap(),
        &vec!["Id".to_owned()]
    );
    assert!(raw.schema[3].columns.is_empty());
    assert!(raw.schema[3].constraints.is_empty());
    assert!(raw.queries.iter().all(|query| {
        query.rel.as_ref().is_some_and(|rel| {
            !rel.row_type.is_empty() && rel.row_type.iter().all(|field| field.nullable)
        })
    }));

    let ir = convert_raw_file(raw).unwrap();
    assert_eq!(ir.schema.tables[0].constraints.not_null, ["id", "region"]);
    assert_eq!(
        ir.schema.tables[0]
            .constraints
            .primary_key
            .as_ref()
            .unwrap(),
        &vec!["id".to_owned(), "region".to_owned()]
    );
    assert_eq!(ir.schema.tables[1].constraints.unique.len(), 1);
    assert_eq!(ir.schema.tables[1].constraints.foreign_keys.len(), 1);
    assert_eq!(ir.schema.tables[1].constraints.checks.len(), 1);
    assert!(matches!(
        ir.schema.tables[1].constraints.checks[0].expression,
        logos_ir::ir::IntegrityPredicate::Or { .. }
    ));
    assert_eq!(
        ir.schema.tables[1].constraints.checks[0].source_sql,
        "((note)::text <> ''::text) OR active"
    );
    assert_eq!(ir.schema.tables[1].constraints.unique_indexes.len(), 2);
    let typed_expression_index = &ir.schema.tables[1].constraints.unique_indexes[0];
    assert!(matches!(
        typed_expression_index.terms[0].expression,
        logos_ir::ir::IntegrityValueExpr::Lower { .. }
    ));
    assert_eq!(
        typed_expression_index.terms[0].operator_class.as_deref(),
        Some("varchar_pattern_ops")
    );
    assert_eq!(
        typed_expression_index.terms[1].direction,
        logos_ir::ir::IntegritySortDirection::Desc
    );
    assert!(typed_expression_index.predicate.is_some());
    assert_eq!(
        typed_expression_index.predicate_sql.as_deref(),
        Some("(active AND (post_action_type_id = ANY (ARRAY[3, 4, 7, 8])))")
    );
    assert!(matches!(
        ir.schema.tables[1].constraints.unique_indexes[1].terms[0].expression,
        logos_ir::ir::IntegrityValueExpr::Coalesce { .. }
    ));
    assert_eq!(
        ir.schema.tables[2]
            .constraints
            .primary_key
            .as_ref()
            .unwrap(),
        &vec!["Id".to_owned()]
    );
    assert!(
        ir.schema
            .tables
            .iter()
            .flat_map(|table| &table.columns)
            .all(|column| column.nullable)
    );
    assert!(
        ir.queries
            .iter()
            .flat_map(|query| query.output())
            .all(|column| column.nullable)
    );
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_accepts_quoted_keywords_and_postgres_identifier_boundaries() {
    let repo = repo_root();
    let temp = temp_dir("postgres-schema-identifier-boundaries");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    let ascii_relation = "r".repeat(63);
    let ascii_column = "c".repeat(63);
    let ascii_index = "i".repeat(63);
    let multibyte_relation = format!("{}r", "é".repeat(31));
    let multibyte_column = format!("{}c", "é".repeat(31));
    let multibyte_index = format!("{}i", "é".repeat(31));
    assert_eq!(ascii_relation.len(), 63);
    assert_eq!(multibyte_relation.len(), 63);

    fs::write(
        &schema,
        format!(
            "CREATE TABLE {ascii_relation} (\n\
               {ascii_column} int,\n\
               CONSTRAINT {ascii_index} UNIQUE ({ascii_column})\n\
             );\n\
             CREATE TABLE \"{multibyte_relation}\" (\n\
               \"{multibyte_column}\" int,\n\
               CONSTRAINT \"{multibyte_index}\" UNIQUE (\"{multibyte_column}\")\n\
             );\n\
             CREATE TABLE \"select\" (\n\
               \"authorization\" int,\n\
               CONSTRAINT \"cross\" PRIMARY KEY (\"authorization\")\n\
             );\n\
             CREATE TABLE named_not_null (\n\
               a int CONSTRAINT shared NOT NULL,\n\
               b int CONSTRAINT shared NOT NULL,\n\
               c int CONSTRAINT same NOT NULL CONSTRAINT same PRIMARY KEY\n\
             );\n"
        ),
    )
    .unwrap();
    fs::write(&query, "SELECT 1;\n").unwrap();

    let raw = run_calcite(&repo, &schema, &query);
    assert_eq!(raw.schema.len(), 4);
    assert_eq!(raw.schema[0].name, ascii_relation);
    assert_eq!(raw.schema[0].columns[0].name, ascii_column);
    assert_eq!(raw.schema[1].name, multibyte_relation);
    assert_eq!(raw.schema[1].columns[0].name, multibyte_column);
    assert_eq!(raw.schema[2].name, "select");
    assert_eq!(raw.schema[2].columns[0].name, "authorization");
    assert_eq!(raw.schema[3].constraints.not_null, ["a", "b", "c"]);
    assert_eq!(
        raw.schema[3].constraints.primary_key.as_ref().unwrap(),
        &["c".to_owned()]
    );
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_accepts_only_the_closed_postgres_schema_type_matrix() {
    let repo = repo_root();
    let temp = temp_dir("closed-postgres-schema-type-matrix");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    let unspecified = i32::MIN;
    let cases = [
        ("TEXT", "VARCHAR", "VARCHAR", -1, unspecified),
        ("BPCHAR", "CHAR", "CHAR", -1, unspecified),
        ("BOOLEAN", "BOOLEAN", "BOOLEAN", -1, unspecified),
        ("BOOL", "BOOLEAN", "BOOLEAN", -1, unspecified),
        ("DATE", "DATE", "DATE", -1, unspecified),
        ("BIGINT", "BIGINT", "BIGINT", -1, unspecified),
        ("INT8", "BIGINT", "BIGINT", -1, unspecified),
        ("INT", "INTEGER", "INTEGER", -1, unspecified),
        ("INTEGER", "INTEGER", "INTEGER", -1, unspecified),
        ("REAL", "FLOAT", "FLOAT", -1, unspecified),
        ("FLOAT4", "FLOAT", "FLOAT", -1, unspecified),
        ("FLOAT8", "DOUBLE", "DOUBLE", -1, unspecified),
        ("VARCHAR", "VARCHAR", "VARCHAR", -1, unspecified),
        ("VARCHAR(7)", "VARCHAR", "VARCHAR(7)", 7, unspecified),
        ("CHAR", "CHAR", "CHAR", -1, unspecified),
        ("CHAR(7)", "CHAR", "CHAR(7)", 7, unspecified),
        ("CHARACTER", "CHAR", "CHAR", -1, unspecified),
        ("CHARACTER(7)", "CHAR", "CHAR(7)", 7, unspecified),
        ("CHARACTER VARYING", "VARCHAR", "VARCHAR", -1, unspecified),
        (
            "CHARACTER VARYING(7)",
            "VARCHAR",
            "VARCHAR(7)",
            7,
            unspecified,
        ),
        ("DECIMAL", "DECIMAL", "DECIMAL", -1, unspecified),
        ("DECIMAL(7)", "DECIMAL", "DECIMAL(7)", 7, unspecified),
        ("DECIMAL(7,2)", "DECIMAL", "DECIMAL(7, 2)", 7, 2),
        ("NUMERIC", "DECIMAL", "DECIMAL", -1, unspecified),
        ("NUMERIC(7)", "DECIMAL", "DECIMAL(7)", 7, unspecified),
        ("NUMERIC(7,0)", "DECIMAL", "DECIMAL(7, 0)", 7, 0),
        ("FLOAT", "DOUBLE", "DOUBLE", -1, unspecified),
        ("FLOAT(1)", "FLOAT", "FLOAT", -1, unspecified),
        ("FLOAT(24)", "FLOAT", "FLOAT", -1, unspecified),
        ("FLOAT(25)", "DOUBLE", "DOUBLE", -1, unspecified),
        ("FLOAT(53)", "DOUBLE", "DOUBLE", -1, unspecified),
        ("DOUBLE PRECISION", "DOUBLE", "DOUBLE", -1, unspecified),
        ("TIME", "TIME", "TIME", -1, unspecified),
        ("TIME(0)", "TIME", "TIME(0)", 0, unspecified),
        ("TIME(6)", "TIME", "TIME(6)", 6, unspecified),
        ("TIMESTAMP", "TIMESTAMP", "TIMESTAMP(6)", 6, unspecified),
        ("TIMESTAMP(0)", "TIMESTAMP", "TIMESTAMP(0)", 0, unspecified),
        ("TIMESTAMP(6)", "TIMESTAMP", "TIMESTAMP(6)", 6, unspecified),
        (
            "TIMESTAMP WITH TIME ZONE",
            "TIMESTAMP_WITH_TIME_ZONE",
            "TIMESTAMP_WITH_TIME_ZONE(6)",
            6,
            unspecified,
        ),
        (
            "TIMESTAMP(3) WITH TIME ZONE",
            "TIMESTAMP_WITH_TIME_ZONE",
            "TIMESTAMP_WITH_TIME_ZONE(3)",
            3,
            unspecified,
        ),
        (
            "TIMESTAMP WITHOUT TIME ZONE",
            "TIMESTAMP",
            "TIMESTAMP(6)",
            6,
            unspecified,
        ),
        (
            "TIMESTAMP(3) WITHOUT TIME ZONE",
            "TIMESTAMP",
            "TIMESTAMP(3)",
            3,
            unspecified,
        ),
        (
            "TIMESTAMPTZ",
            "TIMESTAMP_WITH_TIME_ZONE",
            "TIMESTAMP_WITH_TIME_ZONE(6)",
            6,
            unspecified,
        ),
        (
            "TIMESTAMPTZ(3)",
            "TIMESTAMP_WITH_TIME_ZONE",
            "TIMESTAMP_WITH_TIME_ZONE(3)",
            3,
            unspecified,
        ),
    ];
    let columns = cases
        .iter()
        .enumerate()
        .map(|(index, (declared, ..))| format!("c{index} {declared}"))
        .collect::<Vec<_>>()
        .join(",\n");
    fs::write(&schema, format!("CREATE TABLE t(\n{columns}\n);\n")).unwrap();
    fs::write(&query, "SELECT 1;\n").unwrap();

    let raw = run_calcite(&repo, &schema, &query);
    assert_eq!(raw.schema.len(), 1);
    assert_eq!(raw.schema[0].columns.len(), cases.len());
    for (column, (declared, ty, full_type, precision, scale)) in
        raw.schema[0].columns.iter().zip(cases)
    {
        assert_eq!(
            column.declared_type.as_deref(),
            Some(declared),
            "{declared}"
        );
        assert_eq!(column.ty, ty, "{declared}");
        assert_eq!(column.full_type.as_deref(), Some(full_type), "{declared}");
        assert_eq!(column.precision, Some(precision), "{declared}");
        assert_eq!(column.scale, Some(scale), "{declared}");
    }
    fs::remove_dir_all(temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_rejects_ambiguous_or_malformed_create_table_constraints() {
    let repo = repo_root();
    let temp = temp_dir("invalid-postgres-table-constraints");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&query, "select 1;\n").unwrap();

    for (label, ddl, expected) in [
        (
            "leading-string-garbage",
            "'garbage'; CREATE TABLE t(a int);",
            "unsupported or unconsumed schema statement",
        ),
        (
            "leading-dollar-garbage",
            "$x$garbage$x$; CREATE TABLE t(a int);",
            "unsupported or unconsumed schema statement",
        ),
        (
            "leading-quoted-garbage",
            "\"garbage\"; CREATE TABLE t(a int);",
            "unsupported or unconsumed schema statement",
        ),
        (
            "leading-backtick-garbage",
            "`garbage`; CREATE TABLE t(a int);",
            "unsupported or unconsumed schema statement",
        ),
        (
            "leading-bracket-garbage",
            "[garbage]; CREATE TABLE t(a int);",
            "unsupported or unconsumed schema statement",
        ),
        (
            "trailing-comma",
            "CREATE TABLE t(a int,);",
            "empty entry in CREATE TABLE",
        ),
        (
            "leading-comma",
            "CREATE TABLE t(,a int);",
            "empty entry in CREATE TABLE",
        ),
        (
            "double-comma",
            "CREATE TABLE t(a int,,b int);",
            "empty entry in CREATE TABLE",
        ),
        (
            "duplicate-column",
            "create table t(a int, A int);",
            "duplicate PostgreSQL column identity",
        ),
        (
            "hyphenated-bare-column",
            "CREATE TABLE t(a-b int);",
            "invalid PostgreSQL column identifier",
        ),
        (
            "empty-quoted-column",
            "CREATE TABLE t(\"\" int);",
            "schema identifiers must not be empty",
        ),
        (
            "backtick-column",
            "CREATE TABLE t(`a` int);",
            "invalid PostgreSQL column identifier",
        ),
        (
            "bracket-column",
            "CREATE TABLE t([a] int);",
            "invalid PostgreSQL column identifier",
        ),
        (
            "duplicate-not-null",
            "CREATE TABLE t(a int NOT NULL NOT NULL);",
            "duplicate inline NOT NULL declaration",
        ),
        (
            "not-null-garbage-tail",
            "CREATE TABLE t(a int NOT NULL garbage);",
            "unsupported or malformed column-constraint tail",
        ),
        (
            "dangling-named-inline",
            "CREATE TABLE t(a int CONSTRAINT c);",
            "named inline constraints support only NOT NULL and PRIMARY KEY",
        ),
        (
            "nonsensical-named-inline",
            "CREATE TABLE t(a int CONSTRAINT c garbage);",
            "named inline constraints support only NOT NULL and PRIMARY KEY",
        ),
        (
            "empty-named-inline",
            "CREATE TABLE t(a int CONSTRAINT \"\" NOT NULL);",
            "schema identifiers must not be empty",
        ),
        (
            "reserved-r-relation-name",
            "CREATE TABLE select(a int);",
            "reserved keyword requires identifier quoting",
        ),
        (
            "reserved-t-relation-name",
            "CREATE TABLE authorization(a int);",
            "reserved keyword requires identifier quoting",
        ),
        (
            "reserved-r-column-name",
            "CREATE TABLE t(select int);",
            "reserved keyword requires identifier quoting",
        ),
        (
            "reserved-t-column-name",
            "CREATE TABLE t(authorization int);",
            "reserved keyword requires identifier quoting",
        ),
        (
            "reserved-r-table-constraint-name",
            "CREATE TABLE t(a int, CONSTRAINT select UNIQUE(a));",
            "reserved keyword requires identifier quoting",
        ),
        (
            "reserved-t-inline-constraint-name",
            "CREATE TABLE t(a int CONSTRAINT authorization PRIMARY KEY);",
            "reserved keyword requires identifier quoting",
        ),
        (
            "reserved-r-key-reference",
            "CREATE TABLE t(a int, PRIMARY KEY(select));",
            "reserved keyword requires identifier quoting",
        ),
        (
            "reserved-t-key-reference",
            "CREATE TABLE t(a int, UNIQUE(authorization));",
            "reserved keyword requires identifier quoting",
        ),
        (
            "unsupported-default",
            "CREATE TABLE t(a text DEFAULT 'x');",
            "unsupported or malformed column-constraint tail",
        ),
        (
            "incomplete-default",
            "CREATE TABLE t(a text DEFAULT);",
            "unsupported or malformed column-constraint tail",
        ),
        (
            "unsupported-check",
            "CREATE TABLE t(a int CHECK (a > 0));",
            "unsupported or malformed column-constraint tail",
        ),
        (
            "incomplete-check",
            "CREATE TABLE t(a int CHECK);",
            "unsupported or malformed column-constraint tail",
        ),
        (
            "unsupported-collate",
            "CREATE TABLE t(a text COLLATE \"C\");",
            "unsupported or malformed column-constraint tail",
        ),
        (
            "unsupported-generated",
            "CREATE TABLE t(a int GENERATED ALWAYS AS IDENTITY);",
            "unsupported or malformed column-constraint tail",
        ),
        (
            "unsupported-references",
            "CREATE TABLE p(id int); CREATE TABLE t(a int REFERENCES p(id));",
            "unsupported or malformed column-constraint tail",
        ),
        (
            "unsupported-inline-unique",
            "CREATE TABLE t(a int UNIQUE);",
            "unsupported or malformed column-constraint tail",
        ),
        (
            "non-postgres-any-type",
            "CREATE TABLE t(a ANY);",
            "unsupported or malformed PostgreSQL column type",
        ),
        (
            "non-postgres-string-type",
            "CREATE TABLE t(a STRING);",
            "unsupported or malformed PostgreSQL column type",
        ),
        (
            "non-postgres-tinyint-type",
            "CREATE TABLE t(a TINYINT);",
            "unsupported or malformed PostgreSQL column type",
        ),
        (
            "unsupported-smallint-type",
            "CREATE TABLE t(a SMALLINT);",
            "unsupported or malformed PostgreSQL column type",
        ),
        (
            "non-postgres-datetime-type",
            "CREATE TABLE t(a DATETIME);",
            "unsupported or malformed PostgreSQL column type",
        ),
        (
            "non-postgres-timestampz-type",
            "CREATE TABLE t(a TIMESTAMPZ);",
            "unsupported or malformed PostgreSQL column type",
        ),
        (
            "non-postgres-plain-double-type",
            "CREATE TABLE t(a DOUBLE);",
            "unsupported or malformed PostgreSQL column type",
        ),
        (
            "non-postgres-local-timestamp-type",
            "CREATE TABLE t(a TIMESTAMP WITH LOCAL TIME ZONE);",
            "unsupported or malformed PostgreSQL column type",
        ),
        (
            "text-prefix-is-not-a-type",
            "CREATE TABLE t(a TEXTUAL);",
            "unsupported or malformed PostgreSQL column type",
        ),
        (
            "integer-prefix-is-not-a-type",
            "CREATE TABLE t(a INTERRUPT);",
            "unsupported or malformed PostgreSQL column type",
        ),
        (
            "boolean-prefix-is-not-a-type",
            "CREATE TABLE t(a BOOLISH);",
            "unsupported or malformed PostgreSQL column type",
        ),
        (
            "timestamp-prefix-is-not-a-type",
            "CREATE TABLE t(a TIMESTAMPTZONED);",
            "unsupported or malformed PostgreSQL column type",
        ),
        (
            "fixed-float-alias-cannot-take-a-modifier",
            "CREATE TABLE t(a FLOAT8(4));",
            "unsupported or malformed PostgreSQL column type",
        ),
        (
            "fixed-integer-alias-cannot-take-a-modifier",
            "CREATE TABLE t(a SMALLINT(2));",
            "unsupported or malformed PostgreSQL column type",
        ),
        (
            "double-precision-cannot-take-a-modifier",
            "CREATE TABLE t(a DOUBLE PRECISION(2));",
            "unsupported or malformed PostgreSQL column type",
        ),
        (
            "time-without-time-zone-is-outside-the-closed-grammar",
            "CREATE TABLE t(a TIME WITHOUT TIME ZONE);",
            "unsupported or malformed PostgreSQL column type",
        ),
        (
            "float-zero-precision",
            "CREATE TABLE t(a FLOAT(0));",
            "FLOAT precision must be between 1 and 53",
        ),
        (
            "float-excess-precision",
            "CREATE TABLE t(a FLOAT(54));",
            "FLOAT precision must be between 1 and 53",
        ),
        (
            "timestamp-excess-precision",
            "CREATE TABLE t(a TIMESTAMP(7));",
            "temporal precision must be between 0 and 6",
        ),
        (
            "time-excess-precision",
            "CREATE TABLE t(a TIME(7));",
            "temporal precision must be between 0 and 6",
        ),
        (
            "varchar-zero-length",
            "CREATE TABLE t(a VARCHAR(0));",
            "character length must be between 1 and 10485760",
        ),
        (
            "char-zero-length",
            "CREATE TABLE t(a CHAR(0));",
            "character length must be between 1 and 10485760",
        ),
        (
            "numeric-zero-precision",
            "CREATE TABLE t(a NUMERIC(0));",
            "NUMERIC precision must be between 1 and 1000",
        ),
        (
            "numeric-excess-precision",
            "CREATE TABLE t(a NUMERIC(1001));",
            "NUMERIC precision must be between 1 and 1000",
        ),
        (
            "numeric-excess-scale",
            "CREATE TABLE t(a NUMERIC(1, 1001));",
            "NUMERIC scale must be between 0 and 1000",
        ),
        (
            "numeric-negative-scale",
            "CREATE TABLE t(a NUMERIC(7, -2));",
            "unsupported or malformed PostgreSQL column type",
        ),
        (
            "numeric-explicit-plus-scale",
            "CREATE TABLE t(a NUMERIC(7, +2));",
            "unsupported or malformed PostgreSQL column type",
        ),
        (
            "numeric-negative-excess-scale",
            "CREATE TABLE t(a NUMERIC(1, -1001));",
            "unsupported or malformed PostgreSQL column type",
        ),
        (
            "numeric-explicit-sentinel-scale",
            "CREATE TABLE t(a NUMERIC(1, -2147483648));",
            "unsupported or malformed PostgreSQL column type",
        ),
        (
            "empty-primary-key",
            "create table t(a int, primary key ());",
            "PRIMARY KEY entries must be PostgreSQL column identifiers",
        ),
        (
            "duplicate-primary-key-column",
            "create table t(a int, primary key (a, a));",
            "duplicate PRIMARY KEY column",
        ),
        (
            "unknown-primary-key-column",
            "create table t(a int, primary key (missing));",
            "names unknown column",
        ),
        (
            "multiple-primary-keys",
            "create table t(a int primary key, b int, primary key (b));",
            "multiple primary-key declarations",
        ),
        (
            "table-primary-key-tail",
            "create table t(a int, primary key (a) garbage);",
            "unsupported trailing PRIMARY KEY syntax",
        ),
        (
            "inline-primary-key-tail",
            "create table t(a int primary key garbage);",
            "unsupported or malformed column-constraint tail",
        ),
        (
            "malformed-not-null",
            "create table t(a int not maybe);",
            "malformed inline NOT NULL declaration",
        ),
        (
            "dangling-table-constraint",
            "CREATE TABLE t(a int, CONSTRAINT c);",
            "unsupported table constraint",
        ),
        (
            "unique-garbage",
            "CREATE TABLE t(a int, UNIQUE garbage);",
            "UNIQUE is missing its parenthesized column list",
        ),
        (
            "unique-empty-list",
            "CREATE TABLE t(a int, UNIQUE ());",
            "UNIQUE entries must be PostgreSQL column identifiers",
        ),
        (
            "unique-unknown-column",
            "CREATE TABLE t(a int, UNIQUE (missing));",
            "UNIQUE for table t names unknown column",
        ),
        (
            "unique-duplicate-column",
            "CREATE TABLE t(a int, UNIQUE (a, a));",
            "duplicate UNIQUE column",
        ),
        (
            "unique-trailing-syntax",
            "CREATE TABLE t(a int, UNIQUE (a) garbage);",
            "unsupported trailing UNIQUE syntax",
        ),
        (
            "unique-list-trailing-comma",
            "CREATE TABLE t(a int, UNIQUE (a,));",
            "UNIQUE entries must be PostgreSQL column identifiers",
        ),
        (
            "unique-list-leading-comma",
            "CREATE TABLE t(a int, UNIQUE (,a));",
            "UNIQUE entries must be PostgreSQL column identifiers",
        ),
        (
            "unique-list-double-comma",
            "CREATE TABLE t(a int, b int, UNIQUE (a,,b));",
            "UNIQUE entries must be PostgreSQL column identifiers",
        ),
        (
            "unique-empty-quoted-column",
            "CREATE TABLE t(a int, UNIQUE (\"\"));",
            "schema identifiers must not be empty",
        ),
        (
            "unsupported-table-check",
            "CREATE TABLE t(a int, CHECK (a > 0));",
            "unsupported integrity-expression token >",
        ),
        (
            "unsupported-foreign-key-match-full",
            "CREATE TABLE p(id int PRIMARY KEY); \
             CREATE TABLE t(a int, FOREIGN KEY (a) REFERENCES p(id) MATCH FULL);",
            "only PostgreSQL MATCH SIMPLE foreign keys are supported",
        ),
        (
            "foreign-key-references-non-unique-key",
            "CREATE TABLE p(id int); \
             CREATE TABLE t(a int, FOREIGN KEY (a) REFERENCES p(id));",
            "references non-unique key",
        ),
        (
            "unsupported-unique-index-operator-class",
            "CREATE TABLE t(a text); \
             CREATE UNIQUE INDEX t_idx ON t(a text_pattern_ops);",
            "unsupported PostgreSQL unique-index operator class",
        ),
        (
            "unsupported-partial-index-predicate",
            "CREATE TABLE t(a int); \
             CREATE UNIQUE INDEX t_idx ON t(a) WHERE a > 0;",
            "unsupported integrity-expression token >",
        ),
        (
            "duplicate-named-table-constraint",
            "CREATE TABLE t(a int, CONSTRAINT c UNIQUE (a), CONSTRAINT c PRIMARY KEY (a));",
            "duplicate named table constraint",
        ),
        (
            "table-versus-inline-primary-key-index-name",
            "CREATE TABLE idx(a int CONSTRAINT idx PRIMARY KEY);",
            "relation namespace collision",
        ),
        (
            "table-versus-table-unique-index-name",
            "CREATE TABLE idx(a int, CONSTRAINT idx UNIQUE(a));",
            "relation namespace collision",
        ),
        (
            "earlier-table-versus-later-index-name",
            "CREATE TABLE idx(a int); CREATE TABLE t(a int, CONSTRAINT IDX UNIQUE(a));",
            "relation namespace collision",
        ),
        (
            "earlier-index-name-versus-later-table",
            "CREATE TABLE t(a int, CONSTRAINT idx UNIQUE(a)); CREATE TABLE IDX(a int);",
            "duplicate PostgreSQL relation identity",
        ),
        (
            "table-index-names-across-tables",
            "CREATE TABLE t(a int, CONSTRAINT idx UNIQUE(a)); \
             CREATE TABLE u(a int, CONSTRAINT IDX PRIMARY KEY(a));",
            "relation namespace collision",
        ),
        (
            "inline-and-table-index-name-collision",
            "CREATE TABLE t(a int CONSTRAINT idx PRIMARY KEY, b int, \
             CONSTRAINT IDX UNIQUE(b));",
            "relation namespace collision",
        ),
        (
            "inline-index-names-across-tables",
            "CREATE TABLE t(a int CONSTRAINT idx PRIMARY KEY); \
             CREATE TABLE u(a int CONSTRAINT IDX PRIMARY KEY);",
            "relation namespace collision",
        ),
        (
            "qualified-create-table",
            "create table public.t(a int);",
            "schema-qualified CREATE TABLE names are not supported",
        ),
        (
            "alter-table-primary-key",
            "create table t(a int); alter table t add primary key (a);",
            "ALTER TABLE schema mutations are not supported",
        ),
        (
            "partitioned-table",
            "create table t(a int) partition by hash (a);",
            "unsupported trailing CREATE TABLE clause",
        ),
        (
            "inherited-table",
            "create table parent(a int); create table child() inherits (parent);",
            "unsupported trailing CREATE TABLE clause",
        ),
        (
            "table-access-method",
            "create table t(a int) using heap;",
            "unsupported trailing CREATE TABLE clause",
        ),
        (
            "create-index",
            "create table t(a int); create index t_a_idx on t(a);",
            "unsupported or unconsumed schema statement",
        ),
    ] {
        fs::write(&schema, format!("{ddl}\n")).unwrap();
        let diagnostics = run_calcite_failure(&repo, &schema, &query);
        assert!(
            diagnostics.contains(expected),
            "{label}: expected {expected:?}\noutput:\n{diagnostics}"
        );
    }

    let ascii_64 = "a".repeat(64);
    let multibyte_64 = "é".repeat(32);
    let invalid_identifiers = vec![
        (
            "64-byte-ascii-relation",
            format!("CREATE TABLE {ascii_64}(a int);"),
            "exceeds the 63-byte limit",
        ),
        (
            "64-byte-ascii-column",
            format!("CREATE TABLE t({ascii_64} int);"),
            "exceeds the 63-byte limit",
        ),
        (
            "64-byte-ascii-table-constraint",
            format!("CREATE TABLE t(a int, CONSTRAINT {ascii_64} UNIQUE(a));"),
            "exceeds the 63-byte limit",
        ),
        (
            "64-byte-ascii-inline-constraint",
            format!("CREATE TABLE t(a int CONSTRAINT {ascii_64} PRIMARY KEY);"),
            "exceeds the 63-byte limit",
        ),
        (
            "64-byte-ascii-key-reference",
            format!("CREATE TABLE t(a int, PRIMARY KEY({ascii_64}));"),
            "exceeds the 63-byte limit",
        ),
        (
            "64-byte-multibyte-relation",
            format!("CREATE TABLE \"{multibyte_64}\"(a int);"),
            "exceeds the 63-byte limit",
        ),
        (
            "64-byte-multibyte-column",
            format!("CREATE TABLE t(\"{multibyte_64}\" int);"),
            "exceeds the 63-byte limit",
        ),
        (
            "64-byte-multibyte-table-constraint",
            format!("CREATE TABLE t(a int, CONSTRAINT \"{multibyte_64}\" UNIQUE(a));"),
            "exceeds the 63-byte limit",
        ),
        (
            "64-byte-multibyte-inline-constraint",
            format!("CREATE TABLE t(a int CONSTRAINT \"{multibyte_64}\" PRIMARY KEY);"),
            "exceeds the 63-byte limit",
        ),
        (
            "64-byte-multibyte-key-reference",
            format!("CREATE TABLE t(a int, PRIMARY KEY(\"{multibyte_64}\"));"),
            "exceeds the 63-byte limit",
        ),
        (
            "nul-relation",
            "CREATE TABLE \"a\0b\"(a int);".to_owned(),
            "must not contain NUL",
        ),
        (
            "nul-column",
            "CREATE TABLE t(\"a\0b\" int);".to_owned(),
            "must not contain NUL",
        ),
        (
            "nul-table-constraint",
            "CREATE TABLE t(a int, CONSTRAINT \"a\0b\" UNIQUE(a));".to_owned(),
            "must not contain NUL",
        ),
        (
            "nul-inline-constraint",
            "CREATE TABLE t(a int CONSTRAINT \"a\0b\" PRIMARY KEY);".to_owned(),
            "must not contain NUL",
        ),
        (
            "nul-key-reference",
            "CREATE TABLE t(a int, PRIMARY KEY(\"a\0b\"));".to_owned(),
            "must not contain NUL",
        ),
    ];
    for (label, ddl, expected) in invalid_identifiers {
        fs::write(&schema, format!("{ddl}\n")).unwrap();
        let diagnostics = run_calcite_failure(&repo, &schema, &query);
        assert!(
            diagnostics.contains(expected),
            "{label}: expected {expected:?}\noutput:\n{diagnostics}"
        );
    }
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_excludes_comments_from_declared_typmod() {
    let repo = repo_root();
    let temp = temp_dir("schema-comments");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(
        &schema,
        "create table t(\n  block varchar /* note (64) */,\n  line varchar -- note (63)\n);\n",
    )
    .unwrap();
    fs::write(
        &query,
        "select cast(block as varchar(64)) as block, cast(line as varchar(63)) as line from t;\n",
    )
    .unwrap();

    let calcite = run_calcite(&repo, &schema, &query);
    assert!(calcite.schema[0].columns.iter().all(|column| {
        column
            .declared_type
            .as_deref()
            .is_some_and(|ty| ty.eq_ignore_ascii_case("VARCHAR"))
    }));
    let ir = convert_raw_file(calcite).unwrap();
    let RelExpr::Project { exprs, .. } = &ir.queries[0].rel else {
        panic!("expected project");
    };
    assert!(matches!(
        &exprs[0].parsed,
        ScalarAst::TypeAnnotation { ty, .. } if ty == "VARCHAR(64)"
    ));
    assert!(matches!(
        &exprs[1].parsed,
        ScalarAst::TypeAnnotation { ty, .. } if ty == "VARCHAR(63)"
    ));
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_preserves_timestamp_cast_across_schema_comment() {
    let repo = repo_root();
    let temp = temp_dir("schema-timestamp-comment");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&schema, "create table t(ts timestamp /* note (0) */);\n").unwrap();
    fs::write(
        &query,
        "select x from (select cast(ts as timestamp(0)) as x from t) s;\n",
    )
    .unwrap();

    let calcite = run_calcite(&repo, &schema, &query);
    assert!(
        calcite.schema[0].columns[0]
            .declared_type
            .as_deref()
            .is_some_and(|ty| ty.eq_ignore_ascii_case("TIMESTAMP"))
    );
    let ir = convert_raw_file(calcite).unwrap();
    let RelExpr::Project { exprs, .. } = &ir.queries[0].rel else {
        panic!("expected flattened project");
    };
    assert!(matches!(
        &exprs[0].parsed,
        ScalarAst::TypeAnnotation { ty, .. } if ty == "TIMESTAMP(0)"
    ));
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_rejects_unknown_schema_type_tail() {
    let repo = repo_root();
    let temp = temp_dir("schema-malformed-tail");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&schema, "create table t(v varchar dfault chr(65));\n").unwrap();
    fs::write(&query, "select cast(v as varchar(65)) as x from t;\n").unwrap();

    let diagnostic = run_calcite_failure(&repo, &schema, &query);
    assert!(diagnostic.contains("unsupported or malformed PostgreSQL column type"));
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_recovers_flattened_exact_timestamp_literal() {
    let repo = repo_root();
    let temp = temp_dir("flattened-timestamp");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&schema, "create table t(v integer);\n").unwrap();
    fs::write(
        &query,
        "select x from (select cast('1970-01-01 00:00:01.123456' as timestamp(6)) as x from t) s;\n",
    )
    .unwrap();

    let ir = convert_raw_file(run_calcite(&repo, &schema, &query)).unwrap();
    let RelExpr::Project { exprs, .. } = &ir.queries[0].rel else {
        panic!("expected flattened project");
    };
    assert!(matches!(
        &exprs[0].parsed,
        ScalarAst::TypeAnnotation { expr, ty }
            if ty == "TIMESTAMP(6)"
                && matches!(
                    expr.as_ref(),
                    ScalarAst::Call { op: ScalarOp::Cast, args, .. }
                        if matches!(
                            args.as_slice(),
                            [ScalarAst::Literal { raw }]
                                if raw == "'1970-01-01 00:00:01.123456'"
                        )
                )
    ));
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_preserves_postgres_time_microseconds() {
    let repo = repo_root();
    let temp = temp_dir("time-microseconds");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&schema, "create table t(id integer);\n").unwrap();
    fs::write(
        &query,
        "select time '12:34:56.123456' as exact_time from t;\n",
    )
    .unwrap();

    let raw = run_calcite(&repo, &schema, &query);
    let project = raw.queries[0].rel.as_ref().expect("TIME query relation");
    let literal = &project.project_rex[0];
    assert_eq!(literal.ty.as_deref(), Some("TIME"));
    assert_eq!(literal.precision, Some(6));
    assert_eq!(literal.time_literal.as_deref(), Some("12:34:56.123456"));
    assert_eq!(
        literal.source_sql.as_deref(),
        Some("TIME '12:34:56.123456'")
    );

    let ir = convert_raw_file(raw).expect("convert exact PostgreSQL TIME literal");
    let RelExpr::Project { exprs, .. } = &ir.queries[0].rel else {
        panic!("expected TIME projection");
    };
    assert!(matches!(
        &exprs[0].parsed,
        ScalarAst::TypeAnnotation { expr, ty }
            if ty == "TIME(6)"
                && matches!(expr.as_ref(), ScalarAst::Literal { raw } if raw == "12:34:56.123456")
    ));
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_maps_only_exact_direct_between_and_not_in_expansions() {
    let repo = repo_root();
    let temp = temp_dir("direct-between-and-not-in-expansions");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&schema, "create table t(a integer, b integer);\n").unwrap();
    fs::write(
        &query,
        "select * from t where a = 0 or b between 25 and 54;\n",
    )
    .unwrap();

    let raw = run_calcite(&repo, &schema, &query);
    let condition = first_condition_rex(raw.queries[0].rel.as_ref().unwrap());
    let between = find_rex_by_source_sql(condition, "`b` BETWEEN ASYMMETRIC 25 AND 54")
        .expect("direct BETWEEN expansion");
    assert_eq!(between.kind.as_deref(), Some("AND"));
    assert_eq!(between.operands.len(), 2);
    assert_eq!(
        between.operands[0].kind.as_deref(),
        Some("GREATER_THAN_OR_EQUAL")
    );
    assert_eq!(
        between.operands[1].kind.as_deref(),
        Some("LESS_THAN_OR_EQUAL")
    );
    assert_eq!(
        between.operands[0].operands[1].source_sql.as_deref(),
        Some("25")
    );
    assert_eq!(
        between.operands[1].operands[1].source_sql.as_deref(),
        Some("54")
    );
    convert_raw_file(raw.clone()).expect("convert exact direct BETWEEN expansion");

    let mut forged_bound = raw;
    let condition = find_first_filter_mut(
        forged_bound.queries[0]
            .rel
            .as_mut()
            .expect("BETWEEN relation"),
    )
    .and_then(|filter| filter.condition_rex.as_mut())
    .expect("BETWEEN condition");
    let between = find_rex_by_source_sql_mut(condition, "`b` BETWEEN ASYMMETRIC 25 AND 54")
        .expect("mutable BETWEEN expansion");
    between.operands[1].operands[1].literal_value2 = Some("55".to_owned());
    assert!(convert_raw_file(forged_bound).is_err());

    let case = repo.join(
        "benchmarks/core/.generated/sqlsolver/nonwetune-flat/\
         verieql-calcite__calcite-125",
    );
    let raw = run_calcite(&repo, &case.join("schema.sql"), &case.join("sql2.sql"));
    let not_in = find_rel_rex_by_source_kind(
        raw.queries[0].rel.as_ref().expect("NOT IN target relation"),
        "NOT_IN",
    )
    .expect("generated outer NOT for source NOT IN");
    assert_eq!(not_in.kind.as_deref(), Some("NOT"));
    let positive = &not_in.operands[0];
    assert_eq!(positive.kind.as_deref(), Some("OR"));
    assert_eq!(positive.source_kind.as_deref(), Some("IN"));
    assert_eq!(positive.source_operator.as_deref(), Some("IN"));
    assert_eq!(positive.operands.len(), 2);
    for (comparison, expected) in positive.operands.iter().zip(["4", "6"]) {
        assert_eq!(comparison.kind.as_deref(), Some("EQUALS"));
        assert_eq!(comparison.source_kind.as_deref(), Some("EQUALS"));
        assert_eq!(comparison.operands[1].source_sql.as_deref(), Some(expected));
    }
    convert_raw_file(raw.clone()).expect("convert exact NOT IN expansion");

    let mut forged_positive = raw;
    let positive =
        find_rel_rex_by_source_kind_mut(forged_positive.queries[0].rel.as_mut().unwrap(), "NOT_IN")
            .unwrap()
            .operands
            .first_mut()
            .unwrap();
    positive.source_kind = Some("NOT_IN".to_owned());
    positive.source_operator = Some("NOT IN".to_owned());
    assert!(convert_raw_file(forged_positive).is_err());

    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and frozen benchmark inputs"]
fn calcite_wrapper_transactionally_emits_tpch8_with_exact_derived_case_sources() {
    with_large_calcite_stack(|| {
        let repo = repo_root();
        let case =
            repo.join("benchmarks/core/.generated/sqlsolver/nonwetune-flat/rbot-tpch__query8");
        for sql in ["sql1.sql", "sql2.sql"] {
            let raw = run_calcite(&repo, &case.join("schema.sql"), &case.join(sql));
            assert!(raw.queries[0].error.is_none(), "{sql}");
            let case_rex = find_rel_rex_by_source_kind(
                raw.queries[0].rel.as_ref().expect("TPCH8 relation"),
                "CASE",
            )
            .filter(|rex| {
                rex.source_sql
                    .as_deref()
                    .is_some_and(|source| source.contains("CASE WHEN `nation` ="))
            })
            .expect("outer aggregate-input CASE");
            assert_eq!(case_rex.kind.as_deref(), Some("CASE"));
            let product = &case_rex.operands[1];
            assert_eq!(product.kind.as_deref(), Some("TIMES"));
            assert_eq!(product.source_operator.as_deref(), Some("*"));
            let expansion = product
                .source_expansion
                .as_ref()
                .expect("direct derived volume-alias expansion");
            assert_eq!(expansion.kind, "DIRECT_DERIVED_OUTPUT_ALIAS");
            assert_eq!(expansion.reference_text, "volume");
            assert_eq!(expansion.output_alias_text, "volume");
            assert_eq!(
                product.source_node_id.as_deref(),
                Some(expansion.definition_node_id.as_str())
            );
            assert_eq!(
                product.source_text.as_deref(),
                Some(expansion.definition_text.as_str())
            );
            let one = &product.operands[1].operands[0];
            assert_eq!(one.text.as_deref(), Some("1"));
            assert_eq!(one.source_sql.as_deref(), Some("1"));
            assert_eq!(one.source_kind.as_deref(), Some("LITERAL"));

            let converted =
                convert_raw_file(raw.clone()).unwrap_or_else(|error| panic!("{sql}: {error}"));
            let (_, aggregate_output) = first_ir_aggregate(&converted.queries[0].rel);
            let postgres_extract_type = SqlType::Decimal {
                precision: None,
                scale: None,
            };
            assert_eq!(aggregate_output[0].name, "o_year", "{sql}");
            assert_eq!(aggregate_output[0].ty, postgres_extract_type, "{sql}");
            assert_eq!(converted.queries[0].output()[0].name, "o_year", "{sql}");
            assert_eq!(
                converted.queries[0].output()[0].ty,
                postgres_extract_type,
                "{sql}"
            );

            let mut forged_group_type = raw.clone();
            let aggregate = first_aggregate_mut(
                forged_group_type.queries[0]
                    .rel
                    .as_mut()
                    .expect("TPCH8 typed-group relation"),
            );
            assert_eq!(aggregate.row_type[0].ty, aggregate.inputs[0].row_type[0].ty);
            aggregate.row_type[0].ty = "INTEGER".to_owned();
            aggregate.row_type[0].full_type = Some("INTEGER".to_owned());
            aggregate.row_type[0].precision = Some(10);
            assert!(
                matches!(
                    convert_raw_file(forged_group_type),
                    Err(logos_ir::Error::InvalidRelSourceProvenance(_))
                ),
                "{sql}: an Aggregate group carrier retyped away from its raw input must fail closed"
            );

            let mut forged_group_binding = raw;
            let aggregate = first_aggregate_mut(
                forged_group_binding.queries[0]
                    .rel
                    .as_mut()
                    .expect("TPCH8 source-grouping relation"),
            );
            let grouping = aggregate
                .source_grouping
                .as_mut()
                .expect("TPCH8 exact source grouping");
            assert_eq!(grouping.group_indexes, [0]);
            assert_eq!(grouping.source_operand_indexes, [vec![0]]);
            grouping.source_operand_indexes[0][0] = 1;
            assert!(
                matches!(
                    convert_raw_file(forged_group_binding),
                    Err(logos_ir::Error::InvalidRelSourceProvenance(_))
                ),
                "{sql}: a forged source GROUP BY operand binding must fail closed"
            );
        }
    });
}

#[test]
#[ignore = "requires the Java Calcite wrapper and frozen benchmark inputs"]
fn calcite_wrapper_closes_only_exact_duplicate_is_null_idempotence() {
    let repo = repo_root();
    let case = repo.join(
        "benchmarks/core/.generated/sqlsolver/nonwetune-flat/\
         verieql-calcite__calcite-84",
    );
    let raw = run_calcite(&repo, &case.join("schema.sql"), &case.join("sql1.sql"));
    let outer_wildcard = raw.queries[0].rel.as_ref().expect("outer wildcard Project");
    let inner_wildcard = &outer_wildcard.inputs[0].inputs[0];
    for (label, project) in [("outer", outer_wildcard), ("nested", inner_wildcard)] {
        let [rex] = project.project_rex.as_slice() else {
            panic!("{label} one-column wildcard did not produce one RexInputRef");
        };
        assert!(
            rex.source_sql.is_none(),
            "{label} wildcard became scalar SQL"
        );
        assert!(
            rex.source_node_id.is_none(),
            "{label} wildcard borrowed a scalar span"
        );
        assert!(
            rex.source_text.is_none(),
            "{label} wildcard became scalar text"
        );
        assert!(
            rex.source_kind.is_none(),
            "{label} wildcard became a scalar identifier"
        );
        assert!(rex.source_identifier_names.is_empty());
        assert!(rex.source_identifier_quoted.is_empty());
    }
    let collapsed = find_rel_rex_by_source_kind(
        raw.queries[0].rel.as_ref().expect("Calcite-84 relation"),
        "AND",
    )
    .expect("duplicate IS NULL collapse");
    assert_eq!(collapsed.kind.as_deref(), Some("IS_NULL"));
    assert_eq!(
        collapsed.source_text.as_deref(),
        Some("N IS NULL AND N IS NULL")
    );
    assert_eq!(collapsed.operands.len(), 1);
    assert_eq!(collapsed.operands[0].source_text.as_deref(), Some("N"));
    convert_raw_file(raw.clone()).expect("exact duplicate IS NULL idempotence");

    let mut single_conjunct = raw.clone();
    let collapsed =
        find_rel_rex_by_source_kind_mut(single_conjunct.queries[0].rel.as_mut().unwrap(), "AND")
            .unwrap();
    collapsed.source_node_id = Some("1:86-1:94".to_owned());
    collapsed.source_text = Some("N IS NULL".to_owned());
    assert!(
        convert_raw_file(single_conjunct).is_err(),
        "one conjunct must not authorize the duplicate-predicate collapse"
    );

    let mut forged_scalar_star = raw.clone();
    let star = &mut forged_scalar_star.queries[0]
        .rel
        .as_mut()
        .unwrap()
        .project_rex[0];
    star.source_sql = Some("*".to_owned());
    star.source_node_id = Some("1:8-1:8".to_owned());
    star.source_text = Some("*".to_owned());
    star.source_kind = Some("IDENTIFIER".to_owned());
    star.source_identifier_names = vec![String::new()];
    star.source_identifier_quoted = vec![false];
    assert!(
        convert_raw_file(forged_scalar_star).is_err(),
        "a relational wildcard must not be admitted as a pseudo scalar identifier"
    );

    let mut wrong_survivor = raw;
    find_rel_rex_by_source_kind_mut(wrong_survivor.queries[0].rel.as_mut().unwrap(), "AND")
        .unwrap()
        .operands[0]
        .source_identifier_names = vec!["other".to_owned()];
    assert!(
        convert_raw_file(wrong_survivor).is_err(),
        "the surviving InputRef must retain the duplicated identifier exactly"
    );
}

#[test]
#[ignore = "requires the Java Calcite wrapper and frozen benchmark inputs"]
fn calcite_wrapper_preserves_wetune65_distinct_wildcard_order() {
    let repo = repo_root();
    let case = repo.join("benchmarks/core/.generated/sqlsolver/wetune-issues/65");
    let raw = run_calcite(&repo, &case.join("schema.sql"), &case.join("sql2.sql"));
    assert!(raw.queries[0].error.is_none());
    convert_raw_file(raw).expect("WeTune 65 SELECT DISTINCT * exact wildcard order");
}

#[test]
#[ignore = "requires the Java Calcite wrapper and frozen benchmark inputs"]
fn calcite_wrapper_resolves_aggregate_inputs_through_exact_ordered_cte_scope() {
    with_large_calcite_stack(|| {
        fn revenue_aggregate(rel: &CalciteRel) -> Option<&CalciteRel> {
            if rel.rel_type == "LogicalAggregate"
                && rel.row_type.get(1).map(|field| field.name.as_str()) == Some("revenue")
                && matches!(rel.agg_call_details.as_slice(), [call] if call.text == "SUM($1)")
                && rel.inputs.first().is_some_and(|input| {
                    matches!(input.source_input_cte_uses.as_slice(), [Some(cte)]
                        if cte.relation_text == "my_revenue")
                })
            {
                return Some(rel);
            }
            rel.inputs.iter().find_map(revenue_aggregate)
        }

        fn revenue_aggregate_mut(rel: &mut CalciteRel) -> Option<&mut CalciteRel> {
            if rel.rel_type == "LogicalAggregate"
                && rel.row_type.get(1).map(|field| field.name.as_str()) == Some("revenue")
                && matches!(rel.agg_call_details.as_slice(), [call] if call.text == "SUM($1)")
                && rel.inputs.first().is_some_and(|input| {
                    matches!(input.source_input_cte_uses.as_slice(), [Some(cte)]
                        if cte.relation_text == "my_revenue")
                })
            {
                return Some(rel);
            }
            rel.inputs.iter_mut().find_map(revenue_aggregate_mut)
        }

        let repo = repo_root();
        let case =
            repo.join("benchmarks/core/.generated/sqlsolver/nonwetune-flat/rbot-dsb__query054");
        let mut mutation_seed = None;
        for sql in ["sql1.sql", "sql2.sql"] {
            let raw = run_calcite(&repo, &case.join("schema.sql"), &case.join(sql));
            let segment = find_rel_rex_by_source_fragment(
                raw.queries[0].rel.as_ref().expect("Q054 relation"),
                "CAST(`revenue` / 50 AS INTEGER)",
            )
            .expect("segments CTE cast");
            assert_eq!(segment.kind.as_deref(), Some("CAST"));
            assert_eq!(segment.source_kind.as_deref(), Some("CAST"));
            let division = &segment.operands[0];
            assert_eq!(division.source_sql.as_deref(), Some("`revenue` / 50"));
            assert_eq!(division.operands[1].source_sql.as_deref(), Some("50"));
            let aggregate = revenue_aggregate(raw.queries[0].rel.as_ref().unwrap())
                .expect("my_revenue Aggregate");
            assert!(aggregate.source_grouping.is_none());
            let carrier = &aggregate.inputs[0];
            let cte = carrier.source_input_cte_uses[0]
                .as_ref()
                .expect("my_revenue CTE edge");
            assert!(
                cte.definition_query_text
                    .starts_with("select c_customer_sk, sum(ss_ext_sales_price) as revenue")
            );
            assert!(
                cte.definition_query_text
                    .ends_with("group by c_customer_sk")
            );
            assert_eq!(carrier.project_rex[0].index, Some(0));
            assert_eq!(carrier.project_rex[1].index, Some(17));
            let call = &aggregate.agg_call_details[0];
            assert_eq!(call.function, "SUM");
            assert_eq!(call.arg_list, [1]);
            assert!(call.source_text.is_none());
            assert!(call.source_operands.is_empty());
            if sql == "sql1.sql" {
                mutation_seed = Some(raw.clone());
            }
            convert_raw_file(raw).unwrap_or_else(|error| panic!("{sql}: {error}"));
        }

        let pristine = mutation_seed.expect("Q054 mutation seed");
        let mut wrong_expansion_ordinal = pristine.clone();
        let aggregate = first_aggregate_mut(
            wrong_expansion_ordinal.queries[0]
                .rel
                .as_mut()
                .expect("Q054 relation"),
        );
        let grouping = aggregate
            .source_grouping
            .as_ref()
            .expect("outer segment GROUP BY authority");
        assert_eq!(
            grouping.source_operands[0][0].source_text.as_deref(),
            Some("segment")
        );
        let expansion = aggregate.inputs[0].project_rex[0]
            .source_expansion
            .as_mut()
            .expect("segment direct-CTE expansion");
        assert_eq!(expansion.public_output_index, Some(0));
        expansion.public_output_index = Some(1);
        assert!(
            convert_raw_file(wrong_expansion_ordinal).is_err(),
            "a grouping reference must not borrow a different direct-CTE public ordinal"
        );

        let mut wrong_group = pristine.clone();
        let aggregate = revenue_aggregate_mut(wrong_group.queries[0].rel.as_mut().unwrap())
            .expect("mutable my_revenue Aggregate");
        aggregate.group_set = Some(vec![1]);
        aggregate.group_sets = Some(vec![vec![1]]);
        assert!(
            convert_raw_file(wrong_group).is_err(),
            "a coherent positional GROUP BY mutation must not borrow the exact c_customer_sk role"
        );

        let mut wrong_call = pristine.clone();
        let aggregate = revenue_aggregate_mut(wrong_call.queries[0].rel.as_mut().unwrap())
            .expect("mutable my_revenue Aggregate");
        let call = &mut aggregate.agg_call_details[0];
        call.text = "COUNT($1)".to_owned();
        call.function = "COUNT".to_owned();
        call.kind = "COUNT".to_owned();
        assert!(
            convert_raw_file(wrong_call).is_err(),
            "a generated COUNT must not inherit the exact source SUM authority"
        );

        let mut wrong_argument = pristine.clone();
        let aggregate = revenue_aggregate_mut(wrong_argument.queries[0].rel.as_mut().unwrap())
            .expect("mutable my_revenue Aggregate");
        aggregate.agg_call_details[0].text = "SUM($0)".to_owned();
        aggregate.agg_call_details[0].arg_list = vec![0];
        assert!(
            convert_raw_file(wrong_argument).is_err(),
            "SUM(c_customer_sk) must not inherit SUM(ss_ext_sales_price) authority"
        );

        let mut wrong_output = pristine.clone();
        revenue_aggregate_mut(wrong_output.queries[0].rel.as_mut().unwrap())
            .expect("mutable my_revenue Aggregate")
            .row_type[1]
            .name = "forged_revenue".to_owned();
        assert!(
            convert_raw_file(wrong_output).is_err(),
            "the exact public revenue output identity must remain positional and named"
        );

        let temp = temp_dir("ordered-cte-project-provenance");
        let schema = temp.join("schema.sql");
        let query = temp.join("query.sql");
        fs::write(&schema, "create table base(revenue decimal(12, 2));\n").unwrap();
        fs::write(
            &query,
            "with prior as (select revenue / 7 as q from base), \
         selected as (select cast(revenue / 50 as integer) as segment from base), \
         later as (select revenue / 99 as segment from base) \
         select segment, count(*) as n, segment * 50 as segment_base \
         from selected group by segment order by segment;\n",
        )
        .unwrap();
        let raw = run_calcite(&repo, &schema, &query);
        let segment = find_rel_rex_by_source_fragment(
            raw.queries[0].rel.as_ref().unwrap(),
            "CAST(`revenue` / 50 AS INTEGER)",
        )
        .expect("selected CTE expression");
        assert_eq!(
            segment.operands[0].operands[1].source_sql.as_deref(),
            Some("50")
        );
        assert!(find_rel_rex_by_source_fragment(
        raw.queries[0].rel.as_ref().unwrap(),
        "`revenue` / 99",
    )
    .is_none());
        fs::remove_dir_all(&temp).unwrap();
    });
}

#[test]
#[ignore = "requires the Java Calcite wrapper and frozen benchmark inputs"]
fn calcite_wrapper_keeps_exact_case_cast_explicit_when_simplification_is_disabled() {
    let repo = repo_root();
    let case = repo.join(
        "benchmarks/core/.generated/sqlsolver/nonwetune-flat/\
         verieql-calcite__calcite-88",
    );
    let raw = run_calcite(&repo, &case.join("schema.sql"), &case.join("sql2.sql"));
    let project = raw.queries[0].rel.as_ref().expect("Calcite-88 target");
    let root = &project.project_rex[0];
    assert_eq!(root.kind.as_deref(), Some("CAST"));
    assert_eq!(root.source_kind.as_deref(), Some("CAST"));
    let case = &root.operands[0];
    assert_eq!(case.kind.as_deref(), Some("CASE"));
    assert_eq!(case.source_kind.as_deref(), Some("CASE"));
    assert_eq!(case.operands.len(), 3);
    assert_eq!(case.operands[0].source_kind.as_deref(), Some("EQUALS"));
    assert_eq!(
        case.operands[0].operands[0].source_identifier_names,
        ["empno"]
    );
    assert_eq!(case.operands[1].source_sql.as_deref(), Some("1"));
    assert_eq!(case.operands[2].source_sql.as_deref(), Some("2"));

    let converted = convert_raw_file(raw.clone()).expect("reconstruct exact CASE cast");
    let RelExpr::Project { exprs, .. } = &converted.queries[0].rel else {
        panic!("Calcite-88 target must remain a Project")
    };
    assert!(scalar_contains_cast(&exprs[0].parsed));

    let mut forged_descendant = raw;
    forged_descendant.queries[0]
        .rel
        .as_mut()
        .unwrap()
        .project_rex[0]
        .operands[0]
        .operands[2]
        .literal_value2 = Some("3".to_owned());
    assert!(convert_raw_file(forged_descendant).is_err());
}

#[test]
#[ignore = "requires the Java Calcite wrapper and frozen benchmark inputs"]
fn calcite_wrapper_preserves_grouping_authority_through_derived_aliases() {
    let repo = repo_root();
    let case = repo.join(
        "benchmarks/core/.generated/sqlsolver/nonwetune-flat/\
         verieql-calcite__calcite-199",
    );
    let raw = run_calcite(&repo, &case.join("schema.sql"), &case.join("sql2.sql"));
    let aggregate = first_aggregate(raw.queries[0].rel.as_ref().unwrap());
    let grouping = aggregate
        .source_grouping
        .as_ref()
        .expect("derived-alias grouping authority");
    assert_eq!(grouping.kind, "GROUPING_SETS");
    assert_eq!(grouping.group_indexes, [0, 1]);
    assert_eq!(grouping.grouping_sets, [vec![0, 1], vec![0]]);
    assert_eq!(grouping.source_operand_indexes, [vec![0, 1], vec![0]]);
    assert_eq!(
        grouping
            .source_operands
            .iter()
            .map(Vec::len)
            .collect::<Vec<_>>(),
        [2, 1]
    );
    convert_raw_file(raw.clone()).expect("convert derived-alias grouping sets");

    let mut missing = raw.clone();
    first_aggregate_mut(missing.queries[0].rel.as_mut().unwrap()).source_grouping = None;
    assert!(convert_raw_file(missing).is_err());

    let mut borrowed_repeated_occurrence = raw;
    let grouping = first_aggregate_mut(
        borrowed_repeated_occurrence.queries[0]
            .rel
            .as_mut()
            .unwrap(),
    )
    .source_grouping
    .as_mut()
    .unwrap();
    grouping.source_operands[1][0] = grouping.source_operands[0][0].clone();
    assert!(convert_raw_file(borrowed_repeated_occurrence).is_err());
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_keeps_internal_search_rewrite_path_closed() {
    let repo = repo_root();
    let temp = temp_dir("closed-search-rewrite-path");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&schema, "create table t(a integer);\n").unwrap();
    fs::write(
        &query,
        "select a from t where a in (1, 2, 3, 4) or (a >= 8 and a < 10);\n",
    )
    .unwrap();

    let raw = run_calcite(&repo, &schema, &query);
    assert!(
        !rel_contains_search(raw.queries[0].rel.as_ref().unwrap()),
        "the production wrapper must retain the source predicate tree instead of emitting SEARCH"
    );
    convert_raw_file(raw).expect("the retained source predicate tree converts without SEARCH");
    fs::remove_dir_all(temp).unwrap();
}

#[test]
#[ignore = "requires both Calcite wrappers and frozen benchmark inputs"]
fn calcite_wrappers_disable_unsafe_rex_simplification() {
    with_large_calcite_stack(|| {
        let repo = repo_root();
        let direct_cases = [
            ("rbot-dsb__query050", ["sql1.sql", "sql2.sql"].as_slice()),
            ("rbot-dsb__query099", ["sql1.sql", "sql2.sql"].as_slice()),
            ("rbot-tpch__query12", ["sql1.sql", "sql2.sql"].as_slice()),
            ("verieql-calcite__calcite-125", ["sql1.sql"].as_slice()),
        ];
        for (case_name, sql_files) in direct_cases {
            let case = repo.join(format!(
                "benchmarks/core/.generated/sqlsolver/nonwetune-flat/{case_name}"
            ));
            for sql in sql_files {
                let raw = run_calcite(&repo, &case.join("schema.sql"), &case.join(sql));
                let rel = raw.queries[0]
                    .rel
                    .as_ref()
                    .unwrap_or_else(|| panic!("{case_name}/{sql}: relation"));
                assert!(
                    !rel_contains_search(rel),
                    "{case_name}/{sql}: simplify=false must retain the source boolean tree"
                );
                convert_raw_file(raw).unwrap_or_else(|error| panic!("{case_name}/{sql}: {error}"));
            }
        }

        let wetune = repo.join("benchmarks/core/.generated/sqlsolver/wetune-issues/17");
        let temp = temp_dir("simplify-false-wetune17");
        for sql in ["sql1.sql", "sql2.sql"] {
            let raw = run_calcite_sqlglot(
                &repo,
                &wetune.join("schema.sql"),
                &wetune.join(sql),
                &temp.join(format!("{sql}.normalized.sql")),
            );
            assert!(
                !rel_contains_search(raw.queries[0].rel.as_ref().unwrap()),
                "wetune17/{sql}: production wrapper must not synthesize SEARCH"
            );
            convert_raw_file(raw).unwrap_or_else(|error| panic!("wetune17/{sql}: {error}"));
        }
        fs::remove_dir_all(&temp).unwrap();

        let calc15 = repo.join(
            "benchmarks/core/.generated/sqlsolver/nonwetune-flat/\
             verieql-calcite__calcite-15",
        );
        let raw = run_calcite(&repo, &calc15.join("schema.sql"), &calc15.join("sql1.sql"));
        let root = &raw.queries[0].rel.as_ref().unwrap().project_rex[0];
        assert_eq!(root.kind.as_deref(), Some("CASE"));
        assert_eq!(root.source_kind.as_deref(), Some("CASE"));
        assert_eq!(root.operands.len(), 3);
        convert_raw_file(raw).expect("Calcite-15 source CASE remains explicit");

        let calc359 = repo.join(
            "benchmarks/core/.generated/sqlsolver/nonwetune-flat/\
             verieql-calcite__calcite-359",
        );
        for sql in ["sql1.sql", "sql2.sql"] {
            let raw = run_calcite(&repo, &calc359.join("schema.sql"), &calc359.join(sql));
            let rel = raw.queries[0].rel.as_ref().unwrap();
            let case = find_rel_rex_by_source_kind(rel, "CASE")
                .unwrap_or_else(|| panic!("Calcite-359/{sql}: source CASE"));
            assert_eq!(case.kind.as_deref(), Some("CASE"));
            assert!(
                !rel_contains_unprovenanced_noncartesian_literal(rel),
                "Calcite-359/{sql}: retained CASE descendants need exact source provenance"
            );
            convert_raw_file(raw).unwrap_or_else(|error| panic!("Calcite-359/{sql}: {error}"));
        }
    });
}

#[test]
#[ignore = "requires the Java Calcite wrapper and frozen benchmark inputs"]
fn calcite_wrapper_recovers_exact_not_in_subquery_source_context() {
    with_large_calcite_stack(|| {
        let repo = repo_root();
        let cases = [
            ("rbot-tpch__query16", "sql1.sql", "'%Customer%Complaints%'"),
            ("rbot-tpch__query16", "sql2.sql", "'%Customer%Complaints%'"),
            ("verieql-calcite__calcite-46", "sql1.sql", "2"),
        ];
        let mut pristine = None;
        for (case_name, sql_file, nested_literal) in cases {
            let case = repo.join(format!(
                "benchmarks/core/.generated/sqlsolver/nonwetune-flat/{case_name}"
            ));
            let raw = run_calcite_postgres_c(&repo, &case.join("schema.sql"), &case.join(sql_file));
            let rel = raw.queries[0]
                .rel
                .as_ref()
                .unwrap_or_else(|| panic!("{case_name}/{sql_file}: relation"));
            let subquery = find_first_in_subquery(rel)
                .unwrap_or_else(|| panic!("{case_name}/{sql_file}: positive IN RexSubQuery"));
            assert_eq!(subquery.operator.as_deref(), Some("IN"));
            assert_eq!(subquery.op_kind.as_deref(), Some("IN"));
            assert_eq!(subquery.source_kind.as_deref(), Some("IN"));
            assert_eq!(subquery.source_operator.as_deref(), Some("IN"));
            assert_eq!(subquery.operands.len(), 1);
            assert!(
                subquery
                    .source_sql
                    .as_deref()
                    .is_some_and(|source| source.contains(" IN (SELECT"))
            );
            let literal = find_rel_rex_by_exact_source_sql(
                subquery.subquery_rel.as_deref().unwrap(),
                nested_literal,
            )
            .unwrap_or_else(|| panic!("{case_name}/{sql_file}: nested source literal"));
            assert_eq!(literal.source_kind.as_deref(), Some("LITERAL"));
            convert_raw_file(raw.clone())
                .unwrap_or_else(|error| panic!("{case_name}/{sql_file}: {error}"));
            if case_name == "verieql-calcite__calcite-46" {
                pristine = Some(raw);
            }
        }

        let calcite46 = repo.join(
            "benchmarks/core/.generated/sqlsolver/nonwetune-flat/\
             verieql-calcite__calcite-46",
        );
        let mode_temp = temp_dir("calcite46-complete-frontend-matrix");
        for sql_file in ["sql1.sql", "sql2.sql"] {
            let direct = run_calcite_postgres_c(
                &repo,
                &calcite46.join("schema.sql"),
                &calcite46.join(sql_file),
            );
            convert_raw_file(direct)
                .unwrap_or_else(|error| panic!("Calcite-46/{sql_file}/direct: {error}"));

            let no_identify = run_calcite_sqlglot_postgres_c_mode(
                &repo,
                &calcite46.join("schema.sql"),
                &calcite46.join(sql_file),
                &mode_temp.join(format!("{sql_file}.no-identify.sql")),
                true,
            );
            convert_raw_file(no_identify)
                .unwrap_or_else(|error| panic!("Calcite-46/{sql_file}/no-identify: {error}"));

            let identified_path = mode_temp.join(format!("{sql_file}.identify.sql"));
            let identified = run_calcite_sqlglot_postgres_c_mode(
                &repo,
                &calcite46.join("schema.sql"),
                &calcite46.join(sql_file),
                &identified_path,
                false,
            );
            assert!(identified.queries[0].error.is_none());
            convert_raw_file(identified)
                .unwrap_or_else(|error| panic!("Calcite-46/{sql_file}/identify: {error}"));
            let identified_sql = fs::read_to_string(identified_path).unwrap();
            assert!(
                identified_sql.contains("\"emp\"") && !identified_sql.contains("\"EMP\""),
                "PostgreSQL identify mode must fold an unquoted EMP before quoting: {identified_sql}"
            );
        }
        fs::remove_dir_all(&mode_temp).unwrap();

        let pristine = pristine.expect("Calcite-46 mutation seed");
        let reject = |label: &str, forged: CalciteFile| {
            assert!(
                convert_raw_file(forged).is_err(),
                "forged NOT IN subquery {label} unexpectedly converted"
            );
        };

        let mut unary = pristine.clone();
        find_first_in_subquery_mut(unary.queries[0].rel.as_mut().unwrap())
            .unwrap()
            .operands
            .clear();
        reject("unary arity", unary);

        let mut operator = pristine.clone();
        let subquery =
            find_first_in_subquery_mut(operator.queries[0].rel.as_mut().unwrap()).unwrap();
        subquery.operator = Some("EXISTS".to_owned());
        subquery.op_kind = Some("EXISTS".to_owned());
        reject("operator", operator);

        let mut arity = pristine.clone();
        let subquery = find_first_in_subquery_mut(arity.queries[0].rel.as_mut().unwrap()).unwrap();
        subquery.operands.push(subquery.operands[0].clone());
        reject("binary left context", arity);

        let mut projection = pristine.clone();
        let subquery =
            find_first_in_subquery_mut(projection.queries[0].rel.as_mut().unwrap()).unwrap();
        subquery.subquery_rel.as_mut().unwrap().project_rex[0].index = Some(0);
        reject("structured subquery projection", projection);

        let mut context = pristine.clone();
        let subquery =
            find_first_in_subquery_mut(context.queries[0].rel.as_mut().unwrap()).unwrap();
        subquery.operands[0].index = Some(1);
        reject("outer input context", context);

        let mut derived_alias = pristine.clone();
        let subquery =
            find_first_in_subquery_mut(derived_alias.queries[0].rel.as_mut().unwrap()).unwrap();
        let filter = find_rel_type_mut(subquery.subquery_rel.as_mut().unwrap(), "LogicalFilter")
            .expect("nested derived-table filter");
        filter.inputs[0].row_type[2].name = "other_r".to_owned();
        reject("derived alias/base-field lineage", derived_alias);

        let mut wrong_identifier_scope = pristine.clone();
        let subquery =
            find_first_in_subquery_mut(wrong_identifier_scope.queries[0].rel.as_mut().unwrap())
                .unwrap();
        let outer_identifier_node_id = subquery.operands[0]
            .source_node_id
            .clone()
            .expect("outer EMPNO source span");
        let outer_identifier_text = subquery.operands[0].source_text.clone();
        let nested_identifier = &mut subquery
            .subquery_rel
            .as_deref_mut()
            .expect("nested NOT IN query")
            .project_rex[0];
        assert_eq!(
            nested_identifier.source_text, outer_identifier_text,
            "mutation needs identical EMPNO source text"
        );
        assert_ne!(
            nested_identifier.source_node_id.as_deref(),
            Some(outer_identifier_node_id.as_str()),
            "outer and nested EMPNO must start in different query blocks"
        );
        nested_identifier.source_node_id = Some(outer_identifier_node_id);
        reject(
            "identical identifier from the outer query block",
            wrong_identifier_scope,
        );
    });
}

#[test]
#[ignore = "requires the Java Calcite wrapper and frozen benchmark inputs"]
fn calcite_wrapper_closes_qualified_wildcard_set_subquery_tree() {
    with_large_calcite_stack(|| {
        let repo = repo_root();
        let case = repo.join("benchmarks/core/.generated/sqlsolver/wetune-issues/45");
        let pristine = run_calcite(&repo, &case.join("schema.sql"), &case.join("sql1.sql"));
        let outer = pristine.queries[0]
            .rel
            .as_ref()
            .expect("wetune45 outer relation");
        let in_subquery = find_first_in_subquery(outer).expect("wetune45 IN subquery");
        let nested = in_subquery
            .subquery_rel
            .as_deref()
            .expect("wetune45 generated nested relation");
        assert_eq!(nested.rel_type, "LogicalProject");
        assert_eq!(nested.project_rex[0].source_text.as_deref(), Some("id"));
        let set = nested.inputs.first().expect("nested UNION ALL");
        assert_eq!(set.rel_type, "LogicalUnion");
        assert_eq!(set.all, Some(true));
        assert_eq!(set.inputs.len(), 2);
        for arm in &set.inputs {
            assert_eq!(arm.rel_type, "LogicalProject");
            assert_eq!(arm.project_rex.len(), 26);
            assert_eq!(arm.project_rex[0].index, Some(0));
            assert!(
                arm.source_text
                    .as_deref()
                    .is_some_and(|source| source.contains("notes.*"))
            );
        }
        convert_raw_file(pristine.clone()).expect("wetune45 exact wildcard set tree");

        let reject = |label: &str, forged: CalciteFile| {
            assert!(
                convert_raw_file(forged).is_err(),
                "forged qualified-wildcard set tree {label} unexpectedly converted"
            );
        };

        let mut set_mode = pristine.clone();
        let subquery =
            find_first_in_subquery_mut(set_mode.queries[0].rel.as_mut().unwrap()).unwrap();
        find_rel_type_mut(
            subquery.subquery_rel.as_deref_mut().unwrap(),
            "LogicalUnion",
        )
        .expect("mutable nested UNION ALL")
        .all = Some(false);
        reject("set mode", set_mode);

        let mut public_index = pristine.clone();
        let subquery =
            find_first_in_subquery_mut(public_index.queries[0].rel.as_mut().unwrap()).unwrap();
        let root = subquery.subquery_rel.as_deref_mut().unwrap();
        root.project_rex[0].text = Some("$1".to_owned());
        root.project_rex[0].index = Some(1);
        reject("public output ordinal", public_index);

        let mut wildcard_order = pristine;
        let subquery =
            find_first_in_subquery_mut(wildcard_order.queries[0].rel.as_mut().unwrap()).unwrap();
        let set = find_rel_type_mut(
            subquery.subquery_rel.as_deref_mut().unwrap(),
            "LogicalUnion",
        )
        .expect("mutable nested UNION ALL");
        let first_arm = &mut set.inputs[0];
        assert_eq!(first_arm.row_type[0].ty, first_arm.row_type[3].ty);
        first_arm.project_rex[0].text = Some("$3".to_owned());
        first_arm.project_rex[0].index = Some(3);
        reject("qualified wildcard order", wildcard_order);
    });
}

#[test]
#[ignore = "requires the SQLGlot/Calcite wrappers and frozen benchmark inputs"]
fn calcite_wrapper_closes_coalesce_inside_complete_nested_where_tree() {
    with_large_calcite_stack(|| {
        let repo = repo_root();
        let case = repo.join("benchmarks/core/.generated/sqlsolver/wetune-issues/4");
        let temp = temp_dir("wetune4-nested-coalesce-tree");
        let pristine = run_calcite_sqlglot_postgres_c_mode(
            &repo,
            &case.join("schema.sql"),
            &case.join("sql1.sql"),
            &temp.join("sql1.normalized.sql"),
            false,
        );
        let outer = find_first_in_subquery(
            pristine.queries[0]
                .rel
                .as_ref()
                .expect("wetune4 outer relation"),
        )
        .expect("wetune4 outer IN subquery");
        assert!(
            outer
                .source_sql
                .as_deref()
                .is_some_and(|sql| sql.contains("topics") && sql.contains(" IN (SELECT"))
        );
        let nested = outer
            .subquery_rel
            .as_deref()
            .expect("wetune4 generated nested relation");
        let coalesce = find_generated_coalesce(nested).expect("nested source COALESCE");
        assert_eq!(coalesce.kind.as_deref(), Some("CASE"));
        assert_eq!(coalesce.operands.len(), 3);
        assert_eq!(coalesce.operands[0].kind.as_deref(), Some("IS_NOT_NULL"));
        convert_raw_file(pristine.clone()).expect("wetune4 nested COALESCE must convert");

        let reject = |label: &str, forged: CalciteFile| {
            assert!(
                convert_raw_file(forged).is_err(),
                "forged wetune4 nested COALESCE tree {label} unexpectedly converted"
            );
        };

        let mut detached_return = pristine.clone();
        let subquery =
            find_first_in_subquery_mut(detached_return.queries[0].rel.as_mut().unwrap()).unwrap();
        let coalesce =
            find_generated_coalesce_mut(subquery.subquery_rel.as_deref_mut().unwrap()).unwrap();
        let returned = coalesce.operands[1]
            .operands
            .first_mut()
            .expect("generated COALESCE returned carrier");
        let returned_index = returned.index.expect("returned carrier input index");
        returned.index = Some(returned_index - 1);
        reject("detached returned value", detached_return);

        let mut swapped_roles = pristine;
        let subquery =
            find_first_in_subquery_mut(swapped_roles.queries[0].rel.as_mut().unwrap()).unwrap();
        find_generated_coalesce_mut(subquery.subquery_rel.as_deref_mut().unwrap())
            .unwrap()
            .operands
            .swap(1, 2);
        reject("swapped return/fallback roles", swapped_roles);

        fs::remove_dir_all(temp).unwrap();
    });
}

#[test]
#[ignore = "requires the Java Calcite wrapper"]
fn calcite_wrapper_closes_grouped_window_keys_inside_nested_in_tree() {
    with_large_calcite_stack(|| {
        let repo = repo_root();
        let temp = temp_dir("grouped-window-nested-in-tree");
        let schema = temp.join("schema.sql");
        let query = temp.join("query.sql");
        fs::write(&schema, "create table t(k integer, v integer);\n").unwrap();
        fs::write(
            &query,
            "select k from t where k in (select k from (select k, rank() over \
             (partition by k order by sum(v) desc nulls last) as ranking from t group by k) \
             as ranked where ranking <= 5);\n",
        )
        .unwrap();

        let pristine = run_calcite_postgres_c(&repo, &schema, &query);
        let outer = pristine.queries[0].rel.as_ref().expect("outer relation");
        let in_subquery = find_first_in_subquery(outer).expect("nested IN RexSubQuery");
        let nested = in_subquery
            .subquery_rel
            .as_deref()
            .expect("nested IN relational tree");
        let rank = find_rel_rex_by_source_fragment(nested, "RANK() OVER")
            .expect("source-bound grouped RANK window");
        assert_eq!(rank.class.as_deref(), Some("RexOver"));
        let window = rank.window.as_deref().expect("RANK window metadata");
        assert_eq!(window.partition_keys.len(), 1);
        assert_eq!(window.order_keys.len(), 1);
        assert_eq!(window.partition_keys[0].source_text.as_deref(), Some("k"));
        assert_eq!(
            window.order_keys[0].expr.source_text.as_deref(),
            Some("sum(v)")
        );
        assert_eq!(window.order_keys[0].direction, "DESCENDING");
        assert_eq!(window.order_keys[0].null_direction, "LAST");
        let aggregate = first_aggregate(nested);
        assert_eq!(aggregate.agg_call_details.len(), 1);
        assert_eq!(
            aggregate.agg_call_details[0].source_text.as_deref(),
            Some("sum(v)")
        );
        assert_eq!(aggregate.agg_call_details[0].arg_list, vec![1]);
        assert_eq!(
            aggregate.inputs[0].row_type[1].name, "v",
            "the Aggregate argument index must bind v, not the window partition key"
        );
        convert_raw_file(pristine.clone()).expect("grouped window nested IN must convert");

        let reject = |label: &str, forged: CalciteFile| {
            assert!(
                convert_raw_file(forged).is_err(),
                "forged grouped-window tree {label} unexpectedly converted"
            );
        };

        let mut partition = pristine.clone();
        let subquery =
            find_first_in_subquery_mut(partition.queries[0].rel.as_mut().unwrap()).unwrap();
        first_window_rex_mut(subquery.subquery_rel.as_deref_mut().unwrap(), "RANK")
            .unwrap()
            .window
            .as_deref_mut()
            .unwrap()
            .partition_keys[0]
            .index = Some(1);
        reject("partition index", partition);

        let mut order = pristine.clone();
        let subquery = find_first_in_subquery_mut(order.queries[0].rel.as_mut().unwrap()).unwrap();
        first_window_rex_mut(subquery.subquery_rel.as_deref_mut().unwrap(), "RANK")
            .unwrap()
            .window
            .as_deref_mut()
            .unwrap()
            .order_keys[0]
            .expr
            .index = Some(0);
        reject("order index", order);

        let mut direction = pristine.clone();
        let subquery =
            find_first_in_subquery_mut(direction.queries[0].rel.as_mut().unwrap()).unwrap();
        first_window_rex_mut(subquery.subquery_rel.as_deref_mut().unwrap(), "RANK")
            .unwrap()
            .window
            .as_deref_mut()
            .unwrap()
            .order_keys[0]
            .direction = "ASCENDING".to_owned();
        reject("order direction", direction);

        let mut nulls = pristine.clone();
        let subquery = find_first_in_subquery_mut(nulls.queries[0].rel.as_mut().unwrap()).unwrap();
        first_window_rex_mut(subquery.subquery_rel.as_deref_mut().unwrap(), "RANK")
            .unwrap()
            .window
            .as_deref_mut()
            .unwrap()
            .order_keys[0]
            .null_direction = "FIRST".to_owned();
        reject("NULL placement", nulls);

        let mut argument = pristine.clone();
        let subquery =
            find_first_in_subquery_mut(argument.queries[0].rel.as_mut().unwrap()).unwrap();
        first_aggregate_mut(subquery.subquery_rel.as_deref_mut().unwrap()).agg_call_details[0]
            .arg_list[0] = 0;
        reject("Aggregate argument", argument);

        let mut borrowed_span = pristine;
        let subquery =
            find_first_in_subquery_mut(borrowed_span.queries[0].rel.as_mut().unwrap()).unwrap();
        let rank =
            first_window_rex_mut(subquery.subquery_rel.as_deref_mut().unwrap(), "RANK").unwrap();
        let window = rank.window.as_deref_mut().unwrap();
        window.partition_keys[0].source_node_id = window.order_keys[0].expr.source_node_id.clone();
        reject("borrowed source span", borrowed_span);

        fs::remove_dir_all(&temp).unwrap();
    });
}

#[test]
#[ignore = "requires the Java Calcite wrapper and frozen benchmark inputs"]
fn calcite_wrapper_closes_q070_ranked_in_subquery_trees() {
    fn collect_in_subqueries_from_rex<'a>(rex: &'a CalciteRex, output: &mut Vec<&'a CalciteRex>) {
        if rex.class.as_deref() == Some("RexSubQuery") && rex.source_kind.as_deref() == Some("IN") {
            output.push(rex);
        }
        for operand in &rex.operands {
            collect_in_subqueries_from_rex(operand, output);
        }
        if let Some(subquery) = rex.subquery_rel.as_deref() {
            collect_in_subqueries(subquery, output);
        }
    }

    fn collect_in_subqueries<'a>(rel: &'a CalciteRel, output: &mut Vec<&'a CalciteRex>) {
        for rex in rel_rexes(rel) {
            collect_in_subqueries_from_rex(rex, output);
        }
        for input in &rel.inputs {
            collect_in_subqueries(input, output);
        }
    }

    with_large_calcite_stack(|| {
        let repo = repo_root();
        let case = repo
            .join("benchmarks/core/.generated/sqlsolver/nonwetune-flat/tpcds-variants__query070");
        for sql_file in ["sql1.sql", "sql2.sql"] {
            let raw = run_calcite_postgres_c(&repo, &case.join("schema.sql"), &case.join(sql_file));
            let rel = raw.queries[0]
                .rel
                .as_ref()
                .unwrap_or_else(|| panic!("q070/{sql_file}: relation"));
            let mut subqueries = Vec::new();
            collect_in_subqueries(rel, &mut subqueries);
            assert!(
                !subqueries.is_empty(),
                "q070/{sql_file}: ranked IN subquery"
            );
            for subquery in subqueries {
                let nested = subquery
                    .subquery_rel
                    .as_deref()
                    .expect("q070 nested generated relation");
                let rank = find_rel_rex_by_source_fragment(nested, "RANK() OVER")
                    .expect("q070 grouped RANK window");
                let window = rank.window.as_deref().expect("q070 RANK window metadata");
                assert_eq!(window.partition_keys.len(), 1);
                assert_eq!(window.order_keys.len(), 1);
                assert_eq!(
                    window.partition_keys[0].source_text.as_deref(),
                    Some("s_state")
                );
                assert_eq!(
                    window.order_keys[0].expr.source_text.as_deref(),
                    Some("SUM(ss_net_profit)")
                );
                let aggregate = first_aggregate(nested);
                assert_eq!(aggregate.agg_call_details.len(), 1);
                assert_eq!(
                    aggregate.agg_call_details[0].source_text.as_deref(),
                    Some("SUM(ss_net_profit)")
                );
                let argument = aggregate.agg_call_details[0].arg_list[0];
                assert_eq!(
                    aggregate.inputs[0].project_rex[argument]
                        .source_text
                        .as_deref(),
                    Some("ss_net_profit"),
                    "q070/{sql_file}: Aggregate input must bind the SUM operand, not OVER"
                );
            }
            assert!(
                raw.queries[0].source_analysis_error.is_none(),
                "q070/{sql_file}: frozen PostgreSQL input already expands nested ORDER BY aliases"
            );
            let converted = convert_raw_file(raw.clone())
                .unwrap_or_else(|error| panic!("q070/{sql_file}: conversion failed: {error}"));
            assert!(
                converted.queries[0]
                    .analysis_errors
                    .iter()
                    .all(|error| !matches!(
                        error,
                        QueryAnalysisError::PostgresOrderByAliasExpressionUndefinedColumn { .. }
                    )),
                "q070/{sql_file}: expanded GROUPING expression must remain executable PostgreSQL"
            );
            if sql_file == "sql1.sql" {
                fn hidden_order_project(raw: &mut CalciteFile) -> &mut CalciteRel {
                    &mut raw.queries[0]
                        .rel
                        .as_mut()
                        .expect("q070 source relation")
                        .inputs[0]
                        .inputs[0]
                }

                fn grouping_expansion(raw: &mut CalciteFile) -> &mut CalciteRex {
                    &mut hidden_order_project(raw).project_rex[5].operands[0].operands[0]
                }

                fn repeated_grouping(raw: &mut CalciteFile) -> &mut CalciteRex {
                    &mut grouping_expansion(raw).operands[0]
                }

                let reject = |label: &str, forged: CalciteFile| {
                    assert!(
                        convert_raw_file(forged).is_err(),
                        "q070 hidden ORDER BY mutation {label} must fail closed"
                    );
                };

                let mut reordered_definition = raw.clone();
                grouping_expansion(&mut reordered_definition)
                    .operands
                    .swap(0, 1);
                reject("reordered generated definition", reordered_definition);

                let mut wrong_type = raw.clone();
                let expansion = grouping_expansion(&mut wrong_type);
                expansion.nullable = !expansion.nullable;
                reject("generated definition type", wrong_type);

                let mut visible_terminal = raw.clone();
                hidden_order_project(&mut visible_terminal)
                    .project_rex
                    .swap(4, 5);
                reject("terminal Rex moved into visible output", visible_terminal);

                let mut detached_sort_owner = raw.clone();
                let sort = &mut detached_sort_owner.queries[0].rel.as_mut().unwrap().inputs[0];
                let first_expression = sort.source_order.as_ref().unwrap().items[0]
                    .expression_node_id
                    .clone();
                sort.source_order.as_mut().unwrap().items[1].expression_node_id = first_expression;
                reject(
                    "detached parent Sort sourceOrder binding",
                    detached_sort_owner,
                );

                let mut borrowed_select_span = raw.clone();
                let aggregate_call = hidden_order_project(&mut borrowed_select_span).inputs[0]
                    .agg_call_details[1]
                    .clone();
                let grouping = repeated_grouping(&mut borrowed_select_span);
                grouping.source_sql = aggregate_call.source_sql;
                grouping.source_node_id = aggregate_call.source_node_id;
                grouping.source_text = aggregate_call.source_text;
                grouping.source_kind = aggregate_call.source_kind;
                grouping.source_operator = aggregate_call.source_operator;
                reject("borrowed SELECT-list aggregate span", borrowed_select_span);

                let mut wrong_operator = raw.clone();
                repeated_grouping(&mut wrong_operator).source_operator = Some("sum".to_owned());
                reject("wrong repeated aggregate operator", wrong_operator);

                let mut wrong_query_owner = raw.clone();
                let order_expression_id = wrong_query_owner.queries[0].rel.as_ref().unwrap().inputs
                    [0]
                .source_order
                .as_ref()
                .unwrap()
                .items[1]
                    .expression_node_id
                    .clone();
                hidden_order_project(&mut wrong_query_owner).inputs[0].source_query_block_id =
                    Some(order_expression_id);
                reject("wrong Aggregate query owner", wrong_query_owner);

                let mut unrelated_bad_edge = raw.clone();
                let terminal = &mut hidden_order_project(&mut unrelated_bad_edge).project_rex[5];
                terminal.operands[1].source_text = Some("lochierarchy".to_owned());
                reject("unrelated terminal operand edge", unrelated_bad_edge);
            }
        }
    });
}

#[test]
#[ignore = "requires the Java Calcite wrapper and frozen benchmark inputs"]
fn calcite_wrapper_recovers_only_the_exact_nullable_numeric_window_sum_role() {
    fn sort_mut(rel: &mut CalciteRel) -> Option<&mut CalciteRel> {
        if rel.rel_type == "LogicalSort" {
            return Some(rel);
        }
        rel.inputs.iter_mut().find_map(sort_mut)
    }

    with_large_calcite_stack(|| {
        let repo = repo_root();
        let case = repo
            .join("benchmarks/core/.generated/sqlsolver/nonwetune-flat/tpcds-variants__query051");
        let raw = run_calcite_postgres_c(&repo, &case.join("schema.sql"), &case.join("sql1.sql"));
        let rel = raw.queries[0].rel.as_ref().expect("TPC-DS 51 relation");
        let mut generated = Vec::new();
        collect_nested_window_sum_rexes(rel, &mut generated);
        assert_eq!(generated.len(), 2, "web/store nullable window SUM roots");
        for rex in generated {
            assert_eq!(rex.kind.as_deref(), Some("CASE"));
            assert_eq!(rex.source_kind.as_deref(), Some("OVER"));
            assert_eq!(rex.source_window_function.as_deref(), Some("SUM"));
            let zero = &rex.operands[0].operands[1];
            assert_eq!(zero.text.as_deref(), Some("0:BIGINT"));
            assert!(zero.source_sql.is_none());
            assert_eq!(
                serde_json::to_value(&rex.operands[0].operands[0].window).unwrap(),
                serde_json::to_value(&rex.operands[1].operands[0].window).unwrap()
            );
        }

        let mut direct_max_argument = raw.clone();
        let max = first_window_rex_mut(direct_max_argument.queries[0].rel.as_mut().unwrap(), "MAX")
            .expect("Q051 direct MAX window");
        let expansion = max.operands[0]
            .source_expansion
            .as_ref()
            .expect("MAX argument derived-output expansion");
        assert_eq!(expansion.reference_text, "web_sales");
        assert_eq!(expansion.definition_text, "web.cume_sales");
        assert_eq!(
            max.operands[0].source_text.as_deref(),
            Some(expansion.definition_text.as_str())
        );

        let mut whole_function_owner = raw.clone();
        let max =
            first_window_rex_mut(whole_function_owner.queries[0].rel.as_mut().unwrap(), "MAX")
                .expect("Q051 direct MAX window");
        let root_id = max.source_node_id.clone().unwrap();
        let root_start = root_id
            .strip_prefix("1:")
            .and_then(|id| id.split_once("-1:").map(|(start, _)| start))
            .and_then(|start| start.parse::<usize>().ok())
            .expect("single-line Q051 MAX span");
        let function_text = max
            .source_text
            .as_deref()
            .and_then(|source| source.split_once(" OVER ").map(|(function, _)| function))
            .unwrap()
            .to_owned();
        let operand = &mut max.operands[0];
        operand.source_expansion = None;
        operand.source_sql = Some(function_text.clone());
        operand.source_node_id = Some(format!(
            "1:{root_start}-1:{}",
            root_start + function_text.len() - 1
        ));
        operand.source_text = Some(function_text);
        operand.source_kind = Some("OTHER_FUNCTION".to_owned());
        operand.source_operator = Some("MAX".to_owned());
        operand.source_identifier_names.clear();
        operand.source_identifier_quoted.clear();
        assert!(
            convert_raw_file(whole_function_owner).is_err(),
            "Q051 accepted obsolete whole-MAX ownership for the direct argument"
        );

        let converted = convert_raw_file(raw.clone()).expect("convert exact nullable window SUMs");
        let mut order_name_drift = raw.clone();
        let sort = sort_mut(order_name_drift.queries[0].rel.as_mut().unwrap()).unwrap();
        sort.row_type[0].name = "forged_item_sk".to_owned();
        sort.inputs[0].row_type[0].name = "forged_item_sk".to_owned();
        assert!(
            convert_raw_file(order_name_drift).is_err(),
            "Q051 accepted a coherent generated WITH-output name mutation"
        );
        let mut order_index_drift = raw.clone();
        sort_mut(order_index_drift.queries[0].rel.as_mut().unwrap())
            .unwrap()
            .collation[0]
            .field_index = 1;
        assert!(
            convert_raw_file(order_index_drift).is_err(),
            "Q051 accepted a generated Sort-index mutation"
        );
        let mut normalized = Vec::new();
        collect_nested_window_sum_ir_exprs(&converted.queries[0].rel, &mut normalized);
        assert_eq!(normalized.len(), 2);
        for (expr, column) in normalized {
            assert!(matches!(
                &expr.parsed,
                ScalarAst::Window { parsed }
                    if parsed.function.eq_ignore_ascii_case("SUM")
                        && matches!(parsed.args.as_slice(), [ScalarAst::InputRef { index: 2 }])
            ));
            assert_eq!(
                column.ty,
                SqlType::Decimal {
                    precision: None,
                    scale: None
                }
            );
            assert!(column.nullable);
        }
        let (calls, aggregate_output) = first_ir_aggregate(&converted.queries[0].rel);
        assert_eq!(calls[0].function, "SUM");
        assert_eq!(
            aggregate_output[2].ty,
            SqlType::Decimal {
                precision: None,
                scale: None
            }
        );

        let exact_semantics = ir_scalar_asts(&converted.queries[0].rel);
        let mut rendered_window_drift = raw.clone();
        let root =
            first_nested_window_sum_rex_mut(rendered_window_drift.queries[0].rel.as_mut().unwrap())
                .unwrap();
        assert!(
            root.source_text
                .as_deref()
                .is_some_and(|text| text.to_ascii_lowercase().contains(" over ")),
            "nullable SUM rewrite must retain its exact source window"
        );
        root.source_sql = Some(
            "SUM(`diagnostic_only`) OVER (ORDER BY `diagnostic_only` DESC ROWS BETWEEN CURRENT ROW AND UNBOUNDED FOLLOWING)"
                .to_owned(),
        );
        let rendered_window_drift = convert_raw_file(rendered_window_drift)
            .expect("exact window text and frame override sourceSql");
        assert_eq!(
            ir_scalar_asts(&rendered_window_drift.queries[0].rel),
            exact_semantics,
            "rendered window/frame drift changed declarative semantics"
        );

        let mut exact_window_drift = raw.clone();
        first_nested_window_sum_rex_mut(exact_window_drift.queries[0].rel.as_mut().unwrap())
            .unwrap()
            .source_text = Some(
            "sum(diagnostic_only) over (order by diagnostic_only desc rows between current row and unbounded following)"
                .to_owned(),
        );
        assert!(
            convert_raw_file(exact_window_drift).is_err(),
            "changed exact window text must not validate against the original source span"
        );

        let reject = |label: &str, forged: CalciteFile| {
            let error = match convert_raw_file(forged) {
                Ok(_) => panic!("{label}: forged nullable window SUM unexpectedly converted"),
                Err(error) => error,
            };
            assert!(
                error.to_string().contains("window-SUM rewrite")
                    || error.to_string().contains("source literal")
                    || error.to_string().contains("generated operator")
                    || error.to_string().contains("exact typed input position")
                    || error.to_string().contains("exact source identifier"),
                "{label}: unexpected diagnostic: {error}"
            );
        };

        let mut zero = raw.clone();
        let root = first_nested_window_sum_rex_mut(zero.queries[0].rel.as_mut().unwrap()).unwrap();
        root.operands[0].operands[1].literal_value2 = Some("1".to_owned());
        reject("BIGINT zero payload", zero);

        let mut count_order = raw.clone();
        let root =
            first_nested_window_sum_rex_mut(count_order.queries[0].rel.as_mut().unwrap()).unwrap();
        root.operands[0].operands[0]
            .window
            .as_mut()
            .unwrap()
            .order_keys[0]
            .direction = "DESCENDING".to_owned();
        reject("COUNT window ordering", count_order);

        let mut sum_partition = raw.clone();
        let root = first_nested_window_sum_rex_mut(sum_partition.queries[0].rel.as_mut().unwrap())
            .unwrap();
        root.operands[1].operands[0]
            .window
            .as_mut()
            .unwrap()
            .partition_keys[0]
            .index = Some(1);
        reject("SUM window partition", sum_partition);

        let mut count_argument = raw.clone();
        let root = first_nested_window_sum_rex_mut(count_argument.queries[0].rel.as_mut().unwrap())
            .unwrap();
        root.operands[0].operands[0].operands[0].index = Some(1);
        reject("COUNT argument", count_argument);

        let mut sum_argument = raw.clone();
        let root =
            first_nested_window_sum_rex_mut(sum_argument.queries[0].rel.as_mut().unwrap()).unwrap();
        root.operands[1].operands[0].operands[0].index = Some(1);
        reject("SUM argument", sum_argument);

        let mut typed_null = raw.clone();
        let root =
            first_nested_window_sum_rex_mut(typed_null.queries[0].rel.as_mut().unwrap()).unwrap();
        root.operands[2].full_type = Some("DECIMAL(18, 2)".to_owned());
        reject("typed NULL result", typed_null);

        let mut source_identity = raw.clone();
        first_nested_window_sum_rex_mut(source_identity.queries[0].rel.as_mut().unwrap())
            .unwrap()
            .source_operator = Some("AVG".to_owned());
        reject("source aggregate identity", source_identity);

        let mut source_window_function = raw.clone();
        first_nested_window_sum_rex_mut(source_window_function.queries[0].rel.as_mut().unwrap())
            .unwrap()
            .source_window_function = Some("AVG".to_owned());
        reject("source window function", source_window_function);

        let mut child_window_function = raw.clone();
        first_nested_window_sum_rex_mut(child_window_function.queries[0].rel.as_mut().unwrap())
            .unwrap()
            .operands[0]
            .source_window_function = Some("SUM".to_owned());
        reject("generated child window function", child_window_function);

        let mut identifier_quote_shape = raw.clone();
        first_nested_window_sum_rex_mut(identifier_quote_shape.queries[0].rel.as_mut().unwrap())
            .unwrap()
            .operands[0]
            .operands[0]
            .operands[0]
            .source_identifier_quoted
            .clear();
        reject("source identifier quote arity", identifier_quote_shape);

        let mut aggregate_context = raw.clone();
        first_aggregate_mut(aggregate_context.queries[0].rel.as_mut().unwrap()).agg_call_details
            [0]
        .source_operands[0]
            .source_sql = Some("other_sales_price".to_owned());
        let aggregate_context = convert_raw_file(aggregate_context)
            .expect("rendered aggregate input sourceSql is diagnostic");
        assert_eq!(
            ir_scalar_asts(&aggregate_context.queries[0].rel),
            exact_semantics
        );

        let mut exact_aggregate_context = raw;
        first_aggregate_mut(exact_aggregate_context.queries[0].rel.as_mut().unwrap())
            .agg_call_details[0]
            .source_operands[0]
            .source_text = Some("other_sales_price".to_owned());
        assert!(convert_raw_file(exact_aggregate_context).is_err());
    });
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_compositional_subquery_provenance_is_mandatory_and_fail_closed() {
    fn first_scan(rel: &CalciteRel) -> Option<&CalciteRel> {
        if rel.rel_type == "LogicalTableScan" {
            return Some(rel);
        }
        rel.inputs.iter().find_map(first_scan)
    }

    fn first_scan_mut(rel: &mut CalciteRel) -> Option<&mut CalciteRel> {
        if rel.rel_type == "LogicalTableScan" {
            return Some(rel);
        }
        rel.inputs.iter_mut().find_map(first_scan_mut)
    }

    fn has_generated_no_from_unit(
        correspondence: &logos_ir::calcite::CalciteSourceRelCorrespondence,
    ) -> bool {
        correspondence.source_role == "GENERATED_NO_FROM_UNIT"
            || correspondence
                .inputs
                .iter()
                .any(|input| has_generated_no_from_unit(input.correspondence.as_ref()))
    }

    fn first_exact_t_rex(rel: &CalciteRel) -> Option<&CalciteRex> {
        for rex in rel_rexes(rel) {
            if rex.source_text.as_deref() == Some("t") {
                return Some(rex);
            }
        }
        rel.inputs.iter().find_map(first_exact_t_rex)
    }

    let repo = repo_root();
    let temp = temp_dir("mandatory-compositional-subquery-provenance");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&schema, "create table t(t integer, v integer);\n").unwrap();
    fs::write(
        &query,
        "select v from t where v = (select s.v from t as s);\n\
         select v from t where v = (select 1);\n\
         select t from t;\n",
    )
    .unwrap();

    let pristine = run_calcite_postgres_c(&repo, &schema, &query);
    assert_eq!(pristine.queries.len(), 3);
    for query_index in 0..2 {
        let subquery = find_first_scalar_subquery(
            pristine.queries[query_index]
                .rel
                .as_ref()
                .expect("source-attested scalar-subquery relation"),
        )
        .expect("RexSubQuery");
        assert!(subquery.source_node_id.is_some() && subquery.source_text.is_some());
        assert!(subquery.source_rel_correspondence.is_some());
    }
    let no_from = find_first_scalar_subquery(pristine.queries[1].rel.as_ref().unwrap()).unwrap();
    assert!(has_generated_no_from_unit(
        no_from.source_rel_correspondence.as_deref().unwrap()
    ));
    convert_raw_file(pristine.clone()).expect("convert exact compositional subqueries");

    for query_index in 0..2 {
        let mut deleted = pristine.clone();
        find_first_scalar_subquery_mut(deleted.queries[query_index].rel.as_mut().unwrap())
            .unwrap()
            .source_rel_correspondence = None;
        let error = convert_raw_file(deleted).unwrap_err();
        assert!(
            error
                .to_string()
                .contains("deletes required COMPOSITIONAL_RELATION_CORRESPONDENCE_V1"),
            "query {query_index} deleted correspondence reached a fallback: {error}"
        );
    }

    let mut cross_block_owner = pristine.clone();
    let outer = cross_block_owner.queries[0].rel.as_ref().unwrap();
    let borrowed_query = outer.source_query_block_id.clone().unwrap();
    let borrowed_node = outer.source_node_id.clone().unwrap();
    let borrowed_text = outer.source_text.clone().unwrap();
    let correspondence =
        find_first_scalar_subquery_mut(cross_block_owner.queries[0].rel.as_mut().unwrap())
            .unwrap()
            .source_rel_correspondence
            .as_deref_mut()
            .unwrap();
    correspondence.query_block_id = borrowed_query;
    correspondence.source_node_id = borrowed_node;
    correspondence.source_text = borrowed_text;

    let mut wrong_input_ordinal = pristine.clone();
    find_first_scalar_subquery_mut(wrong_input_ordinal.queries[0].rel.as_mut().unwrap())
        .unwrap()
        .source_rel_correspondence
        .as_deref_mut()
        .unwrap()
        .inputs[0]
        .input_ordinal = 1;

    let mut wrong_output_ordinal = pristine.clone();
    find_first_scalar_subquery_mut(wrong_output_ordinal.queries[0].rel.as_mut().unwrap())
        .unwrap()
        .source_rel_correspondence
        .as_deref_mut()
        .unwrap()
        .output_lineage[0]
        .output_index = 1;

    let mut wrong_dependency = pristine.clone();
    let dependency =
        &mut find_first_scalar_subquery_mut(wrong_dependency.queries[0].rel.as_mut().unwrap())
            .unwrap()
            .source_rel_correspondence
            .as_deref_mut()
            .unwrap()
            .output_lineage[0]
            .inputs[0]
            .input_output_index;
    *dependency = if *dependency == 0 { 1 } else { 0 };

    let outer_occurrence = first_scan(pristine.queries[0].rel.as_ref().unwrap())
        .unwrap()
        .source_table
        .as_ref()
        .unwrap()
        .relation_occurrence_id
        .clone();
    let mut borrowed_occurrence = pristine.clone();
    let inner_scan = first_scan_mut(
        find_first_scalar_subquery_mut(borrowed_occurrence.queries[0].rel.as_mut().unwrap())
            .unwrap()
            .subquery_rel
            .as_deref_mut()
            .unwrap(),
    )
    .unwrap();
    inner_scan.source_table.as_mut().unwrap().output_lineage[0].relation_occurrence_id =
        outer_occurrence;

    let mut duplicate_lineage = pristine.clone();
    let inner_scan = first_scan_mut(
        find_first_scalar_subquery_mut(duplicate_lineage.queries[0].rel.as_mut().unwrap())
            .unwrap()
            .subquery_rel
            .as_deref_mut()
            .unwrap(),
    )
    .unwrap();
    let source_table = inner_scan.source_table.as_mut().unwrap();
    source_table
        .output_lineage
        .push(source_table.output_lineage[0].clone());

    let mut fabricated_alias = pristine.clone();
    let inner_scan = first_scan_mut(
        find_first_scalar_subquery_mut(fabricated_alias.queries[0].rel.as_mut().unwrap())
            .unwrap()
            .subquery_rel
            .as_deref_mut()
            .unwrap(),
    )
    .unwrap();
    let source_table = inner_scan.source_table.as_mut().unwrap();
    source_table.alias_node_id = Some(source_table.relation_node_id.clone());
    source_table.alias_text = Some(source_table.relation_text.clone());
    source_table.alias_names = source_table.table_names.clone();
    source_table.alias_quoted = source_table.table_quoted.clone();

    for (label, mutation) in [
        ("cross-block owner", cross_block_owner),
        ("wrong input ordinal", wrong_input_ordinal),
        ("wrong output ordinal", wrong_output_ordinal),
        ("wrong dependency", wrong_dependency),
        ("borrowed relation occurrence", borrowed_occurrence),
        ("duplicate scan lineage", duplicate_lineage),
        ("fabricated alias", fabricated_alias),
    ] {
        assert!(
            convert_raw_file(mutation).is_err(),
            "accepted {label} provenance mutation"
        );
    }

    // Both tokens spell `t`, so a text-only occurrence check cannot
    // distinguish the SELECT column from the FROM relation.  Move the entire
    // internally coherent table-occurrence payload to the SELECT token; the
    // exact direct-FROM containment check must still reject it.
    let mut borrowed_select_token = pristine.clone();
    let (select_node_id, select_text) = {
        let rex = first_exact_t_rex(borrowed_select_token.queries[2].rel.as_ref().unwrap())
            .expect("SELECT-list t token");
        (
            rex.source_node_id.clone().unwrap(),
            rex.source_text.clone().unwrap(),
        )
    };
    let scan = first_scan_mut(borrowed_select_token.queries[2].rel.as_mut().unwrap()).unwrap();
    let source_table = scan.source_table.as_mut().unwrap();
    source_table.relation_occurrence_id = select_node_id.clone();
    source_table.relation_node_id = select_node_id.clone();
    source_table.relation_text = select_text.clone();
    source_table.table_node_id = select_node_id;
    source_table.table_text = select_text;
    for lineage in &mut source_table.output_lineage {
        lineage.relation_occurrence_id = source_table.relation_occurrence_id.clone();
    }
    assert!(
        convert_raw_file(borrowed_select_token).is_err(),
        "a coherent TableScan occurrence borrowed the identical SELECT token outside FROM"
    );

    fs::remove_dir_all(&temp).unwrap();
}

fn outer_filter_predicate(rel: &RelExpr) -> &ScalarExpr {
    let RelExpr::Project { input, .. } = rel else {
        panic!("expected outer project");
    };
    let RelExpr::Filter { predicate, .. } = input.as_ref() else {
        panic!("expected outer filter");
    };
    predicate
}

/// Collect only the declarative scalar ASTs carried by a relation. This is
/// intentionally narrower than comparing `RelExpr`: rendered source echoes
/// are diagnostic provenance and may differ while the exact-source-derived
/// SQL meaning remains identical.
fn ir_scalar_asts(rel: &RelExpr) -> Vec<ScalarAst> {
    fn collect(rel: &RelExpr, output: &mut Vec<ScalarAst>) {
        match rel {
            RelExpr::TableScan { .. } => {}
            RelExpr::Project { input, exprs, .. } => {
                output.extend(exprs.iter().map(|expr| expr.parsed.clone()));
                collect(input, output);
            }
            RelExpr::Filter {
                input, predicate, ..
            }
            | RelExpr::NativeHaving {
                input, predicate, ..
            } => {
                output.push(predicate.parsed.clone());
                collect(input, output);
            }
            RelExpr::Join {
                left,
                right,
                condition,
                ..
            } => {
                output.push(condition.parsed.clone());
                collect(left, output);
                collect(right, output);
            }
            RelExpr::Aggregate {
                input, agg_calls, ..
            } => {
                for call in agg_calls {
                    output.extend(call.args.iter().map(|arg| arg.parsed.clone()));
                    output.extend(call.filter.iter().map(|filter| filter.parsed.clone()));
                }
                collect(input, output);
            }
            RelExpr::Distinct { input, .. } => collect(input, output),
            RelExpr::Sort {
                input,
                fetch,
                offset,
                ..
            } => {
                output.extend(fetch.iter().map(|expr| expr.parsed.clone()));
                output.extend(offset.iter().map(|expr| expr.parsed.clone()));
                collect(input, output);
            }
            RelExpr::Set { inputs, .. } => {
                for input in inputs {
                    collect(input, output);
                }
            }
            RelExpr::Values { rows, .. } => {
                output.extend(
                    rows.iter()
                        .flat_map(|row| row.iter())
                        .map(|expr| expr.parsed.clone()),
                );
            }
        }
    }

    let mut output = Vec::new();
    collect(rel, &mut output);
    output
}

fn first_condition_rex(rel: &CalciteRel) -> &CalciteRex {
    if let Some(condition) = rel.condition_rex.as_ref() {
        return condition;
    }
    rel.inputs
        .iter()
        .find_map(|input| {
            (!input.inputs.is_empty() || input.condition_rex.is_some())
                .then(|| first_condition_rex(input))
        })
        .expect("expected a relational condition")
}

fn find_first_source_where_filter(rel: &CalciteRel) -> Option<&CalciteRel> {
    if rel.rel_type == "LogicalFilter" && rel.source_where.is_some() {
        return Some(rel);
    }
    for rex in rel.project_rex.iter().chain(rel.condition_rex.iter()) {
        if let Some(subquery) = rex.subquery_rel.as_deref()
            && let Some(found) = find_first_source_where_filter(subquery)
        {
            return Some(found);
        }
    }
    rel.inputs.iter().find_map(find_first_source_where_filter)
}

fn find_first_filter(rel: &CalciteRel) -> Option<&CalciteRel> {
    if rel.rel_type == "LogicalFilter" {
        return Some(rel);
    }
    rel.inputs.iter().find_map(find_first_filter)
}

fn find_first_filter_mut(rel: &mut CalciteRel) -> Option<&mut CalciteRel> {
    if rel.rel_type == "LogicalFilter" {
        return Some(rel);
    }
    for input in &mut rel.inputs {
        if let Some(found) = find_first_filter_mut(input) {
            return Some(found);
        }
    }
    None
}

fn find_first_source_where_filter_mut(rel: &mut CalciteRel) -> Option<&mut CalciteRel> {
    if rel.rel_type == "LogicalFilter" && rel.source_where.is_some() {
        return Some(rel);
    }
    for input in &mut rel.inputs {
        if let Some(found) = find_first_source_where_filter_mut(input) {
            return Some(found);
        }
    }
    None
}

fn find_rex_by_source_sql<'a>(rex: &'a CalciteRex, source_sql: &str) -> Option<&'a CalciteRex> {
    if rex.source_sql.as_deref() == Some(source_sql) {
        return Some(rex);
    }
    rex.operands
        .iter()
        .find_map(|operand| find_rex_by_source_sql(operand, source_sql))
}

fn find_rex_by_source_sql_mut<'a>(
    rex: &'a mut CalciteRex,
    source_sql: &str,
) -> Option<&'a mut CalciteRex> {
    if rex.source_sql.as_deref() == Some(source_sql) {
        return Some(rex);
    }
    for operand in &mut rex.operands {
        if let Some(found) = find_rex_by_source_sql_mut(operand, source_sql) {
            return Some(found);
        }
    }
    None
}

fn find_rel_rex_by_exact_source_sql<'a>(
    rel: &'a CalciteRel,
    source_sql: &str,
) -> Option<&'a CalciteRex> {
    for rex in rel_rexes(rel) {
        if rex.source_sql.as_deref() == Some(source_sql) {
            return Some(rex);
        }
        if let Some(found) = find_rex_by_source_sql(rex, source_sql) {
            return Some(found);
        }
        if let Some(found) = rex
            .subquery_rel
            .as_deref()
            .and_then(|subquery| find_rel_rex_by_exact_source_sql(subquery, source_sql))
        {
            return Some(found);
        }
    }
    rel.inputs
        .iter()
        .find_map(|input| find_rel_rex_by_exact_source_sql(input, source_sql))
}

fn find_rel_rex_by_source_kind<'a>(
    rel: &'a CalciteRel,
    source_kind: &str,
) -> Option<&'a CalciteRex> {
    for rex in rel.project_rex.iter().chain(rel.condition_rex.iter()) {
        if rex.source_kind.as_deref() == Some(source_kind) {
            return Some(rex);
        }
        if let Some(found) = find_rex_by_source_kind(rex, source_kind) {
            return Some(found);
        }
    }
    rel.inputs
        .iter()
        .find_map(|input| find_rel_rex_by_source_kind(input, source_kind))
}

fn find_rex_by_source_kind<'a>(rex: &'a CalciteRex, source_kind: &str) -> Option<&'a CalciteRex> {
    rex.operands.iter().find_map(|operand| {
        (operand.source_kind.as_deref() == Some(source_kind))
            .then_some(operand)
            .or_else(|| find_rex_by_source_kind(operand, source_kind))
    })
}

fn find_rel_rex_by_source_kind_mut<'a>(
    rel: &'a mut CalciteRel,
    source_kind: &str,
) -> Option<&'a mut CalciteRex> {
    for rex in &mut rel.project_rex {
        if rex.source_kind.as_deref() == Some(source_kind) {
            return Some(rex);
        }
        if let Some(found) = find_rex_by_source_kind_mut(rex, source_kind) {
            return Some(found);
        }
    }
    if let Some(rex) = rel.condition_rex.as_mut() {
        if rex.source_kind.as_deref() == Some(source_kind) {
            return Some(rex);
        }
        if let Some(found) = find_rex_by_source_kind_mut(rex, source_kind) {
            return Some(found);
        }
    }
    for input in &mut rel.inputs {
        if let Some(found) = find_rel_rex_by_source_kind_mut(input, source_kind) {
            return Some(found);
        }
    }
    None
}

fn find_rex_by_source_kind_mut<'a>(
    rex: &'a mut CalciteRex,
    source_kind: &str,
) -> Option<&'a mut CalciteRex> {
    for operand in &mut rex.operands {
        if operand.source_kind.as_deref() == Some(source_kind) {
            return Some(operand);
        }
        if let Some(found) = find_rex_by_source_kind_mut(operand, source_kind) {
            return Some(found);
        }
    }
    None
}

fn find_first_in_subquery(rel: &CalciteRel) -> Option<&CalciteRex> {
    for rex in rel_rexes(rel) {
        if let Some(found) = find_first_in_subquery_rex(rex) {
            return Some(found);
        }
    }
    rel.inputs.iter().find_map(find_first_in_subquery)
}

fn find_first_in_subquery_rex(rex: &CalciteRex) -> Option<&CalciteRex> {
    if rex.class.as_deref() == Some("RexSubQuery") && rex.source_kind.as_deref() == Some("IN") {
        return Some(rex);
    }
    for operand in &rex.operands {
        if let Some(found) = find_first_in_subquery_rex(operand) {
            return Some(found);
        }
    }
    rex.subquery_rel.as_deref().and_then(find_first_in_subquery)
}

fn find_first_in_subquery_mut(rel: &mut CalciteRel) -> Option<&mut CalciteRex> {
    for rex in &mut rel.project_rex {
        if let Some(found) = find_first_in_subquery_rex_mut(rex) {
            return Some(found);
        }
    }
    if let Some(rex) = rel.condition_rex.as_mut()
        && let Some(found) = find_first_in_subquery_rex_mut(rex)
    {
        return Some(found);
    }
    if let Some(rex) = rel.fetch_rex.as_mut()
        && let Some(found) = find_first_in_subquery_rex_mut(rex)
    {
        return Some(found);
    }
    if let Some(rex) = rel.offset_rex.as_mut()
        && let Some(found) = find_first_in_subquery_rex_mut(rex)
    {
        return Some(found);
    }
    for input in &mut rel.inputs {
        if let Some(found) = find_first_in_subquery_mut(input) {
            return Some(found);
        }
    }
    None
}

fn find_first_in_subquery_rex_mut(rex: &mut CalciteRex) -> Option<&mut CalciteRex> {
    if rex.class.as_deref() == Some("RexSubQuery") && rex.source_kind.as_deref() == Some("IN") {
        return Some(rex);
    }
    for operand in &mut rex.operands {
        if let Some(found) = find_first_in_subquery_rex_mut(operand) {
            return Some(found);
        }
    }
    rex.subquery_rel
        .as_deref_mut()
        .and_then(find_first_in_subquery_mut)
}

fn find_first_scalar_subquery(rel: &CalciteRel) -> Option<&CalciteRex> {
    for rex in rel_rexes(rel) {
        if let Some(found) = find_first_scalar_subquery_rex(rex) {
            return Some(found);
        }
    }
    rel.inputs.iter().find_map(find_first_scalar_subquery)
}

fn find_first_scalar_subquery_rex(rex: &CalciteRex) -> Option<&CalciteRex> {
    if rex.class.as_deref() == Some("RexSubQuery") && rex.op_kind.as_deref() == Some("SCALAR_QUERY")
    {
        return Some(rex);
    }
    for operand in &rex.operands {
        if let Some(found) = find_first_scalar_subquery_rex(operand) {
            return Some(found);
        }
    }
    rex.subquery_rel
        .as_deref()
        .and_then(find_first_scalar_subquery)
}

fn find_first_scalar_subquery_mut(rel: &mut CalciteRel) -> Option<&mut CalciteRex> {
    for rex in &mut rel.project_rex {
        if let Some(found) = find_first_scalar_subquery_rex_mut(rex) {
            return Some(found);
        }
    }
    if let Some(rex) = rel.condition_rex.as_mut()
        && let Some(found) = find_first_scalar_subquery_rex_mut(rex)
    {
        return Some(found);
    }
    if let Some(rex) = rel.fetch_rex.as_mut()
        && let Some(found) = find_first_scalar_subquery_rex_mut(rex)
    {
        return Some(found);
    }
    if let Some(rex) = rel.offset_rex.as_mut()
        && let Some(found) = find_first_scalar_subquery_rex_mut(rex)
    {
        return Some(found);
    }
    for input in &mut rel.inputs {
        if let Some(found) = find_first_scalar_subquery_mut(input) {
            return Some(found);
        }
    }
    None
}

fn find_first_scalar_subquery_rex_mut(rex: &mut CalciteRex) -> Option<&mut CalciteRex> {
    if rex.class.as_deref() == Some("RexSubQuery") && rex.op_kind.as_deref() == Some("SCALAR_QUERY")
    {
        return Some(rex);
    }
    for operand in &mut rex.operands {
        if let Some(found) = find_first_scalar_subquery_rex_mut(operand) {
            return Some(found);
        }
    }
    rex.subquery_rel
        .as_deref_mut()
        .and_then(find_first_scalar_subquery_mut)
}

fn collect_nested_window_sum_rexes<'a>(rel: &'a CalciteRel, output: &mut Vec<&'a CalciteRex>) {
    for rex in rel_rexes(rel) {
        if rex
            .source_sql
            .as_deref()
            .is_some_and(|source| source.starts_with("SUM(SUM("))
            && rex.source_kind.as_deref() == Some("OVER")
        {
            output.push(rex);
        }
        collect_nested_window_sum_rexes_from_rex(rex, output);
    }
    for input in &rel.inputs {
        collect_nested_window_sum_rexes(input, output);
    }
}

fn collect_nested_window_sum_rexes_from_rex<'a>(
    rex: &'a CalciteRex,
    output: &mut Vec<&'a CalciteRex>,
) {
    for operand in &rex.operands {
        if operand
            .source_sql
            .as_deref()
            .is_some_and(|source| source.starts_with("SUM(SUM("))
            && operand.source_kind.as_deref() == Some("OVER")
        {
            output.push(operand);
        }
        collect_nested_window_sum_rexes_from_rex(operand, output);
    }
    if let Some(subquery) = rex.subquery_rel.as_deref() {
        collect_nested_window_sum_rexes(subquery, output);
    }
}

fn first_nested_window_sum_rex_mut(rel: &mut CalciteRel) -> Option<&mut CalciteRex> {
    for rex in &mut rel.project_rex {
        if rex
            .source_sql
            .as_deref()
            .is_some_and(|source| source.starts_with("SUM(SUM("))
            && rex.source_kind.as_deref() == Some("OVER")
        {
            return Some(rex);
        }
    }
    for input in &mut rel.inputs {
        if let Some(found) = first_nested_window_sum_rex_mut(input) {
            return Some(found);
        }
    }
    None
}

fn first_window_rex_mut<'a>(rel: &'a mut CalciteRel, function: &str) -> Option<&'a mut CalciteRex> {
    fn visit<'a>(rex: &'a mut CalciteRex, function: &str) -> Option<&'a mut CalciteRex> {
        if rex.class.as_deref() == Some("RexOver") && rex.kind.as_deref() == Some(function) {
            return Some(rex);
        }
        for operand in &mut rex.operands {
            if let Some(found) = visit(operand, function) {
                return Some(found);
            }
        }
        None
    }

    for rex in &mut rel.project_rex {
        if let Some(found) = visit(rex, function) {
            return Some(found);
        }
    }
    for input in &mut rel.inputs {
        if let Some(found) = first_window_rex_mut(input, function) {
            return Some(found);
        }
    }
    None
}

fn collect_nested_window_sum_ir_exprs<'a>(
    rel: &'a RelExpr,
    output: &mut Vec<(&'a ScalarExpr, &'a logos_ir::ir::Column)>,
) {
    match rel {
        RelExpr::Project {
            input,
            exprs,
            output: columns,
            ..
        } => {
            output.extend(exprs.iter().zip(columns).filter(|(expr, _)| {
                expr.source
                    .as_ref()
                    .and_then(|source| source.sql.as_deref())
                    .is_some_and(|source| source.starts_with("SUM(SUM("))
            }));
            collect_nested_window_sum_ir_exprs(input, output);
        }
        RelExpr::Filter { input, .. }
        | RelExpr::NativeHaving { input, .. }
        | RelExpr::Aggregate { input, .. }
        | RelExpr::Distinct { input, .. }
        | RelExpr::Sort { input, .. } => collect_nested_window_sum_ir_exprs(input, output),
        RelExpr::Join { left, right, .. } => {
            collect_nested_window_sum_ir_exprs(left, output);
            collect_nested_window_sum_ir_exprs(right, output);
        }
        RelExpr::Set { inputs, .. } => {
            for input in inputs {
                collect_nested_window_sum_ir_exprs(input, output);
            }
        }
        RelExpr::TableScan { .. } | RelExpr::Values { .. } => {}
    }
}

fn find_rel_rex_by_source_fragment<'a>(
    rel: &'a CalciteRel,
    fragment: &str,
) -> Option<&'a CalciteRex> {
    for rex in rel.project_rex.iter().chain(rel.condition_rex.iter()) {
        if rex
            .source_sql
            .as_deref()
            .is_some_and(|source| source.contains(fragment))
        {
            return Some(rex);
        }
        if let Some(found) = find_rex_by_source_fragment(rex, fragment) {
            return Some(found);
        }
    }
    rel.inputs
        .iter()
        .find_map(|input| find_rel_rex_by_source_fragment(input, fragment))
}

fn find_generated_coalesce(rel: &CalciteRel) -> Option<&CalciteRex> {
    fn in_rex(rex: &CalciteRex) -> Option<&CalciteRex> {
        if rex.kind.as_deref() == Some("CASE")
            && rex
                .source_operator
                .as_deref()
                .is_some_and(|operator| operator.eq_ignore_ascii_case("COALESCE"))
        {
            return Some(rex);
        }
        for operand in &rex.operands {
            if let Some(found) = in_rex(operand) {
                return Some(found);
            }
        }
        rex.subquery_rel
            .as_deref()
            .and_then(find_generated_coalesce)
    }

    rel_rexes(rel)
        .find_map(in_rex)
        .or_else(|| rel.inputs.iter().find_map(find_generated_coalesce))
}

fn find_generated_coalesce_mut(rel: &mut CalciteRel) -> Option<&mut CalciteRex> {
    fn in_rex(rex: &mut CalciteRex) -> Option<&mut CalciteRex> {
        if rex.kind.as_deref() == Some("CASE")
            && rex
                .source_operator
                .as_deref()
                .is_some_and(|operator| operator.eq_ignore_ascii_case("COALESCE"))
        {
            return Some(rex);
        }
        for operand in &mut rex.operands {
            if let Some(found) = in_rex(operand) {
                return Some(found);
            }
        }
        rex.subquery_rel
            .as_deref_mut()
            .and_then(find_generated_coalesce_mut)
    }

    for rex in rel
        .project_rex
        .iter_mut()
        .chain(rel.condition_rex.iter_mut())
    {
        if let Some(found) = in_rex(rex) {
            return Some(found);
        }
    }
    for input in &mut rel.inputs {
        if let Some(found) = find_generated_coalesce_mut(input) {
            return Some(found);
        }
    }
    None
}

fn find_rex_by_source_fragment<'a>(rex: &'a CalciteRex, fragment: &str) -> Option<&'a CalciteRex> {
    rex.operands.iter().find_map(|operand| {
        operand
            .source_sql
            .as_deref()
            .is_some_and(|source| source.contains(fragment))
            .then_some(operand)
            .or_else(|| find_rex_by_source_fragment(operand, fragment))
    })
}

fn find_rex_subquery_root<'a>(rex: &'a CalciteRex, rel_type: &str) -> Option<&'a CalciteRex> {
    if rex.class.as_deref() == Some("RexSubQuery")
        && rex
            .subquery_rel
            .as_deref()
            .is_some_and(|rel| rel.rel_type == rel_type)
    {
        return Some(rex);
    }
    rex.operands
        .iter()
        .find_map(|operand| find_rex_subquery_root(operand, rel_type))
}

fn find_rex_subquery_root_mut<'a>(
    rex: &'a mut CalciteRex,
    rel_type: &str,
) -> Option<&'a mut CalciteRex> {
    if rex.class.as_deref() == Some("RexSubQuery")
        && rex
            .subquery_rel
            .as_deref()
            .is_some_and(|rel| rel.rel_type == rel_type)
    {
        return Some(rex);
    }
    for operand in &mut rex.operands {
        if let Some(found) = find_rex_subquery_root_mut(operand, rel_type) {
            return Some(found);
        }
    }
    None
}

fn find_rel_type_mut<'a>(rel: &'a mut CalciteRel, rel_type: &str) -> Option<&'a mut CalciteRel> {
    if rel.rel_type == rel_type {
        return Some(rel);
    }
    for input in &mut rel.inputs {
        if let Some(found) = find_rel_type_mut(input, rel_type) {
            return Some(found);
        }
    }
    None
}

fn find_rex_field_access_mut(rex: &mut CalciteRex) -> Option<&mut CalciteRex> {
    if rex.class.as_deref() == Some("RexFieldAccess") {
        return Some(rex);
    }
    for operand in &mut rex.operands {
        if let Some(found) = find_rex_field_access_mut(operand) {
            return Some(found);
        }
    }
    if let Some(subquery) = rex.subquery_rel.as_deref_mut() {
        return find_rel_field_access_mut(subquery);
    }
    None
}

fn find_rel_field_access_mut(rel: &mut CalciteRel) -> Option<&mut CalciteRex> {
    for rex in &mut rel.project_rex {
        if let Some(found) = find_rex_field_access_mut(rex) {
            return Some(found);
        }
    }
    if let Some(condition) = rel.condition_rex.as_mut()
        && let Some(found) = find_rex_field_access_mut(condition)
    {
        return Some(found);
    }
    for input in &mut rel.inputs {
        if let Some(found) = find_rel_field_access_mut(input) {
            return Some(found);
        }
    }
    None
}

fn first_aggregate(rel: &CalciteRel) -> &CalciteRel {
    if !rel.agg_call_details.is_empty() {
        return rel;
    }
    rel.inputs
        .iter()
        .find_map(|input| {
            (!input.inputs.is_empty() || !input.agg_call_details.is_empty())
                .then(|| first_aggregate(input))
        })
        .expect("expected an aggregate")
}

fn first_aggregate_mut(rel: &mut CalciteRel) -> &mut CalciteRel {
    if !rel.agg_call_details.is_empty() {
        return rel;
    }
    for input in &mut rel.inputs {
        if !input.inputs.is_empty() || !input.agg_call_details.is_empty() {
            return first_aggregate_mut(input);
        }
    }
    panic!("expected an aggregate")
}

fn collect_aggregates<'a>(rel: &'a CalciteRel, output: &mut Vec<&'a CalciteRel>) {
    if !rel.agg_call_details.is_empty() {
        output.push(rel);
    }
    for input in &rel.inputs {
        collect_aggregates(input, output);
    }
}

fn first_ir_aggregate(rel: &RelExpr) -> (&[logos_ir::ir::AggregateCall], &[logos_ir::ir::Column]) {
    match rel {
        RelExpr::Aggregate {
            agg_calls, output, ..
        } => (agg_calls, output),
        RelExpr::Project { input, .. }
        | RelExpr::Filter { input, .. }
        | RelExpr::NativeHaving { input, .. }
        | RelExpr::Distinct { input, .. }
        | RelExpr::Sort { input, .. } => first_ir_aggregate(input),
        RelExpr::Join { left, right, .. } => {
            if contains_ir_aggregate(left) {
                first_ir_aggregate(left)
            } else {
                first_ir_aggregate(right)
            }
        }
        RelExpr::Set { inputs, .. } => inputs
            .iter()
            .find(|input| contains_ir_aggregate(input))
            .map(first_ir_aggregate)
            .expect("expected an aggregate"),
        RelExpr::TableScan { .. } | RelExpr::Values { .. } => {
            panic!("expected an aggregate")
        }
    }
}

fn contains_ir_aggregate(rel: &RelExpr) -> bool {
    match rel {
        RelExpr::Aggregate { .. } => true,
        RelExpr::Project { input, .. }
        | RelExpr::Filter { input, .. }
        | RelExpr::NativeHaving { input, .. }
        | RelExpr::Distinct { input, .. }
        | RelExpr::Sort { input, .. } => contains_ir_aggregate(input),
        RelExpr::Join { left, right, .. } => {
            contains_ir_aggregate(left) || contains_ir_aggregate(right)
        }
        RelExpr::Set { inputs, .. } => inputs.iter().any(contains_ir_aggregate),
        RelExpr::TableScan { .. } | RelExpr::Values { .. } => false,
    }
}

fn rel_contains_search(rel: &CalciteRel) -> bool {
    rel_rexes(rel).any(rex_contains_search) || rel.inputs.iter().any(rel_contains_search)
}

fn rel_contains_unprovenanced_noncartesian_literal(rel: &CalciteRel) -> bool {
    rel_rexes(rel).any(rex_contains_unprovenanced_noncartesian_literal)
        || rel
            .inputs
            .iter()
            .any(rel_contains_unprovenanced_noncartesian_literal)
}

fn rel_contains_literal_with_identifier_source(rel: &CalciteRel) -> bool {
    rel_rexes(rel).any(rex_contains_literal_with_identifier_source)
        || rel
            .inputs
            .iter()
            .any(rel_contains_literal_with_identifier_source)
}

fn rel_rexes(rel: &CalciteRel) -> impl Iterator<Item = &CalciteRex> {
    rel.project_rex
        .iter()
        .chain(rel.condition_rex.iter())
        .chain(rel.fetch_rex.iter())
        .chain(rel.offset_rex.iter())
        .chain(
            rel.tuples
                .iter()
                .flat_map(|rows| rows.iter().flat_map(|row| row.iter())),
        )
}

fn rex_contains_search(rex: &CalciteRex) -> bool {
    rex.op_kind.as_deref() == Some("SEARCH")
        || rex.operands.iter().any(rex_contains_search)
        || rex.subquery_rel.as_deref().is_some_and(rel_contains_search)
        || rex.window.as_deref().is_some_and(|window| {
            window.partition_keys.iter().any(rex_contains_search)
                || window
                    .order_keys
                    .iter()
                    .any(|key| rex_contains_search(&key.expr))
                || window
                    .lower_bound
                    .as_deref()
                    .and_then(|bound| bound.offset.as_deref())
                    .is_some_and(rex_contains_search)
                || window
                    .upper_bound
                    .as_deref()
                    .and_then(|bound| bound.offset.as_deref())
                    .is_some_and(rex_contains_search)
        })
}

fn rex_contains_unprovenanced_noncartesian_literal(rex: &CalciteRex) -> bool {
    rex.class.as_deref() == Some("RexLiteral")
        && rex.source_sql.is_none()
        && rex.text.as_deref() != Some("true")
        || rex
            .operands
            .iter()
            .any(rex_contains_unprovenanced_noncartesian_literal)
        || rex
            .subquery_rel
            .as_deref()
            .is_some_and(rel_contains_unprovenanced_noncartesian_literal)
        || rex.window.as_deref().is_some_and(|window| {
            window
                .partition_keys
                .iter()
                .any(rex_contains_unprovenanced_noncartesian_literal)
                || window
                    .order_keys
                    .iter()
                    .any(|key| rex_contains_unprovenanced_noncartesian_literal(&key.expr))
                || window
                    .lower_bound
                    .as_deref()
                    .and_then(|bound| bound.offset.as_deref())
                    .is_some_and(rex_contains_unprovenanced_noncartesian_literal)
                || window
                    .upper_bound
                    .as_deref()
                    .and_then(|bound| bound.offset.as_deref())
                    .is_some_and(rex_contains_unprovenanced_noncartesian_literal)
        })
}

fn rex_contains_literal_with_identifier_source(rex: &CalciteRex) -> bool {
    rex.class.as_deref() == Some("RexLiteral") && rex.source_kind.as_deref() == Some("IDENTIFIER")
        || rex
            .operands
            .iter()
            .any(rex_contains_literal_with_identifier_source)
        || rex
            .subquery_rel
            .as_deref()
            .is_some_and(rel_contains_literal_with_identifier_source)
        || rex.window.as_deref().is_some_and(|window| {
            window
                .partition_keys
                .iter()
                .any(rex_contains_literal_with_identifier_source)
                || window
                    .order_keys
                    .iter()
                    .any(|key| rex_contains_literal_with_identifier_source(&key.expr))
                || window
                    .lower_bound
                    .as_deref()
                    .and_then(|bound| bound.offset.as_deref())
                    .is_some_and(rex_contains_literal_with_identifier_source)
                || window
                    .upper_bound
                    .as_deref()
                    .and_then(|bound| bound.offset.as_deref())
                    .is_some_and(rex_contains_literal_with_identifier_source)
        })
}

fn scalar_contains_annotation(ast: &ScalarAst, expected: &str) -> bool {
    match ast {
        ScalarAst::TypeAnnotation { expr, ty } => {
            ty == expected || scalar_contains_annotation(expr, expected)
        }
        ScalarAst::Call { args, .. } => args
            .iter()
            .any(|arg| scalar_contains_annotation(arg, expected)),
        _ => false,
    }
}

#[test]
#[ignore = "requires the Java Calcite wrapper and frozen benchmark corpus"]
fn calcite_wrapper_closes_relation_output_lineage_frontier() {
    with_large_calcite_stack(|| {
        let repo = repo_root();
        let cases = [
            "rbot-dsb__query014",
            "rbot-dsb__query039",
            "rbot-dsb__query054",
            "rbot-dsb__query058",
            "rbot-dsb__query059",
            "rbot-dsb__query064",
            "rbot-dsb__query083",
            "tpcds-variants__query014",
            "tpcds-variants__query077",
            "rbot-tpch__query13",
            "rbot-tpch__query22",
            "rbot-tpch__query7",
            "rbot-tpch__query8",
            "rbot-tpch__query9",
            "verieql-calcite__calcite-122",
            "verieql-calcite__calcite-209",
            "verieql-calcite__calcite-212",
            "verieql-calcite__calcite-343",
            "verieql-calcite__calcite-79",
        ];
        let selected = std::env::var("LOGOS_LINEAGE_CASE").ok();
        for case in cases
            .into_iter()
            .filter(|case| selected.as_deref().is_none_or(|selected| selected == *case))
        {
            let directory = repo
                .join("benchmarks/core/.generated/sqlsolver/nonwetune-flat")
                .join(case);
            for query_name in ["sql1.sql", "sql2.sql"] {
                eprintln!("checking {case}/{query_name}");
                let raw = run_calcite_postgres_c(
                    &repo,
                    &directory.join("schema.sql"),
                    &directory.join(query_name),
                );
                let converted = convert_raw_file(raw);
                if matches!(
                    case,
                    "rbot-dsb__query054" | "tpcds-variants__query014" | "tpcds-variants__query077"
                ) {
                    converted.unwrap_or_else(|error| {
                        panic!("{case}/{query_name} required relation lineage failed: {error}")
                    });
                } else if let Err(error) = converted {
                    let diagnostic = error.to_string();
                    assert!(
                        !diagnostic.contains("exact source identifier")
                            || !diagnostic.contains("does not resolve to generated input"),
                        "{case}/{query_name} relation-output lineage regressed: {diagnostic}"
                    );
                }
            }
        }
    });
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_attests_postgres_ambiguous_derived_wildcard_outputs() {
    with_large_calcite_stack(|| {
        fn exact_one_line_fragment(sql: &str, span: &str) -> String {
            let (start, end) = span.split_once('-').expect("source span range");
            let (start_line, start_column) = start.split_once(':').expect("source span start");
            let (end_line, end_column) = end.split_once(':').expect("source span end");
            assert_eq!((start_line, end_line), ("1", "1"));
            assert!(sql.is_ascii(), "fixture uses byte-identical ASCII columns");
            sql[start_column.parse::<usize>().unwrap() - 1..end_column.parse::<usize>().unwrap()]
                .to_owned()
        }

        let repo = repo_root();
        let frozen = repo.join("benchmarks/core/.generated/sqlsolver/nonwetune-flat");
        for case in [
            "verieql-calcite__calcite-209",
            "verieql-calcite__calcite-343",
        ] {
            let directory = frozen.join(case);
            let source = fs::read_to_string(directory.join("sql2.sql")).unwrap();
            let raw = run_calcite(
                &repo,
                &directory.join("schema.sql"),
                &directory.join("sql2.sql"),
            );
            let query = &raw.queries[0];
            assert!(query.error.is_none(), "{case}: Calcite conversion");
            let marker = query
                .source_ambiguous_column_error
                .as_ref()
                .unwrap_or_else(|| panic!("{case}: exact 42702 marker"));
            assert_eq!(
                marker.kind, "POSTGRES_UNQUALIFIED_DERIVED_OUTPUT_AMBIGUOUS_COLUMN",
                "{case}"
            );
            assert_eq!(marker.sql_state, "42702", "{case}");
            assert_eq!(marker.duplicate_count, 2, "{case}");
            assert_eq!(
                marker
                    .matching_outputs
                    .iter()
                    .map(|output| output.output_index)
                    .collect::<Vec<_>>(),
                [6, 15],
                "{case}: ordered exhaustive public matches"
            );
            for (span, text) in [
                (&marker.query_block_id, &marker.source_query_block_sql),
                (
                    &marker.source_identifier_node_id,
                    &marker.source_identifier_sql,
                ),
                (&marker.source_relation_node_id, &marker.source_relation_sql),
            ] {
                assert_eq!(exact_one_line_fragment(&source, span), *text, "{case}");
            }
            let mut origin_spans = std::collections::BTreeSet::new();
            for output in &marker.matching_outputs {
                assert_eq!(output.output_name, "sal", "{case}");
                assert_eq!(
                    exact_one_line_fragment(&source, &output.source_output_item_node_id),
                    output.source_output_item_sql,
                    "{case}"
                );
                assert_eq!(output.source_output_item_sql, "*", "{case}");
                assert_eq!(
                    exact_one_line_fragment(&source, &output.source_origin_relation_node_id),
                    output.source_origin_relation_sql,
                    "{case}"
                );
                assert!(
                    origin_spans.insert(&output.source_origin_relation_node_id),
                    "{case}: each duplicate must have a distinct direct origin"
                );
            }

            let converted = convert_raw_file(raw.clone()).unwrap();
            assert!(converted.queries[0].analysis_errors.iter().any(|error| {
                matches!(
                    error,
                    QueryAnalysisError::PostgresAmbiguousDerivedOutputColumn {
                        sql_state,
                        identifier_name,
                        duplicate_count: 2,
                        matching_outputs,
                        ..
                    } if sql_state == "42702"
                        && identifier_name == "sal"
                        && matching_outputs.iter().map(|output| output.output_index)
                            .eq([6, 15])
                )
            }));

            let assert_rejected = |mutated: CalciteFile, label: &str| {
                assert!(
                    matches!(
                        convert_raw_file(mutated),
                        Err(logos_ir::Error::InvalidRelSourceProvenance(_))
                    ),
                    "{case}: forged ambiguous-column {label} must fail closed"
                );
            };
            let mut missing = raw.clone();
            missing.queries[0].source_ambiguous_column_error = None;
            assert_rejected(missing, "missing marker");

            let mut wrong_count = raw.clone();
            wrong_count.queries[0]
                .source_ambiguous_column_error
                .as_mut()
                .unwrap()
                .duplicate_count = 1;
            assert_rejected(wrong_count, "duplicate count");

            let mut wrong_origin = raw.clone();
            let forged_origin = wrong_origin.queries[0]
                .source_ambiguous_column_error
                .as_ref()
                .unwrap()
                .matching_outputs[1]
                .source_origin_relation_node_id
                .clone();
            wrong_origin.queries[0]
                .source_ambiguous_column_error
                .as_mut()
                .unwrap()
                .matching_outputs[0]
                .source_origin_relation_node_id = forged_origin;
            assert_rejected(wrong_origin, "origin span");

            let mut wrong_root_name = raw.clone();
            wrong_root_name.queries[0].rel.as_mut().unwrap().row_type[0].name = "SAL".to_owned();
            assert_rejected(wrong_root_name, "root output name");

            let mut wrong_candidate_type = raw.clone();
            wrong_candidate_type.queries[0].rel.as_mut().unwrap().inputs[0].row_type[15].ty =
                "BIGINT".to_owned();
            assert_rejected(wrong_candidate_type, "candidate type");

            let non_error = run_calcite(
                &repo,
                &directory.join("schema.sql"),
                &directory.join("sql1.sql"),
            );
            assert!(
                non_error.queries[0].source_ambiguous_column_error.is_none(),
                "{case}: qualified/non-ambiguous source must not borrow 42702"
            );
        }

        let temp = temp_dir("postgres-ambiguous-derived-wildcard-fail-closed");
        let schema = temp.join("schema.sql");
        let query = temp.join("query.sql");
        fs::copy(
            frozen.join("verieql-calcite__calcite-209/schema.sql"),
            &schema,
        )
        .unwrap();
        let duplicate_relation = "(SELECT * FROM EMP AS EMP2, (SELECT * FROM EMP) AS t3 \
UNION ALL SELECT * FROM EMP AS EMP4, (SELECT * FROM EMP) AS t4) AS t5";
        fs::write(
        &query,
        format!(
            "SELECT t5.SAL FROM {duplicate_relation};\n\
             SELECT SAL FROM (SELECT * FROM EMP AS EMP2 UNION ALL SELECT * FROM EMP AS EMP4) AS t5;\n\
             SELECT NOSUCH FROM {duplicate_relation};\n\
             SELECT SAL FROM (SELECT * FROM EMP AS EMP2 UNION ALL SELECT * FROM EMP AS EMP4) \
AS t5(EMPNO, DEPTNO, ENAME, JOB, MGR, HIREDATE, SAL, COMM, SLACKER);\n\
             SELECT SAL FROM (SELECT EMP2.SAL, t3.SAL FROM EMP AS EMP2, \
(SELECT * FROM EMP) AS t3 UNION ALL SELECT EMP4.SAL, t4.SAL FROM EMP AS EMP4, \
(SELECT * FROM EMP) AS t4) AS t5;\n"
        ),
    )
    .unwrap();
        let probes = run_calcite(&repo, &schema, &query);
        assert_eq!(probes.queries.len(), 5);
        assert!(
            probes
                .queries
                .iter()
                .all(|query| query.source_ambiguous_column_error.is_none()),
            "qualified, unique, missing, explicit-column-list, and explicit-projection \
         shapes must all withhold the narrow 42702 marker"
        );
        assert!(
            probes.queries[0].error.is_none(),
            "qualified probe remains valid"
        );
        assert!(
            probes.queries[1].error.is_none(),
            "unique probe remains valid"
        );
        assert!(
            probes.queries[2].error.is_some(),
            "missing probe is rejected"
        );
        assert!(
            probes.queries[3].error.is_none(),
            "explicit column-list probe remains valid"
        );
        assert!(
            probes.queries[4].error.is_some(),
            "explicit duplicate projection is rejected by Calcite, not attested"
        );

        fs::write(&schema, "CREATE TABLE emp (\"SAL\" INT);\n").unwrap();
        fs::write(
            &query,
            "SELECT SAL FROM (SELECT * FROM emp AS e1, emp AS e2 \
UNION ALL SELECT * FROM emp AS e3, emp AS e4) AS d;\n",
        )
        .unwrap();
        let quoted_column = run_calcite(&repo, &schema, &query);
        assert!(
            quoted_column.queries[0]
                .source_ambiguous_column_error
                .is_none(),
            "unquoted sal must not borrow duplicate quoted \"SAL\" outputs"
        );
        assert!(
            quoted_column.queries[0].error.is_some(),
            "PostgreSQL-canonical unquoted sal is absent from the quoted namespace"
        );

        fs::write(&schema, "CREATE TABLE \"EMP\" (sal INT);\n").unwrap();
        fs::write(
            &query,
            "SELECT sal FROM (SELECT * FROM EMP AS e1, EMP AS e2 \
UNION ALL SELECT * FROM EMP AS e3, EMP AS e4) AS d;\n",
        )
        .unwrap();
        let quoted_table = run_calcite(&repo, &schema, &query);
        assert!(
            quoted_table.queries[0]
                .source_ambiguous_column_error
                .is_none(),
            "unquoted emp must not borrow the distinct quoted \"EMP\" relation"
        );
        assert!(
            quoted_table.queries[0].error.is_some(),
            "the quoted-only relation must remain undefined to unquoted EMP"
        );
        fs::remove_dir_all(temp).unwrap();
    });
}

fn scalar_contains_cast(ast: &ScalarAst) -> bool {
    match ast {
        ScalarAst::Call { op, args, .. } => {
            *op == ScalarOp::Cast || args.iter().any(scalar_contains_cast)
        }
        ScalarAst::TypeAnnotation { expr, .. } => scalar_contains_cast(expr),
        _ => false,
    }
}

fn temp_dir(label: &str) -> PathBuf {
    let temp = std::env::temp_dir().join(format!(
        "logos-ir-calcite-wrapper-{label}-{}",
        std::process::id()
    ));
    if temp.exists() {
        fs::remove_dir_all(&temp).unwrap();
    }
    fs::create_dir_all(&temp).unwrap();
    temp
}

fn with_large_calcite_stack(test: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .name("logos-ir-large-wrapper-test".to_owned())
        .stack_size(64 * 1024 * 1024)
        .spawn(test)
        .expect("spawn large-stack Calcite wrapper test")
        .join()
        .expect("large-stack Calcite wrapper test panicked");
}

fn run_calcite(repo: &Path, schema: &Path, query: &Path) -> CalciteFile {
    let output = Command::new(repo.join("scripts/calcite-ir"))
        .arg("--schema")
        .arg(schema)
        .arg("--sql")
        .arg(query)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "calcite wrapper failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    serde_json::from_slice(&output.stdout).unwrap()
}

fn run_calcite_postgres_c(repo: &Path, schema: &Path, query: &Path) -> CalciteFile {
    let output = Command::new(repo.join("scripts/calcite-ir"))
        .arg("--schema")
        .arg(schema)
        .arg("--sql")
        .arg(query)
        .arg("--default-collation")
        .arg("C")
        .arg("--character-classification")
        .arg("C")
        .arg("--locale-provider")
        .arg("libc")
        .arg("--server-encoding")
        .arg("UTF8")
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "Calcite PostgreSQL C wrapper failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    serde_json::from_slice(&output.stdout).unwrap()
}

fn run_calcite_sqlglot_postgres_c_mode(
    repo: &Path,
    schema: &Path,
    query: &Path,
    normalized_output: &Path,
    no_identify: bool,
) -> CalciteFile {
    let mut command = Command::new(repo.join("scripts/calcite-ir-sqlglot"));
    command
        .arg("--schema")
        .arg(schema)
        .arg("--sql")
        .arg(query)
        .arg("--read")
        .arg("postgres")
        .arg("--write")
        .arg("postgres")
        .arg("--normalized-output")
        .arg(normalized_output)
        .arg("--default-collation")
        .arg("C")
        .arg("--character-classification")
        .arg("C")
        .arg("--locale-provider")
        .arg("libc")
        .arg("--server-encoding")
        .arg("UTF8");
    if no_identify {
        command.arg("--no-identify");
    }
    let output = command.output().unwrap();
    assert!(
        output.status.success(),
        "SQLGlot/Calcite PostgreSQL C wrapper failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    serde_json::from_slice(&output.stdout).unwrap()
}

fn run_calcite_failure(repo: &Path, schema: &Path, query: &Path) -> String {
    let output = Command::new(repo.join("scripts/calcite-ir"))
        .arg("--schema")
        .arg(schema)
        .arg("--sql")
        .arg(query)
        .output()
        .unwrap();
    assert!(
        !output.status.success(),
        "Calcite wrapper unexpectedly succeeded\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    )
}

fn run_calcite_sqlglot(
    repo: &Path,
    schema: &Path,
    query: &Path,
    normalized_output: &Path,
) -> CalciteFile {
    let output = Command::new(repo.join("scripts/calcite-ir-sqlglot"))
        .arg("--schema")
        .arg(schema)
        .arg("--sql")
        .arg(query)
        .arg("--read")
        .arg("postgres")
        .arg("--write")
        .arg("postgres")
        .arg("--normalized-output")
        .arg(normalized_output)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "SQLGlot/Calcite wrapper failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    serde_json::from_slice(&output.stdout).unwrap()
}

fn run_calcite_json(repo: &Path, schema: &Path, query: &Path) -> serde_json::Value {
    let output = Command::new(repo.join("scripts/calcite-ir"))
        .arg("--schema")
        .arg(schema)
        .arg("--sql")
        .arg(query)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "calcite wrapper failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    serde_json::from_slice(&output.stdout).unwrap()
}

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .ancestors()
        .nth(2)
        .expect("logos-ir must live under Logos/crates/logos-ir")
        .to_path_buf()
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_closes_complete_declarative_query_shape_roles() {
    fn first_rel_mut<'a>(rel: &'a mut CalciteRel, kind: &str) -> Option<&'a mut CalciteRel> {
        if rel.rel_type == kind {
            return Some(rel);
        }
        rel.inputs
            .iter_mut()
            .find_map(|input| first_rel_mut(input, kind))
    }

    fn one(raw: &CalciteFile, index: usize) -> CalciteFile {
        CalciteFile {
            environment: raw.environment,
            schema: raw.schema.clone(),
            queries: vec![raw.queries[index].clone()],
        }
    }

    let repo = repo_root();
    let temp = temp_dir("complete-declarative-query-shape-roles");
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(
        &schema,
        "create table t(a integer not null, b integer);\ncreate table u(a integer, b integer);\n",
    )
    .unwrap();
    fs::write(
        &query,
        "select a from t where b > 0;\n\
         select a from t limit 2 offset 1;\n\
         select t.a from t join u on t.a = u.a;\n\
         select a from t union all select a from u;\n\
         select distinct a, b from t;\n\
         select r.* from t l join t r on l.a = r.a;\n\
         select distinct count(*) from t group by a;\n\
         select distinct 10 / (a - 1) as risky from t;\n\
         select exists (select distinct 10 / (a - 1) from t);\n",
    )
    .unwrap();

    let raw = run_calcite(&repo, &schema, &query);
    for (index, label) in [
        "WHERE",
        "LIMIT/OFFSET",
        "JOIN",
        "UNION ALL",
        "SELECT DISTINCT",
        "qualified self-join wildcard",
        "DISTINCT plus GROUP BY",
        "DISTINCT error-capable target",
        "EXISTS over DISTINCT error-capable target",
    ]
    .into_iter()
    .enumerate()
    {
        convert_raw_file(one(&raw, index))
            .unwrap_or_else(|error| panic!("exact {label} query shape: {error}"));
    }

    let distinct = convert_raw_file(one(&raw, 4)).expect("plain source DISTINCT");
    assert!(matches!(distinct.queries[0].rel, RelExpr::Distinct { .. }));
    let risky_distinct =
        convert_raw_file(one(&raw, 7)).expect("error-capable source DISTINCT target");
    let RelExpr::Distinct { input, .. } = &risky_distinct.queries[0].rel else {
        panic!("source DISTINCT must retain a native duplicate-elimination node");
    };
    assert!(matches!(input.as_ref(), RelExpr::Project { exprs, .. }
        if matches!(exprs.as_slice(), [expr]
            if matches!(expr.parsed, ScalarAst::Call { op: ScalarOp::Divide, .. }))));

    fn scalar_contains_distinct(ast: &ScalarAst) -> bool {
        match ast {
            ScalarAst::RelSubquery { rel } => rel_contains_distinct(rel),
            ScalarAst::Call { args, .. } => args.iter().any(scalar_contains_distinct),
            ScalarAst::TypeAnnotation { expr, .. } => scalar_contains_distinct(expr),
            ScalarAst::Window { parsed } => {
                parsed.args.iter().any(scalar_contains_distinct)
                    || parsed.partition_by.iter().any(scalar_contains_distinct)
                    || parsed
                        .order_by
                        .iter()
                        .any(|key| scalar_contains_distinct(&key.expr))
                    || parsed
                        .frame
                        .as_ref()
                        .is_some_and(|frame| frame.offset_exprs().any(scalar_contains_distinct))
            }
            _ => false,
        }
    }
    fn rel_contains_distinct(rel: &RelExpr) -> bool {
        match rel {
            RelExpr::Distinct { .. } => true,
            RelExpr::Project { input, exprs, .. } => {
                exprs
                    .iter()
                    .any(|expr| scalar_contains_distinct(&expr.parsed))
                    || rel_contains_distinct(input)
            }
            RelExpr::Filter {
                input, predicate, ..
            }
            | RelExpr::NativeHaving {
                input, predicate, ..
            } => scalar_contains_distinct(&predicate.parsed) || rel_contains_distinct(input),
            RelExpr::Join {
                left,
                right,
                condition,
                ..
            } => {
                scalar_contains_distinct(&condition.parsed)
                    || rel_contains_distinct(left)
                    || rel_contains_distinct(right)
            }
            RelExpr::Aggregate {
                input, agg_calls, ..
            } => {
                agg_calls.iter().any(|call| {
                    call.args
                        .iter()
                        .any(|expr| scalar_contains_distinct(&expr.parsed))
                        || call
                            .filter
                            .as_ref()
                            .is_some_and(|expr| scalar_contains_distinct(&expr.parsed))
                }) || rel_contains_distinct(input)
            }
            RelExpr::Sort {
                input,
                fetch,
                offset,
                ..
            } => {
                fetch
                    .as_ref()
                    .is_some_and(|expr| scalar_contains_distinct(&expr.parsed))
                    || offset
                        .as_ref()
                        .is_some_and(|expr| scalar_contains_distinct(&expr.parsed))
                    || rel_contains_distinct(input)
            }
            RelExpr::Set { inputs, .. } => inputs.iter().any(rel_contains_distinct),
            RelExpr::Values { rows, .. } => rows
                .iter()
                .flatten()
                .any(|expr| scalar_contains_distinct(&expr.parsed)),
            RelExpr::TableScan { .. } => false,
        }
    }
    let exists_distinct =
        convert_raw_file(one(&raw, 8)).expect("EXISTS over error-capable source DISTINCT");
    assert!(rel_contains_distinct(&exists_distinct.queries[0].rel));

    let mut deleted_where = one(&raw, 0);
    let filter = first_rel_mut(
        deleted_where.queries[0].rel.as_mut().unwrap(),
        "LogicalFilter",
    )
    .expect("source WHERE Filter");
    *filter = filter.inputs.remove(0);

    let mut swapped_slice_roles = one(&raw, 1);
    let sort = first_rel_mut(
        swapped_slice_roles.queries[0].rel.as_mut().unwrap(),
        "LogicalSort",
    )
    .expect("keyless sliced Sort");
    std::mem::swap(&mut sort.fetch_rex, &mut sort.offset_rex);

    let mut deleted_join = one(&raw, 2);
    let join = first_rel_mut(deleted_join.queries[0].rel.as_mut().unwrap(), "LogicalJoin")
        .expect("source Join");
    *join = join.inputs.remove(0);

    let mut changed_set = one(&raw, 3);
    let set = first_rel_mut(changed_set.queries[0].rel.as_mut().unwrap(), "LogicalUnion")
        .expect("source UNION ALL");
    set.all = Some(false);

    let mut deleted_distinct = one(&raw, 4);
    let aggregate = first_rel_mut(
        deleted_distinct.queries[0].rel.as_mut().unwrap(),
        "LogicalAggregate",
    )
    .expect("SELECT DISTINCT Aggregate");
    *aggregate = aggregate.inputs.remove(0);

    let mut missing_distinct_authority = one(&raw, 4);
    let aggregate = first_rel_mut(
        missing_distinct_authority.queries[0].rel.as_mut().unwrap(),
        "LogicalAggregate",
    )
    .expect("SELECT DISTINCT Aggregate");
    aggregate.source_distinct = None;

    let mut forged_distinct_group = one(&raw, 6);
    let aggregate = first_rel_mut(
        forged_distinct_group.queries[0].rel.as_mut().unwrap(),
        "LogicalAggregate",
    )
    .expect("outer SELECT DISTINCT Aggregate");
    aggregate.group_set = Some(vec![]);

    let mut swapped_distinct_group_layers = one(&raw, 6);
    let outer = first_rel_mut(
        swapped_distinct_group_layers.queries[0]
            .rel
            .as_mut()
            .unwrap(),
        "LogicalAggregate",
    )
    .expect("outer SELECT DISTINCT Aggregate");
    let inner = &mut outer.inputs[0].inputs[0];
    std::mem::swap(&mut outer.source_grouping, &mut inner.source_grouping);

    for mutation in [
        deleted_where,
        swapped_slice_roles,
        deleted_join,
        changed_set,
        deleted_distinct,
        missing_distinct_authority,
        forged_distinct_group,
        swapped_distinct_group_layers,
    ] {
        assert!(
            convert_raw_file(mutation).is_err(),
            "query-shape mutation must fail closed"
        );
    }
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_keeps_parenthesized_set_arms_inside_their_ast_boundaries() {
    fn collect_sets<'a>(rel: &'a CalciteRel, sets: &mut Vec<&'a CalciteRel>) {
        if matches!(
            rel.rel_type.as_str(),
            "LogicalUnion" | "LogicalIntersect" | "LogicalMinus"
        ) {
            sets.push(rel);
        }
        for input in &rel.inputs {
            collect_sets(input, sets);
        }
    }

    fn find_by_source_id_mut<'a>(
        rel: &'a mut CalciteRel,
        source_id: &str,
    ) -> Option<&'a mut CalciteRel> {
        if rel.source_node_id.as_deref() == Some(source_id) {
            return Some(rel);
        }
        rel.inputs
            .iter_mut()
            .find_map(|input| find_by_source_id_mut(input, source_id))
    }

    fn one_line_source_text(sql: &str, span: &str) -> String {
        let (start, end) = span.split_once('-').expect("source span delimiter");
        let (start_line, start_column) = start.split_once(':').expect("source start");
        let (end_line, end_column) = end.split_once(':').expect("source end");
        assert_eq!(start_line, "1");
        assert_eq!(end_line, "1");
        assert!(sql.is_ascii(), "focused frozen inputs are ASCII");
        let start = start_column.parse::<usize>().unwrap() - 1;
        let end = end_column.parse::<usize>().unwrap();
        sql[start..end].to_owned()
    }

    std::thread::Builder::new()
        .name("parenthesized-set-arm-boundaries".to_owned())
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let repo = repo_root();
            let cases = repo.join("benchmarks/core/.generated/sqlsolver/nonwetune-flat");
            for (case_name, expected_set_ids, malformed_set_id, branch_fetch) in [
                (
                    "verieql-calcite__calcite-152",
                    vec!["1:16-1:148"],
                    "1:72-1:148",
                    Some("10"),
                ),
                (
                    "verieql-calcite__calcite-382",
                    vec!["1:16-1:100"],
                    "1:48-1:100",
                    None,
                ),
                (
                    "verieql-calcite__calcite-383",
                    vec!["1:16-1:146"],
                    "1:71-1:146",
                    Some("0"),
                ),
                (
                    "rbot-dsb__query087",
                    vec!["1:23-1:1119", "1:23-1:755"],
                    "1:24-1:755",
                    None,
                ),
            ] {
                let case = cases.join(case_name);
                let query = case.join("sql2.sql");
                let exact_sql = fs::read_to_string(&query).unwrap();
                let raw = run_calcite(&repo, &case.join("schema.sql"), &query);
                let root = raw.queries[0].rel.as_ref().expect("target relation");
                let mut sets = Vec::new();
                collect_sets(root, &mut sets);
                assert_eq!(
                    sets.iter()
                        .map(|set| set.source_node_id.as_deref().unwrap())
                        .collect::<Vec<_>>(),
                    expected_set_ids,
                    "{case_name}: exact ordered Set-expression extents"
                );
                for set in &sets {
                    assert_eq!(set.source_query_block_id, set.source_node_id);
                    assert_eq!(
                        set.source_text.as_deref(),
                        Some(
                            one_line_source_text(
                                &exact_sql,
                                set.source_node_id.as_deref().unwrap()
                            )
                            .as_str()
                        )
                    );
                }

                if let Some(expected_fetch) = branch_fetch {
                    let set = sets.first().expect("one derived Set");
                    assert_eq!(set.inputs.len(), 2);
                    for input in &set.inputs {
                        assert_eq!(input.rel_type, "LogicalSort");
                        let fetch = input.fetch_rex.as_ref().expect("branch FETCH Rex");
                        assert_eq!(
                            fetch.literal_value2.as_deref(),
                            Some(expected_fetch),
                            "exact arbitrary-precision numeric FETCH payload"
                        );
                        assert_eq!(
                            fetch.source_text.as_deref(),
                            Some(expected_fetch),
                            "FETCH payload remains bound to its exact source token"
                        );
                        assert_ne!(input.source_node_id, input.source_query_block_id);
                        let order = input.source_order.as_ref().expect("branch ORDER BY role");
                        assert_eq!(
                            Some(order.query_node_id.as_str()),
                            input.source_query_block_id.as_deref()
                        );
                        assert_eq!(
                            input.source_text.as_deref(),
                            Some(
                                one_line_source_text(
                                    &exact_sql,
                                    input.source_node_id.as_deref().unwrap()
                                )
                                .as_str()
                            )
                        );
                        assert!(input.source_text.as_deref().unwrap().contains("ORDER BY"));
                    }
                }
                convert_raw_file(raw.clone())
                    .unwrap_or_else(|error| panic!("convert {case_name}/sql2.sql: {error}"));

                let mut crossed_boundary = raw.clone();
                let current_set_id = expected_set_ids.last().unwrap();
                let set = find_by_source_id_mut(
                    crossed_boundary.queries[0].rel.as_mut().unwrap(),
                    current_set_id,
                )
                .expect("mutable exact Set");
                set.source_query_block_id = Some(malformed_set_id.to_owned());
                set.source_node_id = Some(malformed_set_id.to_owned());
                set.source_text = Some(one_line_source_text(&exact_sql, malformed_set_id));
                assert!(
                    convert_raw_file(crossed_boundary).is_err(),
                    "{case_name}: a Set extent crossing a sibling/suffix boundary must fail"
                );

                if branch_fetch.is_some() {
                    let mut suffix_owned_query = raw;
                    let set = find_by_source_id_mut(
                        suffix_owned_query.queries[0].rel.as_mut().unwrap(),
                        expected_set_ids[0],
                    )
                    .expect("mutable derived Set");
                    let sort = set.inputs.first_mut().expect("first ordered arm");
                    let ordered_id = sort.source_node_id.clone().unwrap();
                    let ordered_text = sort.source_text.clone().unwrap();
                    let order = sort.source_order.as_mut().expect("mutable ORDER BY role");
                    order.query_node_id = ordered_id;
                    order.query_text = ordered_text;
                    assert!(
                        convert_raw_file(suffix_owned_query).is_err(),
                        "{case_name}: ORDER/FETCH suffix cannot replace its direct SELECT owner"
                    );
                }
            }
        })
        .expect("spawn parenthesized Set boundary test")
        .join()
        .expect("parenthesized Set boundary test should not panic");
}

#[test]
#[ignore = "requires the Java Calcite wrapper and frozen benchmark inputs"]
fn calcite_wrapper_matches_character_not_in_literals_canonically_in_source_order() {
    let repo = repo_root();
    let cases = repo.join("benchmarks/core/.generated/sqlsolver/nonwetune-flat");
    for case_name in [
        "verieql-calcite__calcite-144",
        "verieql-calcite__calcite-145",
    ] {
        let case = cases.join(case_name);
        for sql_name in ["sql1.sql", "sql2.sql"] {
            let raw = run_calcite(&repo, &case.join("schema.sql"), &case.join(sql_name));
            convert_raw_file(raw)
                .unwrap_or_else(|error| panic!("convert {case_name}/{sql_name}: {error}"));
        }

        let raw = run_calcite(&repo, &case.join("schema.sql"), &case.join("sql2.sql"));
        let not_in = find_rel_rex_by_source_kind(
            raw.queries[0].rel.as_ref().expect("NOT IN relation"),
            "NOT_IN",
        )
        .expect("generated outer NOT for source character NOT IN");
        assert_eq!(not_in.kind.as_deref(), Some("NOT"));
        let positive = not_in.operands.first().expect("positive IN child");
        assert_eq!(positive.kind.as_deref(), Some("OR"));
        assert_eq!(positive.source_kind.as_deref(), Some("IN"));
        assert_eq!(positive.source_operator.as_deref(), Some("IN"));
        assert_eq!(positive.operands.len(), 2);
        assert_eq!(
            positive.operands[0].operands[1].source_text.as_deref(),
            Some("''")
        );
        assert_eq!(
            positive.operands[1].operands[1].source_text.as_deref(),
            Some("'3'")
        );
        convert_raw_file(raw.clone())
            .unwrap_or_else(|error| panic!("convert exact {case_name} NOT IN: {error}"));

        let mut reordered = raw;
        let positive = find_rel_rex_by_source_kind_mut(
            reordered.queries[0].rel.as_mut().expect("NOT IN relation"),
            "NOT_IN",
        )
        .expect("mutable outer NOT")
        .operands
        .first_mut()
        .expect("mutable positive IN child");
        positive.operands.swap(0, 1);
        assert!(
            convert_raw_file(reordered).is_err(),
            "{case_name}: reordered generated comparisons must not borrow source IN candidates"
        );
    }
}

#[test]
#[ignore = "requires the Java Calcite wrapper and frozen benchmark inputs"]
fn calcite_wrapper_completes_nested_query_predicate_parentheses_from_ast_owners() {
    fn collect_rex_subqueries<'a>(rex: &'a CalciteRex, found: &mut Vec<&'a CalciteRex>) {
        if rex.class.as_deref() == Some("RexSubQuery") {
            found.push(rex);
        }
        for operand in &rex.operands {
            collect_rex_subqueries(operand, found);
        }
        if let Some(reference) = rex.reference_expr.as_deref() {
            collect_rex_subqueries(reference, found);
        }
        if let Some(rel) = rex.subquery_rel.as_deref() {
            collect_rel_subqueries(rel, found);
        }
    }

    fn collect_rel_subqueries<'a>(rel: &'a CalciteRel, found: &mut Vec<&'a CalciteRex>) {
        for rex in &rel.project_rex {
            collect_rex_subqueries(rex, found);
        }
        if let Some(rex) = rel.condition_rex.as_ref() {
            collect_rex_subqueries(rex, found);
        }
        for input in &rel.inputs {
            collect_rel_subqueries(input, found);
        }
    }

    fn find_rex_subquery_mut<'a>(
        rex: &'a mut CalciteRex,
        source_id: &str,
    ) -> Option<&'a mut CalciteRex> {
        if rex.class.as_deref() == Some("RexSubQuery")
            && rex.source_node_id.as_deref() == Some(source_id)
        {
            return Some(rex);
        }
        for operand in &mut rex.operands {
            if let Some(found) = find_rex_subquery_mut(operand, source_id) {
                return Some(found);
            }
        }
        if let Some(reference) = rex.reference_expr.as_deref_mut()
            && let Some(found) = find_rex_subquery_mut(reference, source_id)
        {
            return Some(found);
        }
        rex.subquery_rel
            .as_deref_mut()
            .and_then(|rel| find_rel_subquery_mut(rel, source_id))
    }

    fn find_rel_subquery_mut<'a>(
        rel: &'a mut CalciteRel,
        source_id: &str,
    ) -> Option<&'a mut CalciteRex> {
        for rex in &mut rel.project_rex {
            if let Some(found) = find_rex_subquery_mut(rex, source_id) {
                return Some(found);
            }
        }
        if let Some(rex) = rel.condition_rex.as_mut()
            && let Some(found) = find_rex_subquery_mut(rex, source_id)
        {
            return Some(found);
        }
        rel.inputs
            .iter_mut()
            .find_map(|input| find_rel_subquery_mut(input, source_id))
    }

    fn exact_one_line_fragment(sql: &str, span: &str) -> String {
        let (start, end) = span.split_once('-').unwrap();
        let (start_line, start_column) = start.split_once(':').unwrap();
        let (end_line, end_column) = end.split_once(':').unwrap();
        assert_eq!((start_line, end_line), ("1", "1"));
        assert!(sql.is_ascii());
        sql[start_column.parse::<usize>().unwrap() - 1..end_column.parse().unwrap()].to_owned()
    }

    with_large_calcite_stack(|| {
        let repo = repo_root();
        for (case_number, expected_ids, completed_id, truncated_id) in [
            (
                "27",
                vec!["1:161-1:303", "1:332-1:421"],
                "1:161-1:303",
                "1:161-1:302",
            ),
            (
                "31",
                vec!["1:395-1:845", "1:538-1:623", "1:661-1:844"],
                "1:661-1:844",
                "1:661-1:843",
            ),
        ] {
            let case = repo
                .join("benchmarks/core/.generated/sqlsolver/wetune-issues")
                .join(case_number);
            for sql_name in ["sql1.sql", "sql2.sql"] {
                let query = case.join(sql_name);
                let exact_sql = fs::read_to_string(&query).unwrap();
                let raw = run_calcite(&repo, &case.join("schema.sql"), &query);
                let mut subqueries = Vec::new();
                collect_rel_subqueries(
                    raw.queries[0].rel.as_ref().expect("query relation"),
                    &mut subqueries,
                );
                if sql_name == "sql1.sql" {
                    assert_eq!(
                        subqueries
                            .iter()
                            .map(|rex| rex.source_node_id.as_deref().unwrap())
                            .collect::<Vec<_>>(),
                        expected_ids,
                        "wetune{case_number}: exact query-predicate extents"
                    );
                }
                for rex in subqueries {
                    let source_id = rex.source_node_id.as_deref().unwrap();
                    assert_eq!(
                        rex.source_text.as_deref(),
                        Some(exact_one_line_fragment(&exact_sql, source_id).as_str())
                    );
                    assert!(rex.source_text.as_deref().unwrap().ends_with(')'));
                }

                // Wetune31 currently reaches the independent downstream
                // visible-output-mask validator after these exact wrapper
                // assertions; that Rust rule is covered by a separate round.
                if case_number != "27" {
                    continue;
                }
                convert_raw_file(raw.clone()).unwrap_or_else(|error| {
                    panic!("convert wetune{case_number}/{sql_name}: {error}")
                });

                if sql_name == "sql1.sql" {
                    let mut truncated = raw;
                    let rex = find_rel_subquery_mut(
                        truncated.queries[0].rel.as_mut().unwrap(),
                        completed_id,
                    )
                    .expect("mutable completed query predicate");
                    rex.source_node_id = Some(truncated_id.to_owned());
                    rex.source_text = Some(exact_one_line_fragment(&exact_sql, truncated_id));
                    assert!(
                        convert_raw_file(truncated).is_err(),
                        "wetune{case_number}: a missing query close parenthesis must fail closed"
                    );
                }
            }
        }
    });
}

#[test]
#[ignore = "requires SQLGlot, the Java Calcite wrapper, and frozen benchmark inputs"]
fn calcite_wrappers_q086_close_direct_cte_aggregate_output_permutation() {
    fn owner_mut(rel: &mut CalciteRel) -> Option<&mut CalciteRel> {
        let owns_results =
            rel.rel_type == "LogicalProject"
                && rel.inputs.as_slice().first().is_some_and(|input| {
                    rel.inputs.len() == 1 && input.rel_type == "LogicalAggregate"
                })
                && matches!(
                    rel.source_input_cte_uses.as_slice(),
                    [Some(use_)] if {
                        let definition = use_.definition_query_text.to_ascii_lowercase();
                        definition.contains("sum(") && definition.contains("ws_net_paid")
                    }
                )
                && rel
                    .project_rex
                    .iter()
                    .filter(|rex| {
                        rex.source_expansion
                            .as_ref()
                            .is_some_and(|expansion| expansion.kind.starts_with("DIRECT_CTE_"))
                    })
                    .count()
                    >= 3;
        if owns_results {
            return Some(rel);
        }
        rel.inputs.iter_mut().find_map(owner_mut)
    }

    with_large_calcite_stack(|| {
        let repo = repo_root();
        let case = repo
            .join("benchmarks/core/.generated/sqlsolver/nonwetune-flat/tpcds-variants__query086");
        let temp = temp_dir("q086-direct-cte-aggregate-permutation");
        for production in [false, true] {
            let raw = if production {
                run_calcite_sqlglot(
                    &repo,
                    &case.join("schema.sql"),
                    &case.join("sql2.sql"),
                    &temp.join("q086-sql2.normalized.sql"),
                )
            } else {
                run_calcite(&repo, &case.join("schema.sql"), &case.join("sql2.sql"))
            };
            convert_raw_file(raw.clone()).unwrap_or_else(|error| {
                panic!(
                    "Q086/sql2/{} direct CTE Aggregate permutation: {error}",
                    if production { "production" } else { "direct" }
                )
            });

            let reject = |label: &str, mutated: CalciteFile| {
                assert!(
                    convert_raw_file(mutated).is_err(),
                    "Q086/sql2/{} accepted {label}",
                    if production { "production" } else { "direct" }
                );
            };

            let mut wrong_ordinal = raw.clone();
            owner_mut(wrong_ordinal.queries[0].rel.as_mut().unwrap())
                .unwrap()
                .project_rex[0]
                .source_expansion
                .as_mut()
                .unwrap()
                .public_output_index = Some(1);
            reject("a wrong direct-CTE public ordinal", wrong_ordinal);

            let mut wrong_input = raw.clone();
            let rex = &mut owner_mut(wrong_input.queries[0].rel.as_mut().unwrap())
                .unwrap()
                .project_rex[0];
            rex.index = Some(0);
            rex.text = Some("$0".to_owned());
            reject("a wrong Aggregate input index", wrong_input);

            let mut wrong_edge = raw.clone();
            let expansion = owner_mut(wrong_edge.queries[0].rel.as_mut().unwrap())
                .unwrap()
                .project_rex[0]
                .source_expansion
                .as_mut()
                .unwrap();
            expansion.cte_use.as_mut().unwrap().definition_query_node_id =
                expansion.outer_select_node_id.clone();
            reject("an embedded/containing CTE-edge mismatch", wrong_edge);

            let mut wrong_type = raw.clone();
            owner_mut(wrong_type.queries[0].rel.as_mut().unwrap())
                .unwrap()
                .project_rex[0]
                .precision = Some(18);
            reject("a direct-CTE Rex result-type mutation", wrong_type);

            let mut reordered = raw.clone();
            let project = owner_mut(reordered.queries[0].rel.as_mut().unwrap()).unwrap();
            project.project_rex[1].index = Some(1);
            project.project_rex[1].text = Some("$1".to_owned());
            project.project_rex[2].index = Some(0);
            project.project_rex[2].text = Some("$0".to_owned());
            reject("a reordered Aggregate/public mapping", reordered);

            let mut borrowed_span = raw;
            let project = owner_mut(borrowed_span.queries[0].rel.as_mut().unwrap()).unwrap();
            let group_source = {
                let group = &project.inputs[0].inputs[0].project_rex[0];
                (group.source_node_id.clone(), group.source_text.clone())
            };
            project.inputs[0].agg_call_details[0].source_node_id = group_source.0;
            project.inputs[0].agg_call_details[0].source_text = group_source.1;
            reject("a borrowed aggregate-call source span", borrowed_span);
        }
        fs::remove_dir_all(temp).unwrap();
    });
}

#[test]
#[ignore = "requires the Java Calcite wrapper and frozen benchmark inputs"]
fn calcite_wrapper_closes_round191_declarative_provenance_boundaries() {
    fn one(raw: &CalciteFile, index: usize) -> CalciteFile {
        CalciteFile {
            environment: raw.environment,
            schema: raw.schema.clone(),
            queries: vec![raw.queries[index].clone()],
        }
    }

    fn hidden_alias_case(rel: &CalciteRel) -> Option<&CalciteRex> {
        rel.project_rex
            .iter()
            .find(|rex| {
                rex.kind.as_deref() == Some("CASE")
                    && rex.source_text.as_deref().is_some_and(|text| {
                        text.to_ascii_lowercase()
                            .contains("case when lochierarchy = 0")
                    })
            })
            .or_else(|| rel.inputs.iter().find_map(hidden_alias_case))
    }

    fn hidden_grouping_case(rel: &CalciteRel) -> Option<&CalciteRex> {
        rel.project_rex
            .iter()
            .find(|rex| {
                rex.kind.as_deref() == Some("CASE")
                    && rex.source_text.as_deref().is_some_and(|text| {
                        let text = text.to_ascii_lowercase();
                        text.contains("case when (grouping(") && text.contains(" + grouping(")
                    })
            })
            .or_else(|| rel.inputs.iter().find_map(hidden_grouping_case))
    }

    with_large_calcite_stack(|| {
        let repo = repo_root();
        let frozen = repo.join("benchmarks/core/.generated/sqlsolver/nonwetune-flat");

        // The frozen PostgreSQL materializer expands the original nested
        // lochierarchy alias reference back to its GROUPING definition. The
        // hidden ORDER BY CASE must therefore retain that exact later source
        // occurrence, while only its generated omitted ELSE is source-less.
        for query_number in ["036", "070", "086"] {
            let case = frozen.join(format!("tpcds-variants__query{query_number}"));
            let raw = run_calcite(&repo, &case.join("schema.sql"), &case.join("sql1.sql"));
            assert!(raw.queries[0].source_analysis_error.is_none());
            let grouping_case = hidden_grouping_case(raw.queries[0].rel.as_ref().unwrap())
                .unwrap_or_else(|| panic!("q{query_number}: hidden expanded GROUPING CASE"));
            assert_eq!(grouping_case.operands.len(), 3, "q{query_number}");
            assert_eq!(grouping_case.operands[0].kind.as_deref(), Some("EQUALS"));
            let expanded_grouping = &grouping_case.operands[0].operands[0];
            assert_eq!(expanded_grouping.kind.as_deref(), Some("PLUS"));
            assert!(
                expanded_grouping
                    .source_text
                    .as_deref()
                    .is_some_and(
                        |text| text.starts_with("(GROUPING(") && text.contains(" + GROUPING(")
                    ),
                "q{query_number}"
            );
            let expected_operands: &[&str] = match query_number {
                "070" => &["GROUPING(s_state)", "GROUPING(s_county)"],
                _ => &["GROUPING(i_category)", "GROUPING(i_class)"],
            };
            assert_eq!(expanded_grouping.operands.len(), expected_operands.len());
            for (operand, expected) in expanded_grouping.operands.iter().zip(expected_operands) {
                assert_eq!(operand.source_text.as_deref(), Some(*expected));
                assert_eq!(operand.source_kind.as_deref(), Some("OTHER_FUNCTION"));
                assert_eq!(operand.source_operator.as_deref(), Some("grouping"));
                assert!(operand.source_node_id.is_some());
            }
            let terminal = &grouping_case.operands[2];
            assert_eq!(terminal.literal_type_name.as_deref(), Some("NULL"));
            assert_eq!(terminal.literal_value.as_deref(), Some("null"));
            assert_eq!(terminal.ty, grouping_case.ty);
            assert_eq!(terminal.full_type, grouping_case.full_type);
            assert!(terminal.nullable);
            assert!(terminal.source_sql.is_none(), "q{query_number}");
            assert!(terminal.source_node_id.is_none(), "q{query_number}");
            assert!(terminal.source_text.is_none(), "q{query_number}");
            assert!(terminal.source_kind.is_none(), "q{query_number}");
        }

        // A compact same-owner alias query reaches the importer without the
        // later TPC-DS aggregate layers, so mutations close the new CASE
        // authorization itself rather than merely observing raw JSON.
        let temp = temp_dir("round191-case-alias-boundary");
        let schema = temp.join("schema.sql");
        let query = temp.join("query.sql");
        fs::write(&schema, "create table t(a integer, b integer);\n").unwrap();
        fs::write(
            &query,
            "select a + b as lochierarchy, a from t \
             order by case when lochierarchy = 0 then a end;\n\
             select a + b as lochierarchy, a from t \
             order by case when lochierarchy = 0 then a else null end;\n",
        )
        .unwrap();
        let raw = run_calcite(&repo, &schema, &query);
        let implicit = hidden_alias_case(raw.queries[0].rel.as_ref().unwrap()).unwrap();
        let explicit = hidden_alias_case(raw.queries[1].rel.as_ref().unwrap()).unwrap();
        assert!(implicit.operands[2].source_sql.is_none());
        assert_eq!(explicit.operands[2].source_sql.as_deref(), Some("NULL"));
        let converted =
            convert_raw_file(one(&raw, 0)).expect("exact ORDER BY alias-expression analysis error");
        assert!(
            converted.queries[0]
                .analysis_errors
                .iter()
                .any(|error| matches!(
                    error,
                    QueryAnalysisError::PostgresOrderByAliasExpressionUndefinedColumn {
                        output_alias,
                        ..
                    } if output_alias == "lochierarchy"
                )),
            "the converted query must retain the terminal PostgreSQL alias-expression error"
        );

        let mut borrowed_terminal = one(&raw, 0);
        let case = find_rel_rex_by_source_kind_mut(
            borrowed_terminal.queries[0].rel.as_mut().unwrap(),
            "CASE",
        )
        .unwrap();
        let owner_id = case.source_node_id.clone();
        let owner_text = case.source_text.clone();
        let terminal = &mut case.operands[2];
        terminal.source_sql = Some("NULL".to_owned());
        terminal.source_node_id = owner_id;
        terminal.source_text = owner_text;
        terminal.source_kind = Some("LITERAL".to_owned());
        assert!(convert_raw_file(borrowed_terminal).is_err());

        let mut reordered_alias = one(&raw, 0);
        let case = find_rel_rex_by_source_kind_mut(
            reordered_alias.queries[0].rel.as_mut().unwrap(),
            "CASE",
        )
        .unwrap();
        case.operands[0].operands[0].operands.swap(0, 1);
        assert!(
            convert_raw_file(reordered_alias).is_err(),
            "reordered generated alias definition must fail"
        );
        fs::remove_dir_all(&temp).unwrap();

        // Calcite 176 elides the identity Project between the two Aggregates.
        // The direct child must nevertheless be owned by the sole inner
        // derived SELECT, never by the outer aggregate query block.
        let case176 = frozen.join("verieql-calcite__calcite-176");
        let raw176 = run_calcite(
            &repo,
            &case176.join("schema.sql"),
            &case176.join("sql1.sql"),
        );
        let outer = raw176.queries[0].rel.as_ref().unwrap();
        assert_eq!(outer.rel_type, "LogicalAggregate");
        assert_eq!(outer.inputs[0].rel_type, "LogicalAggregate");
        assert_ne!(
            outer.source_query_block_id,
            outer.inputs[0].source_query_block_id
        );
        assert!(
            outer.inputs[0]
                .source_text
                .as_deref()
                .is_some_and(|text| text.starts_with("SELECT SUM(SAL)"))
        );
        convert_raw_file(raw176.clone()).expect("calcite176 exact Aggregate boundary");

        let mut crossed176 = raw176;
        let outer = crossed176.queries[0].rel.as_mut().unwrap();
        let outer_query = outer.source_query_block_id.clone();
        let outer_root = outer.source_root_query_block_id.clone();
        let outer_sql = outer.source_sql.clone();
        let outer_node = outer.source_node_id.clone();
        let outer_text = outer.source_text.clone();
        let child = &mut outer.inputs[0];
        child.source_query_block_id = outer_query;
        child.source_root_query_block_id = outer_root;
        child.source_sql = outer_sql;
        child.source_node_id = outer_node;
        child.source_text = outer_text;
        assert!(
            convert_raw_file(crossed176).is_err(),
            "an inner Aggregate cannot borrow the outer query boundary"
        );

        // The parser leaves ANY_VALUE and SINGLE_VALUE as unresolved function
        // calls, but their exact aggregate name, one argument, and source span
        // must still be attached to the aligned AggregateCall.
        for (case_number, function, source_operator) in [
            ("245", "ANY_VALUE", "any_value"),
            ("246", "SINGLE_VALUE", "single_value"),
        ] {
            let case = frozen.join(format!("verieql-calcite__calcite-{case_number}"));
            for sql_name in ["sql1.sql", "sql2.sql"] {
                let raw = run_calcite(&repo, &case.join("schema.sql"), &case.join(sql_name));
                let aggregate = first_aggregate(raw.queries[0].rel.as_ref().unwrap());
                let [call] = aggregate.agg_call_details.as_slice() else {
                    panic!("calcite{case_number}/{sql_name}: one aggregate call")
                };
                assert_eq!(call.function, function);
                assert_eq!(call.kind, function);
                assert_eq!(call.arg_list, [0]);
                assert_eq!(call.source_operator.as_deref(), Some(source_operator));
                assert_eq!(call.source_kind.as_deref(), Some("OTHER_FUNCTION"));
                assert_eq!(call.source_operands.len(), 1);
                assert_eq!(
                    call.source_operands[0].source_kind.as_deref(),
                    Some("IDENTIFIER")
                );
                assert!(call.source_node_id.is_some());
                assert!(call.source_operands[0].source_node_id.is_some());
                assert_ne!(call.source_node_id, call.source_operands[0].source_node_id);
                if case_number == "245" {
                    convert_raw_file(raw).unwrap_or_else(|error| {
                        panic!("calcite245/{sql_name}: exact ANY_VALUE: {error}")
                    });
                }
            }
        }

        let case245 = frozen.join("verieql-calcite__calcite-245");
        let raw245 = run_calcite(
            &repo,
            &case245.join("schema.sql"),
            &case245.join("sql1.sql"),
        );
        let mut wrong_aggregate_name = raw245.clone();
        first_aggregate_mut(wrong_aggregate_name.queries[0].rel.as_mut().unwrap())
            .agg_call_details[0]
            .source_operator = Some("single_value".to_owned());
        assert!(convert_raw_file(wrong_aggregate_name).is_err());

        let mut wrong_argument = raw245.clone();
        first_aggregate_mut(wrong_argument.queries[0].rel.as_mut().unwrap()).agg_call_details[0]
            .arg_list[0] = 1;
        assert!(convert_raw_file(wrong_argument).is_err());

        let mut borrowed_argument_span = raw245;
        let call =
            &mut first_aggregate_mut(borrowed_argument_span.queries[0].rel.as_mut().unwrap())
                .agg_call_details[0];
        call.source_node_id = call.source_operands[0].source_node_id.clone();
        call.source_text = call.source_operands[0].source_text.clone();
        assert!(convert_raw_file(borrowed_argument_span).is_err());

        // Tuple IN keeps the query exclusively in subqueryRel and maps the
        // exact source ROW members to generated scalar operands in order.
        let case374 = frozen.join("verieql-calcite__calcite-374");
        let raw374 = run_calcite(
            &repo,
            &case374.join("schema.sql"),
            &case374.join("sql1.sql"),
        );
        let tuple_in = find_first_in_subquery(raw374.queries[0].rel.as_ref().unwrap()).unwrap();
        assert_eq!(tuple_in.operands.len(), 2);
        assert_eq!(tuple_in.operands[0].source_text.as_deref(), Some("EMPNO"));
        assert_eq!(tuple_in.operands[1].source_text.as_deref(), Some("DEPTNO"));
        assert!(tuple_in.operands.iter().all(|operand| {
            operand.source_kind.as_deref() == Some("IDENTIFIER")
                && !operand
                    .source_sql
                    .as_deref()
                    .is_some_and(|source| source.contains("SELECT"))
        }));
        assert_eq!(
            tuple_in.subquery_rel.as_ref().unwrap().row_type.len(),
            tuple_in.operands.len()
        );
        convert_raw_file(raw374.clone()).expect("calcite374 exact tuple IN");

        let mut swapped_whole374 = raw374.clone();
        find_first_in_subquery_mut(swapped_whole374.queries[0].rel.as_mut().unwrap())
            .unwrap()
            .operands
            .swap(0, 1);
        assert!(
            convert_raw_file(swapped_whole374).is_err(),
            "a coherent whole-operand swap must not reorder the source ROW"
        );

        let mut reordered374 = raw374.clone();
        let tuple_in =
            find_first_in_subquery_mut(reordered374.queries[0].rel.as_mut().unwrap()).unwrap();
        let (left, right) = tuple_in.operands.split_at_mut(1);
        let left = &mut left[0];
        let right = &mut right[0];
        std::mem::swap(&mut left.source_sql, &mut right.source_sql);
        std::mem::swap(&mut left.source_node_id, &mut right.source_node_id);
        std::mem::swap(&mut left.source_text, &mut right.source_text);
        std::mem::swap(&mut left.source_kind, &mut right.source_kind);
        std::mem::swap(
            &mut left.source_identifier_names,
            &mut right.source_identifier_names,
        );
        std::mem::swap(
            &mut left.source_identifier_quoted,
            &mut right.source_identifier_quoted,
        );
        assert!(convert_raw_file(reordered374).is_err());

        let mut truncated374 = raw374.clone();
        find_first_in_subquery_mut(truncated374.queries[0].rel.as_mut().unwrap())
            .unwrap()
            .operands
            .pop();
        assert!(convert_raw_file(truncated374).is_err());

        let mut wrong_operator374 = raw374.clone();
        find_first_in_subquery_mut(wrong_operator374.queries[0].rel.as_mut().unwrap())
            .unwrap()
            .source_operator = Some("NOT IN".to_owned());
        assert!(convert_raw_file(wrong_operator374).is_err());

        let mut borrowed_row374 = raw374;
        let tuple_in =
            find_first_in_subquery_mut(borrowed_row374.queries[0].rel.as_mut().unwrap()).unwrap();
        let operand = &mut tuple_in.operands[1];
        operand.source_sql = Some("ROW(`empno`, `deptno`)".to_owned());
        operand.source_node_id = Some("1:15-1:29".to_owned());
        operand.source_text = Some("(EMPNO, DEPTNO)".to_owned());
        operand.source_kind = Some("ROW".to_owned());
        operand.source_operator = Some("ROW".to_owned());
        operand.source_identifier_names.clear();
        operand.source_identifier_quoted.clear();
        assert!(convert_raw_file(borrowed_row374).is_err());
    });
}

#[test]
#[ignore = "requires the Java Calcite wrapper and frozen benchmark inputs"]
fn calcite_wrapper_closes_round192_precise_lowering_boundaries() {
    fn first_expanded_rex(rel: &CalciteRel) -> Option<&CalciteRex> {
        fn in_rex(rex: &CalciteRex) -> Option<&CalciteRex> {
            if rex.source_expansion.is_some() {
                return Some(rex);
            }
            rex.operands
                .iter()
                .find_map(in_rex)
                .or_else(|| rex.subquery_rel.as_deref().and_then(first_expanded_rex))
        }
        rel_rexes(rel)
            .find_map(in_rex)
            .or_else(|| rel.inputs.iter().find_map(first_expanded_rex))
    }

    fn first_expanded_rex_mut(rel: &mut CalciteRel) -> Option<&mut CalciteRex> {
        fn in_rex(rex: &mut CalciteRex) -> Option<&mut CalciteRex> {
            if rex.source_expansion.is_some() {
                return Some(rex);
            }
            for operand in &mut rex.operands {
                if let Some(found) = in_rex(operand) {
                    return Some(found);
                }
            }
            rex.subquery_rel
                .as_deref_mut()
                .and_then(first_expanded_rex_mut)
        }
        for rex in &mut rel.project_rex {
            if let Some(found) = in_rex(rex) {
                return Some(found);
            }
        }
        if let Some(rex) = rel.condition_rex.as_mut()
            && let Some(found) = in_rex(rex)
        {
            return Some(found);
        }
        for input in &mut rel.inputs {
            if let Some(found) = first_expanded_rex_mut(input) {
                return Some(found);
            }
        }
        None
    }

    fn ordered_in_mut(rel: &mut CalciteRel) -> Option<&mut CalciteRex> {
        fn in_rex(rex: &mut CalciteRex) -> Option<&mut CalciteRex> {
            if rex.source_in_subquery_order.is_some() {
                return Some(rex);
            }
            for operand in &mut rex.operands {
                if let Some(found) = in_rex(operand) {
                    return Some(found);
                }
            }
            rex.subquery_rel.as_deref_mut().and_then(ordered_in_mut)
        }
        for rex in &mut rel.project_rex {
            if let Some(found) = in_rex(rex) {
                return Some(found);
            }
        }
        if let Some(rex) = rel.condition_rex.as_mut()
            && let Some(found) = in_rex(rex)
        {
            return Some(found);
        }
        for input in &mut rel.inputs {
            if let Some(found) = ordered_in_mut(input) {
                return Some(found);
            }
        }
        None
    }

    fn one_line_span_fragment(sql: &str, span: &str) -> String {
        let (start, end) = span.split_once('-').unwrap();
        let (start_line, start_column) = start.split_once(':').unwrap();
        let (end_line, end_column) = end.split_once(':').unwrap();
        assert_eq!((start_line, end_line), ("1", "1"));
        sql[start_column.parse::<usize>().unwrap() - 1..end_column.parse().unwrap()].to_owned()
    }

    with_large_calcite_stack(|| {
        let repo = repo_root();
        let frozen = repo.join("benchmarks/core/.generated/sqlsolver/nonwetune-flat");

        // Qualified inner pass-through items may define an unqualified or
        // differently qualified outer derived-column reference.  The final
        // direct identifier, not the complete qualified definition text, is
        // the public output name.
        for case_name in [
            "verieql-literature__cex-benchmarks-csep544_hw3-49",
            "verieql-calcite__calcite-233",
        ] {
            let case = frozen.join(case_name);
            for sql_name in ["sql1.sql", "sql2.sql"] {
                let raw = run_calcite(&repo, &case.join("schema.sql"), &case.join(sql_name));
                convert_raw_file(raw).unwrap_or_else(|error| {
                    panic!("{case_name}/{sql_name}: qualified pass-through: {error}")
                });
            }
        }
        let csep = frozen.join("verieql-literature__cex-benchmarks-csep544_hw3-49");
        let raw = run_calcite(&repo, &csep.join("schema.sql"), &csep.join("sql2.sql"));
        let expansion = first_expanded_rex(raw.queries[0].rel.as_ref().unwrap())
            .unwrap()
            .source_expansion
            .as_ref()
            .unwrap();
        assert_eq!(expansion.kind, "DIRECT_DERIVED_PASSTHROUGH");
        assert!(expansion.reference_text.contains('.'));
        assert!(expansion.output_alias_text.contains('.'));

        let mut wrong_index = raw.clone();
        let rex = first_expanded_rex_mut(wrong_index.queries[0].rel.as_mut().unwrap()).unwrap();
        rex.index = rex.index.map(|index| index + 1);
        rex.text = rex.index.map(|index| format!("${index}"));

        let mut wrong_name = raw.clone();
        first_expanded_rex_mut(wrong_name.queries[0].rel.as_mut().unwrap())
            .unwrap()
            .source_expansion
            .as_mut()
            .unwrap()
            .reference_text = "P.NOT_THE_OUTPUT".to_owned();

        let mut wrong_span = raw.clone();
        let expansion = first_expanded_rex_mut(wrong_span.queries[0].rel.as_mut().unwrap())
            .unwrap()
            .source_expansion
            .as_mut()
            .unwrap();
        expansion.output_alias_node_id = expansion.reference_node_id.clone();

        let mut wrong_kind = raw.clone();
        first_expanded_rex_mut(wrong_kind.queries[0].rel.as_mut().unwrap())
            .unwrap()
            .source_expansion
            .as_mut()
            .unwrap()
            .kind = "DIRECT_DERIVED_OUTPUT_ALIAS".to_owned();

        let mut duplicate_output = raw;
        let expansion = first_expanded_rex_mut(duplicate_output.queries[0].rel.as_mut().unwrap())
            .unwrap()
            .source_expansion
            .as_mut()
            .unwrap();
        expansion.inner_select_text =
            expansion
                .inner_select_text
                .replacen("F1.DEST_CITY", "F1.ORIGIN_CITY", 1);

        for mutation in [
            wrong_index,
            wrong_name,
            wrong_span,
            wrong_kind,
            duplicate_output,
        ] {
            assert!(convert_raw_file(mutation).is_err());
        }

        let quoted = temp_dir("round192-quoted-passthrough");
        let quoted_schema = quoted.join("schema.sql");
        let quoted_query = quoted.join("query.sql");
        fs::write(&quoted_schema, "create table \"T\" (\"MiXeD\" integer);\n").unwrap();
        fs::write(
            &quoted_query,
            "select d.\"MiXeD\" from (select \"T\".\"MiXeD\" from \"T\") as d;\n",
        )
        .unwrap();
        let quoted_raw = run_calcite(&repo, &quoted_schema, &quoted_query);
        convert_raw_file(quoted_raw.clone()).expect("quoted direct pass-through");
        let mut quoted_case = quoted_raw;
        first_expanded_rex_mut(quoted_case.queries[0].rel.as_mut().unwrap())
            .unwrap()
            .source_expansion
            .as_mut()
            .unwrap()
            .output_alias_text = "\"T\".\"mixed\"".to_owned();
        assert!(convert_raw_file(quoted_case).is_err());
        fs::remove_dir_all(&quoted).unwrap();

        // The complete filtered output root is distinct from its core call;
        // direct and CAST-child roles both lower, including Calcite's exact
        // same-query reuse of the final DEPTNO=20 Boolean carrier.
        let calcite13 = frozen.join("verieql-calcite__calcite-13");
        let raw13 = run_calcite(
            &repo,
            &calcite13.join("schema.sql"),
            &calcite13.join("sql2.sql"),
        );
        convert_raw_file(raw13.clone()).expect("calcite13 exact filtered outputs");

        let mut wrong_output = raw13.clone();
        let output = find_rel_rex_by_source_kind_mut(
            wrong_output.queries[0].rel.as_mut().unwrap(),
            "FILTER",
        )
        .unwrap();
        output.index = output.index.map(|index| index + 1);
        output.text = output.index.map(|index| format!("${index}"));

        let mut wrong_wrapper = raw13.clone();
        find_rel_rex_by_source_kind_mut(wrong_wrapper.queries[0].rel.as_mut().unwrap(), "FILTER")
            .unwrap()
            .source_operator = Some("OTHER".to_owned());

        let mut wrong_predicate = raw13.clone();
        let aggregate = first_aggregate_mut(wrong_predicate.queries[0].rel.as_mut().unwrap());
        assert_eq!(
            aggregate.inputs[0].project_rex[2].source_text.as_deref(),
            Some("JOB = 'CLERK'")
        );
        aggregate.inputs[0].project_rex[2] = aggregate.inputs[0].project_rex[3].clone();

        let mut wrong_core = raw13.clone();
        let aggregate = first_aggregate_mut(wrong_core.queries[0].rel.as_mut().unwrap());
        aggregate.agg_call_details[1].source_distinct = Some(false);

        for mutation in [wrong_output, wrong_wrapper, wrong_predicate, wrong_core] {
            assert!(convert_raw_file(mutation).is_err());
        }

        // The ordered IN root must end in at least one close parenthesis;
        // extending it through a following AND is equally invalid.
        let wetune46 = repo.join("benchmarks/core/.generated/sqlsolver/wetune-issues/46");
        let raw46 = run_calcite(
            &repo,
            &wetune46.join("schema.sql"),
            &wetune46.join("sql1.sql"),
        );
        convert_raw_file(raw46.clone()).expect("wetune46 exact ordered IN root");
        let source46 = fs::read_to_string(wetune46.join("sql1.sql")).unwrap();
        let mut truncated = raw46.clone();
        let rex = ordered_in_mut(truncated.queries[0].rel.as_mut().unwrap()).unwrap();
        let start = rex
            .source_node_id
            .as_deref()
            .unwrap()
            .split_once('-')
            .unwrap()
            .0
            .to_owned();
        let order_end = rex
            .source_in_subquery_order
            .as_ref()
            .unwrap()
            .order_by_node_id
            .split_once('-')
            .unwrap()
            .1
            .to_owned();
        let truncated_span = format!("{start}-{order_end}");
        rex.source_text = Some(one_line_span_fragment(&source46, &truncated_span));
        rex.source_node_id = Some(truncated_span);
        assert!(convert_raw_file(truncated).is_err());

        let mut non_closing = raw46;
        let rex = ordered_in_mut(non_closing.queries[0].rel.as_mut().unwrap()).unwrap();
        let start = rex
            .source_node_id
            .as_deref()
            .unwrap()
            .split_once('-')
            .unwrap()
            .0;
        let end = rex
            .source_node_id
            .as_deref()
            .unwrap()
            .split_once('-')
            .unwrap()
            .1
            .split_once(':')
            .unwrap()
            .1
            .parse::<usize>()
            .unwrap();
        let non_closing_span = format!("{start}-1:{}", end + 4);
        rex.source_text = Some(one_line_span_fragment(&source46, &non_closing_span));
        rex.source_node_id = Some(non_closing_span);
        assert!(convert_raw_file(non_closing).is_err());

        // SINGLE_VALUE has an exact nullable type-preserving aggregate
        // contract and a declarative query-shape classification. Forged
        // operator/argument/span data must still fail at source authority.
        let calcite246 = frozen.join("verieql-calcite__calcite-246");
        for sql_name in ["sql1.sql", "sql2.sql"] {
            let raw = run_calcite(
                &repo,
                &calcite246.join("schema.sql"),
                &calcite246.join(sql_name),
            );
            convert_raw_file(raw.clone())
                .unwrap_or_else(|error| panic!("{sql_name}: exact SINGLE_VALUE: {error}"));

            let mut wrong_operator = raw.clone();
            first_aggregate_mut(wrong_operator.queries[0].rel.as_mut().unwrap()).agg_call_details
                [0]
            .source_operator = Some("any_value".to_owned());

            let mut wrong_argument = raw.clone();
            let aggregate = first_aggregate_mut(wrong_argument.queries[0].rel.as_mut().unwrap());
            aggregate.agg_call_details[0].arg_list = vec![1];
            aggregate.agg_call_details[0].text = "SINGLE_VALUE($1)".to_owned();

            let mut wrong_span = raw;
            let call = &mut first_aggregate_mut(wrong_span.queries[0].rel.as_mut().unwrap())
                .agg_call_details[0];
            call.source_node_id = call.source_operands[0].source_node_id.clone();
            call.source_text = call.source_operands[0].source_text.clone();

            for mutation in [wrong_operator, wrong_argument, wrong_span] {
                let error = convert_raw_file(mutation).unwrap_err();
                assert!(
                    !error
                        .to_string()
                        .contains("source WHERE=false, HAVING=false, joins=1, aggregate=0"),
                    "forged SINGLE_VALUE data reached the unrelated query-shape blocker: {error}"
                );
            }
        }
    });
}
