use super::*;
use serde_json::json;

#[test]
fn navigation_tags_preserve_wire_spelling() {
    for (side, label, prefix) in [
        (QuerySide::Source, "source", 'S'),
        (QuerySide::Target, "target", 'T'),
    ] {
        assert_eq!(serde_json::to_value(side).unwrap(), json!(label));
        assert_eq!(side.to_string(), label);
        assert_eq!(side.node_prefix(), prefix);
    }
    for (kind, label) in [
        (EdgeKind::Relational, "relational"),
        (EdgeKind::ScalarSubquery, "scalar_subquery"),
    ] {
        assert_eq!(serde_json::to_value(kind).unwrap(), json!(label));
    }
    for (kind, label) in [
        (MismatchKind::OrderedAttribute, "ordered_attribute"),
        (MismatchKind::Arity, "arity"),
    ] {
        assert_eq!(serde_json::to_value(kind).unwrap(), json!(label));
    }
    for (kind, label) in [
        (FormalQueryShapeKind::ScalarExpr, "scalar_expr"),
        (FormalQueryShapeKind::QueryExpr, "query_expr"),
    ] {
        assert_eq!(serde_json::to_value(kind).unwrap(), json!(label));
    }
}

#[test]
fn operator_tags_preserve_wire_spelling() {
    use OperatorKind::*;
    for (kind, label) in [
        (Error, "Error"),
        (Empty, "Empty"),
        (EmptyTuple, "EmptyTuple"),
        (Table, "Table"),
        (Set, "Set"),
        (CrossJoin, "CrossJoin"),
        (Join, "Join"),
        (Projection, "Projection"),
        (Selection, "Selection"),
        (Group, "Group"),
        (GroupingSets, "GroupingSets"),
        (Rank, "Rank"),
        (Window, "Window"),
        (Distinct, "Distinct"),
        (OrderBy, "OrderBy"),
        (Offset, "Offset"),
        (Fetch, "Fetch"),
    ] {
        assert_eq!(serde_json::to_value(kind).unwrap(), json!(label));
    }
}

#[test]
fn generic_statement_envelope_preserves_compact_json_contract() {
    let expanded = StatementShape {
        statement_index: 1,
        exact_sql_sha256: "exact".to_owned(),
        frontend_sql_sha256: "frontend".to_owned(),
        exact_frontend_bytes_equal: false,
        emitted_rocq_root_symbol: "source_query_expr".to_owned(),
        emitted_rocq_output_signature_symbol: "source_output_signature".to_owned(),
        final_output_canonicalization: true,
        output_signature: vec![Attribute {
            name: "x".to_owned(),
            r#type: "Z".to_owned(),
            nullable: None,
        }],
        typed_frontend_tree: CompactOperatorTree {
            node_count: 2,
            max_depth: 2,
            expression: "Projection(Table)".to_owned(),
        },
    };
    let compact = compact_query_statement(&expanded, 7);
    assert_eq!(
        serde_json::to_value(&compact).unwrap(),
        json!({
            "statementIndex": 1,
            "exactSqlSha256": "exact",
            "frontendSqlSha256": "frontend",
            "exactFrontendBytesEqual": false,
            "emittedRocqRootSymbol": "source_query_expr",
            "emittedRocqOutputSignatureSymbol": "source_output_signature",
            "finalOutputCanonicalization": true,
            "outputSignature": [{"name": "x", "type": "Z"}],
            "typedFrontendTree": {"nodeCount": 2, "maxDepth": 2, "rootNode": 7}
        })
    );
    assert_eq!(expanded.typed_frontend_tree.expression, "Projection(Table)");
}
