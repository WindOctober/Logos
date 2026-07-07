use crate::calcite::scalar::try_calcite_scalar;
use crate::ir::{
    JoinType, ScalarExpr, TextRelAggregateCall, TextRelAttr, TextRelNode, TextRelNodeKind,
    TextRelProjectExpr, TextRelShape, TextRelSortKey,
};

pub fn parse_calcite_text_plan(raw: &str) -> Option<TextRelNode> {
    let lines = logical_plan_lines(raw)?;
    if lines.is_empty() {
        return None;
    }

    let borrowed_lines: Vec<_> = lines
        .iter()
        .map(|line| (line.indent, line.text.trim()))
        .collect();
    let (root, next) = parse_node(&borrowed_lines, 0)?;
    if next == borrowed_lines.len() {
        Some(root)
    } else {
        None
    }
}

fn logical_plan_lines(raw: &str) -> Option<Vec<PlanLine>> {
    let mut out = Vec::new();
    let mut current = String::new();
    let mut current_indent = 0usize;
    let mut depth = DelimiterDepth::default();

    for physical in raw.lines() {
        if physical.trim().is_empty() {
            continue;
        }
        if current.is_empty() {
            current_indent = leading_spaces(physical);
            current.push_str(physical.trim());
        } else {
            current.push('\n');
            current.push_str(physical);
        }

        apply_depth_for_str(&mut depth, physical)?;
        if depth.is_balanced() {
            out.push(PlanLine {
                indent: current_indent,
                text: std::mem::take(&mut current),
            });
        }
    }

    if current.is_empty() && depth.is_balanced() {
        Some(out)
    } else {
        None
    }
}

#[derive(Debug, Clone)]
struct PlanLine {
    indent: usize,
    text: String,
}

fn parse_node(lines: &[(usize, &str)], index: usize) -> Option<(TextRelNode, usize)> {
    let (indent, line) = *lines.get(index)?;
    let mut node = parse_node_line(line)?;
    let mut next = index + 1;

    while let Some((next_indent, _)) = lines.get(next) {
        if *next_indent <= indent {
            break;
        }
        let (child, child_next) = parse_node(lines, next)?;
        node.inputs.push(child);
        next = child_next;
    }

    Some((node, next))
}

fn parse_node_line(line: &str) -> Option<TextRelNode> {
    let line = line.trim();
    let (rel_type, attrs) = if let Some(open) = first_top_level_open_paren(line) {
        let rel_type = line[..open].trim();
        if rel_type.is_empty() || !line.ends_with(')') {
            return None;
        }
        let attrs = &line[open + 1..line.len() - 1];
        (rel_type, parse_attrs(attrs)?)
    } else {
        (line, Vec::new())
    };

    Some(TextRelNode {
        rel_type: rel_type.to_owned(),
        kind: classify_text_rel_node_kind(rel_type),
        shape: build_text_rel_shape(rel_type, &attrs),
        attrs,
        inputs: Vec::new(),
        raw_line: line.to_owned(),
    })
}

fn build_text_rel_shape(rel_type: &str, attrs: &[TextRelAttr]) -> TextRelShape {
    match classify_text_rel_node_kind(rel_type) {
        TextRelNodeKind::TableScan => TextRelShape::TableScan {
            table: attr_value(attrs, "table")
                .map(parse_bracket_path)
                .unwrap_or_default(),
        },
        TextRelNodeKind::Project => TextRelShape::Project {
            exprs: attrs
                .iter()
                .filter(|attr| attr.name != "variablesSet")
                .filter_map(|attr| {
                    Some(TextRelProjectExpr {
                        name: attr.name.clone(),
                        expr: attr_scalar(&attr.value)?,
                    })
                })
                .collect(),
            variables_set: attr_value(attrs, "variablesSet").map(ToOwned::to_owned),
        },
        TextRelNodeKind::Filter => TextRelShape::Filter {
            condition: attr_value(attrs, "condition").and_then(attr_scalar),
            variables_set: attr_value(attrs, "variablesSet").map(ToOwned::to_owned),
        },
        TextRelNodeKind::Join => TextRelShape::Join {
            condition: attr_value(attrs, "condition").and_then(attr_scalar),
            join_type: attr_value(attrs, "joinType").and_then(parse_text_join_type),
        },
        TextRelNodeKind::Aggregate => TextRelShape::Aggregate {
            group_keys: attr_value(attrs, "group").and_then(parse_text_group_set),
            grouping_sets: attr_value(attrs, "groups").and_then(parse_text_grouping_sets),
            agg_calls: attrs
                .iter()
                .filter(|attr| attr.name != "group" && attr.name != "groups")
                .map(|attr| TextRelAggregateCall {
                    name: attr.name.clone(),
                    raw: strip_calcite_attr_brackets(&attr.value).to_owned(),
                })
                .collect(),
        },
        TextRelNodeKind::Sort => TextRelShape::Sort {
            sort_keys: parse_text_sort_keys(attrs),
            fetch: attr_value(attrs, "fetch").and_then(attr_scalar),
            offset: attr_value(attrs, "offset").and_then(attr_scalar),
        },
        TextRelNodeKind::Union | TextRelNodeKind::Intersect | TextRelNodeKind::Minus => {
            TextRelShape::Set {
                all: attr_value(attrs, "all").and_then(parse_text_bool),
            }
        }
        TextRelNodeKind::Values => TextRelShape::Values {
            tuples: attr_value(attrs, "tuples").and_then(parse_text_values_tuples),
        },
        TextRelNodeKind::Other { .. } => TextRelShape::Other,
    }
}

fn attr_value<'a>(attrs: &'a [TextRelAttr], name: &str) -> Option<&'a str> {
    attrs
        .iter()
        .find(|attr| attr.name == name)
        .map(|attr| attr.value.as_str())
}

fn attr_scalar(value: &str) -> Option<Box<ScalarExpr>> {
    try_calcite_scalar(strip_calcite_attr_brackets(value).to_owned())
        .ok()
        .map(Box::new)
}

fn strip_calcite_attr_brackets(value: &str) -> &str {
    let trimmed = value.trim();
    trimmed
        .strip_prefix('[')
        .and_then(|inner| inner.strip_suffix(']'))
        .unwrap_or(trimmed)
        .trim()
}

fn parse_bracket_path(value: &str) -> Vec<String> {
    let mut stripped = value.trim();
    loop {
        let Some(inner) = stripped
            .strip_prefix('[')
            .and_then(|inner| inner.strip_suffix(']'))
        else {
            break;
        };
        stripped = inner.trim();
    }
    if stripped.is_empty() {
        Vec::new()
    } else {
        stripped
            .split(',')
            .map(str::trim)
            .filter(|part| !part.is_empty())
            .map(ToOwned::to_owned)
            .collect()
    }
}

fn parse_text_join_type(value: &str) -> Option<JoinType> {
    match strip_calcite_attr_brackets(value)
        .to_ascii_uppercase()
        .as_str()
    {
        "INNER" => Some(JoinType::Inner),
        "LEFT" => Some(JoinType::Left),
        "RIGHT" => Some(JoinType::Right),
        "FULL" => Some(JoinType::Full),
        "SEMI" => Some(JoinType::Semi),
        "ANTI" => Some(JoinType::Anti),
        _ => None,
    }
}

fn parse_text_bool(value: &str) -> Option<bool> {
    match strip_calcite_attr_brackets(value)
        .to_ascii_lowercase()
        .as_str()
    {
        "true" => Some(true),
        "false" => Some(false),
        _ => None,
    }
}

fn parse_text_group_set(value: &str) -> Option<Vec<usize>> {
    let inner = strip_calcite_attr_brackets(value)
        .strip_prefix('{')?
        .strip_suffix('}')?
        .trim();
    if inner.is_empty() {
        return Some(Vec::new());
    }
    inner
        .split(',')
        .map(|part| part.trim().parse::<usize>().ok())
        .collect()
}

fn parse_text_grouping_sets(value: &str) -> Option<Vec<Vec<usize>>> {
    let inner = strip_calcite_attr_brackets(value).trim();
    let sets_text = inner
        .strip_prefix('[')
        .and_then(|value| value.strip_suffix(']'))
        .unwrap_or(inner);
    if sets_text.trim().is_empty() {
        return Some(Vec::new());
    }
    split_top_level_commas(sets_text)?
        .into_iter()
        .map(|part| parse_text_group_set(&format!("[{}]", part.trim())))
        .collect()
}

fn parse_text_sort_keys(attrs: &[TextRelAttr]) -> Vec<TextRelSortKey> {
    let mut keys = Vec::new();
    for attr in attrs {
        let Some(index_text) = attr.name.strip_prefix("sort") else {
            continue;
        };
        let Ok(index) = index_text.parse::<usize>() else {
            continue;
        };
        let direction = attr_value(attrs, &format!("dir{index}"))
            .map(strip_calcite_attr_brackets)
            .map(ToOwned::to_owned);
        let Some(expr) = attr_scalar(&attr.value) else {
            continue;
        };
        keys.push(TextRelSortKey {
            index,
            expr,
            direction,
        });
    }
    keys
}

fn parse_text_values_tuples(value: &str) -> Option<Vec<Vec<Box<ScalarExpr>>>> {
    let rows_text = strip_outer_brackets(value.trim())?;
    if rows_text.trim().is_empty() {
        return Some(Vec::new());
    }
    split_top_level_commas(rows_text)?
        .into_iter()
        .map(|row| {
            let inner = row.trim().strip_prefix('{')?.strip_suffix('}')?.trim();
            if inner.is_empty() {
                return Some(Vec::new());
            }
            split_top_level_commas(inner)?
                .into_iter()
                .map(|value| try_calcite_scalar(value).ok().map(Box::new))
                .collect()
        })
        .collect()
}

fn strip_outer_brackets(value: &str) -> Option<&str> {
    let first = value.strip_prefix('[')?.strip_suffix(']')?.trim();
    Some(
        first
            .strip_prefix('[')
            .and_then(|inner| inner.strip_suffix(']'))
            .unwrap_or(first)
            .trim(),
    )
}

fn parse_attrs(value: &str) -> Option<Vec<TextRelAttr>> {
    let trimmed = value.trim();
    if trimmed.is_empty() {
        return Some(Vec::new());
    }

    split_top_level_commas(trimmed)?
        .into_iter()
        .map(|part| {
            let (name, value) = split_top_level_equals(&part)?;
            Some(TextRelAttr {
                name: name.trim().to_owned(),
                value: value.trim().to_owned(),
            })
        })
        .collect()
}

fn split_top_level_commas(value: &str) -> Option<Vec<String>> {
    let mut out = Vec::new();
    let mut start = 0usize;
    let mut depth = DelimiterDepth::default();
    let mut chars = value.char_indices().peekable();
    let mut skip_until = None;

    while let Some((index, ch)) = chars.next() {
        if skip_until.is_some_and(|end| index < end) {
            continue;
        }
        skip_until = None;
        if let Some(end) = find_sarg_literal_end(value, index) {
            skip_until = Some(end);
            continue;
        }
        if depth.handle_quote(ch, &mut chars) {
            continue;
        }
        if depth.in_string {
            continue;
        }
        match ch {
            ',' if depth.is_top_level() => {
                out.push(value[start..index].trim().to_owned());
                start = index + ch.len_utf8();
            }
            _ => depth.apply(ch)?,
        }
    }

    if !depth.is_balanced() {
        return None;
    }

    let tail = value[start..].trim();
    if !tail.is_empty() {
        out.push(tail.to_owned());
    }
    Some(out)
}

fn split_top_level_equals(value: &str) -> Option<(&str, &str)> {
    let mut depth = DelimiterDepth::default();
    let mut chars = value.char_indices().peekable();
    let mut skip_until = None;

    while let Some((index, ch)) = chars.next() {
        if skip_until.is_some_and(|end| index < end) {
            continue;
        }
        skip_until = None;
        if let Some(end) = find_sarg_literal_end(value, index) {
            skip_until = Some(end);
            continue;
        }
        if depth.handle_quote(ch, &mut chars) {
            continue;
        }
        if depth.in_string {
            continue;
        }
        match ch {
            '=' if depth.is_top_level() => {
                let name = value[..index].trim();
                let value = value[index + ch.len_utf8()..].trim();
                if name.is_empty() || value.is_empty() {
                    return None;
                }
                return Some((name, value));
            }
            _ => depth.apply(ch)?,
        }
    }

    None
}

fn first_top_level_open_paren(value: &str) -> Option<usize> {
    let mut in_string = false;
    let mut chars = value.char_indices().peekable();

    while let Some((index, ch)) = chars.next() {
        if ch == '\'' {
            if in_string && matches!(chars.peek(), Some((_, '\''))) {
                chars.next();
            } else {
                in_string = !in_string;
            }
            continue;
        }
        if !in_string && ch == '(' {
            return Some(index);
        }
    }
    None
}

fn classify_text_rel_node_kind(rel_type: &str) -> TextRelNodeKind {
    match rel_type {
        "LogicalTableScan" => TextRelNodeKind::TableScan,
        "LogicalProject" => TextRelNodeKind::Project,
        "LogicalFilter" => TextRelNodeKind::Filter,
        "LogicalJoin" => TextRelNodeKind::Join,
        "LogicalAggregate" => TextRelNodeKind::Aggregate,
        "LogicalSort" => TextRelNodeKind::Sort,
        "LogicalUnion" => TextRelNodeKind::Union,
        "LogicalIntersect" => TextRelNodeKind::Intersect,
        "LogicalMinus" => TextRelNodeKind::Minus,
        "LogicalValues" => TextRelNodeKind::Values,
        other => TextRelNodeKind::Other {
            rel_type: other.to_owned(),
        },
    }
}

fn leading_spaces(value: &str) -> usize {
    value.chars().take_while(|ch| *ch == ' ').count()
}

fn apply_depth_for_str(depth: &mut DelimiterDepth, value: &str) -> Option<()> {
    let mut chars = value.char_indices().peekable();
    let mut skip_until = None;
    while let Some((index, ch)) = chars.next() {
        if skip_until.is_some_and(|end| index < end) {
            continue;
        }
        skip_until = None;
        if let Some(end) = find_sarg_literal_end(value, index) {
            skip_until = Some(end);
            continue;
        }
        if depth.handle_quote(ch, &mut chars) {
            continue;
        }
        if depth.in_string {
            continue;
        }
        depth.apply(ch)?;
    }
    Some(())
}

fn find_sarg_literal_end(value: &str, start: usize) -> Option<usize> {
    if !value[start..].starts_with("Sarg[") {
        return None;
    }

    let mut in_string = false;
    let mut chars = value[start + "Sarg[".len()..].char_indices().peekable();
    while let Some((relative, ch)) = chars.next() {
        if ch == '\'' {
            if in_string && matches!(chars.peek(), Some((_, '\''))) {
                chars.next();
            } else {
                in_string = !in_string;
            }
            continue;
        }
        if in_string || ch != ']' {
            continue;
        }

        let close = start + "Sarg[".len() + relative + ch.len_utf8();
        let next = value[close..].chars().next();
        if matches!(next, None | Some(')' | ',' | ':')) {
            return Some(close);
        }
    }

    None
}

#[derive(Debug, Clone, Default)]
struct DelimiterDepth {
    paren: usize,
    bracket: usize,
    brace: usize,
    in_string: bool,
    last_char: Option<char>,
}

impl DelimiterDepth {
    fn is_top_level(&self) -> bool {
        self.paren == 0 && self.bracket == 0 && self.brace == 0
    }

    fn is_balanced(&self) -> bool {
        self.is_top_level() && !self.in_string
    }

    fn handle_quote(
        &mut self,
        ch: char,
        chars: &mut std::iter::Peekable<std::str::CharIndices<'_>>,
    ) -> bool {
        if ch != '\'' {
            return false;
        }
        if self.in_string && matches!(chars.peek(), Some((_, '\''))) {
            chars.next();
        } else {
            self.in_string = !self.in_string;
        }
        true
    }

    fn apply(&mut self, ch: char) -> Option<()> {
        match ch {
            '(' if self.brace == 0 && self.last_char != Some('[') => self.paren += 1,
            ')' if self.brace == 0 => self.paren = self.paren.checked_sub(1)?,
            '[' if self.brace == 0 => self.bracket += 1,
            ']' if self.brace == 0 => self.bracket = self.bracket.saturating_sub(1),
            '{' => self.brace += 1,
            '}' => self.brace = self.brace.checked_sub(1)?,
            _ => {}
        }
        self.last_char = Some(ch);
        Some(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::ScalarOp;

    #[test]
    fn parses_indented_text_plan_tree() {
        let raw = "LogicalProject(DEPTNO=[$1])\n  LogicalFilter(condition=[<($0, 20)])\n    LogicalTableScan(table=[[EMP]])";
        let plan = parse_calcite_text_plan(raw).unwrap();

        assert_eq!(plan.kind, TextRelNodeKind::Project);
        assert_eq!(plan.attrs[0].name, "DEPTNO");
        assert_eq!(plan.inputs.len(), 1);
        assert_eq!(plan.inputs[0].kind, TextRelNodeKind::Filter);
        assert_eq!(plan.inputs[0].inputs[0].kind, TextRelNodeKind::TableScan);
    }

    #[test]
    fn parses_attrs_with_nested_commas_and_equals() {
        let raw = "LogicalFilter(condition=[AND(=($0, $1), IN($0, {\nLogicalProject(DEPTNO=[$0])\n  LogicalTableScan(table=[[DEPT]])\n}))], variablesSet=[[$cor0]])";
        let plan = parse_calcite_text_plan(raw).unwrap();

        assert_eq!(plan.kind, TextRelNodeKind::Filter);
        assert_eq!(plan.attrs.len(), 2);
        assert_eq!(plan.attrs[0].name, "condition");
        assert!(plan.attrs[0].value.contains("LogicalProject"));
        assert_eq!(plan.attrs[1].name, "variablesSet");
    }

    #[test]
    fn parses_set_plan_nodes() {
        let raw = "LogicalUnion(all=[true])\n  LogicalTableScan(table=[[A]])\n  LogicalTableScan(table=[[B]])";
        let plan = parse_calcite_text_plan(raw).unwrap();

        assert_eq!(plan.kind, TextRelNodeKind::Union);
        assert_eq!(plan.inputs.len(), 2);
        assert_eq!(plan.shape, TextRelShape::Set { all: Some(true) });
        assert_eq!(
            plan.inputs[0].shape,
            TextRelShape::TableScan {
                table: vec!["A".to_owned()]
            }
        );
    }

    #[test]
    fn lowers_text_plan_node_shapes() {
        let raw = "LogicalAggregate(group=[{0, 1}], agg#0=[COUNT()])\n  LogicalProject(EMPNO=[$0], DEPTNO=[$1])\n    LogicalFilter(condition=[<($0, 20)])\n      LogicalTableScan(table=[[EMP]])";
        let plan = parse_calcite_text_plan(raw).unwrap();

        assert_eq!(
            plan.shape,
            TextRelShape::Aggregate {
                group_keys: Some(vec![0, 1]),
                grouping_sets: None,
                agg_calls: vec![TextRelAggregateCall {
                    name: "agg#0".to_owned(),
                    raw: "COUNT()".to_owned(),
                }],
            }
        );

        let project = &plan.inputs[0];
        let TextRelShape::Project { exprs, .. } = &project.shape else {
            panic!("expected project shape");
        };
        assert_eq!(exprs.len(), 2);
        assert_eq!(exprs[0].name, "EMPNO");
        assert_eq!(exprs[0].expr.raw, "$0");

        let filter = &project.inputs[0];
        let TextRelShape::Filter {
            condition: Some(condition),
            ..
        } = &filter.shape
        else {
            panic!("expected filter condition");
        };
        assert_eq!(condition.raw, "<($0, 20)");
        assert!(matches!(
            condition.parsed,
            crate::ir::ScalarAst::Call {
                op: ScalarOp::Lt,
                ..
            }
        ));
    }

    #[test]
    fn lowers_join_and_sort_shapes() {
        let join = parse_calcite_text_plan(
            "LogicalJoin(condition=[true], joinType=[left])\n  LogicalTableScan(table=[[A]])\n  LogicalTableScan(table=[[B]])",
        )
        .unwrap();
        assert!(matches!(
            join.shape,
            TextRelShape::Join {
                join_type: Some(JoinType::Left),
                ..
            }
        ));

        let sort = parse_calcite_text_plan(
            "LogicalSort(sort0=[$0], dir0=[ASC], offset=[2], fetch=[10])\n  LogicalTableScan(table=[[A]])",
        )
        .unwrap();
        let TextRelShape::Sort {
            sort_keys,
            fetch: Some(fetch),
            offset: Some(offset),
        } = sort.shape
        else {
            panic!("expected sort shape");
        };
        assert_eq!(sort_keys.len(), 1);
        assert_eq!(sort_keys[0].direction.as_deref(), Some("ASC"));
        assert_eq!(fetch.raw, "10");
        assert_eq!(offset.raw, "2");
    }

    #[test]
    fn lowers_values_tuples_shape() {
        let plan =
            parse_calcite_text_plan("LogicalValues(tuples=[[{ 10, 'x' }, { null, +(2, 3) }]])")
                .unwrap();

        let TextRelShape::Values { tuples: Some(rows) } = plan.shape else {
            panic!("expected values tuples");
        };
        assert_eq!(rows.len(), 2);
        assert_eq!(rows[0][0].raw, "10");
        assert_eq!(rows[0][1].raw, "'x'");
        assert_eq!(rows[1][0].raw, "null");
        assert_eq!(rows[1][1].raw, "+(2, 3)");
    }

    #[test]
    fn parses_project_attrs_with_sarg_interval_brackets() {
        let plan = parse_calcite_text_plan(
            "LogicalProject($f11=[CASE(SEARCH(-($23, $0), Sarg[(30..60]]), 1, 0)], $f12=[CASE(SEARCH(-($23, $0), Sarg[(60..90]]), 1, 0)])\n  LogicalTableScan(table=[[store_sales]])",
        )
        .unwrap();

        let TextRelShape::Project { exprs, .. } = plan.shape else {
            panic!("expected project");
        };
        assert_eq!(exprs.len(), 2);
        assert_eq!(exprs[0].name, "$f11");
        assert_eq!(
            exprs[0].expr.raw,
            "CASE(SEARCH(-($23, $0), Sarg[(30..60]]), 1, 0)"
        );
    }

    #[test]
    fn parses_project_attrs_with_typed_sarg_interval_lists() {
        let plan = parse_calcite_text_plan(
            "LogicalProject($f1=[CASE(SEARCH($5, Sarg['1-URGENT':VARCHAR, '2-HIGH':VARCHAR]:VARCHAR), 1, 0)], $f2=[CASE(SEARCH($5, Sarg[(-\u{221e}..'1-URGENT':VARCHAR), ('1-URGENT':VARCHAR..'2-HIGH':VARCHAR), ('2-HIGH':VARCHAR..+\u{221e})]:VARCHAR), 1, 0)])\n  LogicalTableScan(table=[[LINEITEM]])",
        )
        .unwrap();

        let TextRelShape::Project { exprs, .. } = plan.shape else {
            panic!("expected project");
        };
        assert_eq!(exprs.len(), 2);
        assert_eq!(exprs[0].name, "$f1");
        assert_eq!(exprs[1].name, "$f2");
        assert!(exprs[1].expr.raw.contains("Sarg[(-\u{221e}.."));
    }
}
