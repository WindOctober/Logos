use crate::ir::{AggregateCall, Query, RelExpr, ScalarExpr, ValuesTuples};

pub fn query_scalars(query: &Query) -> Vec<&ScalarExpr> {
    let mut out = Vec::new();
    collect_rel_scalars(&query.rel, &mut out);
    out
}

fn collect_rel_scalars<'a>(rel: &'a RelExpr, out: &mut Vec<&'a ScalarExpr>) {
    match rel {
        RelExpr::TableScan { .. } => {}
        RelExpr::Project { input, exprs, .. } => {
            out.extend(exprs);
            collect_rel_scalars(input, out);
        }
        RelExpr::Filter {
            input, predicate, ..
        } => {
            out.push(predicate);
            collect_rel_scalars(input, out);
        }
        RelExpr::Join {
            left,
            right,
            condition,
            ..
        } => {
            out.push(condition);
            collect_rel_scalars(left, out);
            collect_rel_scalars(right, out);
        }
        RelExpr::Aggregate {
            input, agg_calls, ..
        } => {
            for call in agg_calls {
                collect_aggregate_scalars(call, out);
            }
            collect_rel_scalars(input, out);
        }
        RelExpr::Sort {
            input,
            fetch,
            offset,
            ..
        } => {
            if let Some(fetch) = fetch {
                out.push(fetch);
            }
            if let Some(offset) = offset {
                out.push(offset);
            }
            collect_rel_scalars(input, out);
        }
        RelExpr::Set { inputs, .. } => {
            for input in inputs {
                collect_rel_scalars(input, out);
            }
        }
        RelExpr::Values { tuples, .. } => {
            if let ValuesTuples::Rows { rows } = tuples {
                for row in rows {
                    out.extend(row);
                }
            }
        }
    }
}

fn collect_aggregate_scalars<'a>(call: &'a AggregateCall, out: &mut Vec<&'a ScalarExpr>) {
    out.extend(&call.args);
    if let Some(filter) = &call.filter {
        out.push(filter);
    }
}
