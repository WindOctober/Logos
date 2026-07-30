#!/usr/bin/env python3
"""Materialize Calcite-attested coercions for PostgreSQL execution.

The Calcite benchmark is stored in its original SQL form.  Calcite may add
validator casts that PostgreSQL does not add, and its aggregate type system
keeps a few exact-numeric aggregates narrower than PostgreSQL does.  This
module turns only those independently attested differences into explicit SQL
casts.  Every rewrite is bound to an exact source span in generated Calcite IR;
missing, stale, overlapping, or unsupported evidence fails closed.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import re
from typing import Any, Iterator


class CalciteCoercionError(ValueError):
    """Raised when Calcite coercion evidence cannot be applied exactly."""


@dataclass(frozen=True)
class CoercionRewrite:
    start: int
    end: int
    node_id: str
    source_text: str
    replacement: str
    kind: str
    source_type: str
    postgres_native_type: str | None
    calcite_type: str
    ir_path: str

    def as_report(self) -> dict[str, Any]:
        report = {
            "kind": self.kind,
            "sourceNodeId": self.node_id,
            "sourceText": self.source_text,
            "sourceType": self.source_type,
            "calciteType": self.calcite_type,
            "replacement": self.replacement,
            "irPath": self.ir_path,
        }
        if self.postgres_native_type is not None:
            report["postgresNativeType"] = self.postgres_native_type
        return report


@dataclass(frozen=True)
class AggregateResultCoercion:
    operator: str
    source_text: str
    source_type: str
    postgres_native_type: str
    calcite_type: str
    replacement_type: str
    evidence_path: str


_NODE_ID = re.compile(r"^(\d+):(\d+)-(\d+):(\d+)$")

_SUPPORTED_IMPLICIT_CAST_PAIRS = {
    ("NULL", "DECIMAL"),
    ("NULL", "VARCHAR"),
    ("VARCHAR", "INTEGER"),
}

_POSTGRES_SUM_RESULTS = {
    "SMALLINT": "BIGINT",
    "INTEGER": "BIGINT",
    "BIGINT": "NUMERIC",
    "DECIMAL": "NUMERIC",
    "NUMERIC": "NUMERIC",
    "REAL": "REAL",
    "DOUBLE": "DOUBLE",
}
_POSTGRES_AVERAGING_RESULTS = {
    "SMALLINT": "NUMERIC",
    "INTEGER": "NUMERIC",
    "BIGINT": "NUMERIC",
    "DECIMAL": "NUMERIC",
    "NUMERIC": "NUMERIC",
    "REAL": "DOUBLE",
    "DOUBLE": "DOUBLE",
}
_POSTGRES_AGGREGATE_RESULTS: dict[str, dict[str, str]] = {
    "SUM": _POSTGRES_SUM_RESULTS,
    **{
        operator: _POSTGRES_AVERAGING_RESULTS
        for operator in ("AVG", "STDDEV_POP", "STDDEV_SAMP", "VAR_POP", "VAR_SAMP")
    },
}


def materialize_calcite_coercions(
    *,
    repository_root: Path,
    authority_root: Path,
    benchmark_id: str,
    case_id: str,
    source_metadata: dict[str, Any],
    schema_sql: str,
    side: str,
    sql: str,
) -> tuple[str, dict[str, Any] | None]:
    """Insert exact explicit casts proven by one generated Calcite IR side."""

    if benchmark_id != "verieql-calcite":
        return sql, None
    if side not in {"before", "after"}:
        raise CalciteCoercionError(f"invalid Calcite query side: {side}")

    case_root = authority_root / benchmark_id / case_id
    metadata_path = case_root / "metadata.json"
    ir_path = case_root / f"{side}.calcite-ir.json"
    if not metadata_path.is_file() or not ir_path.is_file():
        raise CalciteCoercionError(
            f"{benchmark_id}/{case_id} is missing generated Calcite authority; "
            "run scripts/export-benchmark-ir first"
        )

    metadata = _read_object(metadata_path)
    _validate_metadata(
        metadata,
        benchmark_id,
        case_id,
        source_metadata,
        schema_sql,
    )
    ir = _read_object(ir_path)
    queries = ir.get("queries")
    if (
        not isinstance(queries, list)
        or len(queries) != 1
        or not isinstance(queries[0], dict)
    ):
        raise CalciteCoercionError(f"{ir_path} must contain exactly one Calcite query")
    query = queries[0]
    submitted_sql = query.get("sql")
    if not isinstance(submitted_sql, str) or _program_text(
        submitted_sql
    ) != _program_text(sql):
        raise CalciteCoercionError(
            f"{ir_path} does not describe the current {benchmark_id}/{case_id} {side} SQL"
        )
    relation = query.get("rel")
    if not isinstance(relation, dict):
        raise CalciteCoercionError(f"{ir_path} has no relational Calcite root")

    display_path = _display_path(ir_path, repository_root)
    rewrites = _collect_rewrites(sql, relation, display_path)
    if not rewrites:
        return sql, None
    materialized = _apply_rewrites(sql, rewrites)
    return materialized, {
        "authority": "exact-generated-calcite-ir",
        "authorityPath": display_path,
        "authoritySha256": _sha256(ir_path.read_bytes()),
        "sourceSha256": _sha256(sql.encode()),
        "materializedSha256": _sha256(materialized.encode()),
        "rewriteCount": len(rewrites),
        "rewrites": [rewrite.as_report() for rewrite in rewrites],
        "semanticNote": (
            "Each explicit CAST is bound to an exact Calcite source node. "
            "Rex casts restore validator coercions absent in PostgreSQL; "
            "aggregate result casts restore Calcite's attested observable output type."
        ),
    }


def _collect_rewrites(
    sql: str,
    relation: dict[str, Any],
    display_path: str,
) -> list[CoercionRewrite]:
    candidates: list[CoercionRewrite] = []
    for path, node in _walk(relation):
        candidates.extend(_implicit_rex_cast(sql, node, path, display_path))
        if node.get("type") == "LogicalAggregate":
            candidates.extend(
                _aggregate_result_casts(
                    sql,
                    relation,
                    node,
                    path,
                    display_path,
                )
            )

    by_span: dict[tuple[int, int], CoercionRewrite] = {}
    for rewrite in candidates:
        key = (rewrite.start, rewrite.end)
        previous = by_span.get(key)
        if previous is None:
            by_span[key] = rewrite
        elif previous.replacement != rewrite.replacement:
            raise CalciteCoercionError(
                f"conflicting Calcite coercions at {rewrite.node_id}: "
                f"{previous.replacement!r} versus {rewrite.replacement!r}"
            )

    rewrites = sorted(by_span.values(), key=lambda item: (item.start, item.end))
    for left, right in zip(rewrites, rewrites[1:]):
        if right.start < left.end:
            raise CalciteCoercionError(
                f"overlapping Calcite coercions at {left.node_id} and {right.node_id}"
            )
    return rewrites


def _implicit_rex_cast(
    sql: str,
    node: dict[str, Any],
    path: str,
    display_path: str,
) -> list[CoercionRewrite]:
    if node.get("kind") != "CAST" or node.get("sourceKind") == "CAST":
        return []
    operands = node.get("operands")
    if (
        not isinstance(operands, list)
        or len(operands) != 1
        or not isinstance(operands[0], dict)
    ):
        raise CalciteCoercionError(
            f"{display_path} {path} has a malformed implicit Calcite CAST"
        )
    source_type = _type_name(operands[0].get("type"))
    target_type = _type_name(node.get("type"))
    if source_type == target_type:
        if _value_type_modifiers(operands[0]) == _value_type_modifiers(node):
            return []
        raise CalciteCoercionError(
            f"{display_path} {path} contains an unsupported same-base typmod coercion "
            f"for {target_type}"
        )
    if (source_type, target_type) not in _SUPPORTED_IMPLICIT_CAST_PAIRS:
        raise CalciteCoercionError(
            f"{display_path} {path} contains an unsupported implicit Calcite coercion "
            f"from {source_type} to {target_type}"
        )
    cast_type = _postgres_type(node)
    return [
        _rewrite(
            sql=sql,
            node=node,
            replacement_type=cast_type,
            kind="calcite-implicit-rex-cast",
            source_type=source_type,
            postgres_native_type=None,
            calcite_type=target_type,
            ir_path=path,
            display_path=display_path,
        )
    ]


def _aggregate_result_casts(
    sql: str,
    relation: dict[str, Any],
    aggregate: dict[str, Any],
    path: str,
    display_path: str,
) -> list[CoercionRewrite]:
    inputs = aggregate.get("inputs")
    calls = aggregate.get("aggCallDetails")
    if not isinstance(inputs, list) or not inputs or not isinstance(inputs[0], dict):
        return []
    if not isinstance(calls, list):
        return []
    input_types = inputs[0].get("rowType")
    if not isinstance(input_types, list):
        return []

    coercions = []
    for index, call in enumerate(calls):
        if not isinstance(call, dict):
            continue
        arguments = call.get("argList")
        if not isinstance(arguments, list) or len(arguments) != 1:
            continue
        argument = arguments[0]
        if (
            not isinstance(argument, int)
            or argument < 0
            or argument >= len(input_types)
        ):
            continue
        input_field = input_types[argument]
        if not isinstance(input_field, dict):
            continue
        operator = _type_name(call.get("kind") or call.get("function"))
        source_type = _type_name(input_field.get("type"))
        calcite_type = _type_name(call.get("type"))
        postgres_native_type = _POSTGRES_AGGREGATE_RESULTS.get(operator, {}).get(
            source_type
        )
        if postgres_native_type is None or _same_sql_type_family(
            postgres_native_type, calcite_type
        ):
            continue
        if call.get("sourceKind") != "OTHER_FUNCTION":
            raise CalciteCoercionError(
                f"{display_path} {path}/aggCallDetails/{index} lacks an exact source aggregate"
            )
        source_operator = str(call.get("sourceOperator") or "").upper()
        if source_operator != operator:
            raise CalciteCoercionError(
                f"{display_path} {path}/aggCallDetails/{index} source operator drift"
            )
        source_text = call.get("sourceText")
        if not isinstance(source_text, str) or not source_text:
            raise CalciteCoercionError(
                f"{display_path} {path}/aggCallDetails/{index} has no source text"
            )
        coercions.append(
            AggregateResultCoercion(
                operator=operator,
                source_text=source_text,
                source_type=source_type,
                postgres_native_type=postgres_native_type,
                calcite_type=calcite_type,
                replacement_type=_postgres_type(call),
                evidence_path=f"{path}/aggCallDetails/{index}",
            )
        )

    rewrites = []
    for coercion in coercions:
        matched = False
        for occurrence_path, occurrence in _walk(relation):
            if not _is_aggregate_source_occurrence(occurrence, coercion):
                continue
            matched = True
            rewrites.append(
                _rewrite(
                    sql=sql,
                    node=occurrence,
                    replacement_type=coercion.replacement_type,
                    kind="calcite-aggregate-result-cast",
                    source_type=coercion.source_type,
                    postgres_native_type=coercion.postgres_native_type,
                    calcite_type=coercion.calcite_type,
                    ir_path=(
                        f"{occurrence_path} " f"(evidence: {coercion.evidence_path})"
                    ),
                    display_path=display_path,
                )
            )
        if not matched:
            raise CalciteCoercionError(
                f"{display_path} {coercion.evidence_path} has no source occurrence"
            )
    return rewrites


def _is_aggregate_source_occurrence(
    node: dict[str, Any], coercion: AggregateResultCoercion
) -> bool:
    return (
        node.get("sourceKind") == "OTHER_FUNCTION"
        and str(node.get("sourceOperator") or "").upper() == coercion.operator
        and node.get("sourceText") == coercion.source_text
        and _type_name(node.get("type")) == coercion.calcite_type
    )


def _rewrite(
    *,
    sql: str,
    node: dict[str, Any],
    replacement_type: str,
    kind: str,
    source_type: str,
    postgres_native_type: str | None,
    calcite_type: str,
    ir_path: str,
    display_path: str,
) -> CoercionRewrite:
    node_id = node.get("sourceNodeId")
    source_text = node.get("sourceText")
    if (
        not isinstance(node_id, str)
        or not isinstance(source_text, str)
        or not source_text
    ):
        raise CalciteCoercionError(
            f"{display_path} {ir_path} has no exact source identity"
        )
    start, end = _source_span(sql, node_id)
    if sql[start:end] != source_text:
        raise CalciteCoercionError(
            f"{display_path} {ir_path} source span {node_id} no longer matches {source_text!r}"
        )
    return CoercionRewrite(
        start=start,
        end=end,
        node_id=node_id,
        source_text=source_text,
        replacement=f"CAST({source_text} AS {replacement_type})",
        kind=kind,
        source_type=source_type,
        postgres_native_type=postgres_native_type,
        calcite_type=calcite_type,
        ir_path=ir_path,
    )


def _postgres_type(node: dict[str, Any]) -> str:
    type_name = _type_name(node.get("type"))
    precision = node.get("precision")
    scale = node.get("scale")
    if type_name in {"SMALLINT", "INTEGER", "BIGINT", "BOOLEAN", "DATE"}:
        return type_name
    if type_name in {"DECIMAL", "NUMERIC"}:
        if (
            isinstance(precision, int)
            and precision > 0
            and isinstance(scale, int)
            and 0 <= scale <= precision
        ):
            return f"NUMERIC({precision}, {scale})"
        return "NUMERIC"
    if type_name in {"CHAR", "VARCHAR"}:
        if isinstance(precision, int) and precision > 0:
            return f"{type_name}({precision})"
        return type_name
    if type_name == "REAL":
        return "REAL"
    if type_name == "DOUBLE":
        return "DOUBLE PRECISION"
    if type_name in {"TIME", "TIMESTAMP"}:
        if isinstance(precision, int) and 0 <= precision <= 6:
            return f"{type_name}({precision})"
        return type_name
    raise CalciteCoercionError(f"unsupported Calcite coercion target type: {type_name}")


def _source_span(sql: str, node_id: str) -> tuple[int, int]:
    match = _NODE_ID.fullmatch(node_id)
    if match is None:
        raise CalciteCoercionError(f"invalid Calcite source node ID: {node_id}")
    start_line, start_column, end_line, end_column = map(int, match.groups())
    if min(start_line, start_column, end_line, end_column) < 1:
        raise CalciteCoercionError(f"invalid Calcite source node ID: {node_id}")
    lines = sql.splitlines(keepends=True)
    if start_line > len(lines) or end_line > len(lines):
        raise CalciteCoercionError(f"Calcite source node ID escapes SQL: {node_id}")

    def offset(line: int, column: int) -> int:
        body = lines[line - 1]
        content_length = len(body.rstrip("\r\n"))
        if column - 1 > content_length:
            raise CalciteCoercionError(f"Calcite source column escapes SQL: {node_id}")
        return sum(len(item) for item in lines[: line - 1]) + column - 1

    start = offset(start_line, start_column)
    end = offset(end_line, end_column) + 1
    if start >= end or end > len(sql):
        raise CalciteCoercionError(f"invalid Calcite source span: {node_id}")
    return start, end


def _apply_rewrites(sql: str, rewrites: list[CoercionRewrite]) -> str:
    result = sql
    for rewrite in reversed(rewrites):
        result = result[: rewrite.start] + rewrite.replacement + result[rewrite.end :]
    return result


def _walk(value: Any, path: str = "$") -> Iterator[tuple[str, dict[str, Any]]]:
    if isinstance(value, dict):
        yield path, value
        for key, child in value.items():
            yield from _walk(child, f"{path}/{key}")
    elif isinstance(value, list):
        for index, child in enumerate(value):
            yield from _walk(child, f"{path}/{index}")


def _validate_metadata(
    metadata: dict[str, Any],
    benchmark_id: str,
    case_id: str,
    source_metadata: dict[str, Any],
    schema_sql: str,
) -> None:
    if (
        metadata.get("sourceBenchmark") != benchmark_id
        or metadata.get("sourceCase") != case_id
    ):
        raise CalciteCoercionError(
            f"generated Calcite metadata does not identify {benchmark_id}/{case_id}"
        )
    if metadata.get("source") != source_metadata:
        raise CalciteCoercionError(
            f"generated Calcite metadata source does not match {benchmark_id}/{case_id}"
        )
    schema_sha256 = _sha256(schema_sql.encode())
    if metadata.get("sourceSchemaSha256") != schema_sha256:
        raise CalciteCoercionError(
            f"generated Calcite metadata schema does not match {benchmark_id}/{case_id}"
        )


def _read_object(path: Path) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        raise CalciteCoercionError(f"cannot read {path}: {exc}") from exc
    if not isinstance(value, dict):
        raise CalciteCoercionError(f"{path} must contain a JSON object")
    return value


def _program_text(sql: str) -> str:
    text = sql.strip(" \t\r\n\f")
    if text.endswith(";"):
        text = text[:-1].rstrip(" \t\r\n\f")
    return text


def _type_name(value: Any) -> str:
    if not isinstance(value, str) or not value:
        raise CalciteCoercionError(f"invalid Calcite type name: {value!r}")
    return value.upper()


def _same_sql_type_family(left: str, right: str) -> bool:
    def canonical(type_name: str) -> str:
        return "NUMERIC" if type_name in {"DECIMAL", "NUMERIC"} else type_name

    return canonical(left) == canonical(right)


def _value_type_modifiers(node: dict[str, Any]) -> tuple[Any, ...]:
    """Return value-relevant Calcite type metadata, excluding nullability."""

    precision = node.get("precision")
    if precision == -1:
        precision = None
    scale = node.get("scale")
    if scale == -(2**31):
        scale = None
    return (
        precision,
        scale,
        node.get("charset"),
        node.get("typeCollation"),
    )


def _display_path(path: Path, root: Path) -> str:
    try:
        return str(path.resolve().relative_to(root.resolve()))
    except ValueError:
        return str(path.resolve())


def _sha256(content: bytes) -> str:
    return hashlib.sha256(content).hexdigest()
