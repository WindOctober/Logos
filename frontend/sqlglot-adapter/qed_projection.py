#!/usr/bin/env python3
"""Compute a fail-closed base-column dependency closure for QED DDL fallback.

The script performs SQLGlot qualification/star expansion and projection
pushdown, but returns rewritten SQL only with a separate structural
attestation.  The QED materializer may use exact star expansion, or a narrower
rewrite that removed only dead direct-column outputs from derived SELECTs.
"""

import argparse
import hashlib
import json
import re
from pathlib import Path

import sqlglot
from sqlglot import exp
from sqlglot.optimizer.annotate_types import annotate_types
from sqlglot.optimizer.pushdown_projections import pushdown_projections
from sqlglot.optimizer.qualify import qualify

from qed_star_provenance import (
    expand_top_level_unqualified_star,
    validate_calcite_rel_direct_provenance,
    validate_qed_json_direct_provenance,
)


def sha256_text(value: str) -> str:
    return hashlib.sha256(value.encode()).hexdigest()


def _relation_aliases(expression: exp.Expression) -> set[str]:
    aliases: set[str] = set()
    for relation in expression.find_all(exp.Table, exp.Subquery):
        alias = relation.alias_or_name
        if alias:
            aliases.add(alias.casefold())
    return aliases


def _reject_schema_sensitive_row_shapes(expression: exp.Expression) -> None:
    """Reject shapes for which column projection can silently change SQL meaning.

    SQLGlot deliberately leaves NATURAL JOIN implicit, so removing a common base
    column would also remove a join key.  Its qualification of JOIN USING may
    additionally replace a qualified relation star's column with the coalesced
    USING output, which is not PostgreSQL's ``relation.*`` meaning.  A whole-row
    reference such as [SELECT t] likewise denotes every field of [t] even though
    it is represented as one unqualified [Column].  None of these constructs can
    use a column-dependency report.
    """

    if any(
        str(join.args.get("method") or "").upper() == "NATURAL"
        for join in expression.find_all(exp.Join)
    ):
        raise ValueError("NATURAL JOIN is not safe for QED schema projection")
    if any(join.args.get("using") for join in expression.find_all(exp.Join)):
        raise ValueError("JOIN USING is not safe for QED schema projection")

    aliases = _relation_aliases(expression)
    whole_rows = sorted(
        {
            column.name
            for column in expression.find_all(exp.Column)
            if not column.table and column.name.casefold() in aliases
        },
        key=str.casefold,
    )
    if whole_rows:
        raise ValueError(
            "whole-row relation reference is not safe for QED schema projection: "
            + ", ".join(whole_rows)
        )


def _direct_column_selection(selection: exp.Expression) -> exp.Column | None:
    value = selection.this if isinstance(selection, exp.Alias) else selection
    if isinstance(value, exp.Column) and not isinstance(value.this, exp.Star):
        return value
    return None


def _select_has_relational_star(select: exp.Select) -> bool:
    return any(
        isinstance(selection, exp.Star)
        or (
            isinstance(selection, exp.Column)
            and isinstance(selection.this, exp.Star)
        )
        for selection in select.expressions
    )


def _has_relational_star(expression: exp.Expression) -> bool:
    """Whether a SELECT list contains a row-expanding star (not COUNT(*))."""

    return any(
        _select_has_relational_star(select)
        for select in expression.find_all(exp.Select)
    )


def _star_select_shapes(expression: exp.Expression) -> list[dict]:
    """Record relation shapes whose source-order star expansion must be trusted."""

    cte_names = {
        cte.alias_or_name.casefold()
        for cte in expression.find_all(exp.CTE)
        if cte.alias_or_name
    }

    def relation_kind(relation: object) -> str:
        if isinstance(relation, exp.Subquery):
            return "derived"
        if isinstance(relation, exp.Table):
            return "cte" if relation.name.casefold() in cte_names else "base"
        return type(relation).__name__.casefold()

    shapes = []
    for select in expression.find_all(exp.Select):
        if not _select_has_relational_star(select):
            continue
        from_clause = select.args.get("from_")
        left = from_clause.this if isinstance(from_clause, exp.From) else None
        joins = select.args.get("joins") or []
        shapes.append(
            {
                "fromRelationKind": relation_kind(left),
                "joinRelationKinds": [
                    relation_kind(join.this)
                    for join in joins
                    if isinstance(join, exp.Join)
                ],
            }
        )
    return shapes


def _canonicalize_base_identifiers(
    expression: exp.Expression,
    schema: dict[str, dict[str, str]],
) -> None:
    """Restore schema spelling after PostgreSQL's case-folding qualification."""

    source_names = {name.casefold(): name for name in schema}
    aliases: dict[str, str] = {}
    for table in expression.find_all(exp.Table):
        source_name = source_names.get(table.name.casefold())
        if source_name is None:
            continue
        alias = table.alias_or_name
        folded_alias = alias.casefold()
        previous = aliases.get(folded_alias)
        if previous is not None and previous != source_name:
            raise ValueError(f"base alias {alias!r} resolves to multiple source tables")
        aliases[folded_alias] = source_name
        table.set("this", exp.to_identifier(source_name, quoted=True))

    for column in expression.find_all(exp.Column):
        source_name = aliases.get(column.table.casefold())
        if source_name is None:
            continue
        canonical = {
            name.casefold(): name for name in schema[source_name]
        }.get(column.name.casefold())
        if canonical is None:
            raise ValueError(
                f"qualified source column {source_name}.{column.name} is absent from schema"
            )
        column.set("this", exp.to_identifier(canonical, quoted=True))


def _attest_dead_direct_column_projection(
    original: object,
    projected: object,
    *,
    path: tuple[str | int, ...] = (),
) -> list[dict]:
    """Attest that projection pushdown only removed error-free direct columns.

    This is intentionally much narrower than accepting SQLGlot's optimized SQL
    wholesale.  Every non-selection AST field must be structurally identical;
    a nested SELECT list may only lose an ordered subsequence of [Column] items.
    Calls, casts, arithmetic, subqueries, and top-level outputs are immutable.
    """

    if isinstance(original, exp.Expression):
        if not isinstance(projected, original.__class__):
            raise ValueError(f"projection rewrite changed AST node at {path}")
        removed: list[dict] = []
        original_args = original.args
        projected_args = projected.args
        if set(original_args) != set(projected_args):
            raise ValueError(f"projection rewrite changed AST fields at {path}")
        for key in original_args:
            before = original_args[key]
            after = projected_args[key]
            if isinstance(original, exp.Select) and key == "expressions":
                if not isinstance(before, list) or not isinstance(after, list):
                    raise ValueError(f"projection rewrite malformed SELECT list at {path}")
                if before != after and not isinstance(original.parent, exp.Subquery):
                    raise ValueError(
                        "projection rewrite changed a non-derived query output list"
                    )
                after_index = 0
                for before_index, selection in enumerate(before):
                    if after_index < len(after) and selection == after[after_index]:
                        removed.extend(
                            _attest_dead_direct_column_projection(
                                selection,
                                after[after_index],
                                path=path + (key, before_index),
                            )
                        )
                        after_index += 1
                        continue
                    column = _direct_column_selection(selection)
                    if column is None:
                        raise ValueError(
                            "projection rewrite tried to remove a non-column expression "
                            f"at {path + (key, before_index)}"
                        )
                    if any(
                        original.args.get(field) is not None
                        for field in ("distinct", "group", "having", "qualify")
                    ):
                        raise ValueError(
                            "projection rewrite tried to shorten a DISTINCT/grouped SELECT"
                        )
                    removed.append(
                        {
                            "path": list(path + (key, before_index)),
                            "column": column.name,
                            "table": column.table or None,
                            "selectionSql": selection.sql(dialect="postgres"),
                        }
                    )
                if after_index != len(after):
                    raise ValueError("projection rewrite added or reordered SELECT outputs")
                continue
            removed.extend(
                _attest_dead_direct_column_projection(
                    before,
                    after,
                    path=path + (key,),
                )
            )
        return removed

    if isinstance(original, list):
        if not isinstance(projected, list) or len(original) != len(projected):
            raise ValueError(f"projection rewrite changed AST list at {path}")
        removed: list[dict] = []
        for index, (before, after) in enumerate(zip(original, projected)):
            removed.extend(
                _attest_dead_direct_column_projection(
                    before,
                    after,
                    path=path + (index,),
                )
            )
        return removed

    if original != projected:
        raise ValueError(f"projection rewrite changed scalar AST data at {path}")
    return []


def analyze_query(sql: str, schema: dict[str, dict[str, str]]) -> dict:
    expression = sqlglot.parse_one(sql, read="postgres")
    source_had_star = _has_relational_star(expression)
    source_star_select_shapes = _star_select_shapes(expression)
    _reject_schema_sensitive_row_shapes(expression)
    qualified = qualify(
        expression,
        dialect="postgres",
        schema=schema,
        expand_alias_refs=True,
        expand_stars=True,
        infer_schema=False,
        isolate_tables=False,
        qualify_columns=True,
        allow_partial_qualification=False,
        validate_qualify_columns=True,
        quote_identifiers=True,
        identify=True,
        sql=sql,
    )
    _canonicalize_base_identifiers(qualified, schema)
    _reject_schema_sensitive_row_shapes(qualified)
    projected = pushdown_projections(
        qualified.copy(),
        schema=schema,
        remove_unused_selections=True,
        dialect="postgres",
    )
    removed_direct_columns = _attest_dead_direct_column_projection(
        qualified, projected
    )

    source_names = {name.casefold(): name for name in schema}
    base_aliases: dict[str, str] = {}
    referenced_tables: set[str] = set()
    for table in projected.find_all(exp.Table):
        source_name = source_names.get(table.name.casefold())
        if source_name is None:
            continue
        alias = table.alias_or_name
        folded_alias = alias.casefold()
        previous = base_aliases.get(folded_alias)
        if previous is not None and previous != source_name:
            raise ValueError(f"base alias {alias!r} resolves to multiple source tables")
        base_aliases[folded_alias] = source_name
        referenced_tables.add(source_name)

    dependencies = {name: set() for name in referenced_tables}
    unresolved: list[str] = []
    for column in projected.find_all(exp.Column):
        if isinstance(column.this, exp.Star):
            # Qualification is required to expand every relational wildcard.
            unresolved.append(column.sql(dialect="postgres"))
            continue
        source_name = base_aliases.get(column.table.casefold())
        if source_name is None:
            # A CTE/derived-table reference is expected here; its own base
            # dependencies are visited separately in the same optimized AST.
            continue
        canonical_columns = {
            name.casefold(): name for name in schema[source_name]
        }
        canonical = canonical_columns.get(column.name.casefold())
        if canonical is None:
            raise ValueError(
                f"qualified source column {source_name}.{column.name} is absent from schema"
            )
        dependencies[source_name].add(canonical)

    for select in projected.find_all(exp.Select):
        for selection in select.expressions:
            if isinstance(selection, exp.Star) or (
                isinstance(selection, exp.Column) and isinstance(selection.this, exp.Star)
            ):
                unresolved.append(selection.sql(dialect="postgres"))
    if unresolved:
        raise ValueError(f"unexpanded relational wildcard(s): {sorted(set(unresolved))}")

    outputs = list(projected.named_selects)
    if not outputs:
        raise ValueError("query has no statically known top-level output columns")
    star_expanded_sql = qualified.sql(dialect="postgres")
    optimized_sql = projected.sql(dialect="postgres")
    return {
        "inputSha256": sha256_text(sql),
        "starExpandedSha256": sha256_text(star_expanded_sql),
        "starExpandedSql": star_expanded_sql,
        "optimizedSha256": sha256_text(optimized_sql),
        "optimizedSql": optimized_sql,
        "projectionRewrite": {
            "status": "verified-dead-direct-column-projection",
            "removedSelections": removed_direct_columns,
            "dangerousExpressionsRemoved": False,
            "topLevelOutputPreserved": True,
        },
        "outputArity": len(outputs),
        "sourceHadStar": source_had_star,
        "starSelectShapes": source_star_select_shapes,
        "joinShapes": [
            {
                "side": str(join.args.get("side") or "").upper(),
                "kind": str(join.args.get("kind") or "").upper(),
                "method": str(join.args.get("method") or "").upper(),
            }
            for join in expression.find_all(exp.Join)
        ],
        "outputNames": outputs,
        "referencedTables": sorted(referenced_tables, key=str.casefold),
        "baseColumns": {
            table: sorted(columns, key=str.casefold)
            for table, columns in sorted(dependencies.items(), key=lambda item: item[0].casefold())
        },
    }


def analyze_base_use_query(
    sql: str,
    schema: dict[str, dict[str, str]],
) -> dict:
    """Compute exact syntactic base-column use without rewriting the query.

    This is deliberately more conservative than projection pushdown.  It is
    used only to remove source-schema columns that the original AST never
    observes before applying the opaque VARCHAR bridge.  In particular, a
    grouped derived SELECT is left byte-for-byte intact.
    """

    expression = sqlglot.parse_one(sql, read="postgres")
    _reject_schema_sensitive_row_shapes(expression)
    if _has_relational_star(expression):
        raise ValueError(
            "base-use closure does not admit a relational source star"
        )
    source_names = {name.casefold(): name for name in schema}
    cte_names = {
        cte.alias_or_name.casefold()
        for cte in expression.find_all(exp.CTE)
        if cte.alias_or_name
    }
    if cte_names & set(source_names):
        raise ValueError(
            "base-use closure rejects a CTE that shadows a source table"
        )
    qualified = qualify(
        expression,
        dialect="postgres",
        schema=schema,
        expand_alias_refs=True,
        expand_stars=False,
        infer_schema=False,
        isolate_tables=False,
        qualify_columns=True,
        allow_partial_qualification=False,
        validate_qualify_columns=True,
        quote_identifiers=True,
        identify=True,
        sql=sql,
    )
    _canonicalize_base_identifiers(qualified, schema)
    _reject_schema_sensitive_row_shapes(qualified)

    base_aliases: dict[str, str] = {}
    referenced_tables: set[str] = set()
    for table in qualified.find_all(exp.Table):
        source_name = source_names.get(table.name.casefold())
        if source_name is None:
            continue
        alias = table.alias_or_name
        folded_alias = alias.casefold()
        previous = base_aliases.get(folded_alias)
        if previous is not None and previous != source_name:
            raise ValueError(
                f"base alias {alias!r} resolves to multiple source tables"
            )
        base_aliases[folded_alias] = source_name
        referenced_tables.add(source_name)

    derived_aliases = {
        subquery.alias_or_name.casefold()
        for subquery in qualified.find_all(exp.Subquery)
        if subquery.alias_or_name
    }
    if derived_aliases & set(base_aliases):
        raise ValueError(
            "base-use closure rejects base/derived alias shadowing"
        )

    dependencies = {name: set() for name in referenced_tables}
    for column in qualified.find_all(exp.Column):
        if isinstance(column.this, exp.Star):
            raise ValueError("base-use closure left an unresolved relational star")
        source_name = base_aliases.get(column.table.casefold())
        if source_name is None:
            # Derived-table columns are definitions over base columns visited
            # elsewhere in the same qualified AST.
            continue
        canonical_columns = {
            name.casefold(): name for name in schema[source_name]
        }
        canonical = canonical_columns.get(column.name.casefold())
        if canonical is None:
            raise ValueError(
                f"qualified source column {source_name}.{column.name} is absent"
            )
        dependencies[source_name].add(canonical)

    outputs = list(qualified.named_selects)
    if not outputs:
        raise ValueError("base-use query has no statically known outputs")
    return {
        "inputSha256": sha256_text(sql),
        "queryBytesPreserved": True,
        "outputArity": len(outputs),
        "referencedTables": sorted(referenced_tables, key=str.casefold),
        "baseColumns": {
            table: sorted(columns, key=str.casefold)
            for table, columns in sorted(
                dependencies.items(), key=lambda item: item[0].casefold()
            )
        },
    }


def _is_string_type(value: object) -> bool:
    rendered = str(value).upper()
    return rendered.startswith("VARCHAR")


def _expression_paths(expression: exp.Expression) -> dict[int, list[str | int]]:
    paths: dict[int, list[str | int]] = {}

    def visit(value: object, path: list[str | int]) -> None:
        if isinstance(value, exp.Expression):
            paths[id(value)] = path
            for key, child in value.args.items():
                visit(child, path + [key])
        elif isinstance(value, list):
            for index, child in enumerate(value):
                visit(child, path + [index])

    visit(expression, [])
    return paths


def _atomic_string_operand(expression: exp.Expression) -> bool:
    return (
        isinstance(expression, exp.Column) and _is_string_type(expression.type)
    ) or (isinstance(expression, exp.Literal) and expression.is_string)


def _nested_stars_are_direct_base_pass_through(
    expression: exp.Expression,
    schema: dict[str, dict[str, str]],
) -> bool:
    """Admit unobserved nested stars only over one declared base relation."""

    found = False
    source_tables = {name.casefold(): columns for name, columns in schema.items()}
    for select in expression.find_all(exp.Select):
        if not _select_has_relational_star(select):
            continue
        if select is expression:
            continue
        found = True
        if (
            not isinstance(select.parent, exp.Subquery)
            or len(select.expressions) != 1
            or not isinstance(select.expressions[0], exp.Star)
            or any(
                value is not None
                for value in select.expressions[0].args.values()
            )
            or not isinstance(select.args.get("from_"), exp.From)
            or not isinstance(select.args["from_"].this, exp.Table)
            or select.args.get("joins")
            or any(
                select.args.get(field) is not None
                for field in (
                    "distinct",
                    "group",
                    "having",
                    "qualify",
                    "windows",
                    "order",
                    "limit",
                    "offset",
                    "with_",
                )
            )
        ):
            return False
        table = select.args["from_"].this
        table_alias = table.args.get("alias")
        derived_alias = select.parent.args.get("alias")
        if (
            isinstance(table_alias, exp.TableAlias)
            and table_alias.args.get("columns")
        ) or (
            isinstance(derived_alias, exp.TableAlias)
            and derived_alias.args.get("columns")
        ):
            return False
        columns = source_tables.get(table.name.casefold())
        if columns is None or len({name.casefold() for name in columns}) != len(columns):
            return False
    return found


def _attest_opaque_string_query(
    sql: str,
    schema: dict[str, dict[str, str]],
) -> tuple[exp.Expression, dict]:
    """Close string uses over equality plus the attested plain-LIKE bridge."""

    expression = sqlglot.parse_one(sql, read="postgres")
    source_had_star = _has_relational_star(expression)
    source_had_top_level_star = (
        isinstance(expression, exp.Select)
        and _select_has_relational_star(expression)
    )
    nested_stars_direct_base = _nested_stars_are_direct_base_pass_through(
        expression,
        schema,
    )
    _reject_schema_sensitive_row_shapes(expression)
    qualified = qualify(
        expression,
        dialect="postgres",
        schema=schema,
        expand_alias_refs=True,
        expand_stars=True,
        infer_schema=False,
        isolate_tables=False,
        qualify_columns=True,
        allow_partial_qualification=False,
        validate_qualify_columns=True,
        quote_identifiers=True,
        identify=True,
        sql=sql,
    )
    annotate_types(qualified, schema=schema, dialect="postgres")
    _reject_schema_sensitive_row_shapes(qualified)
    if any(qualified.find_all(exp.Collate)):
        raise ValueError("explicit COLLATE is outside opaque-string abstraction")
    paths = _expression_paths(qualified)
    allowed_uses: list[dict] = []
    literals: list[str] = []
    equality_literals: list[str] = []
    like_rewrites: list[dict] = []
    like_columns: set[int] = set()
    like_literals: set[int] = set()

    # Bridge only plain LIKE/NOT LIKE with two direct VARCHAR operands. QED's
    # prover treats a declared unknown scalar operator as an uninterpreted
    # nullable function. The concrete LIKE relation is one interpretation of
    # that function on the injective encoding image, so only EQ may transfer.
    for like in qualified.find_all(exp.Like):
        if isinstance(like.parent, exp.Escape):
            raise ValueError("LIKE ESCAPE is outside opaque-string abstraction")
        if set(like.args) - {"this", "expression", "negate"}:
            raise ValueError("non-canonical LIKE is outside opaque-string abstraction")
        column = like.this
        literal = like.expression
        if not (
            isinstance(column, exp.Column)
            and _is_string_type(column.type)
            and isinstance(literal, exp.Literal)
            and literal.is_string
        ):
            raise ValueError("LIKE operands are outside the direct VARCHAR fragment")

        identifiers = [column.this]
        table_identifier = column.args.get("table")
        if isinstance(table_identifier, exp.Identifier):
            identifiers.append(table_identifier)
        identifier_spans = [
            (identifier.meta.get("start"), identifier.meta.get("end"))
            for identifier in identifiers
            if isinstance(identifier.meta.get("start"), int)
            and isinstance(identifier.meta.get("end"), int)
        ]
        literal_start = literal.meta.get("start")
        literal_end = literal.meta.get("end")
        if (
            not identifier_spans
            or not isinstance(literal_start, int)
            or not isinstance(literal_end, int)
        ):
            raise ValueError("LIKE lacks exact source operand spans")
        column_start = min(start for start, _ in identifier_spans)
        column_end = max(end for _, end in identifier_spans)
        if not (0 <= column_start <= column_end < literal_start <= literal_end < len(sql)):
            raise ValueError("LIKE source operand spans are malformed")
        operator_text = sql[column_end + 1 : literal_start]
        operator_match = re.fullmatch(
            r"\s+(?:(NOT)\s+)?LIKE\s+",
            operator_text,
            flags=re.IGNORECASE | re.ASCII,
        )
        if operator_match is None or bool(operator_match.group(1)) != bool(
            like.args.get("negate")
        ):
            raise ValueError("LIKE source bytes do not match the qualified AST")
        literal_source = sql[literal_start : literal_end + 1]
        if not (literal_source.startswith("'") and literal_source.endswith("'")):
            raise ValueError("LIKE pattern is not a plain quoted literal")
        # PostgreSQL gives backslash special meaning in LIKE patterns even
        # without an explicit ESCAPE clause, and a terminal escape can raise
        # an execution error.  The uninterpreted-function bridge does not
        # model that error path, so admit only the ordinary, backslash-free
        # literal fragment.
        if "\\" in literal_source:
            raise ValueError("LIKE pattern escapes are outside opaque-string abstraction")

        like_columns.add(id(column))
        like_literals.add(id(literal))
        like_rewrites.append(
            {
                "path": paths[id(like)],
                "sourceStart": column_start,
                "sourceEnd": literal_end,
                "sourceOperand": sql[column_start : column_end + 1],
                "negated": bool(like.args.get("negate")),
                "literalValue": literal.this,
                "valueSha256": sha256_text(literal.this),
            }
        )

    for node in qualified.walk(bfs=False):
        if isinstance(node, exp.Literal) and node.is_string:
            if id(node) in like_literals:
                literals.append(node.this)
                allowed_uses.append(
                    {
                        "kind": "literal",
                        "path": paths[id(node)],
                        "operator": "LIKE-UDF",
                        "valueSha256": sha256_text(node.this),
                        "sourceStart": node.meta["start"],
                        "sourceEnd": node.meta["end"],
                    }
                )
                continue
            parent = node.parent
            if not isinstance(parent, exp.EQ):
                raise ValueError(
                    "string literal is not consumed by direct equality: "
                    + node.sql(dialect="postgres")
                )
            other = parent.expression if parent.this is node else parent.this
            if not isinstance(other, exp.Expression) or not _atomic_string_operand(other):
                raise ValueError("string equality mixes incompatible operand sorts")
            literals.append(node.this)
            equality_literals.append(node.this)
            start = node.meta.get("start")
            end = node.meta.get("end")
            if (
                not isinstance(start, int)
                or not isinstance(end, int)
                or start < 0
                or end < start
                or not sql[start : end + 1].startswith("'")
                or not sql[start : end + 1].endswith("'")
            ):
                raise ValueError("string literal lacks an exact source span")
            allowed_uses.append(
                {
                    "kind": "literal",
                    "path": paths[id(node)],
                    "operator": type(parent).__name__,
                    "valueSha256": sha256_text(node.this),
                    "sourceStart": start,
                    "sourceEnd": end,
                }
            )
            continue

        if isinstance(node, exp.Column) and _is_string_type(node.type):
            if id(node) in like_columns:
                allowed_uses.append(
                    {
                        "kind": "column",
                        "path": paths[id(node)],
                        "operator": "LIKE-UDF",
                        "column": node.name,
                        "table": node.table or None,
                        "type": str(node.type),
                    }
                )
                continue
            parent = node.parent
            operator: str | None = None
            if isinstance(parent, exp.Alias) and parent.this is node:
                operator = "direct-projection"
            elif isinstance(parent, exp.Group):
                operator = "group-key"
            elif (
                isinstance(parent, exp.Distinct)
                and isinstance(parent.parent, exp.Count)
            ):
                operator = "count-distinct"
            elif isinstance(parent, exp.EQ):
                other = parent.expression if parent.this is node else parent.this
                if not isinstance(other, exp.Expression) or not _atomic_string_operand(other):
                    raise ValueError("string equality mixes incompatible operand sorts")
                operator = type(parent).__name__
            if operator is None:
                raise ValueError(
                    "string value escapes the equality-only fragment at "
                    + node.sql(dialect="postgres")
                )
            allowed_uses.append(
                {
                    "kind": "column",
                    "path": paths[id(node)],
                    "operator": operator,
                    "column": node.name,
                    "table": node.table or None,
                    "type": str(node.type),
                }
            )
            continue

        if (
            isinstance(node, exp.Expression)
            and _is_string_type(node.type)
            and not isinstance(node, (exp.Column, exp.Literal, exp.Alias))
            and not (
                isinstance(node, exp.Distinct)
                and isinstance(node.parent, exp.Count)
                and all(
                    isinstance(item, exp.Column) and _is_string_type(item.type)
                    for item in node.expressions
                )
            )
        ):
            raise ValueError(
                "composite string expression is outside opaque-string abstraction: "
                + node.sql(dialect="postgres")
            )

    if _has_relational_star(qualified):
        raise ValueError("opaque-string qualification left an unresolved star")
    outputs = list(qualified.named_selects)
    if not outputs:
        raise ValueError("opaque-string query has no statically known outputs")
    return qualified, {
        "inputSha256": sha256_text(sql),
        "outputArity": len(outputs),
        "allowedUses": allowed_uses,
        "stringOccurrenceCount": len(allowed_uses),
        "literalValues": literals,
        "equalityLiteralValues": equality_literals,
        "likeRewrites": like_rewrites,
        "sourceHadStar": source_had_star,
        "sourceHadTopLevelStar": source_had_top_level_star,
        "nestedStarsDirectBasePassThrough": nested_stars_direct_base,
    }


def analyze_opaque_string_pair(
    queries: list[str],
    schema: dict[str, dict[str, str]],
    allow_nested_relational_stars: list[bool] | None = None,
) -> dict:
    transformed_columns = [
        {"table": table, "column": column, "sourceType": type_name}
        for table, columns in schema.items()
        for column, type_name in columns.items()
        if _is_string_type(type_name)
    ]
    if not transformed_columns:
        raise ValueError("opaque-string abstraction found no string columns")

    if allow_nested_relational_stars is None:
        allow_nested_relational_stars = [False] * len(queries)
    if (
        len(allow_nested_relational_stars) != len(queries)
        or any(not isinstance(value, bool) for value in allow_nested_relational_stars)
    ):
        raise ValueError("opaque-string nested-star permissions are malformed")
    prepared = [_attest_opaque_string_query(query, schema) for query in queries]
    if any(report["sourceHadTopLevelStar"] for _, report in prepared):
        # QED itself stores base fields in name-sorted order.  Keeping a source
        # star byte-for-byte therefore does not preserve declaration-order
        # observations, especially after VARCHAR columns all become INTEGER.
        # Opaque-domain abstraction may compose with a separately attested
        # star bridge in the future, but it must not silently perform one.
        raise ValueError(
            "opaque-string abstraction requires an explicit relational output list"
        )
    if any(
        report["sourceHadStar"]
        and not report["nestedStarsDirectBasePassThrough"]
        and not allowed
        for (_, report), allowed in zip(prepared, allow_nested_relational_stars)
    ):
        raise ValueError(
            "opaque-string abstraction found an unattested nested relational star"
        )
    literal_values = sorted(
        {value for _, report in prepared for value in report["literalValues"]}
    )
    literal_codes = {
        value: 1_000_000 + index for index, value in enumerate(literal_values)
    }
    integer_schema = {
        table: {
            column: "INTEGER" if _is_string_type(type_name) else type_name
            for column, type_name in columns.items()
        }
        for table, columns in schema.items()
    }
    reports: list[dict] = []
    for source_sql, (_, report) in zip(queries, prepared):
        literal_uses = [
            item
            for item in report["allowedUses"]
            if item["kind"] == "literal" and item.get("operator") != "LIKE-UDF"
        ]
        source_literals = report["equalityLiteralValues"]
        if len(literal_uses) != len(source_literals):
            raise ValueError("opaque-string literal occurrence inventory is incomplete")
        # Keep every non-literal source byte intact.  In particular, never use
        # SQLGlot's generic star expansion here: it reverses the observable
        # field order of RIGHT JOIN inputs.  A separate Calcite-authoritative
        # gate may expand a star, but the opaque-domain proof must not silently
        # inherit SQLGlot's relation-order convention.
        transformed_sql = source_sql
        replacements = [
            (
                use["sourceStart"],
                use["sourceEnd"] + 1,
                str(literal_codes[value]),
            )
            for use, value in zip(literal_uses, source_literals)
        ]
        attested_like_rewrites: list[dict] = []
        for rewrite in report["likeRewrites"]:
            code = literal_codes[rewrite["literalValue"]]
            replacement = (
                ("NOT " if rewrite["negated"] else "")
                + "QED_VARCHAR_LIKE("
                + rewrite["sourceOperand"]
                + f", {code})"
            )
            replacements.append(
                (rewrite["sourceStart"], rewrite["sourceEnd"] + 1, replacement)
            )
            attested_like_rewrites.append(
                {
                    "path": rewrite["path"],
                    "negated": rewrite["negated"],
                    "valueSha256": rewrite["valueSha256"],
                    "code": code,
                    "sourceStart": rewrite["sourceStart"],
                    "sourceEnd": rewrite["sourceEnd"],
                }
            )
        replacements.sort(key=lambda item: item[0], reverse=True)
        previous_start = len(source_sql)
        for start, end, replacement in replacements:
            if end > previous_start:
                raise ValueError("opaque-string source rewrites overlap")
            transformed_sql = (
                transformed_sql[:start]
                + replacement
                + transformed_sql[end:]
            )
            previous_start = start
        rebound = qualify(
            sqlglot.parse_one(transformed_sql, read="postgres"),
            dialect="postgres",
            schema=integer_schema,
            expand_alias_refs=True,
            expand_stars=True,
            infer_schema=False,
            isolate_tables=False,
            qualify_columns=True,
            allow_partial_qualification=False,
            validate_qualify_columns=True,
            quote_identifiers=True,
            identify=True,
            sql=transformed_sql,
        )
        annotate_types(rebound, schema=integer_schema, dialect="postgres")
        if any(
            isinstance(node, exp.Literal) and node.is_string
            for node in rebound.walk(bfs=False)
        ) or any(
            isinstance(node, exp.Expression) and _is_string_type(node.type)
            for node in rebound.walk(bfs=False)
        ):
            raise ValueError("opaque-string rewrite left a string-typed occurrence")
        if len(list(rebound.named_selects)) != report["outputArity"]:
            raise ValueError("opaque-string rewrite changed output arity")
        reports.append(
            {
                **{
                    key: value
                    for key, value in report.items()
                    if key
                    not in {"literalValues", "equalityLiteralValues", "likeRewrites"}
                },
                "likeUdfRewrites": attested_like_rewrites,
                "transformedSql": transformed_sql,
                "transformedSha256": sha256_text(transformed_sql),
            }
        )

    return {
        "status": "verified-opaque-string-equality-abstraction",
        "sqlglotVersion": sqlglot.__version__,
        "policy": (
            "injective-string-domain-to-integer-equality-or-attested-like-"
            "udf-fragment"
        ),
        "queries": reports,
        "transformedColumns": transformed_columns,
        "literalEncoding": [
            {
                "valueSha256": sha256_text(value),
                "code": literal_codes[value],
                "occurrences": sum(
                    report["literalValues"].count(value) for _, report in prepared
                ),
            }
            for value in literal_values
        ],
        "nullPreserved": True,
        "encodingInjective": True,
        "declarations": (
            [
                "DECLARE SCALAR FUNCTION QED_VARCHAR_LIKE "
                "(INTEGER, INTEGER) RETURNS BOOLEAN"
            ]
            if any(report["likeRewrites"] for _, report in prepared)
            else []
        ),
        "likeUdfAbstraction": (
            {
                "argumentPolicy": "arbitrary-nullable-integer-arguments",
                "semanticPolicy": "arbitrary-nullable-uninterpreted-function",
                "transferPolicy": (
                    "EQ-for-all-UDF-interpretations-implies-EQ-for-the-concrete-"
                    "strict-LIKE-interpretation"
                ),
                "sourceFragment": (
                    "direct-varchar-column-and-backslash-free-string-literal-"
                    "without-escape"
                ),
            }
            if any(report["likeRewrites"] for _, report in prepared)
            else None
        ),
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", required=True)
    parser.add_argument("--output", required=True)
    parser.add_argument(
        "--mode",
        choices=(
            "projection",
            "base-use-closure",
            "opaque-string",
            "source-star-provenance",
            "qed-star-provenance",
        ),
        default="projection",
    )
    args = parser.parse_args()

    request = json.loads(Path(args.input).read_text())
    if args.mode == "qed-star-provenance":
        source_reports = request.get("sourceStarQueries")
        qed_schemas = request.get("qedSchemas")
        qed_queries = request.get("qedQueries")
        expected_types = request.get("expectedOutputTypes")
        if (
            not isinstance(source_reports, list)
            or len(source_reports) != 2
            or not isinstance(qed_schemas, list)
            or not isinstance(qed_queries, list)
            or len(qed_queries) != 2
            or not isinstance(expected_types, list)
            or not all(isinstance(item, str) for item in expected_types)
        ):
            raise ValueError("QED star-provenance validation request is malformed")
        validations = []
        for source_report, qed_query in zip(source_reports, qed_queries):
            if source_report is None:
                validations.append(None)
                continue
            if not isinstance(source_report, dict) or not isinstance(
                source_report.get("outputs"), list
            ):
                raise ValueError("source star-provenance report is malformed")
            validations.append(
                validate_qed_json_direct_provenance(
                    qed_query,
                    qed_schemas,
                    source_report["outputs"],
                    expected_types,
                )
            )
        if not any(item is not None for item in validations):
            raise ValueError("QED star-provenance request has no star side")
        result = {
            "status": "verified-qed-source-star-provenance-pair",
            "queries": validations,
        }
        Path(args.output).write_text(
            json.dumps(result, indent=2, sort_keys=True) + "\n"
        )
        return 0

    raw_schema = request.get("schema")
    queries = request.get("queries")
    if not isinstance(raw_schema, list) or not isinstance(queries, list) or len(queries) != 2:
        raise ValueError("projection request requires schema and exactly two queries")
    schema: dict[str, dict[str, str]] = {}
    for table in raw_schema:
        name = table.get("name") if isinstance(table, dict) else None
        columns = table.get("columns") if isinstance(table, dict) else None
        if (
            not isinstance(name, str)
            or not isinstance(columns, list)
            or not columns
            or any(
                not isinstance(column, dict)
                or not isinstance(column.get("name"), str)
                or not isinstance(column.get("type"), str)
                for column in columns
            )
        ):
            raise ValueError("projection request contains a malformed table")
        if name.casefold() in {table_name.casefold() for table_name in schema}:
            raise ValueError("projection request contains duplicate table names")
        column_names = [column["name"] for column in columns]
        if len({column.casefold() for column in column_names}) != len(column_names):
            raise ValueError("projection request contains duplicate column names")
        schema[name] = {column["name"]: column["type"] for column in columns}

    if args.mode == "source-star-provenance":
        calcite_rels = request.get("calciteRels")
        if (
            not isinstance(calcite_rels, list)
            or len(calcite_rels) != 2
            or any(not isinstance(rel, dict) for rel in calcite_rels)
        ):
            raise ValueError("source star-provenance request lacks Calcite rels")
        source_reports = []
        for query, rel in zip(queries, calcite_rels):
            parsed = sqlglot.parse_one(query, read="postgres")
            root_has_relational_star = (
                isinstance(parsed, exp.Select)
                and _select_has_relational_star(parsed)
            )
            if not root_has_relational_star:
                source_reports.append(None)
                continue
            if not (
                isinstance(parsed, exp.Select)
                and len(parsed.expressions) == 1
                and isinstance(parsed.expressions[0], exp.Star)
            ):
                raise ValueError(
                    "top-level relational star is outside the exact unqualified-star bridge"
                )
            source_report = expand_top_level_unqualified_star(query, raw_schema)
            source_report["calciteValidation"] = (
                validate_calcite_rel_direct_provenance(
                    rel,
                    raw_schema,
                    source_report["outputs"],
                )
            )
            source_reports.append(source_report)
        result = {
            "status": "verified-source-star-provenance-pair",
            "starSideCount": sum(item is not None for item in source_reports),
            "queries": source_reports,
        }
    elif args.mode == "opaque-string":
        result = analyze_opaque_string_pair(
            queries,
            schema,
            allow_nested_relational_stars=request.get(
                "allowNestedRelationalStars"
            ),
        )
    elif args.mode == "base-use-closure":
        reports = [analyze_base_use_query(query, schema) for query in queries]
        if reports[0]["outputArity"] != reports[1]["outputArity"]:
            raise ValueError("source query output arities disagree")
        combined: dict[str, set[str]] = {}
        referenced_tables: set[str] = set()
        for report in reports:
            referenced_tables.update(report["referencedTables"])
            for table, columns in report["baseColumns"].items():
                combined.setdefault(table, set()).update(columns)
        result = {
            "status": "verified-exact-base-column-use-closure",
            "sqlglotVersion": sqlglot.__version__,
            "policy": "qualify-original-query-without-projection-or-rewrite",
            "queries": reports,
            "outputArity": reports[0]["outputArity"],
            "queryBytesPreserved": True,
            "referencedTables": sorted(referenced_tables, key=str.casefold),
            "baseColumns": {
                table: sorted(columns, key=str.casefold)
                for table, columns in sorted(
                    combined.items(), key=lambda item: item[0].casefold()
                )
            },
        }
    else:
        reports = [analyze_query(query, schema) for query in queries]
        if reports[0]["outputArity"] != reports[1]["outputArity"]:
            raise ValueError("source query output arities disagree")
        combined: dict[str, set[str]] = {}
        referenced_tables: set[str] = set()
        for report in reports:
            referenced_tables.update(report["referencedTables"])
            for table, columns in report["baseColumns"].items():
                combined.setdefault(table, set()).update(columns)
        result = {
            "status": "verified-ast-dependency-closure",
            "sqlglotVersion": sqlglot.__version__,
            "policy": "qualify-expand-stars-then-pushdown-projections",
            "queries": reports,
            "outputArity": reports[0]["outputArity"],
            "referencedTables": sorted(referenced_tables, key=str.casefold),
            "baseColumns": {
                table: sorted(columns, key=str.casefold)
                for table, columns in sorted(
                    combined.items(), key=lambda item: item[0].casefold()
                )
            },
        }
    Path(args.output).write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
