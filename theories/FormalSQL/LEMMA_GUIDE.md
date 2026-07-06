# Logos FormalSQL Lemma Guide

This guide lists Logos-local lemmas available to proof agents.  These files are
read-only proof context; generated proof attempts should edit only the generated
problem workspace.

## Occurrence Semantics

### `query_occ` [`theories/FormalSQL/OccFacts.v`]

multiplicity of tuple `t` in the result of query `q`
on database state `db`.

```coq
Definition query_occ (db : db_state) (q : Query) (t : tuple TNull) :=
  Febag.nb_occ _ t (eval_query_in_state db q).
```

### `query_nonempty` [`theories/FormalSQL/OccFacts.v`]

query `q` has at least one output tuple on `db`.

```coq
Definition query_nonempty (db : db_state) (q : Query) : Prop :=
  exists t, t inBE eval_query_in_state db q.
```

### `query_equiv_iff_occ` [`theories/FormalSQL/OccFacts.v`]

FormalSQL bag equivalence is exactly pointwise
equality of tuple multiplicities.

```coq
Lemma query_equiv_iff_occ :
  forall db q1 q2,
    query_equiv db q1 q2 <->
    forall t, query_occ db q1 t = query_occ db q2 t.
```

### `pi_congr` [`theories/FormalSQL/OccFacts.v`]

if two input queries are bag-equivalent, applying the
same projection to both preserves equivalence.

```coq
Lemma pi_congr :
  forall db s q1 q2,
    query_equiv db q1 q2 ->
    query_equiv db (Pi s q1) (Pi s q2).
```

### `sigma_congr` [`theories/FormalSQL/OccFacts.v`]

if two input queries are bag-equivalent, filtering
both by the same predicate preserves equivalence.

```coq
Lemma sigma_congr :
  forall db f q1 q2,
    query_equiv db q1 q2 ->
    query_equiv db (Sigma f q1) (Sigma f q2).
```

### `formula_true_on_output_equiv` [`theories/FormalSQL/OccFacts.v`]

an invariant that holds for all output tuples of a
query also holds for any bag-equivalent query.

```coq
Lemma formula_true_on_output_equiv :
  forall db q1 q2 f,
    query_equiv db q1 q2 ->
    formula_true_on_output db q1 f ->
    formula_true_on_output db q2 f.
```

## Projection Facts

### `well_sorted_database` [`theories/FormalSQL/PiFacts.v`]

every tuple stored in each base table has labels equal
to the table schema sort.

```coq
Definition well_sorted_database (db : db_state) : Prop :=
  forall tbl t,
    t inBE (@_instance TNull db tbl) ->
    labels TNull t =S= @_basesort TNull db tbl.
```

### `select_list_sort` [`theories/FormalSQL/PiFacts.v`]

the output label set produced by a select list.

```coq
Definition select_list_sort (s : SelectListT) : Fset.set (A TNull) :=
  match s with
  | @_Select_List _ l =>
      Fset.mk_set _ (map (fun x => match x with @Select_As _ _ a => a end) l)
  end.
```

### `pi_sort` [`theories/FormalSQL/PiFacts.v`]

the FormalSQL sort of `Pi s q` is exactly the output
sort of `s`.

```coq
Lemma pi_sort :
  forall db s q,
    @sort TNull relname (@_basesort TNull db) (Pi s q) =S= select_list_sort s.
```

### `pi_output_tuple_has_select_list_sort` [`theories/FormalSQL/PiFacts.v`]

every tuple output by a projection has labels equal to
the select-list output sort.

```coq
Lemma pi_output_tuple_has_select_list_sort :
  forall db s q t,
    well_sorted_database db ->
    t inBE eval_query_in_state db (Pi s q) ->
    labels TNull t =S= select_list_sort s.
```

### `common_pi_output_tuple_implies_same_select_list_sort` [`theories/FormalSQL/PiFacts.v`]

if the same tuple appears in two projected outputs,
then the two select lists have the same output sort.

```coq
Lemma common_pi_output_tuple_implies_same_select_list_sort :
  forall db s1 q1 s2 q2 t,
    well_sorted_database db ->
    t inBE eval_query_in_state db (Pi s1 q1) ->
    t inBE eval_query_in_state db (Pi s2 q2) ->
    select_list_sort s1 =S= select_list_sort s2.
```

### `pi_sort_mismatch_not_equiv_with_witness` [`theories/FormalSQL/PiFacts.v`]

if one projected result is nonempty and the two
select-list output sorts differ, then the projected queries are not equivalent.

```coq
Lemma pi_sort_mismatch_not_equiv_with_witness :
  forall db s1 q1 s2 q2 t,
    well_sorted_database db ->
    t inBE eval_query_in_state db (Pi s1 q1) ->
    (select_list_sort s1 =S= select_list_sort s2 -> False) ->
    ~ query_equiv db (Pi s1 q1) (Pi s2 q2).
```

### `nonempty_pi_equiv_iff_sort_and_occ` [`theories/FormalSQL/PiFacts.v`]

for nonempty projected outputs over a well-sorted
database, query equivalence is equivalent to equal output sorts plus pointwise
equality of tuple multiplicities.

```coq
Lemma nonempty_pi_equiv_iff_sort_and_occ :
  forall db s1 q1 s2 q2,
    well_sorted_database db ->
    query_nonempty db (Pi s1 q1) ->
    query_equiv db (Pi s1 q1) (Pi s2 q2) <->
      select_list_sort s1 =S= select_list_sort s2 /\
      forall t, query_occ db (Pi s1 q1) t = query_occ db (Pi s2 q2) t.
```

## Selection Rewrite Facts

### `formula_implies_on_output` [`theories/FormalSQL/RewriteSpec.v`]

on every tuple output by query `q`, truth of
`premise` implies truth of `conclusion`.  Use this as the generic hook for
case-specific arithmetic or predicate reasoning.

```coq
Definition formula_implies_on_output
    (db : db_state) (q : Query) (premise conclusion : Formula) : Prop :=
  forall t,
    t inBE eval_query_in_state db q ->
    eval_formula_in_state db t premise = true ->
    eval_formula_in_state db t conclusion = true.
```

### `selected_rows_satisfy_filter` [`theories/FormalSQL/RewriteSpec.v`]

every tuple output by `Sigma f q` satisfies `f`.

```coq
Lemma selected_rows_satisfy_filter :
  forall db q f,
    formula_true_on_output db (Sigma f q) f.
```

### `formula_implies_filter_outputs` [`theories/FormalSQL/RewriteSpec.v`]

if `premise` implies `conclusion` on the base query
output, then every tuple output by `Sigma premise q` satisfies `conclusion`.

```coq
Lemma formula_implies_filter_outputs :
  forall db q premise conclusion,
    formula_implies_on_output db q premise conclusion ->
    formula_true_on_output db (Sigma premise q) conclusion.
```

### `eval_conj_and_true_iff` [`theories/FormalSQL/RewriteSpec.v`]

evaluating `p AND h` is the Boolean conjunction of
evaluating `p` and evaluating `h`.

```coq
Lemma eval_conj_and_true_iff :
  forall db env t p h,
    eval_formula_in_env db env t (conj_and p h) =
    (eval_formula_in_env db env t p && eval_formula_in_env db env t h)%bool.
```

### `redundant_conjunct_under_query_invariant` [`theories/FormalSQL/RewriteSpec.v`]

if predicate `h` is true on every output tuple of
`q`, then adding `h` as an extra conjunct under a selection does not change the
query result.

```coq
Lemma redundant_conjunct_under_query_invariant :
  forall db q p h,
    formula_true_on_output db q h ->
    query_equiv db (Sigma (conj_and p h) q) (Sigma p q).
```

### `sigma_sigma_merge` [`theories/FormalSQL/RewriteSpec.v`]

two nested selections can be merged into one selection
with a conjunctive predicate.

```coq
Lemma sigma_sigma_merge :
  forall db q outer inner,
    query_equiv db (Sigma outer (Sigma inner q)) (Sigma (conj_and outer inner) q).
```

## Projection Preservation

### `select_list_preserves_formula` [`theories/FormalSQL/RewriteSpec.v`]

projecting with select list `s` preserves the truth
value of formula `f` on every tuple.  This is the generic predicate-level
projection-preservation premise.

```coq
Definition select_list_preserves_formula
    (db : db_state) (s : SelectListT) (f : Formula) : Prop :=
  forall t,
    eval_formula_in_state db (projected_tuple nil s t) f =
    eval_formula_in_state db t f.
```

### `direct_projection_preserves_attr_value` [`theories/FormalSQL/RewriteSpec.v`]

if a select list directly preserves an attribute under
the same output name and has distinct output attributes, then projection
preserves that attribute's value.

```coq
Lemma direct_projection_preserves_attr_value :
  forall env s a,
    select_list_directly_preserves_attr s a ->
    select_list_outputs_distinct_attrs s ->
    projection_preserves_attr_value env s a.
```

### `projected_filter_outputs_satisfy_preserved_predicate` [`theories/FormalSQL/RewriteSpec.v`]

if a projection preserves predicate `f`, then
`Pi s (Sigma f q)` still satisfies `f` after the projection.

```coq
Lemma projected_filter_outputs_satisfy_preserved_predicate :
  forall db q s f,
    select_list_preserves_formula db s f ->
    formula_true_on_output db (Pi s (Sigma f q)) f.
```

### `projected_filter_outputs_satisfy_implied_predicate` [`theories/FormalSQL/RewriteSpec.v`]

if `premise` implies `conclusion` on `q`, and the
projection preserves `conclusion`, then `Pi s (Sigma premise q)` satisfies
`conclusion`.

```coq
Lemma projected_filter_outputs_satisfy_implied_predicate :
  forall db q s premise conclusion,
    select_list_preserves_formula db s conclusion ->
    formula_implies_on_output db q premise conclusion ->
    formula_true_on_output db (Pi s (Sigma premise q)) conclusion.
```

## Standard Rocq Tools Available

Proof scripts may import standard libraries as needed:

```coq
From Stdlib Require Import String ZArith Lia NArith List.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
```

Use `lia` for linear integer arithmetic and `nia` for nonlinear integer
arithmetic.  Arithmetic facts should be proved in the generated problem or a
separate generated helper file, not added as axioms to the read-only lemma
context.
