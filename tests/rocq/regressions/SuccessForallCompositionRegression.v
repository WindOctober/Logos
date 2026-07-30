(******************************************************************************)
(** Regressions for generic successful-row property composition.             **)
(******************************************************************************)

From Stdlib Require Import List.
From SQLFS Require Import
  Bool3 Env FiniteBag FiniteCollection FiniteSet Formula Projection SqlErrorSemantics
  OrderedSet SqlBagAbstraction SqlOutcome SqlQuerySemantics SqlQuerySyntax.
From Logos.FormalSQL Require Import
  OrderedQueryFacts RelationalAlgebraFacts.

Import Tuple.

Section SuccessForallCompositionRegression.

Context {T : Tuple.Rcd} {relname : Type}.

Variable basesort : relname -> Fset.set (A T).
Variable instance : relname -> Febag.bag (Fecol.CBag (CTuple T)).
Variable unknown : Bool.b (B T).
Variable symbol_runtime_error :
  scalar_operator T -> list (option sql_runtime_error * value T) ->
  option sql_runtime_error.
Variable aggregate_runtime_error :
  aggregate T -> list (option sql_runtime_error * value T) ->
  option sql_runtime_error.
Variable value_is_null : value T -> bool.

Local Abbreviation eval_query :=
  (@eval_query_expr_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).

Local Abbreviation success_Forall :=
  (@query_success_Forall T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).

Theorem representative_Forall_transport_regression :
  forall (property : tuple T -> Prop) first second bag,
    tuple_property_semantic_invariant property ->
    query_same_rows_as_bag first bag ->
    query_same_rows_as_bag second bag ->
    Forall property first ->
    Forall property second.
Proof.
intros property first second bag Hproper Hfirst Hsecond Hforall.
exact
  (@query_same_rows_as_bag_Forall_transport
    T property first second bag Hproper Hfirst Hsecond Hforall).
Qed.

Theorem mapped_representative_regression :
  forall (mapping : tuple T -> tuple T) rows bag,
    (forall first second,
      Oeset.compare (OTuple T) first second = Eq ->
      Oeset.compare (OTuple T) (mapping first) (mapping second) = Eq) ->
    query_same_rows_as_bag rows bag ->
    query_same_rows_as_bag
      (map mapping rows)
      (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
        mapping bag).
Proof.
intros mapping rows bag Hproper Hrows.
exact (@query_same_rows_as_bag_map T mapping rows bag Hproper Hrows).
Qed.

Theorem project_success_Forall_regression :
  forall env select_list input input_property output_property,
    success_Forall env input input_property ->
    (forall row,
      input_property row ->
      output_property
        (projection T (env_t T env row) (@Select_List T select_list))) ->
    success_Forall env
      (QExpr_Project select_list input) output_property.
Proof.
intros env select_list input input_property output_property Hinput Hmap.
exact
  (@query_expr_project_success_Forall
    T relname basesort instance unknown symbol_runtime_error
    aggregate_runtime_error value_is_null env select_list input
    input_property output_property Hinput Hmap).
Qed.

Theorem filter_success_Forall_regression :
  forall env formula input property,
    success_Forall env input property ->
    success_Forall env (QExpr_Filter formula input) property.
Proof.
intros env formula input property Hinput.
exact
  (@query_expr_filter_success_Forall
    T relname basesort instance unknown symbol_runtime_error
    aggregate_runtime_error value_is_null env formula input property Hinput).
Qed.

Theorem union_success_Forall_regression :
  forall env left right property,
    query_expr_sort left =S= query_expr_sort right ->
    tuple_property_semantic_invariant property ->
    success_Forall env left property ->
    success_Forall env right property ->
    success_Forall env (QExpr_Set Union left right) property.
Proof.
intros env left right property Hsort Hproper Hleft Hright.
exact
  (@query_expr_union_success_Forall
    T relname basesort instance unknown symbol_runtime_error
    aggregate_runtime_error value_is_null env left right property
    Hsort Hproper Hleft Hright).
Qed.

Theorem cross_join_success_Forall_regression :
  forall env left right property,
    tuple_property_semantic_invariant property ->
    (forall left_rows right_rows,
      eval_query env left (SqlSuccess left_rows) ->
      eval_query env right (SqlSuccess right_rows) ->
      Forall property
        (Febag.elements (Fecol.CBag (CTuple T))
          (query_cross_join_bag
            (rows_bag T left_rows) (rows_bag T right_rows)))) ->
    success_Forall env (QExpr_CrossJoin left right) property.
Proof.
intros env left right property Hproper Hcross.
exact
  (@query_expr_cross_join_success_Forall
    T relname basesort instance unknown symbol_runtime_error
    aggregate_runtime_error value_is_null env left right property
    Hproper Hcross).
Qed.

End SuccessForallCompositionRegression.

Print Assumptions query_same_rows_as_bag_Forall_transport.
Print Assumptions query_same_rows_as_bag_map.
Print Assumptions query_expr_project_success_Forall.
Print Assumptions query_expr_filter_success_Forall.
Print Assumptions query_expr_union_success_Forall.
Print Assumptions query_expr_cross_join_success_Forall.
