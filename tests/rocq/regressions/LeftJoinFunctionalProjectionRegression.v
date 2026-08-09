Set Implicit Arguments.

From Stdlib Require Import List NArith.
From SQLFS Require Import
  Bool3 Env FiniteBag FiniteCollection FiniteSet FlatData Formula OrderedSet
  SqlBagAbstraction SqlOutcome SqlQuerySemantics SqlQuerySyntax.
From Logos.FormalSQL Require Import RelationalAlgebraFacts.

Import Tuple.

Section LeftJoinFunctionalProjectionRegression.

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
Variable boolean_schedule : boolean_site -> boolean_evaluation_order.

(** This wrapper models schema facts as predicates known only for rows in a
    representative of each successful input bag.  In particular, neither
    projection law is assumed for an arbitrary (possibly malformed) tuple. *)
Theorem left_join_functional_projection_from_representative_invariants :
  forall env predicate matched_select left_select right_select
      (project emit : tuple T -> tuple T) left_bag right_bag joined_bag
      (left_invariant right_invariant : tuple T -> Prop),
    (forall first second,
      Oeset.compare (OTuple T) first second = Eq ->
      Oeset.compare (OTuple T) (project first) (project second) = Eq) ->
    (forall first second,
      Oeset.compare (OTuple T) first second = Eq ->
      Oeset.compare (OTuple T) (emit first) (emit second) = Eq) ->
    (forall left_rows right_rows matrix,
      query_same_rows_as_bag left_rows left_bag ->
      query_same_rows_as_bag right_rows right_bag ->
      @eval_join_conditions_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env predicate left_rows right_rows
        (SqlSuccess matrix) ->
      Forall
        (fun flags =>
          (length (filter (fun flag : bool => flag) flags) <= 1)%nat)
        matrix) ->
    (forall left_rows,
      query_same_rows_as_bag left_rows left_bag ->
      Forall left_invariant left_rows) ->
    (forall right_rows,
      query_same_rows_as_bag right_rows right_bag ->
      Forall right_invariant right_rows) ->
    (forall left right values,
      left_invariant left ->
      right_invariant right ->
      @eval_scalar_values_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule (env_t T env (join_tuple T left right))
        (map fst matched_select) (SqlSuccess values) ->
      Oeset.compare (OTuple T)
        (project (project_row matched_select values)) (emit left) = Eq) ->
    (forall left values,
      left_invariant left ->
      @eval_scalar_values_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule (env_t T env left) (map fst left_select)
        (SqlSuccess values) ->
      Oeset.compare (OTuple T)
        (project (project_row left_select values)) (emit left) = Eq) ->
    @eval_join_bag_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule env QueryJoinLeft predicate matched_select left_select right_select
      left_bag right_bag (SqlSuccess joined_bag) ->
    bag_eq T
      (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
        project joined_bag)
      (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
        emit left_bag).
Proof.
intros env predicate matched_select left_select right_select project emit
  left_bag right_bag joined_bag left_invariant right_invariant
  Hproject_proper Hemit_proper Hfunctional Hleft_representatives
  Hright_representatives Hmatched Hleft Heval.
eapply query_join_left_functional_projection_bag_on_representatives;
  try eassumption.
- intros left_rows right_rows left right values
    Hleft_bag Hright_bag Hleft_in Hright_in Hsource.
  pose proof (Hleft_representatives left_rows Hleft_bag) as Hleft_all.
  pose proof (Hright_representatives right_rows Hright_bag) as Hright_all.
  rewrite Forall_forall in Hleft_all, Hright_all.
  exact (Hmatched left right values
    (Hleft_all left Hleft_in)
    (Hright_all right Hright_in) Hsource).
- intros left_rows left values Hleft_bag Hleft_in Hsource.
  pose proof (Hleft_representatives left_rows Hleft_bag) as Hleft_all.
  rewrite Forall_forall in Hleft_all.
  exact (Hleft left values (Hleft_all left Hleft_in) Hsource).
Qed.

End LeftJoinFunctionalProjectionRegression.
