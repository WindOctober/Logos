(******************************************************************************)
(** Generic regressions for collision-safe query renaming transport.          **)
(******************************************************************************)

Set Implicit Arguments.

From Stdlib Require Import List String Sorting.Permutation.
From SQLFS Require Import FiniteSet FiniteBag FiniteCollection FlatData Env Bool3
  Formula SqlOutcome SqlBagAbstraction SqlQueryContexts SqlQuerySyntax
  SqlQuerySemantics.
From Logos.FormalSQL Require Import RenameTransportFacts.

Import Tuple.

Section GenericTupleAndCollectionRegressions.

Context {T : Tuple.Rcd}.

Local Definition bagT := Febag.bag (Fecol.CBag (CTuple T)).

Example renaming_identity_regression :
  forall row,
    rename_tuple T (fun attribute => attribute) row =t= row.
Proof.
exact (@rename_tuple_identity T).
Qed.

Example renaming_composition_regression :
  forall rho sigma row,
    attribute_rename_injective_on (labels T row) rho ->
    attribute_rename_injective_on
      (Fset.map (A T) (A T) rho (labels T row)) sigma ->
    rename_tuple T sigma (rename_tuple T rho row) =t=
    rename_tuple T (fun attribute => sigma (rho attribute)) row.
Proof.
exact (@rename_tuple_composition T).
Qed.

(** [skipn] followed by [firstn] observes exact positions, so this regression
    checks an order-sensitive unary composition rather than bag equality. *)
Example renaming_ordered_slice_regression :
  forall (rho : attribute T -> attribute T) offset count
      (left right : list (tuple T)),
    rows_rename_equiv rho left right ->
    rows_rename_equiv rho
      (firstn count (skipn offset left))
      (firstn count (skipn offset right)).
Proof.
intros rho offset count left right Hrows.
apply rows_rename_equiv_firstn.
now apply rows_rename_equiv_skipn.
Qed.

Example renaming_permutation_regression :
  forall (rho : attribute T -> attribute T)
      (left right : list (tuple T)),
    Permutation left right ->
    Permutation (rename_rows rho left) (rename_rows rho right).
Proof.
exact (@rename_rows_permutation_transport T).
Qed.

(** Multiplicity reflection is deliberately conditional on cross-row
    collision freedom; a many-to-one attribute map cannot discharge it. *)
Example renaming_bag_multiplicity_regression :
  forall (rho : attribute T -> attribute T) (row : tuple T) (bag : bagT),
    (forall candidate,
      candidate inBE bag ->
      attribute_rename_collision_free_between
        (labels T row) (labels T candidate) rho) ->
    Febag.nb_occ (Fecol.CBag (CTuple T))
      (rename_tuple T rho row) (rename_bag rho bag) =
    Febag.nb_occ (Fecol.CBag (CTuple T)) row bag.
Proof.
exact (@rename_bag_multiplicity_transport T).
Qed.

Example renaming_query_rows_actual_safety_regression :
  forall (rho : attribute T -> attribute T) left right,
    query_rows_rename rho left right ->
    rows_rename_collision_safe rho left /\
    rows_rename_type_safe rho left.
Proof.
intros rho left right Hrows.
exact (proj2 Hrows).
Qed.

Example renaming_query_rows_ordered_slice_regression :
  forall (rho : attribute T -> attribute T) offset count left right,
    query_rows_rename rho left right ->
    query_rows_rename rho
      (firstn count (skipn offset left))
      (firstn count (skipn offset right)).
Proof.
intros rho offset count left right Hrows.
unfold query_rows_rename in *.
apply rows_rename_sound_firstn.
now apply rows_rename_sound_skipn.
Qed.

Example renaming_mapped_bag_source_regression :
  forall (rho : attribute T -> attribute T) (left right : bagT),
    query_bag_source_rename_safe T rho left ->
    bag_eq T right (rename_bag rho left) ->
    query_outcome_rename_transport T rho
      (query_bag_source_local T left)
      (query_bag_source_local T right).
Proof.
exact (@query_bag_source_local_rename_transport T).
Qed.

Example renaming_error_outcome_regression :
  forall (rho : attribute T -> attribute T) error,
    outcome_rename_equiv rho
      (@SqlError (list (tuple T)) error)
      (@SqlError (list (tuple T)) error).
Proof.
intros rho error.
apply (proj2 (@outcome_rename_equiv_error T rho error error)).
reflexivity.
Qed.

End GenericTupleAndCollectionRegressions.

Section GenericSchedulerRegression.

Context {T : Tuple.Rcd}.

Local Definition outcome_predicate :=
  sql_outcome (list (tuple T)) -> Prop.

Local Definition binary_local :=
  list (tuple T) -> list (tuple T) -> outcome_predicate.

(** The scheduler theorem composes two independently transported children and
    preserves both local successes and every exact error category. *)
Example renaming_binary_scheduler_regression :
  forall (rho : attribute T -> attribute T)
      (left_child left_child' right_child right_child' : outcome_predicate)
      (left_local right_local : binary_local),
    query_outcome_rename_transport T rho left_child left_child' ->
    query_outcome_rename_transport T rho right_child right_child' ->
    (forall left_rows left_rows' right_rows right_rows',
      query_rows_rename rho left_rows left_rows' ->
      query_rows_rename rho right_rows right_rows' ->
      query_outcome_rename_transport T rho
        (left_local left_rows right_rows)
        (right_local left_rows' right_rows')) ->
    query_outcome_rename_transport T rho
      (query_binary_outcome_lift T left_child right_child left_local)
      (query_binary_outcome_lift T left_child' right_child' right_local).
Proof.
exact (@query_binary_outcome_lift_transport T).
Qed.

Example renaming_row_map_callback_scheduler_regression :
  forall (rho : attribute T -> attribute T)
      (left_map right_map : tuple T -> sql_outcome (tuple T)),
    query_row_map_callback_rename_compatible T rho left_map right_map ->
    query_row_map_success_rename_safe T rho left_map ->
    query_row_map_scheduler_rename_compatible T rho left_map right_map.
Proof.
exact (@query_row_map_callback_rename_compatible_scheduler T).
Qed.

End GenericSchedulerRegression.

Section ExactScalarRegression.

Context {T : Tuple.Rcd} {relname : Type}.
Context (basesort : relname -> Fset.set (A T)).
Context (instance : relname -> Febag.bag (Fecol.CBag (CTuple T))).
Context (unknown : Bool.b (B T)).
Context
  (symbol_runtime_error :
    scalar_operator T ->
    list (option sql_runtime_error * value T) -> option sql_runtime_error)
  (aggregate_runtime_error :
    aggregate T ->
    list (option sql_runtime_error * value T) -> option sql_runtime_error)
  (value_is_null : value T -> bool)
  (boolean_schedule : boolean_site -> boolean_evaluation_order).

Local Abbreviation eval_scalar_boolean :=
  (@eval_scalar_boolean_expr_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).

(** Exact typed Boolean transport fixes the same Bool3 carrier value.  In
    particular it cannot replace FALSE with UNKNOWN as an acceptance-only
    filter contract could. *)
Example renaming_exact_scalar_bool3_regression :
  forall environment_relation left right left_env right_env,
    @query_scalar_expr_outcome_rename_compatible T relname
      basesort instance unknown symbol_runtime_error
      aggregate_runtime_error value_is_null boolean_schedule
      environment_relation left right ->
    environment_relation left_env right_env ->
    forall truth,
      (eval_scalar_boolean left_env left (SqlSuccess truth) <->
       eval_scalar_boolean right_env right (SqlSuccess truth)).
Proof.
exact (@query_scalar_expr_outcome_rename_compatible_success_iff
  T relname basesort instance unknown symbol_runtime_error
  aggregate_runtime_error value_is_null boolean_schedule).
Qed.

End ExactScalarRegression.

(** The concrete query facade accepts only a textual name map.  Its lifted
    attribute map therefore cannot alter any TNull type or typmod field. *)
Example renaming_tnull_name_only_schema_regression :
  forall db left_env right_env (rename_name : string -> string) left right,
    tnull_query_mapped_schema_outcome_equiv
      db left_env right_env rename_name left right ->
    map (rename_tnull_attribute_name rename_name)
      (query_expr_outputs left) = query_expr_outputs right.
Proof.
exact tnull_query_mapped_schema_outcome_equiv_mapped_schema.
Qed.

(** This facade-level regression quantifies over an arbitrary-length list of
    paired existing query contexts; it does not choose a fixed query topology. *)
Example renaming_arbitrary_context_chain_regression :
  forall db environment_relation (rename_name : string -> string)
      left_contexts right_contexts,
    Forall2
      (tnull_query_rename_context_compatible
        db environment_relation rename_name)
      left_contexts right_contexts ->
    forall left right,
      tnull_query_rename_transport_under
        db environment_relation rename_name left right ->
      tnull_query_rename_transport_under
        db environment_relation rename_name
        (plug_query_rename_contexts left_contexts left)
        (plug_query_rename_contexts right_contexts right).
Proof.
exact tnull_query_renaming_context_chain_transport.
Qed.

Print Assumptions renaming_identity_regression.
Print Assumptions renaming_composition_regression.
Print Assumptions renaming_ordered_slice_regression.
Print Assumptions renaming_permutation_regression.
Print Assumptions renaming_bag_multiplicity_regression.
Print Assumptions renaming_query_rows_actual_safety_regression.
Print Assumptions renaming_query_rows_ordered_slice_regression.
Print Assumptions renaming_mapped_bag_source_regression.
Print Assumptions renaming_error_outcome_regression.
Print Assumptions renaming_binary_scheduler_regression.
Print Assumptions renaming_row_map_callback_scheduler_regression.
Print Assumptions renaming_exact_scalar_bool3_regression.
Print Assumptions renaming_tnull_name_only_schema_regression.
Print Assumptions renaming_arbitrary_context_chain_regression.
