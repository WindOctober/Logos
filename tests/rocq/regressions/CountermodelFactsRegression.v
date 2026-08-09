(******************************************************************************)
(** Regression checks for generic FormalSQL countermodel interfaces.          **)
(******************************************************************************)

From SQLFS Require Import
  SqlSyntax FTuples FiniteBag FiniteCollection FiniteSet Env Bool3 SqlOutcome
  SqlBagAbstraction SqlQuerySyntax SqlQueryFacts.
From Logos.FormalSQL Require Import
  OrderedQueryFacts ProofAgentFacade CountermodelFacts.
From Stdlib Require Import List NArith.

Import ListNotations.
Import Tuple.

Section GenericFunctionalityComposition.

Context {A B : Type}.
Variables source_equiv : A -> A -> Prop.
Variables target_equiv : B -> B -> Prop.
Variables source : sql_outcome A -> Prop.
Variables target : sql_outcome B -> Prop.
Variable transform : A -> B.

Hypothesis target_success :
  forall output,
    target (SqlSuccess output) ->
    exists input,
      source (SqlSuccess input) /\ output = transform input.
Hypothesis transform_proper :
  forall left right,
    source_equiv left right ->
    target_equiv (transform left) (transform right).
Hypothesis source_functional :
  successful_relation_functional source_equiv source.

Example mapped_success_relation_is_functional :
  successful_relation_functional target_equiv target.
Proof.
eapply successful_relation_functional_map; eassumption.
Qed.

End GenericFunctionalityComposition.

Section PossibleBagFunctionalityComposition.

Context {T : Tuple.Rcd}.
Variables inputs left_inputs right_inputs : SqlBagAbstraction.bagT T -> Prop.
Variable unary : unary_bag_relation T.
Variable binary : binary_bag_relation T.

Hypothesis inputs_functional : @possible_bag_functional T inputs.
Hypothesis left_inputs_functional : @possible_bag_functional T left_inputs.
Hypothesis right_inputs_functional : @possible_bag_functional T right_inputs.
Hypothesis unary_extensional : unary_bag_relation_extensional unary.
Hypothesis unary_functional : @unary_bag_relation_functional T unary.
Hypothesis binary_extensional : binary_bag_relation_extensional binary.
Hypothesis binary_functional : @binary_bag_relation_functional T binary.
Variable unary_parent binary_parent : SqlBagAbstraction.bagT T -> Prop.
Hypothesis unary_characterization :
  rel_equiv unary_parent (lift_possible_bag_unary unary inputs).
Hypothesis binary_characterization :
  rel_equiv binary_parent
    (lift_possible_bag_binary binary left_inputs right_inputs).

Example unary_lift_is_functional :
  @possible_bag_functional T (lift_possible_bag_unary unary inputs).
Proof.
eapply lift_possible_bag_unary_functional; eassumption.
Qed.

Example binary_lift_is_functional :
  @possible_bag_functional T
    (lift_possible_bag_binary binary left_inputs right_inputs).
Proof.
eapply lift_possible_bag_binary_functional; eassumption.
Qed.

Example unary_reset_query_bags_are_functional :
  @possible_bag_functional T unary_parent.
Proof.
eapply query_success_bags_functional_of_unary_reset; eassumption.
Qed.

Example binary_reset_query_bags_are_functional :
  @possible_bag_functional T binary_parent.
Proof.
eapply query_success_bags_functional_of_binary_reset; eassumption.
Qed.

End PossibleBagFunctionalityComposition.

Section GenericPropertySeparation.

Context {A : Type}.
Variable value_equiv : A -> A -> Prop.
Variables left right : sql_outcome A -> Prop.
Variable property : A -> Prop.
Variable left_value right_value : A.
Variable error : sql_runtime_error.

Hypothesis property_invariant :
  observation_property_invariant value_equiv property.
Hypothesis left_success : left (SqlSuccess left_value).
Hypothesis right_success : right (SqlSuccess right_value).
Hypothesis left_property : property left_value.
Hypothesis right_property : property right_value.
Hypothesis no_right_property :
  forall value, right (SqlSuccess value) -> ~ property value.
Hypothesis no_left_property :
  forall value, left (SqlSuccess value) -> ~ property value.
Hypothesis left_error : left (SqlError error).
Hypothesis right_error : right (SqlError error).
Hypothesis no_right_error : ~ right (SqlError error).
Hypothesis no_left_error : ~ left (SqlError error).

Example left_success_property_separates :
  outcome_relation_separation value_equiv left right.
Proof.
eapply outcome_relation_separation_of_left_success_property;
  eassumption.
Qed.

Example right_success_property_separates :
  outcome_relation_separation value_equiv left right.
Proof.
eapply outcome_relation_separation_of_right_success_property;
  eassumption.
Qed.

Example left_error_separates :
  outcome_relation_separation value_equiv left right.
Proof.
eapply outcome_relation_separation_of_left_error_absent;
  eassumption.
Qed.

Example right_error_separates :
  outcome_relation_separation value_equiv left right.
Proof.
eapply outcome_relation_separation_of_right_error_absent;
  eassumption.
Qed.

End GenericPropertySeparation.

Section OrderedBagSeparation.

Context {T : Tuple.Rcd}.
Variables left right : sql_outcome (list (tuple T)) -> Prop.
Variables left_rows right_rows : list (tuple T).
Variable witness_row : tuple T.

Hypothesis left_success : left (SqlSuccess left_rows).
Hypothesis right_success : right (SqlSuccess right_rows).
Hypothesis all_right_bags_differ :
  forall rows,
    right (SqlSuccess rows) ->
    ~ bag_eq T (rows_bag T left_rows) (rows_bag T rows).
Hypothesis all_left_bags_differ :
  forall rows,
    left (SqlSuccess rows) ->
    ~ bag_eq T (rows_bag T rows) (rows_bag T right_rows).
Hypothesis all_right_occurrences_differ :
  forall rows,
    right (SqlSuccess rows) ->
    Febag.nb_occ (Fecol.CBag (CTuple T)) witness_row
      (rows_bag T left_rows) <>
    Febag.nb_occ (Fecol.CBag (CTuple T)) witness_row
      (rows_bag T rows).
Hypothesis all_left_occurrences_differ :
  forall rows,
    left (SqlSuccess rows) ->
    Febag.nb_occ (Fecol.CBag (CTuple T)) witness_row
      (rows_bag T rows) <>
    Febag.nb_occ (Fecol.CBag (CTuple T)) witness_row
      (rows_bag T right_rows).

Example left_bag_difference_separates :
  outcome_relation_separation (ordered_rows_equiv T) left right.
Proof.
eapply ordered_outcome_separation_of_left_success_bag_difference;
  eassumption.
Qed.

Example right_bag_difference_separates :
  outcome_relation_separation (ordered_rows_equiv T) left right.
Proof.
eapply ordered_outcome_separation_of_right_success_bag_difference;
  eassumption.
Qed.

Example left_occurrence_difference_separates :
  outcome_relation_separation (ordered_rows_equiv T) left right.
Proof.
eapply ordered_outcome_separation_of_left_success_occurrence_difference;
  eassumption.
Qed.

Example right_occurrence_difference_separates :
  outcome_relation_separation (ordered_rows_equiv T) left right.
Proof.
eapply ordered_outcome_separation_of_right_success_occurrence_difference;
  eassumption.
Qed.

End OrderedBagSeparation.

Section ProgramLift.

Variable db : TNullDatabase.
Variable env : TNullEnvironment.
Variables left_program right_program : TNullQueryProgram.
Variables left_query right_query : TNullQueryExpr.
Variable index : nat.

Hypothesis left_at_index : nth_error left_program index = Some left_query.
Hypothesis right_at_index : nth_error right_program index = Some right_query.
Hypothesis separated :
  TNullQueryExprOutcomeSeparation db env left_query right_query.

Example nth_statement_separation_refutes_program_equivalence :
  ~ TNullQueryProgramOutcomeEq db env left_program right_program.
Proof.
eapply tnull_query_program_nth_separation_sound;
  eassumption.
Qed.

End ProgramLift.

Section OperatorFunctionality.

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

Local Abbreviation success_bags :=
  (@query_success_bags T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).

Example natural_join_functionality_composes :
  forall env left right,
    @possible_bag_functional T (success_bags env left) ->
    @possible_bag_functional T (success_bags env right) ->
    @possible_bag_functional T
      (success_bags env (QExpr_NaturalJoin left right)).
Proof.
intros; unfold possible_bag_functional in *.
now apply query_natural_join_success_bags_functional.
Qed.

Example order_by_bag_functionality_composes :
  forall env keys input,
    @possible_bag_functional T (success_bags env input) ->
    @possible_bag_functional T
      (success_bags env (QExpr_OrderBy keys input)).
Proof.
intros; unfold possible_bag_functional in *.
now apply query_order_by_success_bags_functional.
Qed.

Example row_map_functionality_requires_its_contract :
  forall env outputs row_map input,
    @possible_bag_functional T (success_bags env input) ->
    row_map_success_bag_contract row_map ->
    @possible_bag_functional T
      (success_bags env (QExpr_RowMap outputs row_map input)).
Proof.
intros; unfold possible_bag_functional in *.
now apply query_row_map_success_bags_functional_of_contract.
Qed.

Example rank_functionality_composes :
  forall env partition_keys order_keys rank_attribute rank_value input,
    @possible_bag_functional T (success_bags env input) ->
    @possible_bag_functional T
      (success_bags env
        (QExpr_Rank partition_keys order_keys rank_attribute rank_value input)).
Proof.
intros; unfold possible_bag_functional in *.
now apply query_rank_success_bags_functional.
Qed.

End OperatorFunctionality.

Print Assumptions outcome_relation_separation_of_left_success_property.
Print Assumptions outcome_relation_separation_of_right_success_property.
Print Assumptions ordered_outcome_separation_of_left_success_bag_difference.
Print Assumptions ordered_outcome_separation_of_right_success_occurrence_difference.
Print Assumptions tnull_query_program_nth_separation_sound.
