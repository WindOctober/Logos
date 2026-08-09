From Stdlib Require Import List.
From SQLFS Require Import Bool3 Values.
From Logos Require Import FormalSQL.ScalarPredicateFacts.

Import ListNotations.
Import NullValues.

Check interp_predicate_eq_true_is_true_acceptance.

(** The public lemma is value-generic: it does not require a schema
    conformance or NOT NULL premise. *)
Example arbitrary_value_eq_true_is_true_acceptance (value : value) :
  Bool.is_true Bool3
    (interp_predicate PredicateEq [value; Value_bool (Some true)]) =
  Bool.is_true Bool3
    (interp_predicate PredicateIsTrue [value]).
Proof.
  apply interp_predicate_eq_true_is_true_acceptance.
Qed.

(** In particular, nullable BOOLEAN values have the same filtering decision. *)
Example null_bool_eq_true_is_true_acceptance :
  Bool.is_true Bool3
    (interp_predicate PredicateEq
      [Value_bool None; Value_bool (Some true)]) =
  Bool.is_true Bool3
    (interp_predicate PredicateIsTrue [Value_bool None]).
Proof.
  apply interp_predicate_eq_true_is_true_acceptance.
Qed.

(** The interface intentionally does not assert full Bool3 equality: SQL
    equality on NULL is UNKNOWN, whereas [NULL IS TRUE] is FALSE. *)
Example null_bool_eq_true_is_true_not_bool3_equal :
  interp_predicate PredicateEq
    [Value_bool None; Value_bool (Some true)] <>
  interp_predicate PredicateIsTrue [Value_bool None].
Proof.
  discriminate.
Qed.

Example encoded_coalesce_nonnull_identity
    (value fallback : value) :
  is_null_value value = false ->
  interp_case_values
    [interp_scalar_operator
       (ScalarPredicateValue PredicateIsNotNull) [value];
     value;
     fallback] = value.
Proof.
  intro Hnonnull.
  apply interp_case_values_true_branch_if.
  change
    (value_bool_to_bool3
      (bool3_to_value_bool
        (interp_predicate PredicateIsNotNull [value])) = true3).
  rewrite value_bool_to_bool3_roundtrip.
  now apply interp_predicate_is_not_null_true_iff.
Qed.

Print Assumptions interp_predicate_eq_true_is_true_acceptance.
Print Assumptions interp_case_values_true_branch_if.
Print Assumptions case_runtime_error_true_branch.
