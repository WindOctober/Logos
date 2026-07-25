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

Print Assumptions interp_predicate_eq_true_is_true_acceptance.
