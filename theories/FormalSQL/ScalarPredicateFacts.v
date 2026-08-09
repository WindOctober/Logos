From Stdlib Require Import Bool List String ZArith.
From SQLFS Require Import Bool3 SqlOutcome ValueCore ValuePredicates Values.

Import ListNotations.
Import NullValues.

(** Binary predicates for which SQL NULL in either operand propagates to
    UNKNOWN.  The unary IS predicates deliberately remain outside this class,
    as does IS NOT DISTINCT FROM. *)
Definition strict_binary_predicate (predicate : ValueCore.predicate) : bool :=
  match predicate with
  | PredicateIsNull
  | PredicateIsNotNull
  | PredicateIsTrue
  | PredicateIsNotTrue
  | PredicateIsFalse
  | PredicateIsNotFalse
  | PredicateIsNotDistinctFrom => false
  | _ => true
  end.

(** The six predicates whose ordinary-value semantics is completely determined
    by [order_value_compare].  NUMERIC and floating-point comparisons use
    separate, explicitly typed fallbacks and therefore are not in this class. *)
Definition ordered_comparison_predicate
    (predicate : ValueCore.predicate) : bool :=
  match predicate with
  | PredicateLt | PredicateLte | PredicateGt | PredicateGte
  | PredicateEq | PredicateNeq => true
  | _ => false
  end.

Lemma andb3_unknown_iff : forall left right,
  andb3 left right = unknown3 <->
  (left = unknown3 \/ right = unknown3) /\
  left <> false3 /\ right <> false3.
Proof.
  intros left right.
  destruct left; destruct right; cbn [andb3].
  - split.
    + intro H; discriminate H.
    + intros [[H | H] _]; discriminate H.
  - split.
    + intro H; discriminate H.
    + intros [_ [_ Hright]]; exfalso; apply Hright; reflexivity.
  - split.
    + intro; split; [right; reflexivity | split; discriminate].
    + intro; reflexivity.
  - split.
    + intro H; discriminate H.
    + intros [_ [Hleft _]]; exfalso; apply Hleft; reflexivity.
  - split.
    + intro H; discriminate H.
    + intros [_ [Hleft _]]; exfalso; apply Hleft; reflexivity.
  - split.
    + intro H; discriminate H.
    + intros [_ [Hleft _]]; exfalso; apply Hleft; reflexivity.
  - split.
    + intro; split; [left; reflexivity | split; discriminate].
    + intro; reflexivity.
  - split.
    + intro H; discriminate H.
    + intros [_ [_ Hright]]; exfalso; apply Hright; reflexivity.
  - split.
    + intro; split; [left; reflexivity | split; discriminate].
    + intro; reflexivity.
Qed.

Lemma orb3_unknown_iff : forall left right,
  orb3 left right = unknown3 <->
  (left = unknown3 \/ right = unknown3) /\
  left <> true3 /\ right <> true3.
Proof.
  intros left right.
  destruct left; destruct right; cbn [orb3].
  - split.
    + intro H; discriminate H.
    + intros [_ [Hleft _]]; exfalso; apply Hleft; reflexivity.
  - split.
    + intro H; discriminate H.
    + intros [_ [Hleft _]]; exfalso; apply Hleft; reflexivity.
  - split.
    + intro H; discriminate H.
    + intros [_ [Hleft _]]; exfalso; apply Hleft; reflexivity.
  - split.
    + intro H; discriminate H.
    + intros [[H | H] _]; discriminate H.
  - split.
    + intro H; discriminate H.
    + intros [[H | H] _]; discriminate H.
  - split.
    + intro; split; [right; reflexivity | split; discriminate].
    + intro; reflexivity.
  - split.
    + intro H; discriminate H.
    + intros [_ [_ Hright]]; exfalso; apply Hright; reflexivity.
  - split.
    + intro; split; [left; reflexivity | split; discriminate].
    + intro; reflexivity.
  - split.
    + intro; split; [left; reflexivity | split; discriminate].
    + intro; reflexivity.
Qed.

Lemma negb3_true_iff : forall value,
  negb3 value = true3 <-> value = false3.
Proof.
  intro value; destruct value; cbn [negb3]; split; intro H;
    try discriminate H; reflexivity.
Qed.

Lemma negb3_false_iff : forall value,
  negb3 value = false3 <-> value = true3.
Proof.
  intro value; destruct value; cbn [negb3]; split; intro H;
    try discriminate H; reflexivity.
Qed.

Lemma negb3_unknown_iff : forall value,
  negb3 value = unknown3 <-> value = unknown3.
Proof.
  intro value; destruct value; cbn [negb3]; split; intro H;
    try discriminate H; reflexivity.
Qed.

Lemma value_bool_to_bool3_roundtrip : forall value,
  value_bool_to_bool3 (bool3_to_value_bool value) = value.
Proof.
  intro value; destruct value; reflexivity.
Qed.

Lemma bool3_to_value_bool_injective : forall left right,
  bool3_to_value_bool left = bool3_to_value_bool right -> left = right.
Proof.
  intros left right Heq.
  destruct left, right; try discriminate Heq; reflexivity.
Qed.

Lemma bool3_to_value_bool_is_null_iff : forall value,
  is_null_value (bool3_to_value_bool value) = true <-> value = unknown3.
Proof.
  intro value; destruct value; cbn [bool3_to_value_bool is_null_value];
    split; intro H; try discriminate H; reflexivity.
Qed.

Lemma value_bool_to_bool3_true_iff : forall value,
  value_bool_to_bool3 value = true3 <->
  value = Value_bool (Some true).
Proof.
  intros [string_value | integer | integer32 | integer64 | boolean | single
    | double | numeric | date | time | timestamp | timestamptz];
    try (cbn [value_bool_to_bool3]; split; congruence).
  destruct boolean as [boolean|]; [destruct boolean|];
    cbn [value_bool_to_bool3]; split; congruence.
Qed.

Lemma value_bool_to_bool3_false_iff : forall value,
  value_bool_to_bool3 value = false3 <->
  value = Value_bool (Some false).
Proof.
  intros [string_value | integer | integer32 | integer64 | boolean | single
    | double | numeric | date | time | timestamp | timestamptz];
    try (cbn [value_bool_to_bool3]; split; congruence).
  destruct boolean as [boolean|]; [destruct boolean|];
    cbn [value_bool_to_bool3]; split; congruence.
Qed.

Lemma value_bool_to_bool3_unknown_iff : forall value,
  value_bool_to_bool3 value = unknown3 <->
  value <> Value_bool (Some true) /\
  value <> Value_bool (Some false).
Proof.
  intros [string_value | integer | integer32 | integer64 | boolean | single
    | double | numeric | date | time | timestamp | timestamptz];
    try (cbn [value_bool_to_bool3]; split; [intro; split; discriminate|reflexivity]).
  destruct boolean as [boolean|]; [destruct boolean|];
    cbn [value_bool_to_bool3].
  - split; [discriminate|intros [H _]; exfalso; apply H; reflexivity].
  - split; [discriminate|intros [_ H]; exfalso; apply H; reflexivity].
  - split; [intro; split; discriminate|reflexivity].
Qed.

Lemma default_value_is_typed_null : forall value_type,
  is_null_value (default_value value_type) = true.
Proof.
  intro value_type; destruct value_type; reflexivity.
Qed.

Lemma default_value_preserves_type : forall value_type,
  type_of_value (default_value value_type) = value_type.
Proof.
  intro value_type; destruct value_type; reflexivity.
Qed.

Lemma interp_bool_and_bool3 : forall left right,
  value_bool_to_bool3 (interp_bool_and [left; right]) =
  andb3 (value_bool_to_bool3 left) (value_bool_to_bool3 right).
Proof.
  intros left right; cbn [interp_bool_and].
  apply value_bool_to_bool3_roundtrip.
Qed.

Lemma interp_bool_or_bool3 : forall left right,
  value_bool_to_bool3 (interp_bool_or [left; right]) =
  orb3 (value_bool_to_bool3 left) (value_bool_to_bool3 right).
Proof.
  intros left right; cbn [interp_bool_or].
  apply value_bool_to_bool3_roundtrip.
Qed.

Lemma interp_bool_not_bool3 : forall value,
  value_bool_to_bool3 (interp_bool_not [value]) =
  negb3 (value_bool_to_bool3 value).
Proof.
  intro value; cbn [interp_bool_not].
  apply value_bool_to_bool3_roundtrip.
Qed.

Lemma interp_bool_and_true_iff : forall left right,
  interp_bool_and [left; right] = Value_bool (Some true) <->
  value_bool_to_bool3 left = true3 /\
  value_bool_to_bool3 right = true3.
Proof.
  intros left right.
  change
    (bool3_to_value_bool
       (andb3 (value_bool_to_bool3 left) (value_bool_to_bool3 right)) =
       bool3_to_value_bool true3 <->
     value_bool_to_bool3 left = true3 /\
     value_bool_to_bool3 right = true3).
  destruct (value_bool_to_bool3 left), (value_bool_to_bool3 right);
    cbn [andb3 bool3_to_value_bool]; split; intuition congruence.
Qed.

Lemma interp_bool_and_false_iff : forall left right,
  interp_bool_and [left; right] = Value_bool (Some false) <->
  value_bool_to_bool3 left = false3 \/
  value_bool_to_bool3 right = false3.
Proof.
  intros left right.
  change
    (bool3_to_value_bool
       (andb3 (value_bool_to_bool3 left) (value_bool_to_bool3 right)) =
       bool3_to_value_bool false3 <->
     value_bool_to_bool3 left = false3 \/
     value_bool_to_bool3 right = false3).
  destruct (value_bool_to_bool3 left), (value_bool_to_bool3 right);
    cbn [andb3 bool3_to_value_bool]; split; intuition congruence.
Qed.

Lemma interp_bool_and_unknown_iff : forall left right,
  interp_bool_and [left; right] = Value_bool None <->
  (value_bool_to_bool3 left = unknown3 \/
   value_bool_to_bool3 right = unknown3) /\
  value_bool_to_bool3 left <> false3 /\
  value_bool_to_bool3 right <> false3.
Proof.
  intros left right.
  change
    (bool3_to_value_bool
       (andb3 (value_bool_to_bool3 left) (value_bool_to_bool3 right)) =
       bool3_to_value_bool unknown3 <->
     (value_bool_to_bool3 left = unknown3 \/
      value_bool_to_bool3 right = unknown3) /\
     value_bool_to_bool3 left <> false3 /\
     value_bool_to_bool3 right <> false3).
  split.
  - intro Hresult.
    apply bool3_to_value_bool_injective in Hresult.
    now apply andb3_unknown_iff.
  - intro Hunknown.
    apply f_equal.
    now apply andb3_unknown_iff.
Qed.

Lemma interp_bool_or_true_iff : forall left right,
  interp_bool_or [left; right] = Value_bool (Some true) <->
  value_bool_to_bool3 left = true3 \/
  value_bool_to_bool3 right = true3.
Proof.
  intros left right.
  change
    (bool3_to_value_bool
       (orb3 (value_bool_to_bool3 left) (value_bool_to_bool3 right)) =
       bool3_to_value_bool true3 <->
     value_bool_to_bool3 left = true3 \/
     value_bool_to_bool3 right = true3).
  destruct (value_bool_to_bool3 left), (value_bool_to_bool3 right);
    cbn [orb3 bool3_to_value_bool]; split; intuition congruence.
Qed.

Lemma interp_bool_or_false_iff : forall left right,
  interp_bool_or [left; right] = Value_bool (Some false) <->
  value_bool_to_bool3 left = false3 /\
  value_bool_to_bool3 right = false3.
Proof.
  intros left right.
  change
    (bool3_to_value_bool
       (orb3 (value_bool_to_bool3 left) (value_bool_to_bool3 right)) =
       bool3_to_value_bool false3 <->
     value_bool_to_bool3 left = false3 /\
     value_bool_to_bool3 right = false3).
  destruct (value_bool_to_bool3 left), (value_bool_to_bool3 right);
    cbn [orb3 bool3_to_value_bool]; split; intuition congruence.
Qed.

Lemma interp_bool_or_unknown_iff : forall left right,
  interp_bool_or [left; right] = Value_bool None <->
  (value_bool_to_bool3 left = unknown3 \/
   value_bool_to_bool3 right = unknown3) /\
  value_bool_to_bool3 left <> true3 /\
  value_bool_to_bool3 right <> true3.
Proof.
  intros left right.
  change
    (bool3_to_value_bool
       (orb3 (value_bool_to_bool3 left) (value_bool_to_bool3 right)) =
       bool3_to_value_bool unknown3 <->
     (value_bool_to_bool3 left = unknown3 \/
      value_bool_to_bool3 right = unknown3) /\
     value_bool_to_bool3 left <> true3 /\
     value_bool_to_bool3 right <> true3).
  split.
  - intro Hresult.
    apply bool3_to_value_bool_injective in Hresult.
    now apply orb3_unknown_iff.
  - intro Hunknown.
    apply f_equal.
    now apply orb3_unknown_iff.
Qed.

Lemma interp_bool_not_true_iff : forall value,
  interp_bool_not [value] = Value_bool (Some true) <->
  value_bool_to_bool3 value = false3.
Proof.
  intro value.
  change
    (bool3_to_value_bool (negb3 (value_bool_to_bool3 value)) =
       bool3_to_value_bool true3 <->
     value_bool_to_bool3 value = false3).
  split.
  - intro Hresult; apply bool3_to_value_bool_injective in Hresult.
    now apply negb3_true_iff.
  - intro Hfalse; apply f_equal; now apply negb3_true_iff.
Qed.

Lemma interp_bool_not_false_iff : forall value,
  interp_bool_not [value] = Value_bool (Some false) <->
  value_bool_to_bool3 value = true3.
Proof.
  intro value.
  change
    (bool3_to_value_bool (negb3 (value_bool_to_bool3 value)) =
       bool3_to_value_bool false3 <->
     value_bool_to_bool3 value = true3).
  split.
  - intro Hresult; apply bool3_to_value_bool_injective in Hresult.
    now apply negb3_false_iff.
  - intro Htrue; apply f_equal; now apply negb3_false_iff.
Qed.

Lemma interp_bool_not_unknown_iff : forall value,
  interp_bool_not [value] = Value_bool None <->
  value_bool_to_bool3 value = unknown3.
Proof.
  intro value.
  change
    (bool3_to_value_bool (negb3 (value_bool_to_bool3 value)) =
       bool3_to_value_bool unknown3 <->
     value_bool_to_bool3 value = unknown3).
  split.
  - intro Hresult; apply bool3_to_value_bool_injective in Hresult.
    now apply negb3_unknown_iff.
  - intro Hunknown; apply f_equal; now apply negb3_unknown_iff.
Qed.

Lemma interp_bool_and_wrong_arity : forall values,
  List.length values <> 2%nat -> interp_bool_and values = Value_bool None.
Proof.
  intros values Harity.
  destruct values as [|left values]; [reflexivity|].
  destruct values as [|right values]; [reflexivity|].
  destruct values as [|extra rest].
  - exfalso; apply Harity; reflexivity.
  - reflexivity.
Qed.

Lemma interp_bool_or_wrong_arity : forall values,
  List.length values <> 2%nat -> interp_bool_or values = Value_bool None.
Proof.
  intros values Harity.
  destruct values as [|left values]; [reflexivity|].
  destruct values as [|right values]; [reflexivity|].
  destruct values as [|extra rest].
  - exfalso; apply Harity; reflexivity.
  - reflexivity.
Qed.

Lemma interp_bool_not_wrong_arity : forall values,
  List.length values <> 1%nat -> interp_bool_not values = Value_bool None.
Proof.
  intros values Harity.
  destruct values as [|value values]; [reflexivity|].
  destruct values as [|extra rest].
  - exfalso; apply Harity; reflexivity.
  - reflexivity.
Qed.

Lemma interp_bool_and_bool3_congr : forall left1 right1 left2 right2,
  value_bool_to_bool3 left1 = value_bool_to_bool3 left2 ->
  value_bool_to_bool3 right1 = value_bool_to_bool3 right2 ->
  interp_bool_and [left1; right1] = interp_bool_and [left2; right2].
Proof.
  intros left1 right1 left2 right2 Hleft Hright.
  cbn [interp_bool_and]; now rewrite Hleft, Hright.
Qed.

Lemma interp_bool_or_bool3_congr : forall left1 right1 left2 right2,
  value_bool_to_bool3 left1 = value_bool_to_bool3 left2 ->
  value_bool_to_bool3 right1 = value_bool_to_bool3 right2 ->
  interp_bool_or [left1; right1] = interp_bool_or [left2; right2].
Proof.
  intros left1 right1 left2 right2 Hleft Hright.
  cbn [interp_bool_or]; now rewrite Hleft, Hright.
Qed.

Lemma interp_bool_not_bool3_congr : forall left right,
  value_bool_to_bool3 left = value_bool_to_bool3 right ->
  interp_bool_not [left] = interp_bool_not [right].
Proof.
  intros left right Hvalue.
  cbn [interp_bool_not]; now rewrite Hvalue.
Qed.

Lemma is_null_value_true_elim : forall value,
  is_null_value value = true ->
  (exists typmod,
      value = Value_string (StringValue typmod None)) \/
  value = Value_Z None \/
  value = Value_int32 None \/
  value = Value_int64 None \/
  value = Value_bool None \/
  value = Value_float None \/
  value = Value_double None \/
  value = Value_numeric None \/
  value = Value_date None \/
  value = Value_time None \/
  value = Value_timestamp None \/
  value = Value_timestamptz None.
Proof.
  intros [string_value | [z |] | [integer |] | [bigint |] | [boolean |]
    | [single |] | [double |] | [numeric |] | [date |] | [time |]
    | [timestamp |] | [timestamptz |]] Hnull;
    try discriminate Hnull.
  - destruct string_value as [typmod [text |]]; try discriminate Hnull.
    left; exists typmod; reflexivity.
  - right; left; reflexivity.
  - right; right; left; reflexivity.
  - right; right; right; left; reflexivity.
  - right; right; right; right; left; reflexivity.
  - right; right; right; right; right; left; reflexivity.
  - right; right; right; right; right; right; left; reflexivity.
  - right; right; right; right; right; right; right; left; reflexivity.
  - right; right; right; right; right; right; right; right; left; reflexivity.
  - right; right; right; right; right; right; right; right; right; left;
      reflexivity.
  - right; right; right; right; right; right; right; right; right; right;
      left; reflexivity.
  - right; right; right; right; right; right; right; right; right; right;
      right; reflexivity.
Qed.

Lemma strict_binary_predicate_null_left : forall predicate left right,
  strict_binary_predicate predicate = true ->
  is_null_value left = true ->
  NullValues.interp_predicate predicate [left; right] = unknown3.
Proof.
  intros predicate left right Hstrict Hnull.
  destruct (is_null_value_true_elim left Hnull) as
    [[typmod ->] | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> |
      [-> | [-> | ->]]]]]]]]]]].
  all: destruct predicate; cbn [strict_binary_predicate] in Hstrict;
    try discriminate Hstrict; reflexivity.
Qed.

Lemma strict_binary_predicate_null_right : forall predicate left right,
  strict_binary_predicate predicate = true ->
  is_null_value right = true ->
  NullValues.interp_predicate predicate [left; right] = unknown3.
Proof.
  intros predicate left right Hstrict Hnull.
  destruct (is_null_value_true_elim right Hnull) as
    [[typmod ->] | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> |
      [-> | [-> | ->]]]]]]]]]]].
  all: destruct predicate; cbn [strict_binary_predicate] in Hstrict;
    try discriminate Hstrict.
  all: destruct left as [string_value | [z |] | [integer |] | [bigint |]
    | [boolean |] | [single |] | [double |] | [numeric |] | [date |]
    | [time |] | [timestamp |] | [timestamptz |]]; try reflexivity.
  all: destruct string_value as [left_typmod [text |]]; reflexivity.
Qed.

Lemma strict_binary_predicate_has_arity_two : forall predicate,
  strict_binary_predicate predicate = true ->
  predicate_arity predicate = 2%nat.
Proof.
  intros predicate Hstrict.
  destruct predicate; cbn [strict_binary_predicate predicate_arity] in *;
    try discriminate Hstrict; reflexivity.
Qed.

Lemma strict_binary_predicate_nonunknown_operands_nonnull :
  forall predicate left right,
    strict_binary_predicate predicate = true ->
    NullValues.interp_predicate predicate [left; right] <> unknown3 ->
    is_null_value left = false /\ is_null_value right = false.
Proof.
  intros predicate left right Hstrict Hresult.
  split.
  - destruct (is_null_value left) eqn:Hleft; [|reflexivity].
    exfalso; apply Hresult.
    now apply strict_binary_predicate_null_left.
  - destruct (is_null_value right) eqn:Hright; [|reflexivity].
    exfalso; apply Hresult.
    now apply strict_binary_predicate_null_right.
Qed.

Lemma interp_predicate_wrong_arity_unknown : forall predicate values,
  List.length values <> predicate_arity predicate ->
  NullValues.interp_predicate predicate values = unknown3.
Proof.
  intros predicate values Harity.
  destruct predicate;
    destruct values as [|first [|second [|extra rest]]];
    cbn [predicate_arity NullValues.interp_predicate
      NullPredicates.interp_predicate] in *;
    try (exfalso; apply Harity; reflexivity);
    try reflexivity;
    destruct first as [string_value | [z |] | [integer |] | [bigint |]
      | [boolean |] | [single |] | [double |] | [numeric |] | [date |]
      | [time |] | [timestamp |] | [timestamptz |]]; try reflexivity;
    try (destruct second as [second_string | [second_z |]
      | [second_integer |] | [second_bigint |] | [second_boolean |]
      | [second_single |] | [second_double |] | [second_numeric |]
      | [second_date |] | [second_time |] | [second_timestamp |]
      | [second_timestamptz |]]; try reflexivity);
    try (destruct string_value as [first_typmod [first_text |]]);
    try (destruct second_string as [second_typmod [second_text |]]);
    try (destruct boolean);
    try (destruct second_boolean);
    reflexivity.
Qed.

Lemma interp_predicate_is_null_true_iff : forall value,
  NullValues.interp_predicate PredicateIsNull [value] = true3 <->
  is_null_value value = true.
Proof.
  intro value.
  cbn [NullValues.interp_predicate NullPredicates.interp_predicate].
  destruct (is_null_value value); cbn; split; intro H;
    try discriminate H; reflexivity.
Qed.

Lemma interp_predicate_is_not_null_true_iff : forall value,
  NullValues.interp_predicate PredicateIsNotNull [value] = true3 <->
  is_null_value value = false.
Proof.
  intro value.
  cbn [NullValues.interp_predicate NullPredicates.interp_predicate].
  destruct (is_null_value value); cbn; split; intro H;
    try discriminate H; reflexivity.
Qed.

Lemma interp_predicate_is_null_false_iff : forall value,
  NullValues.interp_predicate PredicateIsNull [value] = false3 <->
  is_null_value value = false.
Proof.
  intro value.
  cbn [NullValues.interp_predicate NullPredicates.interp_predicate].
  destruct (is_null_value value); cbn; split; intro H;
    try discriminate H; reflexivity.
Qed.

Lemma interp_predicate_is_not_null_false_iff : forall value,
  NullValues.interp_predicate PredicateIsNotNull [value] = false3 <->
  is_null_value value = true.
Proof.
  intro value.
  cbn [NullValues.interp_predicate NullPredicates.interp_predicate].
  destruct (is_null_value value); cbn; split; intro H;
    try discriminate H; reflexivity.
Qed.

Lemma interp_predicate_is_not_null_dual : forall value,
  NullValues.interp_predicate PredicateIsNotNull [value] =
  negb3 (NullValues.interp_predicate PredicateIsNull [value]).
Proof.
  intro value.
  cbn [NullValues.interp_predicate NullPredicates.interp_predicate].
  destruct (is_null_value value); reflexivity.
Qed.

Lemma interp_predicate_is_null_never_unknown : forall value,
  NullValues.interp_predicate PredicateIsNull [value] <> unknown3.
Proof.
  intro value.
  cbn [NullValues.interp_predicate NullPredicates.interp_predicate].
  destruct (is_null_value value); discriminate.
Qed.

Lemma interp_predicate_is_not_null_never_unknown : forall value,
  NullValues.interp_predicate PredicateIsNotNull [value] <> unknown3.
Proof.
  intro value.
  cbn [NullValues.interp_predicate NullPredicates.interp_predicate].
  destruct (is_null_value value); discriminate.
Qed.

(** SQL [value = TRUE] and [value IS TRUE] need not return the same Bool3:
    for a nullable Boolean, equality returns UNKNOWN while [IS TRUE] returns
    FALSE.  A filter observes only [Bool.is_true], however, and that acceptance
    decision agrees for every SQL value (including NULL and non-Booleans). *)
Lemma interp_predicate_eq_true_is_true_acceptance : forall value,
  Bool.is_true Bool3
    (NullValues.interp_predicate PredicateEq
      [value; Value_bool (Some true)]) =
  Bool.is_true Bool3
    (NullValues.interp_predicate PredicateIsTrue [value]).
Proof.
  intro value.
  destruct value.
  all: try match goal with
           | string_value : string_value |- _ =>
               destruct string_value as [typmod [text |]]
           | boolean : option bool |- _ =>
               destruct boolean as [boolean |]; [destruct boolean |]
           | optional : option ?A |- _ => destruct optional
           end.
  all: reflexivity.
Qed.

Lemma interp_predicate_is_true_bool3 : forall value,
  NullValues.interp_predicate PredicateIsTrue [bool3_to_value_bool value] =
  match value with true3 => true3 | false3 | unknown3 => false3 end.
Proof.
  intro value; destruct value; reflexivity.
Qed.

Lemma interp_predicate_is_not_true_bool3 : forall value,
  NullValues.interp_predicate PredicateIsNotTrue [bool3_to_value_bool value] =
  match value with true3 => false3 | false3 | unknown3 => true3 end.
Proof.
  intro value; destruct value; reflexivity.
Qed.

Lemma interp_predicate_is_false_bool3 : forall value,
  NullValues.interp_predicate PredicateIsFalse [bool3_to_value_bool value] =
  match value with false3 => true3 | true3 | unknown3 => false3 end.
Proof.
  intro value; destruct value; reflexivity.
Qed.

Lemma interp_predicate_is_not_false_bool3 : forall value,
  NullValues.interp_predicate PredicateIsNotFalse [bool3_to_value_bool value] =
  match value with false3 => false3 | true3 | unknown3 => true3 end.
Proof.
  intro value; destruct value; reflexivity.
Qed.

Lemma interp_predicate_is_true_true_iff : forall value,
  NullValues.interp_predicate PredicateIsTrue [bool3_to_value_bool value] =
    true3 <-> value = true3.
Proof.
  intro value; rewrite interp_predicate_is_true_bool3.
  destruct value; split; congruence.
Qed.

Lemma interp_predicate_is_not_true_true_iff : forall value,
  NullValues.interp_predicate PredicateIsNotTrue [bool3_to_value_bool value] =
    true3 <-> value <> true3.
Proof.
  intro value; rewrite interp_predicate_is_not_true_bool3.
  destruct value; split; congruence.
Qed.

Lemma interp_predicate_is_false_true_iff : forall value,
  NullValues.interp_predicate PredicateIsFalse [bool3_to_value_bool value] =
    true3 <-> value = false3.
Proof.
  intro value; rewrite interp_predicate_is_false_bool3.
  destruct value; split; congruence.
Qed.

Lemma interp_predicate_is_not_false_true_iff : forall value,
  NullValues.interp_predicate PredicateIsNotFalse [bool3_to_value_bool value] =
    true3 <-> value <> false3.
Proof.
  intro value; rewrite interp_predicate_is_not_false_bool3.
  destruct value; split; congruence.
Qed.

Lemma interp_predicate_is_not_true_dual : forall value,
  NullValues.interp_predicate PredicateIsNotTrue [bool3_to_value_bool value] =
  negb3
    (NullValues.interp_predicate PredicateIsTrue [bool3_to_value_bool value]).
Proof.
  intro value.
  rewrite interp_predicate_is_not_true_bool3, interp_predicate_is_true_bool3.
  destruct value; reflexivity.
Qed.

Lemma interp_predicate_is_not_false_dual : forall value,
  NullValues.interp_predicate PredicateIsNotFalse [bool3_to_value_bool value] =
  negb3
    (NullValues.interp_predicate PredicateIsFalse [bool3_to_value_bool value]).
Proof.
  intro value.
  rewrite interp_predicate_is_not_false_bool3, interp_predicate_is_false_bool3.
  destruct value; reflexivity.
Qed.

Lemma interp_is_not_distinct_from_both_null : forall left right,
  is_null_value left = true ->
  is_null_value right = true ->
  NullValues.interp_predicate PredicateIsNotDistinctFrom [left; right] = true3.
Proof.
  intros left right Hleft Hright.
  cbn [NullValues.interp_predicate NullPredicates.interp_predicate].
  rewrite Hleft, Hright; reflexivity.
Qed.

Lemma interp_is_not_distinct_from_exactly_one_null : forall left right,
  (is_null_value left = true /\ is_null_value right = false) \/
  (is_null_value left = false /\ is_null_value right = true) ->
  NullValues.interp_predicate PredicateIsNotDistinctFrom [left; right] = false3.
Proof.
  intros left right [[Hleft Hright] | [Hleft Hright]];
    cbn [NullValues.interp_predicate NullPredicates.interp_predicate];
    rewrite Hleft, Hright; reflexivity.
Qed.

Lemma interp_is_not_distinct_from_never_unknown : forall left right,
  NullValues.interp_predicate PredicateIsNotDistinctFrom [left; right] <>
  unknown3.
Proof.
  intros left right.
  cbn [NullValues.interp_predicate NullPredicates.interp_predicate].
  destruct (is_null_value left), (is_null_value right); cbn;
    try discriminate.
  destruct (same_non_null_value left right); discriminate.
Qed.

Lemma interp_is_not_distinct_from_true_iff : forall left right,
  NullValues.interp_predicate PredicateIsNotDistinctFrom [left; right] = true3
  <->
  (is_null_value left = true /\ is_null_value right = true) \/
  (is_null_value left = false /\ is_null_value right = false /\
   same_non_null_value left right = true).
Proof.
  intros left right.
  cbn [NullValues.interp_predicate NullPredicates.interp_predicate].
  destruct (is_null_value left) eqn:Hleft;
    destruct (is_null_value right) eqn:Hright;
    destruct (same_non_null_value left right) eqn:Hsame;
    cbn; intuition discriminate.
Qed.

Lemma interp_is_not_distinct_from_false_iff : forall left right,
  NullValues.interp_predicate PredicateIsNotDistinctFrom [left; right] = false3
  <->
  (is_null_value left = true /\ is_null_value right = false) \/
  (is_null_value left = false /\ is_null_value right = true) \/
  (is_null_value left = false /\ is_null_value right = false /\
   same_non_null_value left right = false).
Proof.
  intros left right.
  cbn [NullValues.interp_predicate NullPredicates.interp_predicate].
  destruct (is_null_value left) eqn:Hleft;
    destruct (is_null_value right) eqn:Hright;
    destruct (same_non_null_value left right) eqn:Hsame;
    cbn; intuition discriminate.
Qed.

(** A flattened CASE prefix consists of condition/arm pairs, all of whose
    conditions are known not to be TRUE.  This proof-facing relation preserves
    the evaluator's exact FALSE/UNKNOWN short-circuit behavior. *)
Inductive case_prefix_nontrue : list value -> Prop :=
  | CasePrefixNontrueNil : case_prefix_nontrue []
  | CasePrefixNontrueCons : forall condition then_value rest,
      value_bool_to_bool3 condition <> true3 ->
      case_prefix_nontrue rest ->
      case_prefix_nontrue (condition :: then_value :: rest).

(** The runtime counterpart additionally requires every skipped condition to
    have evaluated without error.  A skipped arm's own error is intentionally
    unrestricted because SQL CASE does not observe it. *)
Inductive case_runtime_prefix_skippable :
    list (option sql_runtime_error * value) -> Prop :=
  | CaseRuntimePrefixSkippableNil : case_runtime_prefix_skippable []
  | CaseRuntimePrefixSkippableCons :
      forall condition then_error then_value rest,
        value_bool_to_bool3 condition <> true3 ->
        case_runtime_prefix_skippable rest ->
        case_runtime_prefix_skippable
          ((None, condition) :: (then_error, then_value) :: rest).

Lemma interp_case_values_empty :
  interp_case_values [] = Value_Z None.
Proof.
  reflexivity.
Qed.

Lemma interp_case_values_else : forall else_value,
  interp_case_values [else_value] = else_value.
Proof.
  intro else_value; reflexivity.
Qed.

Lemma interp_case_values_true_branch : forall then_value rest,
  interp_case_values
    (bool3_to_value_bool true3 :: then_value :: rest) = then_value.
Proof.
  intros then_value rest; reflexivity.
Qed.

Lemma interp_case_values_true_branch_if : forall condition then_value rest,
  value_bool_to_bool3 condition = true3 ->
  interp_case_values (condition :: then_value :: rest) = then_value.
Proof.
  intros condition then_value rest Hcondition.
  cbn [interp_case_values]; now rewrite Hcondition.
Qed.

Lemma interp_case_values_skip_nontrue : forall condition then_value rest,
  value_bool_to_bool3 condition <> true3 ->
  interp_case_values (condition :: then_value :: rest) =
  interp_case_values rest.
Proof.
  intros condition then_value rest Hcondition.
  cbn [interp_case_values].
  destruct (value_bool_to_bool3 condition).
  - exfalso; apply Hcondition; reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma interp_case_values_skip_prefix : forall prefix suffix,
  case_prefix_nontrue prefix ->
  interp_case_values (prefix ++ suffix) = interp_case_values suffix.
Proof.
  intros prefix suffix Hprefix; induction Hprefix.
  - reflexivity.
  - cbn [List.app].
    rewrite interp_case_values_skip_nontrue by exact H.
    exact IHHprefix.
Qed.

Lemma interp_case_values_first_true :
  forall prefix condition then_value rest,
    case_prefix_nontrue prefix ->
    value_bool_to_bool3 condition = true3 ->
    interp_case_values
      (prefix ++ condition :: then_value :: rest) = then_value.
Proof.
  intros prefix condition then_value rest Hprefix Hcondition.
  rewrite interp_case_values_skip_prefix by exact Hprefix.
  now apply interp_case_values_true_branch_if.
Qed.

Lemma case_runtime_error_empty :
  case_runtime_error [] = None.
Proof.
  reflexivity.
Qed.

Lemma case_runtime_error_else : forall else_error else_value,
  case_runtime_error [(else_error, else_value)] = else_error.
Proof.
  intros else_error else_value; reflexivity.
Qed.

Lemma case_runtime_error_condition_error : forall error condition then_error
    then_value rest,
  case_runtime_error
    ((Some error, condition) :: (then_error, then_value) :: rest) = Some error.
Proof.
  intros error condition then_error then_value rest; reflexivity.
Qed.

Lemma case_runtime_error_true_branch : forall condition then_error then_value rest,
  value_bool_to_bool3 condition = true3 ->
  case_runtime_error
    ((None, condition) :: (then_error, then_value) :: rest) = then_error.
Proof.
  intros condition then_error then_value rest Hcondition.
  cbn [case_runtime_error]; rewrite Hcondition; reflexivity.
Qed.

Lemma case_runtime_error_skip_nontrue : forall condition then_error then_value rest,
  value_bool_to_bool3 condition <> true3 ->
  case_runtime_error
    ((None, condition) :: (then_error, then_value) :: rest) =
  case_runtime_error rest.
Proof.
  intros condition then_error then_value rest Hcondition.
  cbn [case_runtime_error].
  destruct (value_bool_to_bool3 condition).
  - exfalso; apply Hcondition; reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma case_runtime_error_skipped_arm_irrelevant :
  forall condition first_error first_value second_error second_value rest,
    value_bool_to_bool3 condition <> true3 ->
    case_runtime_error
      ((None, condition) :: (first_error, first_value) :: rest) =
    case_runtime_error
      ((None, condition) :: (second_error, second_value) :: rest).
Proof.
  intros condition first_error first_value second_error second_value rest
    Hcondition.
  rewrite !case_runtime_error_skip_nontrue by exact Hcondition.
  reflexivity.
Qed.

Lemma case_runtime_error_skip_prefix : forall prefix suffix,
  case_runtime_prefix_skippable prefix ->
  case_runtime_error (prefix ++ suffix) = case_runtime_error suffix.
Proof.
  intros prefix suffix Hprefix; induction Hprefix.
  - reflexivity.
  - cbn [List.app].
    rewrite case_runtime_error_skip_nontrue by exact H.
    exact IHHprefix.
Qed.

Lemma case_runtime_error_first_true :
  forall prefix condition then_error then_value rest,
    case_runtime_prefix_skippable prefix ->
    value_bool_to_bool3 condition = true3 ->
    case_runtime_error
      (prefix ++ (None, condition) :: (then_error, then_value) :: rest) =
    then_error.
Proof.
  intros prefix condition then_error then_value rest Hprefix Hcondition.
  rewrite case_runtime_error_skip_prefix by exact Hprefix.
  now apply case_runtime_error_true_branch.
Qed.

Lemma case_runtime_error_some_member : forall observations error,
  case_runtime_error observations = Some error ->
  exists observation,
    In observation observations /\ fst observation = Some error.
Proof.
  fix IH 1.
  intros observations error Herror.
  destruct observations as [|[condition_error condition] observations].
  - discriminate Herror.
  - destruct observations as [|[then_error then_value] rest].
    + cbn [case_runtime_error] in Herror.
      exists (condition_error, condition); split; [now left|exact Herror].
    + cbn [case_runtime_error] in Herror.
      destruct condition_error as [condition_failure|].
      * inversion Herror; subst.
        exists (Some error, condition); split; [now left|reflexivity].
      * destruct (value_bool_to_bool3 condition).
        -- destruct then_error as [then_failure|]; [|discriminate Herror].
           inversion Herror; subst.
           exists (Some error, then_value); split; [now right; left|reflexivity].
        -- destruct (IH rest error Herror) as [observation [Hin Hmember]].
           exists observation; split; [now right; right|exact Hmember].
        -- destruct (IH rest error Herror) as [observation [Hin Hmember]].
           exists observation; split; [now right; right|exact Hmember].
Qed.

Lemma case_runtime_error_none_of_all_none : forall observations,
  Forall (fun observation => fst observation = None) observations ->
  case_runtime_error observations = None.
Proof.
  intros observations Hall.
  destruct (case_runtime_error observations) as [error|] eqn:Herror;
    [|reflexivity].
  destruct (case_runtime_error_some_member observations error Herror)
    as [observation [Hin Hmember]].
  rewrite Forall_forall in Hall.
  specialize (Hall observation Hin).
  rewrite Hmember in Hall; discriminate Hall.
Qed.

Lemma interp_scalar_case_values : forall values,
  interp_scalar_operator ScalarCase values = interp_case_values values.
Proof.
  intro values; reflexivity.
Qed.

Lemma interp_scalar_case_runtime_error : forall observations,
  interp_scalar_operator_runtime_error ScalarCase observations =
  case_runtime_error observations.
Proof.
  intro observations; reflexivity.
Qed.

Lemma interp_predicate_lt_of_order_compare : forall left right ordering,
  NullPredicates.order_value_compare left right = Some ordering ->
  NullValues.interp_predicate PredicateLt [left; right] =
  match ordering with Lt => true3 | Eq | Gt => false3 end.
Proof.
  intros left right ordering Hordering.
  cbn [NullValues.interp_predicate NullPredicates.interp_predicate].
  rewrite Hordering; destruct ordering; reflexivity.
Qed.

Lemma interp_predicate_lte_of_order_compare : forall left right ordering,
  NullPredicates.order_value_compare left right = Some ordering ->
  NullValues.interp_predicate PredicateLte [left; right] =
  match ordering with Gt => false3 | Eq | Lt => true3 end.
Proof.
  intros left right ordering Hordering.
  cbn [NullValues.interp_predicate NullPredicates.interp_predicate].
  rewrite Hordering; destruct ordering; reflexivity.
Qed.

Lemma interp_predicate_gt_of_order_compare : forall left right ordering,
  NullPredicates.order_value_compare left right = Some ordering ->
  NullValues.interp_predicate PredicateGt [left; right] =
  match ordering with Gt => true3 | Eq | Lt => false3 end.
Proof.
  intros left right ordering Hordering.
  cbn [NullValues.interp_predicate NullPredicates.interp_predicate].
  rewrite Hordering; destruct ordering; reflexivity.
Qed.

Lemma interp_predicate_gte_of_order_compare : forall left right ordering,
  NullPredicates.order_value_compare left right = Some ordering ->
  NullValues.interp_predicate PredicateGte [left; right] =
  match ordering with Lt => false3 | Eq | Gt => true3 end.
Proof.
  intros left right ordering Hordering.
  cbn [NullValues.interp_predicate NullPredicates.interp_predicate].
  rewrite Hordering; destruct ordering; reflexivity.
Qed.

Lemma interp_predicate_eq_of_order_compare : forall left right ordering,
  NullPredicates.order_value_compare left right = Some ordering ->
  NullValues.interp_predicate PredicateEq [left; right] =
  match ordering with Eq => true3 | Lt | Gt => false3 end.
Proof.
  intros left right ordering Hordering.
  cbn [NullValues.interp_predicate NullPredicates.interp_predicate].
  rewrite Hordering; destruct ordering; reflexivity.
Qed.

Lemma interp_predicate_neq_of_order_compare : forall left right ordering,
  NullPredicates.order_value_compare left right = Some ordering ->
  NullValues.interp_predicate PredicateNeq [left; right] =
  match ordering with Eq => false3 | Lt | Gt => true3 end.
Proof.
  intros left right ordering Hordering.
  cbn [NullValues.interp_predicate NullPredicates.interp_predicate].
  rewrite Hordering; destruct ordering; reflexivity.
Qed.

Lemma interp_predicate_eq_neq_dual_on_ordered_values : forall left right ordering,
  NullPredicates.order_value_compare left right = Some ordering ->
  NullValues.interp_predicate PredicateNeq [left; right] =
  negb3 (NullValues.interp_predicate PredicateEq [left; right]).
Proof.
  intros left right ordering Hordering.
  rewrite (interp_predicate_eq_of_order_compare left right ordering Hordering).
  rewrite (interp_predicate_neq_of_order_compare left right ordering Hordering).
  destruct ordering; reflexivity.
Qed.

Lemma interp_predicate_lt_true_iff_of_order_compare : forall left right ordering,
  NullPredicates.order_value_compare left right = Some ordering ->
  (NullValues.interp_predicate PredicateLt [left; right] = true3 <->
   ordering = Lt).
Proof.
  intros left right ordering Hordering.
  rewrite (interp_predicate_lt_of_order_compare left right ordering Hordering).
  destruct ordering; cbn; split; congruence.
Qed.

Lemma interp_predicate_lte_true_iff_of_order_compare : forall left right ordering,
  NullPredicates.order_value_compare left right = Some ordering ->
  (NullValues.interp_predicate PredicateLte [left; right] = true3 <->
   ordering <> Gt).
Proof.
  intros left right ordering Hordering.
  rewrite (interp_predicate_lte_of_order_compare left right ordering Hordering).
  destruct ordering; cbn; split; congruence.
Qed.

Lemma interp_predicate_gt_true_iff_of_order_compare : forall left right ordering,
  NullPredicates.order_value_compare left right = Some ordering ->
  (NullValues.interp_predicate PredicateGt [left; right] = true3 <->
   ordering = Gt).
Proof.
  intros left right ordering Hordering.
  rewrite (interp_predicate_gt_of_order_compare left right ordering Hordering).
  destruct ordering; cbn; split; congruence.
Qed.

Lemma interp_predicate_gte_true_iff_of_order_compare : forall left right ordering,
  NullPredicates.order_value_compare left right = Some ordering ->
  (NullValues.interp_predicate PredicateGte [left; right] = true3 <->
   ordering <> Lt).
Proof.
  intros left right ordering Hordering.
  rewrite (interp_predicate_gte_of_order_compare left right ordering Hordering).
  destruct ordering; cbn; split; congruence.
Qed.

Lemma interp_predicate_eq_true_iff_of_order_compare : forall left right ordering,
  NullPredicates.order_value_compare left right = Some ordering ->
  (NullValues.interp_predicate PredicateEq [left; right] = true3 <->
   ordering = Eq).
Proof.
  intros left right ordering Hordering.
  rewrite (interp_predicate_eq_of_order_compare left right ordering Hordering).
  destruct ordering; cbn; split; congruence.
Qed.

Lemma interp_predicate_neq_true_iff_of_order_compare : forall left right ordering,
  NullPredicates.order_value_compare left right = Some ordering ->
  (NullValues.interp_predicate PredicateNeq [left; right] = true3 <->
   ordering <> Eq).
Proof.
  intros left right ordering Hordering.
  rewrite (interp_predicate_neq_of_order_compare left right ordering Hordering).
  destruct ordering; cbn; split; congruence.
Qed.

Lemma interp_predicate_lt_gte_dual_on_ordered_values : forall left right ordering,
  NullPredicates.order_value_compare left right = Some ordering ->
  NullValues.interp_predicate PredicateGte [left; right] =
  negb3 (NullValues.interp_predicate PredicateLt [left; right]).
Proof.
  intros left right ordering Hordering.
  rewrite (interp_predicate_lt_of_order_compare left right ordering Hordering).
  rewrite (interp_predicate_gte_of_order_compare left right ordering Hordering).
  destruct ordering; reflexivity.
Qed.

Lemma interp_predicate_lte_gt_dual_on_ordered_values : forall left right ordering,
  NullPredicates.order_value_compare left right = Some ordering ->
  NullValues.interp_predicate PredicateGt [left; right] =
  negb3 (NullValues.interp_predicate PredicateLte [left; right]).
Proof.
  intros left right ordering Hordering.
  rewrite (interp_predicate_lte_of_order_compare left right ordering Hordering).
  rewrite (interp_predicate_gt_of_order_compare left right ordering Hordering).
  destruct ordering; reflexivity.
Qed.

Lemma interp_ordered_comparison_congr :
  forall predicate left1 right1 left2 right2 ordering,
    ordered_comparison_predicate predicate = true ->
    NullPredicates.order_value_compare left1 right1 = Some ordering ->
    NullPredicates.order_value_compare left2 right2 = Some ordering ->
    NullValues.interp_predicate predicate [left1; right1] =
    NullValues.interp_predicate predicate [left2; right2].
Proof.
  intros predicate left1 right1 left2 right2 ordering Hpredicate Hleft Hright.
  destruct predicate; cbn [ordered_comparison_predicate] in Hpredicate;
    try discriminate Hpredicate;
    cbn [NullValues.interp_predicate NullPredicates.interp_predicate];
    rewrite Hleft, Hright; reflexivity.
Qed.

Lemma scalar_predicate_runtime_error_is_children : forall predicate observations,
  interp_scalar_operator_runtime_error
    (ScalarPredicateValue predicate) observations =
  first_observation_error observations.
Proof.
  intros predicate observations.
  cbn [interp_scalar_operator_runtime_error scalar_operator_local_runtime_error].
  destruct (first_observation_error observations); reflexivity.
Qed.

Lemma scalar_boolean_runtime_error_is_children : forall operator observations,
  interp_scalar_operator_runtime_error (ScalarBoolean operator) observations =
  first_observation_error observations.
Proof.
  intros operator observations; destruct operator;
    cbn [interp_scalar_operator_runtime_error scalar_operator_local_runtime_error];
    destruct (first_observation_error observations); reflexivity.
Qed.
