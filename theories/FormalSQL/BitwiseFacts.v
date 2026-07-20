From Stdlib Require Import Lia List Sorting.Permutation String ZArith
  ZArith.ZModOffset ZArith.Zbitwise ZArith.Znat Zmod.Bits.
From SQLFS Require Import GenericInstance SqlOutcome SqlSyntax Values.

Import ListNotations.
Import NullValues.
Open Scope Z_scope.
Open Scope string_scope.

Definition int32_word := bits 32.
Definition int64_word := bits 64.

Definition int32_to_word (x : int32) : int32_word :=
  bits.of_Z 32 (int32_value x).
Definition int64_to_word (x : int64) : int64_word :=
  bits.of_Z 64 (int64_value x).

Definition int32_from_word (word : int32_word) : int32.
Proof.
  refine (Int32 (Zmod.signed word) _).
  pose proof (bits.signed_range' word ltac:(lia)) as Hrange.
  unfold int32_min, int32_max.
  change (-2147483648 <= Zmod.signed word < 2147483648) in Hrange.
  lia.
Defined.

Definition int64_from_word (word : int64_word) : int64.
Proof.
  refine (Int64 (Zmod.signed word) _).
  pose proof (bits.signed_range' word ltac:(lia)) as Hrange.
  unfold int64_min, int64_max.
  change (-9223372036854775808 <= Zmod.signed word <
    9223372036854775808) in Hrange.
  lia.
Defined.

Lemma int32_from_twos_complement_as_word : forall z,
  int32_from_twos_complement z = int32_from_word (bits.of_Z 32 z).
Proof.
  intro z; apply int32_ext.
  unfold int32_from_twos_complement, int32_from_word; cbn [int32_value].
  rewrite bits.signed_of_Z.
  unfold Z.smodulo, Z.omodulo, int32_modulus, int32_min.
  reflexivity.
Qed.

Lemma int64_from_twos_complement_as_word : forall z,
  int64_from_twos_complement z = int64_from_word (bits.of_Z 64 z).
Proof.
  intro z; apply int64_ext.
  unfold int64_from_twos_complement, int64_from_word; cbn [int64_value].
  rewrite bits.signed_of_Z.
  unfold Z.smodulo, Z.omodulo, int64_modulus, int64_min.
  reflexivity.
Qed.

Lemma int32_from_twos_complement_value : forall x,
  int32_from_twos_complement (int32_value x) = x.
Proof.
  intro x; apply int32_ext.
  unfold int32_from_twos_complement; cbn [int32_value].
  rewrite Z.mod_small.
  - lia.
  - pose proof (int32_range x).
    unfold int32_min, int32_max, int32_modulus in *; lia.
Qed.

Lemma int64_from_twos_complement_value : forall x,
  int64_from_twos_complement (int64_value x) = x.
Proof.
  intro x; apply int64_ext.
  unfold int64_from_twos_complement; cbn [int64_value].
  rewrite Z.mod_small.
  - lia.
  - pose proof (int64_range x).
    unfold int64_min, int64_max, int64_modulus in *; lia.
Qed.

Lemma bits_of_Z_land : forall n x y,
  0 <= n ->
  bits.of_Z n (Z.land x y) =
    Zmod.and (bits.of_Z n x) (bits.of_Z n y).
Proof.
  intros n x y Hn; apply Zmod.to_Z_inj.
  rewrite bits.unsigned_of_Z, bits.unsigned_and,
    !bits.unsigned_of_Z.
  apply Z.bits_inj; intro i.
  destruct (Z.ltb_spec i 0) as [Hi | Hi].
  - repeat rewrite Z.testbit_neg_r by lia; reflexivity.
  - destruct (Z.ltb_spec i n) as [Hin | Hin].
    + repeat rewrite ?Z.land_spec, ?Z.mod_pow2_bits_low by lia.
      reflexivity.
    + rewrite Z.mod_pow2_bits_high by lia.
      rewrite Z.land_spec.
      rewrite !Z.mod_pow2_bits_high by lia.
      reflexivity.
Qed.

Lemma bits_of_Z_lor : forall n x y,
  0 <= n ->
  bits.of_Z n (Z.lor x y) =
    Zmod.or (bits.of_Z n x) (bits.of_Z n y).
Proof.
  intros n x y Hn; apply Zmod.to_Z_inj.
  rewrite bits.unsigned_of_Z, bits.unsigned_or,
    !bits.unsigned_of_Z.
  apply Z.bits_inj; intro i.
  destruct (Z.ltb_spec i 0) as [Hi | Hi].
  - repeat rewrite Z.testbit_neg_r by lia; reflexivity.
  - destruct (Z.ltb_spec i n) as [Hin | Hin].
    + repeat rewrite ?Z.lor_spec, ?Z.mod_pow2_bits_low by lia.
      reflexivity.
    + rewrite Z.mod_pow2_bits_high by lia.
      rewrite Z.lor_spec.
      rewrite !Z.mod_pow2_bits_high by lia.
      reflexivity.
Qed.

Lemma int32_bit_and_as_word : forall x y,
  int32_bit_and x y =
    int32_from_word (Zmod.and (int32_to_word x) (int32_to_word y)).
Proof.
  intros x y.
  unfold int32_to_word.
  rewrite <- (bits_of_Z_land 32 (int32_value x) (int32_value y)) by lia.
  rewrite <- int32_from_twos_complement_as_word.
  change (int32_bit_and x y =
    int32_from_twos_complement (int32_value (int32_bit_and x y))).
  symmetry; apply int32_from_twos_complement_value.
Qed.

Lemma int32_bit_or_as_word : forall x y,
  int32_bit_or x y =
    int32_from_word (Zmod.or (int32_to_word x) (int32_to_word y)).
Proof.
  intros x y.
  unfold int32_to_word.
  rewrite <- (bits_of_Z_lor 32 (int32_value x) (int32_value y)) by lia.
  rewrite <- int32_from_twos_complement_as_word.
  change (int32_bit_or x y =
    int32_from_twos_complement (int32_value (int32_bit_or x y))).
  symmetry; apply int32_from_twos_complement_value.
Qed.

Lemma int64_bit_and_as_word : forall x y,
  int64_bit_and x y =
    int64_from_word (Zmod.and (int64_to_word x) (int64_to_word y)).
Proof.
  intros x y.
  unfold int64_to_word.
  rewrite <- (bits_of_Z_land 64 (int64_value x) (int64_value y)) by lia.
  rewrite <- int64_from_twos_complement_as_word.
  change (int64_bit_and x y =
    int64_from_twos_complement (int64_value (int64_bit_and x y))).
  symmetry; apply int64_from_twos_complement_value.
Qed.

Lemma int64_bit_or_as_word : forall x y,
  int64_bit_or x y =
    int64_from_word (Zmod.or (int64_to_word x) (int64_to_word y)).
Proof.
  intros x y.
  unfold int64_to_word.
  rewrite <- (bits_of_Z_lor 64 (int64_value x) (int64_value y)) by lia.
  rewrite <- int64_from_twos_complement_as_word.
  change (int64_bit_or x y =
    int64_from_twos_complement (int64_value (int64_bit_or x y))).
  symmetry; apply int64_from_twos_complement_value.
Qed.

Lemma int32_bit_and_associative : forall x y z,
  int32_bit_and x (int32_bit_and y z) =
  int32_bit_and (int32_bit_and x y) z.
Proof.
  intros; apply int32_ext; cbn [int32_bit_and int32_value].
  apply Z.land_assoc.
Qed.

Lemma int32_bit_or_associative : forall x y z,
  int32_bit_or x (int32_bit_or y z) =
  int32_bit_or (int32_bit_or x y) z.
Proof.
  intros; apply int32_ext; cbn [int32_bit_or int32_value].
  apply Z.lor_assoc.
Qed.

Lemma int64_bit_and_associative : forall x y z,
  int64_bit_and x (int64_bit_and y z) =
  int64_bit_and (int64_bit_and x y) z.
Proof.
  intros; apply int64_ext; cbn [int64_bit_and int64_value].
  apply Z.land_assoc.
Qed.

Lemma int64_bit_or_associative : forall x y z,
  int64_bit_or x (int64_bit_or y z) =
  int64_bit_or (int64_bit_or x y) z.
Proof.
  intros; apply int64_ext; cbn [int64_bit_or int64_value].
  apply Z.lor_assoc.
Qed.

Lemma int32_bit_and_commutative : forall x y,
  int32_bit_and x y = int32_bit_and y x.
Proof.
  intros; apply int32_ext; cbn [int32_bit_and int32_value].
  apply Z.land_comm.
Qed.

Lemma int32_bit_or_commutative : forall x y,
  int32_bit_or x y = int32_bit_or y x.
Proof.
  intros; apply int32_ext; cbn [int32_bit_or int32_value].
  apply Z.lor_comm.
Qed.

Lemma int64_bit_and_commutative : forall x y,
  int64_bit_and x y = int64_bit_and y x.
Proof.
  intros; apply int64_ext; cbn [int64_bit_and int64_value].
  apply Z.land_comm.
Qed.

Lemma int64_bit_or_commutative : forall x y,
  int64_bit_or x y = int64_bit_or y x.
Proof.
  intros; apply int64_ext; cbn [int64_bit_or int64_value].
  apply Z.lor_comm.
Qed.

Lemma int32_bit_and_idempotent : forall x, int32_bit_and x x = x.
Proof.
  intro x; apply int32_ext; cbn [int32_bit_and int32_value].
  apply Z.land_diag.
Qed.

Lemma int32_bit_or_idempotent : forall x, int32_bit_or x x = x.
Proof.
  intro x; apply int32_ext; cbn [int32_bit_or int32_value].
  apply Z.lor_diag.
Qed.

Lemma int64_bit_and_idempotent : forall x, int64_bit_and x x = x.
Proof.
  intro x; apply int64_ext; cbn [int64_bit_and int64_value].
  apply Z.land_diag.
Qed.

Lemma int64_bit_or_idempotent : forall x, int64_bit_or x x = x.
Proof.
  intro x; apply int64_ext; cbn [int64_bit_or int64_value].
  apply Z.lor_diag.
Qed.

Lemma int32_bit_and_closed : forall x y,
  int32_min <= int32_value (int32_bit_and x y) <= int32_max.
Proof. intros; cbn [int32_bit_and int32_value]; apply int32_land_in_range. Qed.

Lemma int32_bit_or_closed : forall x y,
  int32_min <= int32_value (int32_bit_or x y) <= int32_max.
Proof. intros; cbn [int32_bit_or int32_value]; apply int32_lor_in_range. Qed.

Lemma int64_bit_and_closed : forall x y,
  int64_min <= int64_value (int64_bit_and x y) <= int64_max.
Proof. intros; cbn [int64_bit_and int64_value]; apply int64_land_in_range. Qed.

Lemma int64_bit_or_closed : forall x y,
  int64_min <= int64_value (int64_bit_or x y) <= int64_max.
Proof. intros; cbn [int64_bit_or int64_value]; apply int64_lor_in_range. Qed.

(** PostgreSQL integral BIT_AND/BIT_OR ignore NULL inputs and return NULL when
    there is no non-NULL transition value. *)

(** Bitwise transitions are total.  The explicit local branches must remain
    error-free, while errors raised while evaluating an argument still win. *)

(** The optional state is the aggregate transition state: [None] means that a
    partition has no non-NULL input.  These lemmas cover empty, all-NULL, and
    nonempty partitions without introducing a bitwise identity value. *)
Lemma combine_nullable_state_associative : forall A (op : A -> A -> A),
  (forall x y z, op x (op y z) = op (op x y) z) ->
  forall x y z,
    combine_nullable_state op x (combine_nullable_state op y z) =
    combine_nullable_state op (combine_nullable_state op x y) z.
Proof.
  intros A op Hassoc [x|] [y|] [z|]; cbn; try reflexivity.
  now rewrite Hassoc.
Qed.

Lemma combine_nullable_state_commutative : forall A (op : A -> A -> A),
  (forall x y, op x y = op y x) ->
  forall x y,
    combine_nullable_state op x y = combine_nullable_state op y x.
Proof.
  intros A op Hcomm [x|] [y|]; cbn; try reflexivity.
  now rewrite Hcomm.
Qed.

Lemma fold_nullable_state_partition : forall A (op : A -> A -> A),
  (forall x y z, op x (op y z) = op (op x y) z) ->
  forall left right,
    fold_nullable_state op (left ++ right) =
    combine_nullable_state op
      (fold_nullable_state op left) (fold_nullable_state op right).
Proof.
  intros A op Hassoc left; induction left as [|x left IH]; intro right.
  - reflexivity.
  - cbn; rewrite IH.
    change
      (combine_nullable_state op (Some x)
        (combine_nullable_state op (fold_nullable_state op left)
          (fold_nullable_state op right)) =
       combine_nullable_state op
        (combine_nullable_state op (Some x) (fold_nullable_state op left))
        (fold_nullable_state op right)).
    apply combine_nullable_state_associative; exact Hassoc.
Qed.

Lemma fold_nullable_state_permutation : forall A (op : A -> A -> A),
  (forall x y z, op x (op y z) = op (op x y) z) ->
  (forall x y, op x y = op y x) ->
  forall left right,
    Permutation left right ->
    fold_nullable_state op left = fold_nullable_state op right.
Proof.
  intros A op Hassoc Hcomm left right Hperm.
  induction Hperm as [|x left right _ IH|x y rest|left middle right _ IH1 _ IH2].
  - reflexivity.
  - cbn; now rewrite IH.
  - change
      (combine_nullable_state op (Some y)
        (combine_nullable_state op (Some x) (fold_nullable_state op rest)) =
       combine_nullable_state op (Some x)
        (combine_nullable_state op (Some y) (fold_nullable_state op rest))).
    rewrite !combine_nullable_state_associative by exact Hassoc.
    rewrite (combine_nullable_state_commutative A op Hcomm (Some y) (Some x)).
    reflexivity.
  - now rewrite IH1, IH2.
Qed.

Lemma fold_nullable_state_adjacent_duplicate : forall A (op : A -> A -> A),
  (forall x y z, op x (op y z) = op (op x y) z) ->
  (forall x, op x x = x) ->
  forall prefix suffix x,
    fold_nullable_state op (prefix ++ x :: x :: suffix) =
    fold_nullable_state op (prefix ++ x :: suffix).
Proof.
  intros A op Hassoc Hidem prefix suffix x.
  rewrite !fold_nullable_state_partition by exact Hassoc.
  assert (Hhead :
    fold_nullable_state op (x :: x :: suffix) =
    fold_nullable_state op (x :: suffix)).
  {
    cbn.
    destruct (fold_nullable_state op suffix) as [state|] eqn:Hsuffix; cbn.
    - now rewrite Hassoc, Hidem.
    - now rewrite Hidem.
  }
  now rewrite Hhead.
Qed.

Lemma int32_bit_and_fold_partition : forall left right,
  fold_nullable_state int32_bit_and (left ++ right) =
  combine_nullable_state int32_bit_and
    (fold_nullable_state int32_bit_and left)
    (fold_nullable_state int32_bit_and right).
Proof. apply fold_nullable_state_partition, int32_bit_and_associative. Qed.

Lemma int32_bit_or_fold_partition : forall left right,
  fold_nullable_state int32_bit_or (left ++ right) =
  combine_nullable_state int32_bit_or
    (fold_nullable_state int32_bit_or left)
    (fold_nullable_state int32_bit_or right).
Proof. apply fold_nullable_state_partition, int32_bit_or_associative. Qed.

Lemma int64_bit_and_fold_partition : forall left right,
  fold_nullable_state int64_bit_and (left ++ right) =
  combine_nullable_state int64_bit_and
    (fold_nullable_state int64_bit_and left)
    (fold_nullable_state int64_bit_and right).
Proof. apply fold_nullable_state_partition, int64_bit_and_associative. Qed.

Lemma int64_bit_or_fold_partition : forall left right,
  fold_nullable_state int64_bit_or (left ++ right) =
  combine_nullable_state int64_bit_or
    (fold_nullable_state int64_bit_or left)
    (fold_nullable_state int64_bit_or right).
Proof. apply fold_nullable_state_partition, int64_bit_or_associative. Qed.

Lemma int32_bit_and_fold_permutation : forall left right,
  Permutation left right ->
  fold_nullable_state int32_bit_and left =
  fold_nullable_state int32_bit_and right.
Proof.
  apply fold_nullable_state_permutation;
    [apply int32_bit_and_associative | apply int32_bit_and_commutative].
Qed.

Lemma int32_bit_or_fold_permutation : forall left right,
  Permutation left right ->
  fold_nullable_state int32_bit_or left =
  fold_nullable_state int32_bit_or right.
Proof.
  apply fold_nullable_state_permutation;
    [apply int32_bit_or_associative | apply int32_bit_or_commutative].
Qed.

Lemma int64_bit_and_fold_permutation : forall left right,
  Permutation left right ->
  fold_nullable_state int64_bit_and left =
  fold_nullable_state int64_bit_and right.
Proof.
  apply fold_nullable_state_permutation;
    [apply int64_bit_and_associative | apply int64_bit_and_commutative].
Qed.

Lemma int64_bit_or_fold_permutation : forall left right,
  Permutation left right ->
  fold_nullable_state int64_bit_or left =
  fold_nullable_state int64_bit_or right.
Proof.
  apply fold_nullable_state_permutation;
    [apply int64_bit_or_associative | apply int64_bit_or_commutative].
Qed.

Lemma int32_bit_and_fold_distinct_invariant : forall prefix suffix x,
  fold_nullable_state int32_bit_and (prefix ++ x :: x :: suffix) =
  fold_nullable_state int32_bit_and (prefix ++ x :: suffix).
Proof.
  apply fold_nullable_state_adjacent_duplicate;
    [apply int32_bit_and_associative | apply int32_bit_and_idempotent].
Qed.

Lemma int32_bit_or_fold_distinct_invariant : forall prefix suffix x,
  fold_nullable_state int32_bit_or (prefix ++ x :: x :: suffix) =
  fold_nullable_state int32_bit_or (prefix ++ x :: suffix).
Proof.
  apply fold_nullable_state_adjacent_duplicate;
    [apply int32_bit_or_associative | apply int32_bit_or_idempotent].
Qed.

Lemma int64_bit_and_fold_distinct_invariant : forall prefix suffix x,
  fold_nullable_state int64_bit_and (prefix ++ x :: x :: suffix) =
  fold_nullable_state int64_bit_and (prefix ++ x :: suffix).
Proof.
  apply fold_nullable_state_adjacent_duplicate;
    [apply int64_bit_and_associative | apply int64_bit_and_idempotent].
Qed.

Lemma int64_bit_or_fold_distinct_invariant : forall prefix suffix x,
  fold_nullable_state int64_bit_or (prefix ++ x :: x :: suffix) =
  fold_nullable_state int64_bit_or (prefix ++ x :: suffix).
Proof.
  apply fold_nullable_state_adjacent_duplicate;
    [apply int64_bit_or_associative | apply int64_bit_or_idempotent].
Qed.
