From Stdlib Require Import Ascii Bool Lia List String ZArith.
From SQLFS Require Import Bool3 OrderedSet SqlOutcome ValueCore ValuePredicates
  ValueString ValueTemporal ValueTextInteger Values.

Import ListNotations.
Import NullValues.
Open Scope Z_scope.

(** Descriptor decoding is a partial interface: bounded typmods require a
    positive declared width, while the other constructors have canonical
    descriptors. *)
Lemma string_typmod_descriptor_roundtrip : forall typmod,
  (match typmod with
   | StringVarcharN width | StringChar width => (0 < width)%nat
   | StringText | StringVarchar | StringBpchar => True
   end) ->
  string_typmod_from_codes
    (string_typmod_tag typmod) (string_typmod_length typmod) = Some typmod.
Proof.
  intros [| | limit | width |] Hvalid; cbn
    [string_typmod_from_codes string_typmod_tag string_typmod_length].
  - reflexivity.
  - reflexivity.
  - assert (Hpositive : (0 <? Z.of_nat limit) = true).
    { apply Z.ltb_lt; lia. }
    rewrite Hpositive, Nat2Z.id; reflexivity.
  - assert (Hpositive : (0 <? Z.of_nat width) = true).
    { apply Z.ltb_lt; lia. }
    rewrite Hpositive, Nat2Z.id; reflexivity.
  - reflexivity.
Qed.

Lemma string_fits_bounded_typmod_from_length :
  forall typmod width value length,
    (typmod = StringVarcharN width \/ typmod = StringChar width) ->
    utf8_character_length value = Some length ->
    string_fits_typmod typmod value = Nat.leb length width.
Proof.
  intros typmod width value length [-> | ->] Hlength;
    unfold string_fits_typmod; rewrite Hlength; reflexivity.
Qed.

Lemma string_fits_unbounded_typmod_from_length :
  forall typmod value length,
    (typmod = StringText \/ typmod = StringVarchar \/ typmod = StringBpchar) ->
    utf8_character_length value = Some length ->
    string_fits_typmod typmod value = true.
Proof.
  intros typmod value length [-> | [-> | ->]] Hlength;
    unfold string_fits_typmod; rewrite Hlength; reflexivity.
Qed.

(** Assignment coercion is deliberately separate from explicit casts.  These
    inversion laws expose UTF-8 validation, bounded-width checks, and the
    PostgreSQL exception that permits over-width trailing spaces. *)
Lemma string_assignment_coerce_textual_success_iff :
  forall typmod value result,
    (typmod = StringText \/ typmod = StringVarchar) ->
    string_assignment_coerce typmod value = Some result <->
    string_is_valid_utf8 value = true /\ result = value.
Proof.
  intros typmod value result [-> | ->].
  - unfold string_assignment_coerce.
    destruct (string_is_valid_utf8 value) eqn:Hvalid; cbn; split.
    + intro Hresult; inversion Hresult; subst; split; reflexivity.
    + intros [_ ->]; reflexivity.
    + intro Hresult; discriminate Hresult.
    + intros [Hrequired _]; discriminate Hrequired.
  - unfold string_assignment_coerce.
    destruct (string_is_valid_utf8 value) eqn:Hvalid; cbn; split.
    + intro Hresult; inversion Hresult; subst; split; reflexivity.
    + intros [_ ->]; reflexivity.
    + intro Hresult; discriminate Hresult.
    + intros [Hrequired _]; discriminate Hrequired.
Qed.

Lemma string_assignment_coerce_bpchar_success_iff :
  forall value result,
    string_assignment_coerce StringBpchar value = Some result <->
    string_is_valid_utf8 value = true /\
    result = string_canonical_value StringBpchar value.
Proof.
  intros value result; unfold string_assignment_coerce.
  destruct (string_is_valid_utf8 value) eqn:Hvalid; cbn; split.
  - intro Hresult; inversion Hresult; subst; split; reflexivity.
  - intros [_ ->]; reflexivity.
  - intro Hresult; discriminate Hresult.
  - intros [Hrequired _]; discriminate Hrequired.
Qed.

Lemma string_assignment_coerce_varchar_n_success_iff :
  forall width value length result,
    utf8_character_length value = Some length ->
    string_assignment_coerce (StringVarcharN width) value = Some result <->
    (Nat.leb length width = true /\ result = value) \/
    (Nat.leb length width = false /\
     string_all_spaces (string_drop width value) = true /\
     result = string_take width value).
Proof.
  intros width value length result Hlength.
  unfold string_assignment_coerce; rewrite Hlength.
  destruct (Nat.leb length width) eqn:Hfits;
    destruct (string_all_spaces (string_drop width value)) eqn:Hspaces;
    cbn; split; intro Hresult; try discriminate Hresult.
  - inversion Hresult; subst; left; split; reflexivity.
  - destruct Hresult as [[_ ->] | [Hnot _]]; [reflexivity | discriminate].
  - inversion Hresult; subst; left; split; reflexivity.
  - destruct Hresult as [[_ ->] | [Hnot _]]; [reflexivity | discriminate].
  - inversion Hresult; subst; right; repeat split; reflexivity.
  - destruct Hresult as [[Hyes _] | [_ [_ ->]]];
      [discriminate | reflexivity].
  - destruct Hresult as [[Hyes _] | [_ [Hspace _]]]; discriminate.
Qed.

Lemma string_assignment_coerce_char_success_iff :
  forall width value length result,
    utf8_character_length value = Some length ->
    string_assignment_coerce (StringChar width) value = Some result <->
    (Nat.leb length width = true /\
     result = string_canonical_value (StringChar width) value) \/
    (Nat.leb length width = false /\
     string_all_spaces (string_drop width value) = true /\
     result = string_canonical_value (StringChar width) value).
Proof.
  intros width value length result Hlength.
  unfold string_assignment_coerce; rewrite Hlength.
  destruct (Nat.leb length width) eqn:Hfits;
    destruct (string_all_spaces (string_drop width value)) eqn:Hspaces;
    cbn; split; intro Hresult; try discriminate Hresult.
  - inversion Hresult; subst; left; split; reflexivity.
  - destruct Hresult as [[_ ->] | [Hnot _]]; [reflexivity | discriminate].
  - inversion Hresult; subst; left; split; reflexivity.
  - destruct Hresult as [[_ ->] | [Hnot _]]; [reflexivity | discriminate].
  - inversion Hresult; subst; right; repeat split; reflexivity.
  - destruct Hresult as [[Hyes _] | [_ [_ ->]]];
      [discriminate | reflexivity].
  - destruct Hresult as [[Hyes _] | [_ [Hspace _]]]; discriminate.
Qed.

Lemma interp_string_cast_and_coercion_nonnull :
  forall source target value tag length,
    string_typmod_from_codes tag length = Some target ->
    interp_cast_string_explicit
      [Value_string (StringValue source (Some value));
       Value_Z (Some tag); Value_Z (Some length)] =
      Value_string
        (StringValue target (Some (string_cast_value source target value))) /\
    interp_coerce_string_implicit
      [Value_string (StringValue source (Some value));
       Value_Z (Some tag); Value_Z (Some length)] =
      Value_string
        (StringValue target (Some (string_cast_value source target value))).
Proof.
  intros source target value tag length Htarget.
  cbn [interp_cast_string_explicit interp_coerce_string_implicit].
  rewrite Htarget; split; reflexivity.
Qed.

Lemma interp_string_cast_and_coercion_null :
  forall source target tag length,
    string_typmod_from_codes tag length = Some target ->
    interp_cast_string_explicit
      [Value_string (StringValue source None);
       Value_Z (Some tag); Value_Z (Some length)] =
      Value_string (StringValue target None) /\
    interp_coerce_string_implicit
      [Value_string (StringValue source None);
       Value_Z (Some tag); Value_Z (Some length)] =
      Value_string (StringValue target None).
Proof.
  intros source target tag length Htarget.
  cbn [interp_cast_string_explicit interp_coerce_string_implicit].
  rewrite Htarget; split; reflexivity.
Qed.

Lemma interp_string_cast_invalid_descriptor :
  forall source payload tag length,
    string_typmod_from_codes tag length = None ->
    interp_cast_string_explicit
      [Value_string (StringValue source payload);
       Value_Z (Some tag); Value_Z (Some length)] =
      Value_string (StringValue StringText None) /\
    interp_coerce_string_implicit
      [Value_string (StringValue source payload);
       Value_Z (Some tag); Value_Z (Some length)] =
      Value_string (StringValue StringText None).
Proof.
  intros source payload tag length Htarget.
  destruct payload as [value |];
    cbn [interp_cast_string_explicit interp_coerce_string_implicit];
    rewrite Htarget; split; reflexivity.
Qed.

Lemma string_cast_and_coercion_local_runtime_safe : forall cast values,
  (cast = ScalarCastStringExplicit \/ cast = ScalarCoerceStringImplicit) ->
  scalar_operator_local_runtime_error (ScalarCast cast) values = None.
Proof.
  intros cast values [-> | ->]; reflexivity.
Qed.

Lemma string_to_int32_cast_success : forall source input result,
  parse_text_int32 (string_cast_source_value source input) =
    TextIntegerValue result ->
  interp_scalar_operator (ScalarCast ScalarCastStringToInt32)
    [Value_string (StringValue source (Some input))] =
      Value_int32 (Some result) /\
  scalar_operator_local_runtime_error
    (ScalarCast ScalarCastStringToInt32)
    [Value_string (StringValue source (Some input))] = None.
Proof.
  intros source input result Hparse.
  unfold interp_scalar_operator, scalar_operator_local_runtime_error.
  unfold interp_cast_string_to_int32, cast_string_to_int32_runtime_error.
  cbn [StringValue].
  rewrite Hparse; split; reflexivity.
Qed.

Lemma string_to_int64_cast_success : forall source input result,
  parse_text_int64 (string_cast_source_value source input) =
    TextIntegerValue result ->
  interp_scalar_operator (ScalarCast ScalarCastStringToInt64)
    [Value_string (StringValue source (Some input))] =
      Value_int64 (Some result) /\
  scalar_operator_local_runtime_error
    (ScalarCast ScalarCastStringToInt64)
    [Value_string (StringValue source (Some input))] = None.
Proof.
  intros source input result Hparse.
  unfold interp_scalar_operator, scalar_operator_local_runtime_error.
  unfold interp_cast_string_to_int64, cast_string_to_int64_runtime_error.
  cbn [StringValue].
  rewrite Hparse; split; reflexivity.
Qed.

Lemma string_to_int32_cast_invalid : forall source input,
  parse_text_int32 (string_cast_source_value source input) =
    TextIntegerInvalid ->
  scalar_operator_local_runtime_error
    (ScalarCast ScalarCastStringToInt32)
    [Value_string (StringValue source (Some input))] =
      Some (DataException InvalidTextRepresentation).
Proof.
  intros source input Hparse.
  unfold scalar_operator_local_runtime_error, cast_string_to_int32_runtime_error.
  cbn [StringValue].
  now rewrite Hparse.
Qed.

Lemma string_to_int64_cast_invalid : forall source input,
  parse_text_int64 (string_cast_source_value source input) =
    TextIntegerInvalid ->
  scalar_operator_local_runtime_error
    (ScalarCast ScalarCastStringToInt64)
    [Value_string (StringValue source (Some input))] =
      Some (DataException InvalidTextRepresentation).
Proof.
  intros source input Hparse.
  unfold scalar_operator_local_runtime_error, cast_string_to_int64_runtime_error.
  cbn [StringValue].
  now rewrite Hparse.
Qed.

Lemma string_to_int32_cast_out_of_range : forall source input,
  parse_text_int32 (string_cast_source_value source input) =
    TextIntegerOutOfRange ->
  scalar_operator_local_runtime_error
    (ScalarCast ScalarCastStringToInt32)
    [Value_string (StringValue source (Some input))] =
      Some (DataException NumericValueOutOfRange).
Proof.
  intros source input Hparse.
  unfold scalar_operator_local_runtime_error, cast_string_to_int32_runtime_error.
  cbn [StringValue].
  now rewrite Hparse.
Qed.

Lemma string_to_int64_cast_out_of_range : forall source input,
  parse_text_int64 (string_cast_source_value source input) =
    TextIntegerOutOfRange ->
  scalar_operator_local_runtime_error
    (ScalarCast ScalarCastStringToInt64)
    [Value_string (StringValue source (Some input))] =
      Some (DataException NumericValueOutOfRange).
Proof.
  intros source input Hparse.
  unfold scalar_operator_local_runtime_error, cast_string_to_int64_runtime_error.
  cbn [StringValue].
  now rewrite Hparse.
Qed.

Lemma string_to_integer_casts_preserve_null : forall source,
  interp_scalar_operator (ScalarCast ScalarCastStringToInt32)
    [Value_string (StringValue source None)] = Value_int32 None /\
  scalar_operator_local_runtime_error
    (ScalarCast ScalarCastStringToInt32)
    [Value_string (StringValue source None)] = None /\
  interp_scalar_operator (ScalarCast ScalarCastStringToInt64)
    [Value_string (StringValue source None)] = Value_int64 None /\
  scalar_operator_local_runtime_error
    (ScalarCast ScalarCastStringToInt64)
    [Value_string (StringValue source None)] = None.
Proof. intros source; repeat split; reflexivity. Qed.

(** Concatenation consumes a list of already-evaluated string values.  The
    cons laws support proofs without unfolding the recursive payload fold. *)
Lemma string_concat_payload_empty :
  string_concat_payload [] = Some EmptyString.
Proof. reflexivity. Qed.

Lemma string_concat_payload_nonnull_cons_iff :
  forall typmod value rest result,
    string_concat_payload
      (Value_string (StringValue typmod (Some value)) :: rest) = Some result <->
    exists suffix,
      string_concat_payload rest = Some suffix /\
      result = String.append (string_cast_source_value typmod value) suffix.
Proof.
  intros typmod value rest result; cbn [string_concat_payload].
  destruct (string_concat_payload rest) as [suffix |] eqn:Hsuffix; split.
  - intro Hresult; inversion Hresult; subst.
    exists suffix; split; reflexivity.
  - intros [other [Hother Hresult]].
    inversion Hother; subst; reflexivity.
  - intro Hresult; discriminate Hresult.
  - intros [suffix [Hsuffix' _]]; discriminate Hsuffix'.
Qed.

Lemma string_concat_payload_null_cons : forall typmod rest,
  string_concat_payload (Value_string (StringValue typmod None) :: rest) = None.
Proof. reflexivity. Qed.

Lemma interp_string_concat_nonnull_cons :
  forall typmod value rest suffix,
    string_concat_payload rest = Some suffix ->
    interp_string_concat
      (Value_string (StringValue typmod (Some value)) :: rest) =
    Value_string
      (StringValue StringText
        (Some (String.append (string_cast_source_value typmod value) suffix))).
Proof.
  intros typmod value rest suffix Hsuffix.
  unfold interp_string_concat, StringValue.
  f_equal; f_equal.
  apply (proj2 (string_concat_payload_nonnull_cons_iff
    typmod value rest
    (String.append (string_cast_source_value typmod value) suffix))).
  exists suffix; split; [exact Hsuffix | reflexivity].
Qed.

Lemma interp_string_concat_null_cons : forall typmod rest,
  interp_string_concat (Value_string (StringValue typmod None) :: rest) =
  Value_string (StringValue StringText None).
Proof. reflexivity. Qed.

Lemma string_concat_local_runtime_safe : forall values,
  scalar_operator_local_runtime_error ScalarStringConcat values = None.
Proof. reflexivity. Qed.

Lemma string_map_append : forall mapping left right,
  string_map mapping (String.append left right) =
  String.append (string_map mapping left) (string_map mapping right).
Proof.
  intros mapping left; induction left as [|character rest IH]; intro right;
    cbn [string_map String.append].
  - reflexivity.
  - rewrite IH; reflexivity.
Qed.

Lemma string_map_length : forall mapping value,
  String.length (string_map mapping value) = String.length value.
Proof.
  intros mapping value; induction value as [|character rest IH];
    cbn [string_map String.length].
  - reflexivity.
  - rewrite IH; reflexivity.
Qed.

Lemma interp_string_case_nonnull : forall operation typmod value,
  interp_scalar_operator (ScalarStringCase operation)
    [Value_string (StringValue typmod (Some value))] =
  Value_string
    (StringValue StringText
      (Some
        (string_map
          (match operation with
           | ScalarUpper => ascii_to_upper
           | ScalarLower => ascii_to_lower
           end) value))).
Proof.
  intros operation typmod value; destruct operation; reflexivity.
Qed.

Lemma interp_string_case_null : forall operation typmod,
  interp_scalar_operator (ScalarStringCase operation)
    [Value_string (StringValue typmod None)] =
  Value_string (StringValue StringText None).
Proof.
  intros operation typmod; destruct operation; reflexivity.
Qed.

Lemma string_case_local_runtime_safe : forall operation values,
  scalar_operator_local_runtime_error (ScalarStringCase operation) values =
  None.
Proof.
  intros operation values; destruct operation; reflexivity.
Qed.

Lemma string_prefix_refl : forall value,
  String.prefix value value = true.
Proof.
  intro value; induction value as [|character rest IH].
  - reflexivity.
  - cbn [String.prefix].
    destruct (ascii_dec character character) as [_ | Hneq].
    + exact IH.
    + exfalso; apply Hneq; reflexivity.
Qed.

Lemma string_like_prefix_physical_refl : forall typmod value,
  string_like_prefix typmod value (string_physical_value typmod value) = true.
Proof.
  intros typmod value; unfold string_like_prefix.
  apply string_prefix_refl.
Qed.

Lemma interp_like_prefix_true_iff :
  forall input_typmod input prefix_typmod prefix,
    NullValues.interp_predicate PredicateLikePrefix
      [Value_string (StringValue input_typmod (Some input));
       Value_string (StringValue prefix_typmod (Some prefix))] = true3 <->
    string_like_prefix input_typmod input prefix = true.
Proof.
  intros input_typmod input prefix_typmod prefix.
  change
    ((if string_like_prefix input_typmod input prefix
      then true3 else false3) = true3 <->
     string_like_prefix input_typmod input prefix = true).
  destruct (string_like_prefix input_typmod input prefix); cbn;
    split; intro H; try discriminate H; reflexivity.
Qed.

Lemma interp_like_prefix_false_iff :
  forall input_typmod input prefix_typmod prefix,
    NullValues.interp_predicate PredicateLikePrefix
      [Value_string (StringValue input_typmod (Some input));
       Value_string (StringValue prefix_typmod (Some prefix))] = false3 <->
    string_like_prefix input_typmod input prefix = false.
Proof.
  intros input_typmod input prefix_typmod prefix.
  change
    ((if string_like_prefix input_typmod input prefix
      then true3 else false3) = false3 <->
     string_like_prefix input_typmod input prefix = false).
  destruct (string_like_prefix input_typmod input prefix); cbn;
    split; intro H; try discriminate H; reflexivity.
Qed.

Lemma interp_like_percent_true_iff :
  forall input_typmod input pattern_typmod pattern,
    NullValues.interp_predicate PredicateLikePercent
      [Value_string (StringValue input_typmod (Some input));
       Value_string (StringValue pattern_typmod (Some pattern))] = true3 <->
    string_like_percent input_typmod input pattern = true.
Proof.
  intros input_typmod input pattern_typmod pattern.
  change
    ((if string_like_percent input_typmod input pattern
      then true3 else false3) = true3 <->
     string_like_percent input_typmod input pattern = true).
  destruct (string_like_percent input_typmod input pattern); cbn;
    split; intro H; try discriminate H; reflexivity.
Qed.

Lemma interp_like_percent_false_iff :
  forall input_typmod input pattern_typmod pattern,
    NullValues.interp_predicate PredicateLikePercent
      [Value_string (StringValue input_typmod (Some input));
       Value_string (StringValue pattern_typmod (Some pattern))] = false3 <->
    string_like_percent input_typmod input pattern = false.
Proof.
  intros input_typmod input pattern_typmod pattern.
  change
    ((if string_like_percent input_typmod input pattern
      then true3 else false3) = false3 <->
     string_like_percent input_typmod input pattern = false).
  destruct (string_like_percent input_typmod input pattern); cbn;
    split; intro H; try discriminate H; reflexivity.
Qed.

Lemma interp_substring_nonnegative_valid : forall typmod input start count,
  1 <= int32_value start ->
  0 <= int32_value count ->
  interp_substring_nonnegative
    [Value_string (StringValue typmod (Some input));
     Value_int32 (Some start); Value_int32 (Some count)] =
  Value_string
    (StringValue StringText
      (Some
        (string_substring_nonnegative typmod input
          (Z.to_nat (int32_value start - 1))
          (Z.to_nat (int32_value count))))).
Proof.
  intros typmod input start count Hstart Hcount.
  assert (Hstart_bool : (1 <=? int32_value start) = true).
  { apply Z.leb_le; exact Hstart. }
  assert (Hcount_bool : (0 <=? int32_value count) = true).
  { apply Z.leb_le; exact Hcount. }
  cbn [interp_substring_nonnegative].
  rewrite Hstart_bool, Hcount_bool; reflexivity.
Qed.

Lemma interp_substring_nonnegative_null : forall typmod start count,
  interp_substring_nonnegative
    [Value_string (StringValue typmod None); start; count] =
  Value_string (StringValue StringText None).
Proof.
  intros typmod start count; reflexivity.
Qed.

Lemma interp_substring_nonnegative_invalid : forall typmod input start count,
  (int32_value start < 1 \/ int32_value count < 0) ->
  interp_substring_nonnegative
    [Value_string (StringValue typmod (Some input));
     Value_int32 (Some start); Value_int32 (Some count)] =
  Value_string (StringValue StringText None).
Proof.
  intros typmod input start count [Hstart | Hcount].
  - assert (Hstart_bool : (1 <=? int32_value start) = false).
    { apply Z.leb_gt; exact Hstart. }
    cbn [interp_substring_nonnegative]; rewrite Hstart_bool; reflexivity.
  - assert (Hcount_bool : (0 <=? int32_value count) = false).
    { apply Z.leb_gt; exact Hcount. }
    cbn [interp_substring_nonnegative]; rewrite Hcount_bool.
    destruct (1 <=? int32_value start); reflexivity.
Qed.

Lemma substring_nonnegative_local_runtime_safe : forall values,
  scalar_operator_local_runtime_error ScalarSubstringNonnegative values = None.
Proof. reflexivity. Qed.

Lemma string_comparison_values_swap :
  forall left_typmod left right_typmod right,
    string_comparison_values right_typmod right left_typmod left =
    let '(left_value, right_value) :=
      string_comparison_values left_typmod left right_typmod right in
    (right_value, left_value).
Proof.
  intros left_typmod left right_typmod right.
  destruct left_typmod; destruct right_typmod; reflexivity.
Qed.

Lemma sql_string_compare_eq_iff_semantic_values :
  forall left_typmod left right_typmod right,
    sql_string_compare left_typmod left right_typmod right = Eq <->
    let '(left_value, right_value) :=
      string_comparison_values left_typmod left right_typmod right in
    left_value = right_value.
Proof.
  intros left_typmod left right_typmod right.
  unfold sql_string_compare.
  destruct (string_comparison_values left_typmod left right_typmod right)
    as [left_value right_value].
  change
    (Oset.compare Ostring left_value right_value = Eq <->
     left_value = right_value).
  apply Oset.compare_eq_iff.
Qed.

Lemma sql_string_eqb_true_iff_semantic_values :
  forall left_typmod left right_typmod right,
    sql_string_eqb left_typmod left right_typmod right = true <->
    let '(left_value, right_value) :=
      string_comparison_values left_typmod left right_typmod right in
    left_value = right_value.
Proof.
  intros left_typmod left right_typmod right; split; intro Hresult.
  - unfold sql_string_eqb in Hresult.
    destruct (sql_string_compare left_typmod left right_typmod right)
      eqn:Hcompare; try discriminate Hresult.
    apply (proj1 (sql_string_compare_eq_iff_semantic_values
      left_typmod left right_typmod right)); exact Hcompare.
  - apply (proj2 (sql_string_compare_eq_iff_semantic_values
      left_typmod left right_typmod right)) in Hresult.
    unfold sql_string_eqb; rewrite Hresult; reflexivity.
Qed.

Lemma sql_string_compare_opposite :
  forall left_typmod left right_typmod right,
    sql_string_compare left_typmod left right_typmod right =
    CompOpp (sql_string_compare right_typmod right left_typmod left).
Proof.
  intros left_typmod left right_typmod right.
  unfold sql_string_compare.
  rewrite (string_comparison_values_swap
    left_typmod left right_typmod right).
  destruct (string_comparison_values left_typmod left right_typmod right)
    as [left_value right_value].
  cbn.
  apply (Oset.compare_lt_gt Ostring).
Qed.

Lemma sql_string_eqb_symmetric :
  forall left_typmod left right_typmod right,
    sql_string_eqb left_typmod left right_typmod right =
    sql_string_eqb right_typmod right left_typmod left.
Proof.
  intros left_typmod left right_typmod right.
  unfold sql_string_eqb.
  rewrite sql_string_compare_opposite.
  destruct (sql_string_compare right_typmod right left_typmod left);
    reflexivity.
Qed.

Lemma order_value_compare_string_nonnull :
  forall left_typmod left right_typmod right,
    NullPredicates.order_value_compare
      (Value_string (StringValue left_typmod (Some left)))
      (Value_string (StringValue right_typmod (Some right))) =
    Some (sql_string_compare left_typmod left right_typmod right).
Proof.
  intros left_typmod left right_typmod right; reflexivity.
Qed.

Lemma date_checked_some_iff : forall date,
  date_checked date = Some date <-> date_in_range_bool date = true.
Proof.
  intro date; unfold date_checked.
  destruct (date_in_range_bool date); cbn; split; intro H;
    try discriminate H; reflexivity.
Qed.

Lemma date_checked_none_iff : forall date,
  date_checked date = None <-> date_in_range_bool date = false.
Proof.
  intro date; unfold date_checked.
  destruct (date_in_range_bool date); cbn; split; intro H;
    try discriminate H; reflexivity.
Qed.

Lemma timestamp_checked_some_iff : forall timestamp,
  timestamp_checked timestamp = Some timestamp <->
  timestamp_in_range_bool timestamp = true.
Proof.
  intro timestamp; unfold timestamp_checked.
  destruct (timestamp_in_range_bool timestamp); cbn; split; intro H;
    try discriminate H; reflexivity.
Qed.

Lemma timestamp_checked_none_iff : forall timestamp,
  timestamp_checked timestamp = None <->
  timestamp_in_range_bool timestamp = false.
Proof.
  intro timestamp; unfold timestamp_checked.
  destruct (timestamp_in_range_bool timestamp); cbn; split; intro H;
    try discriminate H; reflexivity.
Qed.

Lemma order_value_compare_date_nonnull : forall left right,
  NullPredicates.order_value_compare
    (Value_date (Some left)) (Value_date (Some right)) =
  Some (Z.compare left right).
Proof.
  intros left right; reflexivity.
Qed.

Lemma order_value_compare_time_nonnull : forall left right,
  NullPredicates.order_value_compare
    (Value_time (Some left)) (Value_time (Some right)) =
  Some (Z.compare left right).
Proof.
  intros left right; reflexivity.
Qed.

Lemma order_value_compare_timestamp_nonnull : forall left right,
  NullPredicates.order_value_compare
    (Value_timestamp (Some left)) (Value_timestamp (Some right)) =
  Some (Z.compare left right).
Proof.
  intros left right; reflexivity.
Qed.

Lemma order_value_compare_timestamptz_nonnull : forall left right,
  NullPredicates.order_value_compare
    (Value_timestamptz (Some left)) (Value_timestamptz (Some right)) =
  Some (Z.compare left right).
Proof.
  intros left right; reflexivity.
Qed.

Lemma cast_date_to_timestamp_checked_finite : forall date,
  date_is_neg_infinity_bool date = false ->
  date_is_pos_infinity_bool date = false ->
  timestamp_in_range_bool (cast_date_to_timestamp date) = true ->
  cast_date_to_timestamp_checked date = Some (cast_date_to_timestamp date).
Proof.
  intros date Hnegative Hpositive Hrange.
  unfold cast_date_to_timestamp_checked.
  rewrite Hnegative, Hpositive.
  unfold timestamp_checked; rewrite Hrange; reflexivity.
Qed.

Lemma cast_timestamp_to_date_checked_finite : forall timestamp,
  timestamp_is_neg_infinity_bool timestamp = false ->
  timestamp_is_pos_infinity_bool timestamp = false ->
  date_in_range_bool (cast_timestamp_to_date timestamp) = true ->
  cast_timestamp_to_date_checked timestamp = Some (cast_timestamp_to_date timestamp).
Proof.
  intros timestamp Hnegative Hpositive Hrange.
  unfold cast_timestamp_to_date_checked.
  rewrite Hnegative, Hpositive.
  unfold date_checked; rewrite Hrange; reflexivity.
Qed.

Lemma scalar_cast_date_to_timestamp_success_safe : forall date timestamp,
  cast_date_to_timestamp_checked date = Some timestamp ->
  interp_scalar_operator (ScalarCast ScalarCastDateToTimestamp)
    [Value_date (Some date)] = Value_timestamp (Some timestamp) /\
  scalar_operator_local_runtime_error
    (ScalarCast ScalarCastDateToTimestamp) [Value_date (Some date)] = None.
Proof.
  intros date timestamp Hcast; split.
  - cbn [interp_scalar_operator]; rewrite Hcast; reflexivity.
  - cbn [scalar_operator_local_runtime_error
      cast_date_to_timestamp_runtime_error].
    rewrite Hcast; reflexivity.
Qed.

Lemma scalar_cast_timestamp_to_date_success_safe : forall timestamp date,
  cast_timestamp_to_date_checked timestamp = Some date ->
  interp_scalar_operator (ScalarCast ScalarCastTimestampToDate)
    [Value_timestamp (Some timestamp)] = Value_date (Some date) /\
  scalar_operator_local_runtime_error
    (ScalarCast ScalarCastTimestampToDate) [Value_timestamp (Some timestamp)] =
  None.
Proof.
  intros timestamp date Hcast; split.
  - cbn [interp_scalar_operator]; rewrite Hcast; reflexivity.
  - cbn [scalar_operator_local_runtime_error
      cast_timestamp_to_date_runtime_error].
    rewrite Hcast; reflexivity.
Qed.

Lemma scalar_cast_date_to_timestamp_failure_overflow : forall date,
  cast_date_to_timestamp_checked date = None ->
  interp_scalar_operator (ScalarCast ScalarCastDateToTimestamp)
    [Value_date (Some date)] = Value_timestamp None /\
  scalar_operator_local_runtime_error
    (ScalarCast ScalarCastDateToTimestamp) [Value_date (Some date)] =
  datetime_field_overflow.
Proof.
  intros date Hcast; split.
  - cbn [interp_scalar_operator]; rewrite Hcast; reflexivity.
  - cbn [scalar_operator_local_runtime_error
      cast_date_to_timestamp_runtime_error].
    rewrite Hcast; reflexivity.
Qed.

Lemma scalar_cast_timestamp_to_date_failure_overflow : forall timestamp,
  cast_timestamp_to_date_checked timestamp = None ->
  interp_scalar_operator (ScalarCast ScalarCastTimestampToDate)
    [Value_timestamp (Some timestamp)] = Value_date None /\
  scalar_operator_local_runtime_error
    (ScalarCast ScalarCastTimestampToDate) [Value_timestamp (Some timestamp)] =
  datetime_field_overflow.
Proof.
  intros timestamp Hcast; split.
  - cbn [interp_scalar_operator]; rewrite Hcast; reflexivity.
  - cbn [scalar_operator_local_runtime_error
      cast_timestamp_to_date_runtime_error].
    rewrite Hcast; reflexivity.
Qed.

Lemma scalar_temporal_casts_null_safe :
  interp_scalar_operator (ScalarCast ScalarCastDateToTimestamp)
    [Value_date None] = Value_timestamp None /\
  scalar_operator_local_runtime_error
    (ScalarCast ScalarCastDateToTimestamp) [Value_date None] = None /\
  interp_scalar_operator (ScalarCast ScalarCastTimestampToDate)
    [Value_timestamp None] = Value_date None /\
  scalar_operator_local_runtime_error
    (ScalarCast ScalarCastTimestampToDate) [Value_timestamp None] = None.
Proof. repeat split; reflexivity. Qed.

Lemma checked_temporal_casts_preserve_infinities :
  cast_date_to_timestamp_checked postgres_date_neg_infinity =
    Some postgres_timestamp_neg_infinity /\
  cast_date_to_timestamp_checked postgres_date_pos_infinity =
    Some postgres_timestamp_pos_infinity /\
  cast_timestamp_to_date_checked postgres_timestamp_neg_infinity =
    Some postgres_date_neg_infinity /\
  cast_timestamp_to_date_checked postgres_timestamp_pos_infinity =
    Some postgres_date_pos_infinity.
Proof.
  assert (Hdate : postgres_date_pos_infinity <>
      postgres_date_neg_infinity).
  { unfold postgres_date_pos_infinity, postgres_date_neg_infinity,
      postgres_date_end, postgres_date_min; lia. }
  assert (Htimestamp : postgres_timestamp_pos_infinity <>
      postgres_timestamp_neg_infinity).
  { unfold postgres_timestamp_pos_infinity, postgres_timestamp_neg_infinity,
      postgres_timestamp_end, postgres_timestamp_min; lia. }
  split.
  - unfold cast_date_to_timestamp_checked,
      date_is_neg_infinity_bool; rewrite Z.eqb_refl; reflexivity.
  - split.
    + unfold cast_date_to_timestamp_checked, date_is_neg_infinity_bool,
        date_is_pos_infinity_bool.
      rewrite (proj2 (Z.eqb_neq _ _) Hdate), Z.eqb_refl; reflexivity.
    + split.
      * unfold cast_timestamp_to_date_checked,
          timestamp_is_neg_infinity_bool; rewrite Z.eqb_refl; reflexivity.
      * unfold cast_timestamp_to_date_checked,
          timestamp_is_neg_infinity_bool, timestamp_is_pos_infinity_bool.
        rewrite (proj2 (Z.eqb_neq _ _) Htimestamp), Z.eqb_refl; reflexivity.
Qed.

Lemma interp_extract_year_date_finite : forall date,
  date_is_neg_infinity_bool date = false ->
  date_is_pos_infinity_bool date = false ->
  interp_extract_year_date [Value_date (Some date)] =
  Value_numeric (Some (numeric_of_Z (date_extract_year date))).
Proof.
  intros date Hnegative Hpositive.
  cbn [interp_extract_year_date]; rewrite Hnegative, Hpositive; reflexivity.
Qed.

Lemma interp_extract_year_date_infinity : forall date result,
  (date = postgres_date_neg_infinity /\ result = NumericNegInfinity) \/
  (date = postgres_date_pos_infinity /\ result = NumericPosInfinity) ->
  interp_extract_year_date [Value_date (Some date)] =
  Value_numeric (Some result).
Proof.
  intros date result [[-> ->] | [-> ->]].
  - cbn [interp_extract_year_date date_is_neg_infinity_bool].
    reflexivity.
  -
    cbn [interp_extract_year_date date_is_neg_infinity_bool
      date_is_pos_infinity_bool].
    reflexivity.
Qed.

Lemma interp_extract_month_date_finite : forall date,
  date_is_infinity_bool date = false ->
  interp_extract_month_date [Value_date (Some date)] =
  Value_numeric (Some (numeric_of_Z (date_extract_month date))).
Proof.
  intros date Hfinite.
  cbn [interp_extract_month_date]; rewrite Hfinite; reflexivity.
Qed.

Lemma interp_extract_month_date_infinity : forall date,
  date_is_infinity_bool date = true ->
  interp_extract_month_date [Value_date (Some date)] = Value_numeric None.
Proof.
  intros date Hinfinity.
  cbn [interp_extract_month_date]; rewrite Hinfinity; reflexivity.
Qed.

Lemma interp_extract_date_null : forall part,
  interp_scalar_operator (ScalarExtractDate part) [Value_date None] =
  Value_numeric None.
Proof.
  intro part; destruct part; reflexivity.
Qed.

Lemma extract_date_local_runtime_safe : forall part values,
  scalar_operator_local_runtime_error (ScalarExtractDate part) values = None.
Proof.
  intros part values; destruct part; reflexivity.
Qed.

Lemma interp_date_lt_timestamp_true_iff : forall date timestamp,
  NullValues.interp_predicate PredicateDateLtTimestamp
    [Value_date (Some date); Value_timestamp (Some timestamp)] = true3 <->
  date_cmp_timestamp_internal date timestamp = Lt.
Proof.
  intros date timestamp.
  cbn [NullValues.interp_predicate NullPredicates.interp_predicate].
  rewrite <- (date_lt_timestamp_bool_spec date timestamp).
  destruct (date_lt_timestamp_bool date timestamp); cbn;
    split; intro H; try discriminate H; reflexivity.
Qed.

Lemma interp_date_lt_timestamp_false_iff : forall date timestamp,
  NullValues.interp_predicate PredicateDateLtTimestamp
    [Value_date (Some date); Value_timestamp (Some timestamp)] = false3 <->
  date_cmp_timestamp_internal date timestamp <> Lt.
Proof.
  intros date timestamp.
  cbn [NullValues.interp_predicate NullPredicates.interp_predicate].
  unfold date_lt_timestamp_bool.
  destruct (date_cmp_timestamp_internal date timestamp); cbn;
    split; congruence.
Qed.

Lemma interp_date_lte_timestamp_true_iff : forall date timestamp,
  NullValues.interp_predicate PredicateDateLteTimestamp
    [Value_date (Some date); Value_timestamp (Some timestamp)] = true3 <->
  date_cmp_timestamp_internal date timestamp <> Gt.
Proof.
  intros date timestamp.
  cbn [NullValues.interp_predicate NullPredicates.interp_predicate].
  rewrite <- (date_lte_timestamp_bool_spec date timestamp).
  destruct (date_lte_timestamp_bool date timestamp); cbn;
    split; intro H; try discriminate H; reflexivity.
Qed.

Lemma interp_date_lte_timestamp_false_iff : forall date timestamp,
  NullValues.interp_predicate PredicateDateLteTimestamp
    [Value_date (Some date); Value_timestamp (Some timestamp)] = false3 <->
  date_cmp_timestamp_internal date timestamp = Gt.
Proof.
  intros date timestamp.
  cbn [NullValues.interp_predicate NullPredicates.interp_predicate].
  unfold date_lte_timestamp_bool.
  destruct (date_cmp_timestamp_internal date timestamp); cbn;
    split; congruence.
Qed.

Lemma interp_date_gt_timestamp_true_iff : forall date timestamp,
  NullValues.interp_predicate PredicateDateGtTimestamp
    [Value_date (Some date); Value_timestamp (Some timestamp)] = true3 <->
  date_cmp_timestamp_internal date timestamp = Gt.
Proof.
  intros date timestamp.
  cbn [NullValues.interp_predicate NullPredicates.interp_predicate].
  rewrite <- (date_gt_timestamp_bool_spec date timestamp).
  destruct (date_gt_timestamp_bool date timestamp); cbn;
    split; intro H; try discriminate H; reflexivity.
Qed.

Lemma interp_date_gt_timestamp_false_iff : forall date timestamp,
  NullValues.interp_predicate PredicateDateGtTimestamp
    [Value_date (Some date); Value_timestamp (Some timestamp)] = false3 <->
  date_cmp_timestamp_internal date timestamp <> Gt.
Proof.
  intros date timestamp.
  cbn [NullValues.interp_predicate NullPredicates.interp_predicate].
  unfold date_gt_timestamp_bool.
  destruct (date_cmp_timestamp_internal date timestamp); cbn;
    split; congruence.
Qed.

Lemma interp_date_gte_timestamp_true_iff : forall date timestamp,
  NullValues.interp_predicate PredicateDateGteTimestamp
    [Value_date (Some date); Value_timestamp (Some timestamp)] = true3 <->
  date_cmp_timestamp_internal date timestamp <> Lt.
Proof.
  intros date timestamp.
  cbn [NullValues.interp_predicate NullPredicates.interp_predicate].
  rewrite <- (date_gte_timestamp_bool_spec date timestamp).
  destruct (date_gte_timestamp_bool date timestamp); cbn;
    split; intro H; try discriminate H; reflexivity.
Qed.

Lemma interp_date_gte_timestamp_false_iff : forall date timestamp,
  NullValues.interp_predicate PredicateDateGteTimestamp
    [Value_date (Some date); Value_timestamp (Some timestamp)] = false3 <->
  date_cmp_timestamp_internal date timestamp = Lt.
Proof.
  intros date timestamp.
  cbn [NullValues.interp_predicate NullPredicates.interp_predicate].
  unfold date_gte_timestamp_bool.
  destruct (date_cmp_timestamp_internal date timestamp); cbn;
    split; congruence.
Qed.

Definition timestamp_checked_operation
    (unit : scalar_timestamp_unit) : Z -> Z -> option Z :=
  match unit with
  | ScalarTimestampMicrosecond => timestamp_add_microseconds_checked
  | ScalarTimestampSecond => timestamp_add_seconds_checked
  | ScalarTimestampMinute => timestamp_add_minutes_checked
  | ScalarTimestampHour => timestamp_add_hours_checked
  | ScalarTimestampDay => timestamp_add_days_checked
  | ScalarTimestampMonth => timestamp_add_months_checked
  | ScalarTimestampYear => timestamp_add_years_checked
  end.

Lemma timestamp_scalar_add_checked_success : forall unit timestamp amount result,
  timestamp_checked_operation unit timestamp amount = Some result ->
  interp_scalar_operator (ScalarTimestampAdd unit)
    [Value_timestamp (Some timestamp); Value_Z (Some amount)] =
    Value_timestamp (Some result) /\
  scalar_operator_local_runtime_error (ScalarTimestampAdd unit)
    [Value_timestamp (Some timestamp); Value_Z (Some amount)] = None.
Proof.
  intros unit timestamp amount result Hresult.
  destruct unit; cbn [timestamp_checked_operation interp_scalar_operator
    scalar_operator_local_runtime_error timestamp_binary_runtime_error]
    in Hresult |- *; rewrite Hresult; split; reflexivity.
Qed.

Lemma timestamp_scalar_add_checked_failure : forall unit timestamp amount,
  timestamp_checked_operation unit timestamp amount = None ->
  interp_scalar_operator (ScalarTimestampAdd unit)
    [Value_timestamp (Some timestamp); Value_Z (Some amount)] =
    Value_timestamp None /\
  scalar_operator_local_runtime_error (ScalarTimestampAdd unit)
    [Value_timestamp (Some timestamp); Value_Z (Some amount)] =
    datetime_field_overflow.
Proof.
  intros unit timestamp amount Hresult.
  destruct unit; cbn [timestamp_checked_operation interp_scalar_operator
    scalar_operator_local_runtime_error timestamp_binary_runtime_error]
    in Hresult |- *; rewrite Hresult; split; reflexivity.
Qed.

Lemma timestamp_scalar_add_null_safe : forall unit timestamp amount,
  (timestamp = None \/ amount = None) ->
  interp_scalar_operator (ScalarTimestampAdd unit)
    [Value_timestamp timestamp; Value_Z amount] = Value_timestamp None /\
  scalar_operator_local_runtime_error (ScalarTimestampAdd unit)
    [Value_timestamp timestamp; Value_Z amount] = None.
Proof.
  intros unit timestamp amount [-> | ->].
  - destruct unit; split; reflexivity.
  - destruct timestamp as [timestamp |]; destruct unit; split; reflexivity.
Qed.

Lemma timestamp_checked_operation_infinity : forall unit timestamp amount,
  timestamp_is_infinity_bool timestamp = true ->
  timestamp_checked_operation unit timestamp amount = Some timestamp.
Proof.
  intros unit timestamp amount Hinfinity.
  destruct unit; unfold timestamp_checked_operation;
    [unfold timestamp_add_microseconds_checked
    | unfold timestamp_add_seconds_checked
    | unfold timestamp_add_minutes_checked
    | unfold timestamp_add_hours_checked
    | unfold timestamp_add_days_checked
    | unfold timestamp_add_months_checked
    | unfold timestamp_add_years_checked];
    rewrite Hinfinity; reflexivity.
Qed.

Lemma timestamp_scalar_add_preserves_infinity : forall unit timestamp amount,
  timestamp_is_infinity_bool timestamp = true ->
  interp_scalar_operator (ScalarTimestampAdd unit)
    [Value_timestamp (Some timestamp); Value_Z (Some amount)] =
    Value_timestamp (Some timestamp) /\
  scalar_operator_local_runtime_error (ScalarTimestampAdd unit)
    [Value_timestamp (Some timestamp); Value_Z (Some amount)] = None.
Proof.
  intros unit timestamp amount Hinfinity.
  apply timestamp_scalar_add_checked_success.
  apply timestamp_checked_operation_infinity; exact Hinfinity.
Qed.
