(** TNull specialization of the exact normalized-query semantics.

    Query observations are relations over ordered row lists.  Possible-bag
    reasoning is used only through abstraction for order-insensitive proof
    regions; it is not a second query semantics. *)
From Stdlib Require Import List ZArith.
From SQLFS Require Import SqlSyntax GenericInstance Values Bool3 Env FiniteSet SqlOutcome
  SqlQuerySyntax SqlQuerySemantics SqlQueryWellFormed.
From Logos Require Export FormalSQL.TNullSyntax.

Import ListNotations.
Import Tuple.

Definition QueryExpr := @query_expr TNull relname.
Definition QueryProgram := list QueryExpr.
Definition FormulaExpr := @formula_expr TNull relname.
Definition QueryWindowItemT := query_window_item TNull.

(** PostgreSQL ranking functions return non-NULL BIGINT.  The generic query
    semantics turns failure of this checked embedding into SQLSTATE 22003
    (numeric value out of range), so the unbounded logical list carrier never
    becomes stuck at an unrepresentable position. *)
Definition PgRankInt64Value
    (rank : nat) : option (Tuple.value TNull) :=
  match int64_checked (Z.of_nat rank) with
  | Some value => Some (NullValues.Value_int64 (Some value))
  | None => None
  end.

Definition RankExpr
    (partition_keys order_keys : list SortKeyT)
    (rank_attribute : Tuple.attribute TNull)
    (input : QueryExpr) : QueryExpr :=
  @QExpr_Rank TNull relname partition_keys order_keys rank_attribute
    PgRankInt64Value input.

Definition WindowRowNumberItem
    (output : Tuple.attribute TNull) : QueryWindowItemT :=
  @QueryWindowItem TNull output (QueryWindowRowNumber PgRankInt64Value).

Definition WindowAggregateItem
    (output : Tuple.attribute TNull) (term : AggTerm) : QueryWindowItemT :=
  @QueryWindowItem TNull output (QueryWindowAggregate term).

Definition WindowExpr
    (partition_keys order_keys : list SortKeyT)
    (items : list QueryWindowItemT)
    (input : QueryExpr) : QueryExpr :=
  @QExpr_Window TNull relname partition_keys order_keys items input.

(** A declarative, order-preserving row adapter with an explicitly resolved
    result schema. *)
Definition RowMapExpr
    (output_attributes : list (attribute TNull))
    (row_map : tuple TNull -> sql_outcome (tuple TNull))
    (input : QueryExpr) : QueryExpr :=
  @QExpr_RowMap TNull relname
    output_attributes row_map input.

(** Abstract result of PostgreSQL's exact NUMERIC [exp] language operation.
    The model supplies both the finite value and PostgreSQL display scale, or
    reports SQLSTATE 22003. *)
Inductive NumericExpResult : Type :=
  | NumericExpSuccess : numeric -> Z -> NumericExpResult
  | NumericExpValueOutOfRange : NumericExpResult.

Definition NumericExpModel : Type := numeric -> Z -> NumericExpResult.

Definition NumericExpOutputAttributes
    (passthrough : list (attribute TNull))
    (output_numeric_attribute output_dscale_attribute : attribute TNull) :
    list (attribute TNull) :=
  passthrough ++ [output_numeric_attribute; output_dscale_attribute].

Definition NumericExpOutputRow
    (passthrough : list (attribute TNull))
    (output_numeric_attribute output_dscale_attribute : attribute TNull)
    (input : tuple TNull)
    (result : option numeric) (dscale : option Z) : tuple TNull :=
  mk_tuple_lists
    (NumericExpOutputAttributes passthrough
      output_numeric_attribute output_dscale_attribute)
    (map (dot TNull input) passthrough ++
      [NullValues.Value_numeric result; NullValues.Value_Z dscale]).

(** A successful abstract model result is admitted only when it is an exact
    PostgreSQL-storable finite NUMERIC at the supplied display scale.  Requiring
    a fixed point of [numeric_round_to_scale] prevents a model from attaching
    stale scale metadata to a more precise value. *)
Definition NumericExpSuccessValid (result : numeric) (dscale : Z) : bool :=
  match result with
  | NumericFinite _ =>
      numeric_display_scale_valid_bool dscale &&
      (dscale <=? postgres_numeric_max_display_scale) &&
      numeric_runtime_fits_bool result &&
      numeric_eqb (numeric_round_to_scale result dscale) result
  | NumericNegInfinity | NumericPosInfinity | NumericNaN => false
  end.

Definition NumericExpRangeError {A : Type} : sql_outcome A :=
  SqlError (DataException NumericValueOutOfRange).

(** Declarative adapter for [EXP(AVG(int4))].  NULL AVG bypasses the abstract
    EXP model and produces NULL value/scale.  Every non-NULL path consumes the
    AVG display scale explicitly and validates the model result before exposing
    it as SQL data. *)
Definition NumericExpRowAdapter
    (passthrough : list (attribute TNull))
    (avg_value_attribute avg_dscale_attribute : attribute TNull)
    (output_numeric_attribute output_dscale_attribute : attribute TNull)
    (model : NumericExpModel)
    (row : tuple TNull) : sql_outcome (tuple TNull) :=
  match dot TNull row avg_value_attribute with
  | NullValues.Value_numeric None =>
      SqlSuccess
        (NumericExpOutputRow passthrough
          output_numeric_attribute output_dscale_attribute row None None)
  | NullValues.Value_numeric (Some average) =>
      match dot TNull row avg_dscale_attribute with
      | NullValues.Value_Z (Some average_dscale) =>
          match model average average_dscale with
          | NumericExpValueOutOfRange => NumericExpRangeError
          | NumericExpSuccess result result_dscale =>
              if NumericExpSuccessValid result result_dscale
              then
                SqlSuccess
                  (NumericExpOutputRow passthrough
                    output_numeric_attribute output_dscale_attribute row
                    (Some result) (Some result_dscale))
              else NumericExpRangeError
          end
      | _ => NumericExpRangeError
      end
  | _ => NumericExpRangeError
  end.

Definition NumericExpRowMapExpr
    (passthrough : list (attribute TNull))
    (avg_value_attribute avg_dscale_attribute : attribute TNull)
    (output_numeric_attribute output_dscale_attribute : attribute TNull)
    (model : NumericExpModel)
    (input : QueryExpr) : QueryExpr :=
  RowMapExpr
    (NumericExpOutputAttributes passthrough
      output_numeric_attribute output_dscale_attribute)
    (NumericExpRowAdapter passthrough avg_value_attribute avg_dscale_attribute
      output_numeric_attribute output_dscale_attribute model)
    input.

Lemma NumericExpOutputRow_labels :
  forall passthrough output_numeric_attribute output_dscale_attribute
         input result dscale,
    labels TNull
      (NumericExpOutputRow passthrough
        output_numeric_attribute output_dscale_attribute input result dscale)
    =S=
    Fset.mk_set (A TNull)
      (NumericExpOutputAttributes passthrough
        output_numeric_attribute output_dscale_attribute).
Proof.
intros; unfold NumericExpOutputRow, mk_tuple_lists.
apply labels_mk_tuple.
Qed.

Lemma NumericExpRowAdapter_well_sorted :
  forall passthrough avg_value_attribute avg_dscale_attribute
         output_numeric_attribute output_dscale_attribute model,
    @query_row_map_well_sorted TNull
      (Fset.mk_set (A TNull)
        (NumericExpOutputAttributes passthrough
          output_numeric_attribute output_dscale_attribute))
      (NumericExpRowAdapter passthrough avg_value_attribute
        avg_dscale_attribute output_numeric_attribute
        output_dscale_attribute model).
Proof.
intros passthrough avg_value_attribute avg_dscale_attribute
  output_numeric_attribute output_dscale_attribute model input output Houtput.
unfold NumericExpRowAdapter in Houtput.
repeat
  match type of Houtput with
  | context [match ?scrutinee with _ => _ end] =>
      destruct scrutinee eqn:?
  end;
  try discriminate;
  inversion Houtput; subst;
  apply NumericExpOutputRow_labels.
Qed.

Lemma NumericExpRowMapExpr_admissible :
  forall basesort passthrough avg_value_attribute avg_dscale_attribute
         output_numeric_attribute output_dscale_attribute model input,
    @query_expr_admissible TNull relname basesort input ->
    @query_output_attributes_unique TNull
      (NumericExpOutputAttributes passthrough
        output_numeric_attribute output_dscale_attribute) ->
    @query_expr_admissible TNull relname basesort
      (NumericExpRowMapExpr passthrough avg_value_attribute
        avg_dscale_attribute output_numeric_attribute
        output_dscale_attribute model input).
Proof.
intros basesort passthrough avg_value_attribute avg_dscale_attribute
  output_numeric_attribute output_dscale_attribute model input Hinput Hunique.
repeat split; try assumption.
apply NumericExpRowAdapter_well_sorted.
Qed.

Lemma NumericExpRowAdapter_null :
  forall passthrough avg_value_attribute avg_dscale_attribute
         output_numeric_attribute output_dscale_attribute model row,
    dot TNull row avg_value_attribute = NullValues.Value_numeric None ->
    NumericExpRowAdapter passthrough avg_value_attribute avg_dscale_attribute
      output_numeric_attribute output_dscale_attribute model row =
    SqlSuccess
      (NumericExpOutputRow passthrough
        output_numeric_attribute output_dscale_attribute row None None).
Proof.
intros; unfold NumericExpRowAdapter; now rewrite H.
Qed.

Lemma NumericExpRowAdapter_success :
  forall passthrough avg_value_attribute avg_dscale_attribute
         output_numeric_attribute output_dscale_attribute model row
         average average_dscale result result_dscale,
    dot TNull row avg_value_attribute =
      NullValues.Value_numeric (Some average) ->
    dot TNull row avg_dscale_attribute =
      NullValues.Value_Z (Some average_dscale) ->
    model average average_dscale =
      NumericExpSuccess result result_dscale ->
    NumericExpSuccessValid result result_dscale = true ->
    NumericExpRowAdapter passthrough avg_value_attribute avg_dscale_attribute
      output_numeric_attribute output_dscale_attribute model row =
    SqlSuccess
      (NumericExpOutputRow passthrough
        output_numeric_attribute output_dscale_attribute row
        (Some result) (Some result_dscale)).
Proof.
intros; unfold NumericExpRowAdapter; now rewrite H, H0, H1, H2.
Qed.

Lemma NumericExpRowAdapter_invalid_success :
  forall passthrough avg_value_attribute avg_dscale_attribute
         output_numeric_attribute output_dscale_attribute model row
         average average_dscale result result_dscale,
    dot TNull row avg_value_attribute =
      NullValues.Value_numeric (Some average) ->
    dot TNull row avg_dscale_attribute =
      NullValues.Value_Z (Some average_dscale) ->
    model average average_dscale =
      NumericExpSuccess result result_dscale ->
    NumericExpSuccessValid result result_dscale = false ->
    NumericExpRowAdapter passthrough avg_value_attribute avg_dscale_attribute
      output_numeric_attribute output_dscale_attribute model row =
    @NumericExpRangeError (tuple TNull).
Proof.
intros; unfold NumericExpRowAdapter; now rewrite H, H0, H1, H2.
Qed.

Lemma NumericExpRowAdapter_out_of_range :
  forall passthrough avg_value_attribute avg_dscale_attribute
         output_numeric_attribute output_dscale_attribute model row
         average average_dscale,
    dot TNull row avg_value_attribute =
      NullValues.Value_numeric (Some average) ->
    dot TNull row avg_dscale_attribute =
      NullValues.Value_Z (Some average_dscale) ->
    model average average_dscale = NumericExpValueOutOfRange ->
    NumericExpRowAdapter passthrough avg_value_attribute avg_dscale_attribute
      output_numeric_attribute output_dscale_attribute model row =
    @NumericExpRangeError (tuple TNull).
Proof.
intros; unfold NumericExpRowAdapter; now rewrite H, H0, H1.
Qed.

Lemma NumericExpSuccessValid_invalid_scale :
  forall result dscale,
    numeric_display_scale_valid_bool dscale = false ->
    NumericExpSuccessValid result dscale = false.
Proof.
intros [| finite | |] dscale Hscale; try reflexivity.
unfold NumericExpSuccessValid; now rewrite Hscale.
Qed.

Lemma NumericExpSuccessValid_nonfinite :
  forall dscale,
    NumericExpSuccessValid NumericNegInfinity dscale = false /\
    NumericExpSuccessValid NumericPosInfinity dscale = false /\
    NumericExpSuccessValid NumericNaN dscale = false.
Proof.
intro; repeat split; reflexivity.
Qed.

Definition eval_query_expr_outcome_in_env
    (db : db_state)
    (env : Env.env TNull)
    (q : QueryExpr) :=
  @eval_query_expr_outcome TNull relname
    (@_basesort TNull db)
    (@_instance TNull db)
    unknown3
    contains_nulls
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error
    NullValues.is_null_value
    env
    q.

Lemma eval_query_expr_row_map_child_error :
  forall db env output_attributes row_map input error,
    eval_query_expr_outcome_in_env db env input (SqlError error) ->
    eval_query_expr_outcome_in_env db env
      (RowMapExpr output_attributes row_map input) (SqlError error).
Proof.
intros; apply EQuery_RowMapChildError; exact H.
Qed.

Definition eval_query_expr_outcome_in_state
    (db : db_state)
    (q : QueryExpr) :=
  eval_query_expr_outcome_in_env db nil q.

Definition query_expr_equiv_in_env
    (db : db_state)
    (env : Env.env TNull)
    (left right : QueryExpr) : Prop :=
  @query_expr_equiv TNull relname
    (@_basesort TNull db)
    (@_instance TNull db)
    unknown3
    contains_nulls
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error
    NullValues.is_null_value
    env
    left
    right.

Definition query_expr_equiv_in_state
    (db : db_state)
    (left right : QueryExpr) : Prop :=
  query_expr_equiv_in_env db nil left right.

Definition query_expr_outcome_equiv_in_env
    (db : db_state)
    (env : Env.env TNull)
    (left right : QueryExpr) : Prop :=
  @query_expr_outcome_equiv TNull relname
    (@_basesort TNull db)
    (@_instance TNull db)
    unknown3
    contains_nulls
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error
    NullValues.is_null_value
    env
    left
    right.

Definition query_expr_outcome_equiv_in_state
    (db : db_state)
    (left right : QueryExpr) : Prop :=
  query_expr_outcome_equiv_in_env db nil left right.

Definition query_program_equiv_in_env
    (db : db_state)
    (env : Env.env TNull)
    (left right : QueryProgram) : Prop :=
  @query_program_equiv TNull relname
    (@_basesort TNull db)
    (@_instance TNull db)
    unknown3
    contains_nulls
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error
    NullValues.is_null_value
    env
    left
    right.

Definition query_program_equiv_in_state
    (db : db_state)
    (left right : QueryProgram) : Prop :=
  query_program_equiv_in_env db nil left right.

Definition query_program_outcome_equiv_in_env
    (db : db_state)
    (env : Env.env TNull)
    (left right : QueryProgram) : Prop :=
  @query_program_outcome_equiv TNull relname
    (@_basesort TNull db)
    (@_instance TNull db)
    unknown3
    contains_nulls
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error
    NullValues.is_null_value
    env
    left
    right.

Definition query_program_outcome_equiv_in_state
    (db : db_state)
    (left right : QueryProgram) : Prop :=
  query_program_outcome_equiv_in_env db nil left right.
