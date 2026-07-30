(** TNull specialization of the exact normalized-query semantics.

    Query observations are relations over ordered row lists.  Possible-bag
    reasoning is used only through abstraction for order-insensitive proof
    regions; it is not a second query semantics. *)
From Stdlib Require Import List ZArith.
From SQLFS Require Import SqlSyntax GenericInstance Values Bool3 Env OrderedSet FiniteSet
  FiniteBag FiniteCollection FlatData
  Formula SchemaConstraints SqlOutcome SqlQuerySyntax SqlQuerySemantics
  SqlQueryWellFormed SqlOrder.
From Logos Require Export FormalSQL.TNullSyntax.

Import ListNotations.
Import Tuple.

Definition QueryExpr := @query_expr TNull relname.
Definition QueryProgram := list QueryExpr.
Definition FormulaExpr := @formula_expr TNull relname.
Definition QueryWindowItemT := query_window_item TNull.

Definition TNullNumericKindType (kind : scalar_numeric_kind) : type TNull :=
  match kind with
  | ScalarInt32 => type_int32
  | ScalarInt64 => type_int64
  | ScalarFloat => type_float
  | ScalarDouble => type_double
  | ScalarNumeric => type_numeric
  end.

(** Closed type/signature catalog for the scalar operators admitted by Logos.
    The value interpreters are deliberately total on malformed argument lists;
    exact generated queries must instead pass this catalog, so a total fallback
    can never be mistaken for PostgreSQL typing. *)
Definition TNullTypeEqb (left right : type TNull) : bool :=
  match left, right with
  | type_string, type_string
  | type_Z, type_Z
  | type_int32, type_int32
  | type_int64, type_int64
  | type_bool, type_bool
  | type_float, type_float
  | type_double, type_double
  | type_numeric, type_numeric
  | type_date, type_date
  | type_time, type_time
  | type_timestamp, type_timestamp
  | type_timestamptz, type_timestamptz => true
  | _, _ => false
  end.

Fixpoint TNullTypeListEqb
    (left right : list (type TNull)) : bool :=
  match left, right with
  | nil, nil => true
  | left_type :: left_rest, right_type :: right_rest =>
      TNullTypeEqb left_type right_type &&
        TNullTypeListEqb left_rest right_rest
  | _, _ => false
  end.

Definition TNullRequireArgumentTypes
    (expected actual : list (type TNull)) (result_type : type TNull) :
    option (type TNull) :=
  if TNullTypeListEqb expected actual then Some result_type else None.

Definition TNullIntegralType (argument_type : type TNull) : bool :=
  match argument_type with
  | type_Z | type_int32 | type_int64 => true
  | _ => false
  end.

Definition TNullEqualityPairTypes
    (left right : type TNull) : bool :=
  (TNullIntegralType left && TNullIntegralType right) ||
    TNullTypeEqb left right.

Definition TNullGenericOrderPairTypes
    (left right : type TNull) : bool :=
  (TNullIntegralType left && TNullIntegralType right) ||
    match left, right with
    | type_string, type_string
    | type_bool, type_bool
    | type_numeric, type_numeric
    | type_date, type_date
    | type_time, type_time
    | type_timestamp, type_timestamp
    | type_timestamptz, type_timestamptz => true
    | _, _ => false
    end.

Definition TNullPredicateArgumentTypesValid
    (predicate : predicate TNull) (argument_types : list (type TNull)) : bool :=
  match predicate with
  | PredicateIsNull | PredicateIsNotNull =>
      match argument_types with
      | _ :: nil => true
      | _ => false
      end
  | PredicateIsTrue | PredicateIsNotTrue
  | PredicateIsFalse | PredicateIsNotFalse =>
      TNullTypeListEqb [type_bool] argument_types
  | PredicateFloatLt | PredicateFloatLte
  | PredicateFloatGt | PredicateFloatGte =>
      TNullTypeListEqb [type_float; type_float] argument_types
  | PredicateDoubleLt | PredicateDoubleLte
  | PredicateDoubleGt | PredicateDoubleGte =>
      TNullTypeListEqb [type_double; type_double] argument_types
  | PredicateDateLtTimestamp | PredicateDateLteTimestamp
  | PredicateDateGtTimestamp | PredicateDateGteTimestamp =>
      TNullTypeListEqb [type_date; type_timestamp] argument_types
  | PredicateLikePrefix | PredicateLikePercent =>
      TNullTypeListEqb [type_string; type_string] argument_types
  | PredicateLt | PredicateLte | PredicateGt | PredicateGte =>
      match argument_types with
      | left_type :: right_type :: nil =>
          TNullGenericOrderPairTypes left_type right_type
      | _ => false
      end
  | PredicateEq | PredicateNeq | PredicateIsNotDistinctFrom =>
      match argument_types with
      | left_type :: right_type :: nil =>
          TNullEqualityPairTypes left_type right_type
      | _ => false
      end
  end.

Definition TNullNumericSourceType
    (source : scalar_numeric_source) : type TNull :=
  match source with
  | ScalarSourceZ => type_Z
  | ScalarSourceInt32 => type_int32
  | ScalarSourceInt64 => type_int64
  | ScalarSourceNumeric => type_numeric
  end.

Fixpoint TNullCaseResultType
    (argument_types : list (type TNull)) : option (type TNull) :=
  match argument_types with
  | condition_type :: branch_type :: rest =>
      if TNullTypeEqb condition_type type_bool then
        match rest with
        | else_type :: nil =>
            if TNullTypeEqb branch_type else_type
            then Some branch_type else None
        | _ =>
            match TNullCaseResultType rest with
            | Some result_type =>
                if TNullTypeEqb branch_type result_type
                then Some result_type else None
            | None => None
            end
        end
      else None
  | _ => None
  end.

Definition TNullScalarOperatorOutputType
    (operator : scalar_operator TNull) (argument_types : list (type TNull)) :
    option (type TNull) :=
  match operator with
  | ScalarPredicateValue predicate =>
      if TNullPredicateArgumentTypesValid predicate argument_types
      then Some type_bool else None
  | ScalarBoolean ScalarAnd | ScalarBoolean ScalarOr =>
      TNullRequireArgumentTypes [type_bool; type_bool] argument_types type_bool
  | ScalarBoolean ScalarNot =>
      TNullRequireArgumentTypes [type_bool] argument_types type_bool
  | ScalarCase => TNullCaseResultType argument_types
  | ScalarStringCase _ =>
      TNullRequireArgumentTypes [type_string] argument_types type_string
  | ScalarExtractDate _ =>
      TNullRequireArgumentTypes [type_date] argument_types type_numeric
  | ScalarCast ScalarCastIdentity =>
      match argument_types with
      | result_type :: nil => Some result_type
      | _ => None
      end
  | ScalarCast (ScalarCastToNumeric source) =>
      TNullRequireArgumentTypes [TNullNumericSourceType source]
        argument_types type_numeric
  | ScalarCast (ScalarCastToNumericTypmod source) =>
      TNullRequireArgumentTypes
        [TNullNumericSourceType source; type_Z; type_Z]
        argument_types type_numeric
  | ScalarCast ScalarCastInt32ToDouble =>
      TNullRequireArgumentTypes [type_int32] argument_types type_double
  | ScalarCast ScalarCastInt32ToInt64 =>
      TNullRequireArgumentTypes [type_int32] argument_types type_int64
  | ScalarCast ScalarCastInt64ToInt32 =>
      TNullRequireArgumentTypes [type_int64] argument_types type_int32
  | ScalarCast ScalarCastNumericToInt32 =>
      TNullRequireArgumentTypes [type_numeric] argument_types type_int32
  | ScalarCast ScalarCastStringToInt32 =>
      TNullRequireArgumentTypes [type_string] argument_types type_int32
  | ScalarCast ScalarCastStringToInt64 =>
      TNullRequireArgumentTypes [type_string] argument_types type_int64
  | ScalarCast ScalarCastDateToTimestamp =>
      TNullRequireArgumentTypes [type_date] argument_types type_timestamp
  | ScalarCast ScalarCastTimestampToDate =>
      TNullRequireArgumentTypes [type_timestamp] argument_types type_date
  | ScalarCast ScalarCastStringExplicit
  | ScalarCast ScalarCoerceStringImplicit =>
      TNullRequireArgumentTypes [type_string; type_Z; type_Z]
        argument_types type_string
  | ScalarAdd kind | ScalarSubtract kind | ScalarMultiply kind =>
      let numeric_type := TNullNumericKindType kind in
      TNullRequireArgumentTypes [numeric_type; numeric_type]
        argument_types numeric_type
  | ScalarDivide ScalarNumeric =>
      TNullRequireArgumentTypes
        [type_numeric; type_Z; type_numeric; type_Z]
        argument_types type_numeric
  | ScalarDivide kind =>
      let numeric_type := TNullNumericKindType kind in
      TNullRequireArgumentTypes [numeric_type; numeric_type]
        argument_types numeric_type
  | ScalarNegate kind =>
      let numeric_type := TNullNumericKindType kind in
      TNullRequireArgumentTypes [numeric_type] argument_types numeric_type
  | ScalarNumericDivideResultScale =>
      TNullRequireArgumentTypes
        [type_numeric; type_Z; type_numeric; type_Z]
        argument_types type_Z
  | ScalarNumericDivideTypmod =>
      TNullRequireArgumentTypes
        [type_numeric; type_Z; type_numeric; type_Z; type_Z; type_Z]
        argument_types type_numeric
  | ScalarPowerHalfInt64ToInt32 =>
      TNullRequireArgumentTypes [type_int64] argument_types type_int32
  | ScalarStringConcat =>
      TNullRequireArgumentTypes [type_string; type_string]
        argument_types type_string
  | ScalarSubstringNonnegative =>
      TNullRequireArgumentTypes [type_string; type_int32; type_int32]
        argument_types type_string
  | ScalarTimestampAdd _ =>
      TNullRequireArgumentTypes [type_timestamp; type_Z]
        argument_types type_timestamp
  end.

Definition TNullAggregateFunctionOutputType
    (function : aggregate_function) : type TNull :=
  match function with
  | AggregateCount => type_int64
  | AggregateSumZ | AggregateMaxZ | AggregateMinZ | AggregateAverageZ => type_Z
  | AggregateSumInt32 => type_int64
  | AggregateSumInt64Numeric
  | AggregateSumNumeric
  | AggregateAverageInt32Numeric
  | AggregateAverageInt64Numeric
  | AggregateVariancePopulationInt32
  | AggregateVarianceSampleInt32
  | AggregateStddevPopulationInt32
  | AggregateStddevSampleInt32
  | AggregateStddevSampleNumericFixed _ _
  | AggregateAverageNumericFixed _ _
  | AggregateAverageNumericAtScale _ => type_numeric
  | AggregateSumFloat | AggregateMaxFloat | AggregateMinFloat => type_float
  | AggregateSumDouble | AggregateMaxDouble | AggregateMinDouble
  | AggregateAverageFloat | AggregateAverageDouble => type_double
  | AggregateBitAndInt32 | AggregateBitOrInt32
  | AggregateMaxInt32 | AggregateMinInt32
  | AggregateSingleValueInt32 => type_int32
  | AggregateBitAndInt64 | AggregateBitOrInt64
  | AggregateMaxInt64 | AggregateMinInt64 => type_int64
  | AggregateMaxNumeric | AggregateMinNumeric => type_numeric
  | AggregateMaxString => type_string
  | AggregateNumericDisplayScale _ => type_Z
  end.

Definition TNullAggregateFunctionArgumentTypeValid
    (function : aggregate_function) (argument_type : type TNull) : bool :=
  match function with
  | AggregateCount => true
  | AggregateSumZ | AggregateMaxZ | AggregateMinZ | AggregateAverageZ =>
      TNullTypeEqb argument_type type_Z
  | AggregateSumInt32
  | AggregateBitAndInt32 | AggregateBitOrInt32
  | AggregateMaxInt32 | AggregateMinInt32
  | AggregateSingleValueInt32
  | AggregateAverageInt32Numeric
  | AggregateNumericDisplayScale _
  | AggregateVariancePopulationInt32
  | AggregateVarianceSampleInt32
  | AggregateStddevPopulationInt32
  | AggregateStddevSampleInt32 =>
      TNullTypeEqb argument_type type_int32
  | AggregateSumInt64Numeric
  | AggregateBitAndInt64 | AggregateBitOrInt64
  | AggregateMaxInt64 | AggregateMinInt64
  | AggregateAverageInt64Numeric =>
      TNullTypeEqb argument_type type_int64
  | AggregateSumFloat | AggregateMaxFloat | AggregateMinFloat
  | AggregateAverageFloat =>
      TNullTypeEqb argument_type type_float
  | AggregateSumDouble | AggregateMaxDouble | AggregateMinDouble
  | AggregateAverageDouble =>
      TNullTypeEqb argument_type type_double
  | AggregateSumNumeric | AggregateMaxNumeric | AggregateMinNumeric
  | AggregateStddevSampleNumericFixed _ _
  | AggregateAverageNumericFixed _ _
  | AggregateAverageNumericAtScale _ =>
      TNullTypeEqb argument_type type_numeric
  | AggregateMaxString => TNullTypeEqb argument_type type_string
  end.

Definition TNullAggregateOutputType (aggregate : aggregate TNull) : type TNull :=
  match aggregate with
  | AggregateCall function _ => TNullAggregateFunctionOutputType function
  | AggregateCountStar => type_int64
  end.

Definition TNullAggregateArgumentTypeValid
    (aggregate : aggregate TNull) (argument_type : type TNull) : bool :=
  match aggregate with
  | AggregateCall function _ =>
      TNullAggregateFunctionArgumentTypeValid function argument_type
  | AggregateCountStar => true
  end.

Fixpoint TNullFunTermTypeFuel (fuel : nat) (term : FunTerm) :
    option (type TNull) :=
  match fuel with
  | O => None
  | S fuel' =>
      match term with
      | F_Constant _ value => Some (NullValues.type_of_value value)
      | F_Dot _ attribute => Some (type_of_attribute TNull attribute)
      | F_Expr _ operator arguments =>
          match TNullFunTermTypesFuel fuel' arguments with
          | Some argument_types =>
              TNullScalarOperatorOutputType operator argument_types
          | None => None
          end
      end
  end
with TNullFunTermTypesFuel (fuel : nat) (terms : list FunTerm) :
    option (list (type TNull)) :=
  match fuel with
  | O => None
  | S fuel' =>
      match terms with
      | nil => Some nil
      | term :: rest =>
          match TNullFunTermTypeFuel fuel' term,
                TNullFunTermTypesFuel fuel' rest with
          | Some term_type, Some rest_types => Some (term_type :: rest_types)
          | _, _ => None
          end
      end
  end.

Definition TNullFunTermType (term : FunTerm) : option (type TNull) :=
  TNullFunTermTypeFuel (S (size_funterm TNull term)) term.

Fixpoint TNullAggTermTypeFuel (fuel : nat) (term : AggTerm) :
    option (type TNull) :=
  match fuel with
  | O => None
  | S fuel' =>
      match term with
      | A_Expr _ function_term => TNullFunTermType function_term
      | A_agg _ aggregate function_term =>
          match TNullFunTermType function_term with
          | Some argument_type =>
              if TNullAggregateArgumentTypeValid aggregate argument_type
              then Some (TNullAggregateOutputType aggregate) else None
          | None => None
          end
      | A_fun _ operator arguments =>
          match TNullAggTermTypesFuel fuel' arguments with
          | Some argument_types =>
              TNullScalarOperatorOutputType operator argument_types
          | None => None
          end
      end
  end
with TNullAggTermTypesFuel (fuel : nat) (terms : list AggTerm) :
    option (list (type TNull)) :=
  match fuel with
  | O => None
  | S fuel' =>
      match terms with
      | nil => Some nil
      | term :: rest =>
          match TNullAggTermTypeFuel fuel' term,
                TNullAggTermTypesFuel fuel' rest with
          | Some term_type, Some rest_types => Some (term_type :: rest_types)
          | _, _ => None
          end
      end
  end.

Definition TNullAggTermType (term : AggTerm) : option (type TNull) :=
  TNullAggTermTypeFuel (S (size_aggterm TNull term)) term.

Definition TNullLeafHasType (result_type : type TNull) (term : AggTerm) : Prop :=
  TNullAggTermType term = Some result_type.

Definition TNullCallHasType
    (result_type : type TNull) (operator : scalar_operator TNull)
    (argument_types : list (type TNull)) : Prop :=
  TNullScalarOperatorOutputType operator argument_types = Some result_type.

Definition TNullPredicateHasTypes
    (predicate : predicate TNull) (argument_types : list (type TNull)) : Prop :=
  TNullPredicateArgumentTypesValid predicate argument_types = true.

Definition TNullQueryExprNativeScalarAdmissible
    (basesort : relname -> Fset.set (A TNull)) (query : QueryExpr) : Prop :=
  @query_expr_native_scalar_admissible TNull relname basesort
    NullValues.is_null_value query.

Definition TNullScalarExprNativeAdmissible
    (basesort : relname -> Fset.set (A TNull)) (phase : scalar_phase)
    {kind : scalar_result_kind}
    (expression : @scalar_expr TNull relname kind) : Prop :=
  @scalar_expr_native_admissible TNull relname basesort
    NullValues.is_null_value phase kind expression.

Definition TNullQueryExprTypedNativeScalarAdmissible
    (basesort : relname -> Fset.set (A TNull)) (query : QueryExpr) : Prop :=
  @query_expr_typed_native_scalar_admissible TNull relname basesort
    TNullLeafHasType TNullCallHasType TNullPredicateHasTypes type_int64 type_bool
    NullValues.is_null_value query.

Definition TNullQueryExprTypedNativeScalarAdmissibleWithOutputs
    (basesort : relname -> Fset.set (A TNull))
    (query : QueryExpr) (expected_outputs : list (attribute TNull)) : Prop :=
  TNullQueryExprTypedNativeScalarAdmissible basesort query /\
  query_expr_outputs query = expected_outputs.

Lemma TNullQueryExprTypedNativeScalarAdmissible_is_admissible :
  forall basesort query,
    TNullQueryExprTypedNativeScalarAdmissible basesort query ->
    @query_expr_admissible TNull relname basesort query.
Proof.
  intros basesort query [[Hadmissible _] _]; exact Hadmissible.
Qed.

Lemma TNullQueryExprTypedNativeScalarAdmissibleWithOutputs_is_admissible :
  forall basesort query expected_outputs,
    TNullQueryExprTypedNativeScalarAdmissibleWithOutputs
      basesort query expected_outputs ->
    @query_expr_admissible TNull relname basesort query /\
    query_expr_outputs query = expected_outputs.
Proof.
  intros basesort query expected_outputs [Htyped Houtputs].
  split; [now apply TNullQueryExprTypedNativeScalarAdmissible_is_admissible
    | exact Houtputs].
Qed.

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

Definition WindowFullPartitionAggregateItem
    (output : Tuple.attribute TNull) (term : AggTerm) : QueryWindowItemT :=
  @QueryWindowItem TNull output
    (QueryWindowFullPartitionAggregate term).

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

(** General compositional transport for generated exact-query admissibility.
    These results use only extensional equality of base-table sorts; they do
    not inspect instances, assert query success, or weaken SQL semantics. *)
Section AdmissibilityBaseSortTransport.

Context {T : Tuple.Rcd} {generic_relname : Type}.
Variables first_basesort second_basesort :
  generic_relname -> Fset.set (A T).
Hypothesis Hbasesort :
  forall relation, first_basesort relation =S= second_basesort relation.

(** Exact-query base-sort transport only needs to move the table-scan schema
    equality; all other constructors compose their induction hypotheses. *)
Scheme All for list.
Scheme All for prod.

Lemma prop_forall_list_all_transport {A : Type}
    (recursive_property source_property target_property : A -> Prop) :
  (forall value,
    recursive_property value -> source_property value -> target_property value) ->
  forall values,
    list_all A recursive_property values ->
    prop_forall source_property values ->
    prop_forall target_property values.
Proof.
  intros Hvalue values Hall; induction Hall; cbn [prop_forall]; auto.
  intros [Hhead Htail]; split; [now apply Hvalue | now apply IHHall].
Qed.

Scheme query_expr_admissibility_induction := Induction for query_expr Sort Prop
with formula_expr_admissibility_induction :=
  Induction for formula_expr Sort Prop
with scalar_expr_admissibility_induction :=
  Induction for scalar_expr Sort Prop.

Combined Scheme query_formula_expr_admissibility_mutind
  from query_expr_admissibility_induction,
    formula_expr_admissibility_induction,
    scalar_expr_admissibility_induction.

Lemma scalar_expr_list_all_admissible_transport :
  forall expressions :
      list (@scalar_expr T generic_relname ScalarResultValue),
    list_all _
      (fun expression => forall phase,
        @scalar_expr_admissible T generic_relname first_basesort
          phase ScalarResultValue expression ->
        @scalar_expr_admissible T generic_relname second_basesort
          phase ScalarResultValue expression)
      expressions ->
    forall phase,
      prop_forall
        (@scalar_expr_admissible T generic_relname first_basesort
          phase ScalarResultValue) expressions ->
      prop_forall
        (@scalar_expr_admissible T generic_relname second_basesort
          phase ScalarResultValue) expressions.
Proof.
  intros expressions Hall; induction Hall; intros phase Hsource;
    cbn [prop_forall] in *; auto.
  destruct Hsource as [Hhead Htail]; split.
  - now apply (p phase).
  - now apply IHHall.
Qed.

Lemma scalar_select_list_all_admissible_transport :
  forall select_list : list
      (@scalar_expr T generic_relname ScalarResultValue * attribute T),
    list_all _
      (prod_all _
        (fun expression => forall phase,
          @scalar_expr_admissible T generic_relname first_basesort
            phase ScalarResultValue expression ->
          @scalar_expr_admissible T generic_relname second_basesort
            phase ScalarResultValue expression)
        _ (fun _ => unit)) select_list ->
    forall phase,
      prop_forall
        (fun item =>
          @scalar_expr_admissible T generic_relname first_basesort
            phase ScalarResultValue (fst item) /\
          scalar_expr_type (fst item) = type_of_attribute T (snd item))
        select_list ->
      prop_forall
        (fun item =>
          @scalar_expr_admissible T generic_relname second_basesort
            phase ScalarResultValue (fst item) /\
          scalar_expr_type (fst item) = type_of_attribute T (snd item))
        select_list.
Proof.
  intros select_list Hall.
  induction Hall as [|item Hitem rest Hrest IH];
    intros phase Hsource; cbn [prop_forall] in *; auto.
  inversion Hitem as [expression Hexpression attribute Hunit]; subst.
  destruct Hsource as [[Hhead Htype] Htail]; split.
  - split; [now apply (Hexpression phase) | exact Htype].
  - now apply IH.
Qed.

Lemma query_formula_scalar_expr_admissible_basesort_extensional :
  (forall query,
    @query_expr_admissible T generic_relname first_basesort query ->
    @query_expr_admissible T generic_relname second_basesort query) /\
  (forall formula phase,
    @formula_expr_admissible_at T generic_relname first_basesort phase formula ->
    @formula_expr_admissible_at T generic_relname second_basesort phase formula) /\
  (forall kind (expression : @scalar_expr T generic_relname kind) phase,
    @scalar_expr_admissible T generic_relname first_basesort
      phase kind expression ->
    @scalar_expr_admissible T generic_relname second_basesort
      phase kind expression).
Proof.
  apply query_formula_expr_admissibility_mutind; intros; cbn in *; try tauto.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: repeat split; try assumption; try eauto.
  all: try match goal with
  | IH : forall phase : scalar_phase, ?P phase -> ?Q phase,
    Hsource : ?P ?phase |- ?Q ?phase =>
      exact (IH phase Hsource)
  end.
  all: try match goal with
  | IH : forall _ : scalar_phase, _ |- _ =>
      apply IH; assumption
  end.
  all: try (eapply scalar_select_list_all_admissible_transport;
    [eassumption | eassumption]).
  all: try (eapply scalar_expr_list_all_admissible_transport;
    [eassumption | eassumption]).
  all: try (
    eapply (@prop_forall_list_all_transport _ _ _ _);
    [ intros [expression attribute] Hrecursive Hsource;
      inversion Hrecursive; subst; cbn in Hsource |- *;
      destruct Hsource as [Hadmissible Htype];
      split; [eauto | exact Htype]
    | eassumption
    | eassumption ]).
  all: try match goal with
  | Hsort : ?left =S= first_basesort ?table
      |- ?left =S= second_basesort ?table =>
      let Htable := fresh "Htable" in
      pose proof (Hbasesort table) as Htable;
      rewrite Fset.equal_spec in Hsort, Htable |- *;
      intro attribute;
      rewrite <- (Htable attribute);
      exact (Hsort attribute)
  end.
  all: try match goal with
  | IH : ?source -> ?target, Hsource : ?source |- ?target =>
      exact (IH Hsource)
  end.
  all: eauto.
Qed.

Lemma query_formula_expr_admissible_basesort_extensional :
  (forall query,
    @query_expr_admissible T generic_relname first_basesort query ->
    @query_expr_admissible T generic_relname second_basesort query) /\
  (forall formula,
    @formula_expr_admissible T generic_relname first_basesort formula ->
    @formula_expr_admissible T generic_relname second_basesort formula).
Proof.
  split.
  - exact (proj1 query_formula_scalar_expr_admissible_basesort_extensional).
  - intros formula Hformula.
    unfold formula_expr_admissible in *.
    exact
      (proj1 (proj2 query_formula_scalar_expr_admissible_basesort_extensional)
        formula ScalarPhaseHaving Hformula).
Qed.

Theorem query_expr_admissible_basesort_extensional :
  forall query,
    @query_expr_admissible T generic_relname first_basesort query ->
    @query_expr_admissible T generic_relname second_basesort query.
Proof.
  exact (proj1 query_formula_expr_admissible_basesort_extensional).
Qed.

Theorem formula_expr_admissible_basesort_extensional :
  forall formula,
    @formula_expr_admissible T generic_relname first_basesort formula ->
    @formula_expr_admissible T generic_relname second_basesort formula.
Proof.
  exact (proj2 query_formula_expr_admissible_basesort_extensional).
Qed.

End AdmissibilityBaseSortTransport.

(** Exact-query certificates carry the authoritative ordered output witness in
    addition to admissibility.  Generated proofs can therefore discharge
    parent-node side conditions against a small typed list instead of
    reducing the complete child query again. *)
Section CompositionalQueryExprAdmissibility.

Context {T : Tuple.Rcd} {generic_relname : Type}.
Variable basesort : generic_relname -> Fset.set (A T).

Definition query_expr_admissible_with_outputs
    (query : @query_expr T generic_relname)
    (expected_outputs : list (attribute T)) : Prop :=
  @query_expr_admissible T generic_relname basesort query /\
  query_expr_outputs query = expected_outputs.

Lemma query_expr_admissible_of_with_outputs :
  forall query expected_outputs,
    query_expr_admissible_with_outputs query expected_outputs ->
    @query_expr_admissible T generic_relname basesort query.
Proof.
  intros query expected_outputs [Hadmissible _]; exact Hadmissible.
Qed.

Lemma query_expr_admissible_with_outputs_change :
  forall query first_outputs second_outputs,
    query_expr_admissible_with_outputs query first_outputs ->
    first_outputs = second_outputs ->
    query_expr_admissible_with_outputs query second_outputs.
Proof.
  intros query first_outputs second_outputs
    [Hadmissible Houtputs] Hequal.
  split; [exact Hadmissible | now rewrite Houtputs].
Qed.

Lemma query_output_attributes_unique_from_all_diff :
  forall outputs : list (attribute T),
    ListFacts.all_diff outputs ->
    @query_output_attributes_unique T outputs.
Proof.
  intros outputs Hdistinct.
  unfold query_output_attributes_unique.
  rewrite Fset.cardinal_spec.
  exact
    (ListPermut._permut_length
      (Fset.permut_elements_mk_set (A T) outputs Hdistinct)).
Qed.

Lemma query_sort_keys_in_outputs :
  forall (outputs : list (attribute T)) keys,
    Forall
      (fun key => In (sort_key_attribute key) outputs)
      keys ->
    query_sort_keys_in_scope (@query_outputs_sort T outputs) keys.
Proof.
  intros outputs keys Hkeys key Hkey.
  unfold query_outputs_sort.
  rewrite Fset.mem_mk_set, OrderedSet.Oset.mem_bool_true_iff.
  rewrite Forall_forall in Hkeys; now apply Hkeys.
Qed.

Lemma query_attribute_not_in_outputs :
  forall (outputs : list (attribute T)) attribute,
    ~ In attribute outputs ->
    ~ attribute inS (@query_outputs_sort T outputs).
Proof.
  intros outputs attribute Hnot_in.
  unfold query_outputs_sort.
  rewrite Fset.mem_mk_set, OrderedSet.Oset.mem_bool_true_iff.
  exact Hnot_in.
Qed.

Lemma query_expr_admissible_with_outputs_error :
  forall (outputs : list (attribute T)) error,
    @query_output_attributes_unique T outputs ->
    query_expr_admissible_with_outputs
      (@QExpr_Error T generic_relname outputs error) outputs.
Proof.
  intros outputs error Houtputs; split; cbn; assumption || reflexivity.
Qed.

Lemma query_expr_admissible_with_outputs_values :
  forall (outputs : list (attribute T)) rows,
    @query_output_attributes_unique T outputs ->
    @query_values_well_sorted T (@query_outputs_sort T outputs) rows ->
    query_expr_admissible_with_outputs
      (@QExpr_Values T generic_relname outputs rows) outputs.
Proof.
  intros outputs rows Houtputs Hrows; split; cbn; intuition.
Qed.

(** The SQL unit relation has one zero-column row.  Proving this once avoids
    asking every generated module to normalize the concrete finite-bag
    implementation merely to establish that the empty tuple has no labels. *)
Lemma query_expr_admissible_with_outputs_empty_tuple :
  query_expr_admissible_with_outputs
    (@QExpr_Values T generic_relname nil
      (Febag.singleton (Fecol.CBag (CTuple T)) (empty_tuple T))) nil.
Proof.
  split.
  - cbn [query_expr_admissible].
    split.
    + apply query_output_attributes_unique_from_all_diff; constructor.
    + unfold query_values_well_sorted.
      intros row Hrow.
      rewrite Febag.mem_nb_occ, Febag.nb_occ_singleton in Hrow.
      unfold Oeset.eq_bool in Hrow.
      destruct (Oeset.compare (OTuple T) row (empty_tuple T))
        eqn:Hcompare; cbn in Hrow; try discriminate.
      rewrite Fset.equal_spec.
      intro attribute.
      pose proof (@tuple_eq_labels T row (empty_tuple T) Hcompare) as Hlabels.
      pose proof (@labels_empty_tuple T) as Hempty.
      rewrite Fset.equal_spec in Hlabels, Hempty.
      rewrite Hlabels, Hempty.
      unfold query_outputs_sort.
      rewrite Fset.mem_mk_set, Fset.empty_spec.
      reflexivity.
  - reflexivity.
Qed.

Lemma query_expr_admissible_with_outputs_table :
  forall (outputs : list (attribute T)) table,
    @query_output_attributes_unique T outputs ->
    @query_outputs_sort T outputs =S= basesort table ->
    query_expr_admissible_with_outputs
      (@QExpr_Table T generic_relname outputs table) outputs.
Proof.
  intros outputs table Houtputs Hsort; split; cbn; intuition.
Qed.

Lemma query_expr_admissible_with_outputs_set :
  forall operation left right left_outputs right_outputs,
    query_expr_admissible_with_outputs left left_outputs ->
    query_expr_admissible_with_outputs right right_outputs ->
    left_outputs = right_outputs ->
    query_expr_admissible_with_outputs
      (@QExpr_Set T generic_relname operation left right) left_outputs.
Proof.
  intros operation left right left_outputs right_outputs
    [Hleft Hleft_outputs] [Hright Hright_outputs] Houtputs.
  split.
  - cbn [query_expr_admissible].
    repeat split; try assumption.
    now rewrite Hleft_outputs, Hright_outputs.
  - cbn [query_expr_outputs]; exact Hleft_outputs.
Qed.

Lemma query_expr_admissible_with_outputs_natural_join :
  forall left right left_outputs right_outputs,
    query_expr_admissible_with_outputs left left_outputs ->
    query_expr_admissible_with_outputs right right_outputs ->
    query_expr_admissible_with_outputs
      (@QExpr_NaturalJoin T generic_relname left right)
      (@query_natural_join_outputs T left_outputs right_outputs).
Proof.
  intros left right left_outputs right_outputs
    [Hleft Hleft_outputs] [Hright Hright_outputs].
  split.
  - cbn [query_expr_admissible]; now split.
  - cbn [query_expr_outputs]; now rewrite Hleft_outputs, Hright_outputs.
Qed.

Lemma query_expr_admissible_with_outputs_cross_join :
  forall left right left_outputs right_outputs,
    query_expr_admissible_with_outputs left left_outputs ->
    query_expr_admissible_with_outputs right right_outputs ->
    @query_output_sorts_disjoint T
      (@query_outputs_sort T left_outputs)
      (@query_outputs_sort T right_outputs) ->
    query_expr_admissible_with_outputs
      (@QExpr_CrossJoin T generic_relname left right)
      (left_outputs ++ right_outputs).
Proof.
  intros left right left_outputs right_outputs
    [Hleft Hleft_outputs] [Hright Hright_outputs] Hdisjoint.
  split.
  - cbn [query_expr_admissible].
    repeat split; try assumption.
    unfold query_expr_sort; now rewrite Hleft_outputs, Hright_outputs.
  - cbn [query_expr_outputs]; now rewrite Hleft_outputs, Hright_outputs.
Qed.

Lemma query_expr_admissible_with_outputs_join :
  forall kind predicate matched_select left_select right_select
      left right left_outputs right_outputs,
    @formula_expr_admissible_at T generic_relname basesort
      ScalarPhaseOn predicate ->
    query_expr_admissible_with_outputs left left_outputs ->
    query_expr_admissible_with_outputs right right_outputs ->
    query_join_projection_sorts_compatible
      kind matched_select left_select right_select ->
    query_join_projections_unique
      kind matched_select left_select right_select ->
    query_join_projections_phase_admissible
      kind matched_select left_select right_select ->
    query_expr_admissible_with_outputs
      (@QExpr_Join T generic_relname kind predicate
        matched_select left_select right_select left right)
      (match kind with
       | QueryJoinSemi | QueryJoinAnti => select_list_outputs left_select
       | _ => select_list_outputs matched_select
       end).
Proof.
  intros kind predicate matched_select left_select right_select
    left right left_outputs right_outputs Hpredicate
    [Hleft _] [Hright _] Hcompatible Hunique Hphase.
  split.
  - cbn [query_expr_admissible]; tauto.
  - reflexivity.
Qed.

Lemma query_expr_admissible_with_outputs_project :
  forall select_list input input_outputs,
    query_expr_admissible_with_outputs input input_outputs ->
    query_select_list_outputs_unique select_list ->
    select_list_phase_admissible ScalarPhaseRowSelect select_list ->
    query_expr_admissible_with_outputs
      (@QExpr_Project T generic_relname select_list input)
      (select_list_outputs select_list).
Proof.
  intros select_list input input_outputs [Hinput _] Hunique Hphase.
  split; cbn [query_expr_admissible query_expr_outputs]; intuition.
Qed.

Lemma query_expr_admissible_with_outputs_scalar_project :
  forall select_list input input_outputs,
    query_expr_admissible_with_outputs input input_outputs ->
    @query_output_attributes_unique T (scalar_select_outputs select_list) ->
    Forall
      (fun item =>
        @scalar_expr_admissible T generic_relname basesort
          ScalarPhaseRowSelect ScalarResultValue (fst item) /\
        scalar_expr_type (fst item) = type_of_attribute T (snd item))
      select_list ->
    query_expr_admissible_with_outputs
      (@QExpr_ScalarProject T generic_relname select_list input)
      (scalar_select_outputs select_list).
Proof.
  intros select_list input input_outputs [Hinput _] Hunique Hitems.
  split.
  - cbn [query_expr_admissible].
    repeat split; try assumption.
    clear Hinput Hunique.
    induction Hitems; cbn [prop_forall]; [exact I |].
    split; [assumption | exact IHHitems].
  - reflexivity.
Qed.

Lemma query_expr_admissible_with_outputs_row_map :
  forall (outputs : list (attribute T)) row_map input input_outputs,
    query_expr_admissible_with_outputs input input_outputs ->
    @query_output_attributes_unique T outputs ->
    @query_row_map_well_sorted T (@query_outputs_sort T outputs) row_map ->
    query_expr_admissible_with_outputs
      (@QExpr_RowMap T generic_relname outputs row_map input) outputs.
Proof.
  intros outputs row_map input input_outputs [Hinput _] Houtputs Hrow_map.
  split; cbn [query_expr_admissible query_expr_outputs]; intuition.
Qed.

Lemma query_expr_admissible_with_outputs_filter :
  forall predicate input input_outputs,
    query_expr_admissible_with_outputs input input_outputs ->
    @formula_expr_admissible_at T generic_relname basesort
      ScalarPhaseWhere predicate ->
    query_expr_admissible_with_outputs
      (@QExpr_Filter T generic_relname predicate input) input_outputs.
Proof.
  intros predicate input input_outputs
    [Hinput Hinput_outputs] Hpredicate.
  split.
  - cbn [query_expr_admissible]; now split.
  - cbn [query_expr_outputs]; exact Hinput_outputs.
Qed.

Lemma query_expr_admissible_with_outputs_scalar_filter :
  forall predicate input input_outputs,
    query_expr_admissible_with_outputs input input_outputs ->
    @scalar_expr_admissible T generic_relname basesort
      ScalarPhaseWhere ScalarResultBoolean predicate ->
    query_expr_admissible_with_outputs
      (@QExpr_ScalarFilter T generic_relname predicate input) input_outputs.
Proof.
  intros predicate input input_outputs
    [Hinput Hinput_outputs] Hpredicate.
  split.
  - cbn [query_expr_admissible]; now split.
  - cbn [query_expr_outputs]; exact Hinput_outputs.
Qed.

Lemma formula_expr_scalar_admissible_at :
  forall phase predicate,
    @scalar_expr_admissible T generic_relname basesort
      phase ScalarResultBoolean predicate ->
    @formula_expr_admissible_at T generic_relname basesort phase
      (@FExpr_Scalar T generic_relname predicate).
Proof.
  intros phase predicate Hpredicate; exact Hpredicate.
Qed.

Lemma formula_expr_scalar_admissible :
  forall predicate,
    @scalar_expr_admissible T generic_relname basesort
      ScalarPhaseHaving ScalarResultBoolean predicate ->
    @formula_expr_admissible T generic_relname basesort
      (@FExpr_Scalar T generic_relname predicate).
Proof.
  intros predicate Hpredicate; exact Hpredicate.
Qed.

Lemma query_expr_admissible_with_outputs_group :
  forall select_list group_terms having input input_outputs,
    query_expr_admissible_with_outputs input input_outputs ->
    @formula_expr_admissible T generic_relname basesort having ->
    query_select_list_outputs_unique select_list ->
    select_list_phase_admissible ScalarPhaseSelect select_list ->
    prop_forall (aggterm_phase_admissible ScalarPhaseGroupBy) group_terms ->
    query_expr_admissible_with_outputs
      (@QExpr_Group T generic_relname
        select_list group_terms having input)
      (select_list_outputs select_list).
Proof.
  intros select_list group_terms having input input_outputs
    [Hinput _] Hhaving Hunique Hselect Hgroup_terms.
  split; cbn [query_expr_admissible query_expr_outputs]; intuition.
Qed.

Lemma query_expr_admissible_with_outputs_scalar_group :
  forall select_list group_keys group_terms having input input_outputs,
    query_expr_admissible_with_outputs input input_outputs ->
    @query_output_attributes_unique T (scalar_select_outputs select_list) ->
    Forall
      (fun item =>
        @scalar_expr_admissible T generic_relname basesort
          ScalarPhaseSelect ScalarResultValue (fst item) /\
        scalar_expr_type (fst item) = type_of_attribute T (snd item))
      select_list ->
    @scalar_expr_admissible T generic_relname basesort
      ScalarPhaseHaving ScalarResultBoolean having ->
    Forall
      (@scalar_expr_admissible T generic_relname basesort
        ScalarPhaseGroupBy ScalarResultValue) group_keys ->
    scalar_group_key_terms group_keys = Some group_terms ->
    query_expr_admissible_with_outputs
      (@QExpr_ScalarGroup T generic_relname
        select_list group_keys having input)
      (scalar_select_outputs select_list).
Proof.
  intros select_list group_keys group_terms having input input_outputs
    [Hinput _] Hunique Hselect Hhaving Hkeys Hextract.
  split; [|reflexivity].
  cbn [query_expr_admissible].
  repeat split; try assumption.
  - clear Hinput Hunique Hhaving Hkeys Hextract.
    induction Hselect; cbn [prop_forall]; [exact I |].
    split; [assumption | exact IHHselect].
  - clear Hinput Hunique Hhaving Hselect Hextract.
    induction Hkeys; cbn [prop_forall]; [exact I |].
    split; [assumption | exact IHHkeys].
  - now exists group_terms.
Qed.

Lemma query_expr_admissible_with_outputs_grouping_sets :
  forall grouping_sets input input_outputs,
    query_expr_admissible_with_outputs input input_outputs ->
    query_grouping_sets_well_formed grouping_sets ->
    query_grouping_sets_phase_admissible grouping_sets ->
    query_expr_admissible_with_outputs
      (@QExpr_GroupingSets T generic_relname grouping_sets input)
      (query_grouping_sets_outputs grouping_sets).
Proof.
  intros grouping_sets input input_outputs [Hinput _] Hgroups Hphase.
  split; cbn [query_expr_admissible query_expr_outputs]; intuition.
Qed.

Lemma query_expr_admissible_with_outputs_rank :
  forall partition_keys order_keys rank_attribute embed_rank
      input input_outputs,
    query_expr_admissible_with_outputs input input_outputs ->
    query_sort_keys_in_scope
      (@query_outputs_sort T input_outputs) partition_keys ->
    query_sort_keys_in_scope
      (@query_outputs_sort T input_outputs) order_keys ->
    ~ rank_attribute inS (@query_outputs_sort T input_outputs) ->
    query_expr_admissible_with_outputs
      (@QExpr_Rank T generic_relname partition_keys order_keys
        rank_attribute embed_rank input)
      (input_outputs ++ rank_attribute :: nil).
Proof.
  intros partition_keys order_keys rank_attribute embed_rank
    input input_outputs [Hinput Hinput_outputs]
    Hpartition Horder Hfresh.
  split.
  - cbn [query_expr_admissible].
    repeat split; try assumption;
      unfold query_expr_sort; now rewrite Hinput_outputs.
  - cbn [query_expr_outputs]; now rewrite Hinput_outputs.
Qed.

Lemma query_expr_admissible_with_outputs_window :
  forall partition_keys order_keys items input input_outputs,
    query_expr_admissible_with_outputs input input_outputs ->
    query_sort_keys_in_scope
      (@query_outputs_sort T input_outputs) partition_keys ->
    query_sort_keys_in_scope
      (@query_outputs_sort T input_outputs) order_keys ->
    Forall
      (fun item =>
        ~ qwi_attribute item inS (@query_outputs_sort T input_outputs))
      items ->
    length (map (@qwi_attribute T) items) =
      Fset.cardinal (A T)
        (Fset.mk_set (A T) (map (@qwi_attribute T) items)) ->
    query_expr_admissible_with_outputs
      (@QExpr_Window T generic_relname partition_keys order_keys items input)
      (input_outputs ++ map (@qwi_attribute T) items).
Proof.
  intros partition_keys order_keys items input input_outputs
    [Hinput Hinput_outputs] Hpartition Horder Hfresh Hunique.
  split.
  - cbn [query_expr_admissible].
    repeat split; try assumption.
    + unfold query_expr_sort; now rewrite Hinput_outputs.
    + unfold query_expr_sort; now rewrite Hinput_outputs.
    + unfold query_expr_sort; now rewrite Hinput_outputs.
  - cbn [query_expr_outputs]; now rewrite Hinput_outputs.
Qed.

Lemma query_expr_admissible_with_outputs_distinct :
  forall input input_outputs,
    query_expr_admissible_with_outputs input input_outputs ->
    query_expr_admissible_with_outputs
      (@QExpr_Distinct T generic_relname input) input_outputs.
Proof.
  intros input input_outputs [Hinput Hinput_outputs].
  split; cbn [query_expr_admissible query_expr_outputs]; assumption.
Qed.

Lemma query_expr_admissible_with_outputs_order_by :
  forall keys input input_outputs,
    query_expr_admissible_with_outputs input input_outputs ->
    query_sort_keys_in_scope (@query_outputs_sort T input_outputs) keys ->
    query_expr_admissible_with_outputs
      (@QExpr_OrderBy T generic_relname keys input) input_outputs.
Proof.
  intros keys input input_outputs [Hinput Hinput_outputs] Hkeys.
  split.
  - cbn [query_expr_admissible]; split; [assumption |].
    unfold query_expr_sort; now rewrite Hinput_outputs.
  - cbn [query_expr_outputs]; exact Hinput_outputs.
Qed.

Lemma query_expr_admissible_with_outputs_offset :
  forall count input input_outputs,
    query_expr_admissible_with_outputs input input_outputs ->
    query_expr_admissible_with_outputs
      (@QExpr_Offset T generic_relname count input) input_outputs.
Proof.
  intros count input input_outputs [Hinput Hinput_outputs].
  split; cbn [query_expr_admissible query_expr_outputs]; assumption.
Qed.

Lemma query_expr_admissible_with_outputs_fetch :
  forall count input input_outputs,
    query_expr_admissible_with_outputs input input_outputs ->
    query_expr_admissible_with_outputs
      (@QExpr_Fetch T generic_relname count input) input_outputs.
Proof.
  intros count input input_outputs [Hinput Hinput_outputs].
  split; cbn [query_expr_admissible query_expr_outputs]; assumption.
Qed.

Lemma formula_expr_not_admissible :
  forall formula,
    @formula_expr_admissible T generic_relname basesort formula ->
    @formula_expr_admissible T generic_relname basesort
      (@FExpr_Not T generic_relname formula).
Proof.
  intros formula Hformula.
  cbn [formula_expr_admissible].
  exact Hformula.
Qed.

Lemma formula_expr_not_admissible_at :
  forall phase formula,
    @formula_expr_admissible_at T generic_relname basesort phase formula ->
    @formula_expr_admissible_at T generic_relname basesort phase
      (@FExpr_Not T generic_relname formula).
Proof.
  intros phase formula Hformula; exact Hformula.
Qed.

Lemma formula_expr_quant_admissible_at_from_outputs :
  forall phase quantifier predicate arguments subquery expected_outputs,
    query_expr_admissible_with_outputs subquery expected_outputs ->
    prop_forall (aggterm_phase_admissible phase) arguments ->
    length arguments = 1%nat ->
    length expected_outputs = 1%nat ->
    (length arguments + length expected_outputs)%nat =
      predicate_arity T predicate ->
    @formula_expr_admissible_at T generic_relname basesort phase
      (@FExpr_Quant T generic_relname
        quantifier predicate arguments subquery).
Proof.
  intros phase quantifier predicate arguments subquery expected_outputs
    [Hquery Houtputs] Hphase Harguments Hsubquery Harity.
  cbn [formula_expr_admissible_at].
  repeat split; try assumption; now rewrite Houtputs.
Qed.

Lemma formula_expr_in_admissible_at_from_outputs :
  forall phase (select_items : list (@select T)) subquery expected_outputs,
    query_expr_admissible_with_outputs subquery expected_outputs ->
    select_list_phase_admissible phase (@_Select_List T select_items) ->
    query_in_positionally_aligned
      (@_Select_List T select_items) expected_outputs ->
    @formula_expr_admissible_at T generic_relname basesort phase
      (@FExpr_In T generic_relname select_items subquery).
Proof.
  intros phase select_items subquery expected_outputs
    [Hquery Houtputs] Hphase Haligned.
  cbn [formula_expr_admissible_at].
  split; [exact Hquery |].
  split; [exact Hphase |].
  split.
  - unfold query_expr_sort, select_list_sort, query_outputs_sort.
    rewrite Houtputs.
    pose proof Haligned as Hpositioned.
    destruct Hpositioned as [_ [_ Hposition]].
    rewrite Hposition; apply Fset.equal_refl.
  - now rewrite Houtputs.
Qed.

Lemma formula_expr_exists_admissible_at_from_outputs :
  forall phase subquery expected_outputs,
    query_expr_admissible_with_outputs subquery expected_outputs ->
    @formula_expr_admissible_at T generic_relname basesort phase
      (@FExpr_Exists T generic_relname subquery).
Proof.
  intros phase subquery expected_outputs [Hquery _]; exact Hquery.
Qed.

Lemma aggterm_phase_admissible_having :
  forall term : @aggterm T,
    aggterm_phase_admissible ScalarPhaseHaving term.
Proof.
  intro term; left; reflexivity.
Qed.

Lemma select_list_phase_admissible_having :
  forall select_items : list (@select T),
    select_list_phase_admissible ScalarPhaseHaving
      (@_Select_List T select_items).
Proof.
  intro select_items; induction select_items as [|[term attribute] rest IH];
    cbn [select_list_phase_admissible prop_forall].
  - exact I.
  - split; [apply aggterm_phase_admissible_having | exact IH].
Qed.

Lemma formula_expr_quant_admissible_from_outputs :
  forall quantifier predicate arguments subquery expected_outputs,
    query_expr_admissible_with_outputs subquery expected_outputs ->
    length arguments = 1%nat ->
    length expected_outputs = 1%nat ->
    (length arguments + length expected_outputs)%nat =
      predicate_arity T predicate ->
    @formula_expr_admissible T generic_relname basesort
      (@FExpr_Quant T generic_relname
        quantifier predicate arguments subquery).
Proof.
  intros quantifier predicate arguments subquery expected_outputs
    [Hquery Houtputs] Harguments Hsubquery Harity.
  eapply formula_expr_quant_admissible_at_from_outputs.
  - now split.
  - clear Harguments Hsubquery Harity Houtputs.
    induction arguments; cbn [prop_forall];
      [exact I | split; [apply aggterm_phase_admissible_having | exact IHarguments]].
  - exact Harguments.
  - now rewrite Houtputs.
  - now rewrite Houtputs.
Qed.

Lemma formula_expr_in_admissible_from_outputs :
  forall (select_items : list (@select T)) subquery expected_outputs,
    query_expr_admissible_with_outputs subquery expected_outputs ->
    query_in_positionally_aligned
      (@_Select_List T select_items) expected_outputs ->
    @formula_expr_admissible T generic_relname basesort
      (@FExpr_In T generic_relname select_items subquery).
Proof.
  intros select_items subquery expected_outputs
    [Hquery Houtputs] Haligned.
  eapply formula_expr_in_admissible_at_from_outputs.
  - now split.
  - apply select_list_phase_admissible_having.
  - now rewrite Houtputs.
Qed.

Lemma formula_expr_exists_admissible_from_outputs :
  forall subquery expected_outputs,
    query_expr_admissible_with_outputs subquery expected_outputs ->
    @formula_expr_admissible T generic_relname basesort
      (@FExpr_Exists T generic_relname subquery).
Proof.
  intros subquery expected_outputs [Hquery _].
  exact Hquery.
Qed.

End CompositionalQueryExprAdmissibility.

(** Schema conformance states the same pointwise base-sort equality in the
    opposite orientation from certificate transport. *)
Theorem query_expr_admissible_database_schema_transport :
  forall expected constraints actual query,
    database_conforms_schema expected constraints actual ->
    @query_expr_admissible TNull relname (@_basesort TNull expected) query ->
    @query_expr_admissible TNull relname (@_basesort TNull actual) query.
Proof.
  intros expected constraints actual query Hschema Hadmissible.
  eapply query_expr_admissible_basesort_extensional.
  - intro relation.
    pose proof
      (database_conforms_schema_basesort
        expected constraints actual Hschema relation) as Hactual.
    rewrite Fset.equal_spec in Hactual |- *.
    intro attribute; symmetry; apply Hactual.
  - exact Hadmissible.
Qed.
