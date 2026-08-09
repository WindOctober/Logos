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

(** Reflection laws for the closed TNull type catalog.  These let admission
    proofs reason about signatures without unfolding the catalog cases. *)
Lemma TNullTypeEqb_eq :
  forall left right,
    TNullTypeEqb left right = true <-> left = right.
Proof.
intros left right; destruct left, right; cbn; split;
  intro H; try discriminate; reflexivity.
Qed.

Lemma TNullTypeListEqb_eq :
  forall left right,
    TNullTypeListEqb left right = true <-> left = right.
Proof.
induction left as [|left_type left_rest IH];
  destruct right as [|right_type right_rest]; cbn.
- split; reflexivity.
- split; intro H; discriminate.
- split; intro H; discriminate.
- rewrite Bool.Bool.andb_true_iff, TNullTypeEqb_eq, IH.
  split.
  + intros [-> ->]; reflexivity.
  + intro H; inversion H; now split.
Qed.

Definition TNullRequireArgumentTypes
    (expected actual : list (type TNull)) (result_type : type TNull) :
    option (type TNull) :=
  if TNullTypeListEqb expected actual then Some result_type else None.

Lemma TNullRequireArgumentTypes_some_iff :
  forall expected actual result_type inferred_type,
    TNullRequireArgumentTypes expected actual result_type =
      Some inferred_type <->
    expected = actual /\ result_type = inferred_type.
Proof.
intros expected actual result_type inferred_type.
unfold TNullRequireArgumentTypes.
destruct (TNullTypeListEqb expected actual) eqn:Htypes.
- apply TNullTypeListEqb_eq in Htypes; subst actual.
  split.
  + intro H; inversion H; now split.
  + intros [_ ->]; reflexivity.
- split.
  + discriminate.
  + intros [Hequal _]; subst actual.
    pose proof
      (proj2 (TNullTypeListEqb_eq expected expected) eq_refl) as Hrefl.
    congruence.
Qed.

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

(** Primitive syntax/type bridges for the TNull constructors exposed by
    [TNullSyntax].  Aggregate validity remains an explicit premise. *)
Lemma TNullFunTermType_Constant :
  forall value,
    TNullFunTermType (Constant value) =
      Some (NullValues.type_of_value value).
Proof.
reflexivity.
Qed.

Lemma TNullFunTermType_Dot :
  forall attribute,
    TNullFunTermType (Dot attribute) =
      Some (type_of_attribute TNull attribute).
Proof.
reflexivity.
Qed.

Lemma TNullAggTermType_AExpr :
  forall term,
    TNullAggTermType (AExpr term) = TNullFunTermType term.
Proof.
reflexivity.
Qed.

Lemma TNullAggTermType_AAggregate :
  forall function quantifier argument argument_type,
    TNullFunTermType argument = Some argument_type ->
    TNullAggTermType (AAggregate function quantifier argument) =
      if TNullAggregateFunctionArgumentTypeValid function argument_type
      then Some (TNullAggregateFunctionOutputType function) else None.
Proof.
intros function quantifier argument argument_type Htype.
change
  (match TNullFunTermType argument with
   | Some actual_type =>
       if TNullAggregateFunctionArgumentTypeValid function actual_type
       then Some (TNullAggregateFunctionOutputType function) else None
   | None => None
   end =
   if TNullAggregateFunctionArgumentTypeValid function argument_type
   then Some (TNullAggregateFunctionOutputType function) else None).
now rewrite Htype.
Qed.

Lemma TNullAggTermType_ACountStar :
  TNullAggTermType ACountStar = Some type_int64.
Proof.
reflexivity.
Qed.

(** A strict flat function term remains useful inside the reviewed aggregate
    kernel, but it must not smuggle lazy CASE, schedule-sensitive Boolean
    evaluation, or predicate-to-value conversion below the typed scalar AST. *)
Definition TNullStrictScalarOperatorAllowed
    (operator : scalar_operator TNull) : bool :=
  match operator with
  | ScalarBoolean _ | ScalarPredicateValue _ | ScalarCase => false
  | _ => true
  end.

Fixpoint TNullStrictFunTermAllowed (term : FunTerm) : bool :=
  match term with
  | F_Constant _ _ | F_Dot _ _ => true
  | F_Expr _ operator arguments =>
      TNullStrictScalarOperatorAllowed operator &&
        forallb TNullStrictFunTermAllowed arguments
  end.

(** A scalar leaf is atomic, or it is the one retained true-aggregate kernel.
    Ordinary flat calls use [SExpr_Call]; Boolean scheduling, predicates, and
    CASE use their dedicated typed constructors. *)
Definition TNullScalarLeafAllowed (term : AggTerm) : bool :=
  match term with
  | A_Expr _ (F_Constant _ _) | A_Expr _ (F_Dot _ _) => true
  | A_agg _ _ argument => TNullStrictFunTermAllowed argument
  | A_Expr _ (F_Expr _ _ _) | A_fun _ _ _ => false
  end.

Definition TNullLeafHasType (result_type : type TNull) (term : AggTerm) : Prop :=
  TNullScalarLeafAllowed term = true /\
  TNullAggTermType term = Some result_type.

Definition TNullCallHasType
    (result_type : type TNull) (operator : scalar_operator TNull)
    (argument_types : list (type TNull)) : Prop :=
  TNullStrictScalarOperatorAllowed operator = true /\
  TNullScalarOperatorOutputType operator argument_types = Some result_type.

Definition TNullPredicateHasTypes
    (predicate : predicate TNull) (argument_types : list (type TNull)) : Prop :=
  TNullPredicateArgumentTypesValid predicate argument_types = true.

Definition TNullQueryExprAdmissible
    (basesort : relname -> Fset.set (A TNull)) (query : QueryExpr) : Prop :=
  @query_expr_admissible TNull relname basesort
      TNullLeafHasType TNullCallHasType TNullPredicateHasTypes
      type_int64 type_bool NullValues.is_null_value query /\
  @query_expr_analysis_error_well_placed TNull relname query /\
  @query_expr_boolean_sites_well_formed TNull relname query.

Definition TNullScalarExprAdmissible
    (basesort : relname -> Fset.set (A TNull)) (phase : scalar_phase)
    {kind : scalar_result_kind}
    (expression : @scalar_expr TNull relname kind) : Prop :=
  @scalar_expr_admissible TNull relname basesort
      TNullLeafHasType TNullCallHasType TNullPredicateHasTypes
      type_int64 type_bool NullValues.is_null_value phase kind expression /\
  @scalar_expr_contains_analysis_error TNull relname kind expression = false /\
  @scalar_expr_boolean_sites_well_formed TNull relname kind expression.

Definition TNullQueryExprAdmissibleWithOutputs
    (basesort : relname -> Fset.set (A TNull))
    (query : QueryExpr) (expected_outputs : list (attribute TNull)) : Prop :=
  TNullQueryExprAdmissible basesort query /\
  query_expr_outputs query = expected_outputs.

Lemma TNullQueryExprAdmissibleWithOutputs_intro :
  forall basesort query expected_outputs,
    (@query_expr_admissible TNull relname basesort
      TNullLeafHasType TNullCallHasType TNullPredicateHasTypes
      type_int64 type_bool NullValues.is_null_value query /\
     query_expr_outputs query = expected_outputs) ->
    query_expr_analysis_error_well_placed query ->
    query_expr_boolean_sites_well_formed query ->
    TNullQueryExprAdmissibleWithOutputs basesort query expected_outputs.
Proof.
intros basesort query expected_outputs [Hadmissible Houtputs]
  Herror Hsites.
unfold TNullQueryExprAdmissibleWithOutputs.
split.
- unfold TNullQueryExprAdmissible.
  split; [exact Hadmissible|now split].
- exact Houtputs.
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

Definition eval_query_expr_outcome_in_env
    (db : db_state)
    (env : Env.env TNull)
    (q : QueryExpr) :=
  @eval_query_expr_possible_outcome TNull relname
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
intros db env output_attributes row_map input error [schedule H].
exists schedule; now apply EQuery_RowMapChildError.
Qed.

Definition eval_query_expr_outcome_in_state
    (db : db_state)
    (q : QueryExpr) :=
  eval_query_expr_outcome_in_env db nil q.

Definition query_expr_equiv_in_env
    (db : db_state)
    (env : Env.env TNull)
    (left right : QueryExpr) : Prop :=
  @query_expr_possible_equiv TNull relname
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
  @query_expr_possible_outcome_equiv TNull relname
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
  @query_program_possible_equiv TNull relname
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
  @query_program_possible_outcome_equiv TNull relname
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
Variables leaf_has_type : type T -> @aggterm T -> Prop.
Variable call_has_type :
  type T -> scalar_operator T -> list (type T) -> Prop.
Variable predicate_has_types : predicate T -> list (type T) -> Prop.
Variables rank_type boolean_type : type T.
Variable value_is_null : value T -> bool.
Variables first_basesort second_basesort :
  generic_relname -> Fset.set (A T).
Hypothesis Hbasesort :
  forall relation, first_basesort relation =S= second_basesort relation.

Scheme All for list.
Scheme All for prod.

Local Lemma prop_forall_list_all_transport {A : Type}
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
with scalar_expr_admissibility_induction :=
  Induction for scalar_expr Sort Prop.

Combined Scheme query_scalar_expr_admissibility_mutind
  from query_expr_admissibility_induction,
    scalar_expr_admissibility_induction.

Local Lemma scalar_expr_list_all_admissible_transport :
  forall kind (expressions : list (@scalar_expr T generic_relname kind)),
    list_all _
      (fun expression => forall phase,
        @scalar_expr_admissible T generic_relname first_basesort
          leaf_has_type call_has_type predicate_has_types
          rank_type boolean_type value_is_null phase kind expression ->
        @scalar_expr_admissible T generic_relname second_basesort
          leaf_has_type call_has_type predicate_has_types
          rank_type boolean_type value_is_null phase kind expression)
      expressions ->
    forall phase,
      prop_forall
        (@scalar_expr_admissible T generic_relname first_basesort
          leaf_has_type call_has_type predicate_has_types
          rank_type boolean_type value_is_null phase kind) expressions ->
      prop_forall
        (@scalar_expr_admissible T generic_relname second_basesort
          leaf_has_type call_has_type predicate_has_types
          rank_type boolean_type value_is_null phase kind) expressions.
Proof.
  intros kind expressions Hall; induction Hall; intros phase Hsource;
    cbn [prop_forall] in *; auto.
  destruct Hsource as [Hhead Htail]; split.
  - now apply (p phase).
  - now apply IHHall.
Qed.

Local Lemma scalar_select_list_all_admissible_transport :
  forall select_list : list
      (@scalar_expr T generic_relname ScalarResultValue * attribute T),
    list_all _
      (prod_all _
        (fun expression => forall phase,
          @scalar_expr_admissible T generic_relname first_basesort
            leaf_has_type call_has_type predicate_has_types
            rank_type boolean_type value_is_null
            phase ScalarResultValue expression ->
          @scalar_expr_admissible T generic_relname second_basesort
            leaf_has_type call_has_type predicate_has_types
            rank_type boolean_type value_is_null
            phase ScalarResultValue expression)
        _ (fun _ => unit)) select_list ->
    forall phase,
      prop_forall
        (fun item =>
          @scalar_expr_admissible T generic_relname first_basesort
            leaf_has_type call_has_type predicate_has_types
            rank_type boolean_type value_is_null
            phase ScalarResultValue (fst item) /\
          scalar_expr_type (fst item) = type_of_attribute T (snd item))
        select_list ->
      prop_forall
        (fun item =>
          @scalar_expr_admissible T generic_relname second_basesort
            leaf_has_type call_has_type predicate_has_types
            rank_type boolean_type value_is_null
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

Local Lemma scalar_join_selects_all_admissible_transport :
  forall kind matched_select left_select right_select,
    list_all _
      (prod_all _
        (fun expression => forall phase,
          @scalar_expr_admissible T generic_relname first_basesort
            leaf_has_type call_has_type predicate_has_types
            rank_type boolean_type value_is_null
            phase ScalarResultValue expression ->
          @scalar_expr_admissible T generic_relname second_basesort
            leaf_has_type call_has_type predicate_has_types
            rank_type boolean_type value_is_null
            phase ScalarResultValue expression)
        _ (fun _ => unit)) matched_select ->
    list_all _
      (prod_all _
        (fun expression => forall phase,
          @scalar_expr_admissible T generic_relname first_basesort
            leaf_has_type call_has_type predicate_has_types
            rank_type boolean_type value_is_null
            phase ScalarResultValue expression ->
          @scalar_expr_admissible T generic_relname second_basesort
            leaf_has_type call_has_type predicate_has_types
            rank_type boolean_type value_is_null
            phase ScalarResultValue expression)
        _ (fun _ => unit)) left_select ->
    list_all _
      (prod_all _
        (fun expression => forall phase,
          @scalar_expr_admissible T generic_relname first_basesort
            leaf_has_type call_has_type predicate_has_types
            rank_type boolean_type value_is_null
            phase ScalarResultValue expression ->
          @scalar_expr_admissible T generic_relname second_basesort
            leaf_has_type call_has_type predicate_has_types
            rank_type boolean_type value_is_null
            phase ScalarResultValue expression)
        _ (fun _ => unit)) right_select ->
    (match kind with
     | QueryJoinInner =>
         prop_forall
           (fun item =>
             @scalar_expr_admissible T generic_relname first_basesort
               leaf_has_type call_has_type predicate_has_types
               rank_type boolean_type value_is_null
               ScalarPhaseRowSelect ScalarResultValue (fst item) /\
             scalar_expr_type (fst item) =
               type_of_attribute T (snd item)) matched_select
     | QueryJoinLeft =>
         prop_forall
           (fun item =>
             @scalar_expr_admissible T generic_relname first_basesort
               leaf_has_type call_has_type predicate_has_types
               rank_type boolean_type value_is_null
               ScalarPhaseRowSelect ScalarResultValue (fst item) /\
             scalar_expr_type (fst item) =
               type_of_attribute T (snd item)) matched_select /\
         prop_forall
           (fun item =>
             @scalar_expr_admissible T generic_relname first_basesort
               leaf_has_type call_has_type predicate_has_types
               rank_type boolean_type value_is_null
               ScalarPhaseRowSelect ScalarResultValue (fst item) /\
             scalar_expr_type (fst item) =
               type_of_attribute T (snd item)) left_select
     | QueryJoinRight =>
         prop_forall
           (fun item =>
             @scalar_expr_admissible T generic_relname first_basesort
               leaf_has_type call_has_type predicate_has_types
               rank_type boolean_type value_is_null
               ScalarPhaseRowSelect ScalarResultValue (fst item) /\
             scalar_expr_type (fst item) =
               type_of_attribute T (snd item)) matched_select /\
         prop_forall
           (fun item =>
             @scalar_expr_admissible T generic_relname first_basesort
               leaf_has_type call_has_type predicate_has_types
               rank_type boolean_type value_is_null
               ScalarPhaseRowSelect ScalarResultValue (fst item) /\
             scalar_expr_type (fst item) =
               type_of_attribute T (snd item)) right_select
     | QueryJoinFull =>
         prop_forall
           (fun item =>
             @scalar_expr_admissible T generic_relname first_basesort
               leaf_has_type call_has_type predicate_has_types
               rank_type boolean_type value_is_null
               ScalarPhaseRowSelect ScalarResultValue (fst item) /\
             scalar_expr_type (fst item) =
               type_of_attribute T (snd item)) matched_select /\
         prop_forall
           (fun item =>
             @scalar_expr_admissible T generic_relname first_basesort
               leaf_has_type call_has_type predicate_has_types
               rank_type boolean_type value_is_null
               ScalarPhaseRowSelect ScalarResultValue (fst item) /\
             scalar_expr_type (fst item) =
               type_of_attribute T (snd item)) left_select /\
         prop_forall
           (fun item =>
             @scalar_expr_admissible T generic_relname first_basesort
               leaf_has_type call_has_type predicate_has_types
               rank_type boolean_type value_is_null
               ScalarPhaseRowSelect ScalarResultValue (fst item) /\
             scalar_expr_type (fst item) =
               type_of_attribute T (snd item)) right_select
     | QueryJoinSemi | QueryJoinAnti =>
         prop_forall
           (fun item =>
             @scalar_expr_admissible T generic_relname first_basesort
               leaf_has_type call_has_type predicate_has_types
               rank_type boolean_type value_is_null
               ScalarPhaseRowSelect ScalarResultValue (fst item) /\
             scalar_expr_type (fst item) =
               type_of_attribute T (snd item)) left_select
     end) ->
    match kind with
    | QueryJoinInner =>
        prop_forall
          (fun item =>
            @scalar_expr_admissible T generic_relname second_basesort
              leaf_has_type call_has_type predicate_has_types
              rank_type boolean_type value_is_null
              ScalarPhaseRowSelect ScalarResultValue (fst item) /\
            scalar_expr_type (fst item) =
              type_of_attribute T (snd item)) matched_select
    | QueryJoinLeft =>
        prop_forall
          (fun item =>
            @scalar_expr_admissible T generic_relname second_basesort
              leaf_has_type call_has_type predicate_has_types
              rank_type boolean_type value_is_null
              ScalarPhaseRowSelect ScalarResultValue (fst item) /\
            scalar_expr_type (fst item) =
              type_of_attribute T (snd item)) matched_select /\
        prop_forall
          (fun item =>
            @scalar_expr_admissible T generic_relname second_basesort
              leaf_has_type call_has_type predicate_has_types
              rank_type boolean_type value_is_null
              ScalarPhaseRowSelect ScalarResultValue (fst item) /\
            scalar_expr_type (fst item) =
              type_of_attribute T (snd item)) left_select
    | QueryJoinRight =>
        prop_forall
          (fun item =>
            @scalar_expr_admissible T generic_relname second_basesort
              leaf_has_type call_has_type predicate_has_types
              rank_type boolean_type value_is_null
              ScalarPhaseRowSelect ScalarResultValue (fst item) /\
            scalar_expr_type (fst item) =
              type_of_attribute T (snd item)) matched_select /\
        prop_forall
          (fun item =>
            @scalar_expr_admissible T generic_relname second_basesort
              leaf_has_type call_has_type predicate_has_types
              rank_type boolean_type value_is_null
              ScalarPhaseRowSelect ScalarResultValue (fst item) /\
            scalar_expr_type (fst item) =
              type_of_attribute T (snd item)) right_select
    | QueryJoinFull =>
        prop_forall
          (fun item =>
            @scalar_expr_admissible T generic_relname second_basesort
              leaf_has_type call_has_type predicate_has_types
              rank_type boolean_type value_is_null
              ScalarPhaseRowSelect ScalarResultValue (fst item) /\
            scalar_expr_type (fst item) =
              type_of_attribute T (snd item)) matched_select /\
        prop_forall
          (fun item =>
            @scalar_expr_admissible T generic_relname second_basesort
              leaf_has_type call_has_type predicate_has_types
              rank_type boolean_type value_is_null
              ScalarPhaseRowSelect ScalarResultValue (fst item) /\
            scalar_expr_type (fst item) =
              type_of_attribute T (snd item)) left_select /\
        prop_forall
          (fun item =>
            @scalar_expr_admissible T generic_relname second_basesort
              leaf_has_type call_has_type predicate_has_types
              rank_type boolean_type value_is_null
              ScalarPhaseRowSelect ScalarResultValue (fst item) /\
            scalar_expr_type (fst item) =
              type_of_attribute T (snd item)) right_select
    | QueryJoinSemi | QueryJoinAnti =>
        prop_forall
          (fun item =>
            @scalar_expr_admissible T generic_relname second_basesort
              leaf_has_type call_has_type predicate_has_types
              rank_type boolean_type value_is_null
              ScalarPhaseRowSelect ScalarResultValue (fst item) /\
            scalar_expr_type (fst item) =
              type_of_attribute T (snd item)) left_select
    end.
Proof.
  intros kind matched_select left_select right_select
    Hmatched Hleft Hright Hsource.
  destruct kind; cbn in Hsource |- *;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat split;
    eapply scalar_select_list_all_admissible_transport;
    eassumption.
Qed.

Local Lemma scalar_grouping_sets_all_admissible_transport :
  forall grouping_sets,
    list_all _
      (prod_all _
        (list_all _
          (prod_all _
            (fun expression => forall phase,
              @scalar_expr_admissible T generic_relname first_basesort
                leaf_has_type call_has_type predicate_has_types
                rank_type boolean_type value_is_null
                phase ScalarResultValue expression ->
              @scalar_expr_admissible T generic_relname second_basesort
                leaf_has_type call_has_type predicate_has_types
                rank_type boolean_type value_is_null
                phase ScalarResultValue expression)
            _ (fun _ => unit)))
        _
        (list_all _
          (fun expression => forall phase,
            @scalar_expr_admissible T generic_relname first_basesort
              leaf_has_type call_has_type predicate_has_types
              rank_type boolean_type value_is_null
              phase ScalarResultValue expression ->
            @scalar_expr_admissible T generic_relname second_basesort
              leaf_has_type call_has_type predicate_has_types
              rank_type boolean_type value_is_null
              phase ScalarResultValue expression))) grouping_sets ->
    prop_forall
      (fun grouping_set =>
        prop_forall
          (fun item =>
            @scalar_expr_admissible T generic_relname first_basesort
              leaf_has_type call_has_type predicate_has_types
              rank_type boolean_type value_is_null
              ScalarPhaseSelect ScalarResultValue (fst item) /\
            scalar_expr_type (fst item) =
              type_of_attribute T (snd item)) (fst grouping_set) /\
        prop_forall
          (@scalar_expr_admissible T generic_relname first_basesort
            leaf_has_type call_has_type predicate_has_types
            rank_type boolean_type value_is_null
            ScalarPhaseGroupBy ScalarResultValue) (snd grouping_set) /\
        exists group_terms,
          scalar_group_key_terms (snd grouping_set) = Some group_terms)
      grouping_sets ->
    prop_forall
      (fun grouping_set =>
        prop_forall
          (fun item =>
            @scalar_expr_admissible T generic_relname second_basesort
              leaf_has_type call_has_type predicate_has_types
              rank_type boolean_type value_is_null
              ScalarPhaseSelect ScalarResultValue (fst item) /\
            scalar_expr_type (fst item) =
              type_of_attribute T (snd item)) (fst grouping_set) /\
        prop_forall
          (@scalar_expr_admissible T generic_relname second_basesort
            leaf_has_type call_has_type predicate_has_types
            rank_type boolean_type value_is_null
            ScalarPhaseGroupBy ScalarResultValue) (snd grouping_set) /\
        exists group_terms,
          scalar_group_key_terms (snd grouping_set) = Some group_terms)
      grouping_sets.
Proof.
  intros grouping_sets Hall; induction Hall as [|grouping_set Hgroup rest Hrest IH];
    intros Hsource; cbn [prop_forall] in *; auto.
  inversion Hgroup as [select_list Hselect group_keys Hkeys]; subst.
  destruct Hsource as [[Hselect_source [Hkeys_source Hextract]] Htail].
  split.
  - repeat split.
    + eapply scalar_select_list_all_admissible_transport; eassumption.
    + eapply scalar_expr_list_all_admissible_transport; eassumption.
    + exact Hextract.
  - now apply IH.
Qed.

Lemma query_scalar_expr_admissible_basesort_extensional :
  (forall query,
    @query_expr_admissible T generic_relname first_basesort
      leaf_has_type call_has_type predicate_has_types
      rank_type boolean_type value_is_null query ->
    @query_expr_admissible T generic_relname second_basesort
      leaf_has_type call_has_type predicate_has_types
      rank_type boolean_type value_is_null query) /\
  (forall kind (expression : @scalar_expr T generic_relname kind) phase,
    @scalar_expr_admissible T generic_relname first_basesort
      leaf_has_type call_has_type predicate_has_types
      rank_type boolean_type value_is_null phase kind expression ->
    @scalar_expr_admissible T generic_relname second_basesort
      leaf_has_type call_has_type predicate_has_types
      rank_type boolean_type value_is_null phase kind expression).
Proof.
  apply query_scalar_expr_admissibility_mutind; intros; cbn in *; try tauto.
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
  all: try (eapply scalar_join_selects_all_admissible_transport;
    eassumption).
  all: try (eapply scalar_grouping_sets_all_admissible_transport;
    eassumption).
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
  all: try (unfold scalar_expr_in_positionally_aligned in *; tauto).
  all: eauto.
Qed.

Theorem query_expr_admissible_basesort_extensional :
  forall query,
    @query_expr_admissible T generic_relname first_basesort
      leaf_has_type call_has_type predicate_has_types
      rank_type boolean_type value_is_null query ->
    @query_expr_admissible T generic_relname second_basesort
      leaf_has_type call_has_type predicate_has_types
      rank_type boolean_type value_is_null query.
Proof.
  exact (proj1 query_scalar_expr_admissible_basesort_extensional).
Qed.

Theorem scalar_expr_admissible_basesort_extensional :
  forall kind (expression : @scalar_expr T generic_relname kind) phase,
    @scalar_expr_admissible T generic_relname first_basesort
      leaf_has_type call_has_type predicate_has_types
      rank_type boolean_type value_is_null phase kind expression ->
    @scalar_expr_admissible T generic_relname second_basesort
      leaf_has_type call_has_type predicate_has_types
      rank_type boolean_type value_is_null phase kind expression.
Proof.
  exact (proj2 query_scalar_expr_admissible_basesort_extensional).
Qed.

End AdmissibilityBaseSortTransport.

(** Compositional certificates package the one canonical admissibility
    judgment with its authoritative ordered output witness. *)
Section CompositionalQueryExprAdmissibility.

Context {T : Tuple.Rcd} {generic_relname : Type}.
Variable basesort : generic_relname -> Fset.set (A T).
Variables leaf_has_type : type T -> @aggterm T -> Prop.
Variable call_has_type :
  type T -> scalar_operator T -> list (type T) -> Prop.
Variable predicate_has_types : predicate T -> list (type T) -> Prop.
Variables rank_type boolean_type : type T.
Variable value_is_null : value T -> bool.

Definition query_expr_admissible_with_outputs
    (query : @query_expr T generic_relname)
    (expected_outputs : list (attribute T)) : Prop :=
  @query_expr_admissible T generic_relname basesort
    leaf_has_type call_has_type predicate_has_types
    rank_type boolean_type value_is_null query /\
  query_expr_outputs query = expected_outputs.

Lemma query_expr_admissible_of_with_outputs :
  forall query expected_outputs,
    query_expr_admissible_with_outputs query expected_outputs ->
    @query_expr_admissible T generic_relname basesort
      leaf_has_type call_has_type predicate_has_types
      rank_type boolean_type value_is_null query.
Proof.
  intros query expected_outputs [Hadmissible _]; exact Hadmissible.
Qed.

Lemma query_expr_admissible_with_outputs_change :
  forall query first_outputs second_outputs,
    query_expr_admissible_with_outputs query first_outputs ->
    first_outputs = second_outputs ->
    query_expr_admissible_with_outputs query second_outputs.
Proof.
  intros query first_outputs second_outputs [Hadmissible Houtputs] Hequal.
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
    Forall (fun key => In (sort_key_attribute key) outputs) keys ->
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
    @scalar_expr_admissible T generic_relname basesort
      leaf_has_type call_has_type predicate_has_types
      rank_type boolean_type value_is_null
      ScalarPhaseOn ScalarResultBoolean predicate ->
    query_expr_admissible_with_outputs left left_outputs ->
    query_expr_admissible_with_outputs right right_outputs ->
    query_join_projection_sorts_compatible
      kind matched_select left_select right_select ->
    query_join_projections_unique
      kind matched_select left_select right_select ->
    (match kind with
     | QueryJoinInner =>
         prop_forall
           (fun item =>
             @scalar_expr_admissible T generic_relname basesort
               leaf_has_type call_has_type predicate_has_types
               rank_type boolean_type value_is_null
               ScalarPhaseRowSelect ScalarResultValue (fst item) /\
             scalar_expr_type (fst item) =
               type_of_attribute T (snd item))
           matched_select
     | QueryJoinLeft =>
         prop_forall
           (fun item =>
             @scalar_expr_admissible T generic_relname basesort
               leaf_has_type call_has_type predicate_has_types
               rank_type boolean_type value_is_null
               ScalarPhaseRowSelect ScalarResultValue (fst item) /\
             scalar_expr_type (fst item) =
               type_of_attribute T (snd item))
           matched_select /\
         prop_forall
           (fun item =>
             @scalar_expr_admissible T generic_relname basesort
               leaf_has_type call_has_type predicate_has_types
               rank_type boolean_type value_is_null
               ScalarPhaseRowSelect ScalarResultValue (fst item) /\
             scalar_expr_type (fst item) =
               type_of_attribute T (snd item))
           left_select
     | QueryJoinRight =>
         prop_forall
           (fun item =>
             @scalar_expr_admissible T generic_relname basesort
               leaf_has_type call_has_type predicate_has_types
               rank_type boolean_type value_is_null
               ScalarPhaseRowSelect ScalarResultValue (fst item) /\
             scalar_expr_type (fst item) =
               type_of_attribute T (snd item))
           matched_select /\
         prop_forall
           (fun item =>
             @scalar_expr_admissible T generic_relname basesort
               leaf_has_type call_has_type predicate_has_types
               rank_type boolean_type value_is_null
               ScalarPhaseRowSelect ScalarResultValue (fst item) /\
             scalar_expr_type (fst item) =
               type_of_attribute T (snd item))
           right_select
     | QueryJoinFull =>
         prop_forall
           (fun item =>
             @scalar_expr_admissible T generic_relname basesort
               leaf_has_type call_has_type predicate_has_types
               rank_type boolean_type value_is_null
               ScalarPhaseRowSelect ScalarResultValue (fst item) /\
             scalar_expr_type (fst item) =
               type_of_attribute T (snd item))
           matched_select /\
         prop_forall
           (fun item =>
             @scalar_expr_admissible T generic_relname basesort
               leaf_has_type call_has_type predicate_has_types
               rank_type boolean_type value_is_null
               ScalarPhaseRowSelect ScalarResultValue (fst item) /\
             scalar_expr_type (fst item) =
               type_of_attribute T (snd item))
           left_select /\
         prop_forall
           (fun item =>
             @scalar_expr_admissible T generic_relname basesort
               leaf_has_type call_has_type predicate_has_types
               rank_type boolean_type value_is_null
               ScalarPhaseRowSelect ScalarResultValue (fst item) /\
             scalar_expr_type (fst item) =
               type_of_attribute T (snd item))
           right_select
     | QueryJoinSemi | QueryJoinAnti =>
         prop_forall
           (fun item =>
             @scalar_expr_admissible T generic_relname basesort
               leaf_has_type call_has_type predicate_has_types
               rank_type boolean_type value_is_null
               ScalarPhaseRowSelect ScalarResultValue (fst item) /\
             scalar_expr_type (fst item) =
               type_of_attribute T (snd item))
           left_select
     end) ->
    query_expr_admissible_with_outputs
      (@QExpr_Join T generic_relname kind predicate
        matched_select left_select right_select left right)
      (match kind with
       | QueryJoinSemi | QueryJoinAnti =>
           scalar_select_outputs left_select
       | _ => scalar_select_outputs matched_select
       end).
Proof.
  intros kind predicate matched_select left_select right_select
    left right left_outputs right_outputs Hpredicate
    [Hleft _] [Hright _] Hcompatible Hunique Hselects.
  split.
  - cbn [query_expr_admissible]; tauto.
  - reflexivity.
Qed.

Lemma query_expr_admissible_with_outputs_project :
  forall select_list input input_outputs,
    query_expr_admissible_with_outputs input input_outputs ->
    query_select_list_outputs_unique select_list ->
    prop_forall
      (fun item =>
        @scalar_expr_admissible T generic_relname basesort
          leaf_has_type call_has_type predicate_has_types
          rank_type boolean_type value_is_null
          ScalarPhaseRowSelect ScalarResultValue (fst item) /\
        scalar_expr_type (fst item) = type_of_attribute T (snd item))
      select_list ->
    query_expr_admissible_with_outputs
      (@QExpr_Project T generic_relname select_list input)
      (scalar_select_outputs select_list).
Proof.
  intros select_list input input_outputs [Hinput _] Hunique Hitems.
  split; cbn [query_expr_admissible query_expr_outputs]; intuition.
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
    @scalar_expr_admissible T generic_relname basesort
      leaf_has_type call_has_type predicate_has_types
      rank_type boolean_type value_is_null
      ScalarPhaseWhere ScalarResultBoolean predicate ->
    query_expr_admissible_with_outputs
      (@QExpr_Filter T generic_relname predicate input) input_outputs.
Proof.
  intros predicate input input_outputs [Hinput Houtputs] Hpredicate.
  split.
  - cbn [query_expr_admissible]; now split.
  - cbn [query_expr_outputs]; exact Houtputs.
Qed.

Lemma query_expr_admissible_with_outputs_group :
  forall select_list group_keys group_terms having input input_outputs,
    query_expr_admissible_with_outputs input input_outputs ->
    @query_output_attributes_unique T (scalar_select_outputs select_list) ->
    prop_forall
      (fun item =>
        @scalar_expr_admissible T generic_relname basesort
          leaf_has_type call_has_type predicate_has_types
          rank_type boolean_type value_is_null
          ScalarPhaseSelect ScalarResultValue (fst item) /\
        scalar_expr_type (fst item) = type_of_attribute T (snd item))
      select_list ->
    @scalar_expr_admissible T generic_relname basesort
      leaf_has_type call_has_type predicate_has_types
      rank_type boolean_type value_is_null
      ScalarPhaseHaving ScalarResultBoolean having ->
    prop_forall
      (@scalar_expr_admissible T generic_relname basesort
        leaf_has_type call_has_type predicate_has_types
        rank_type boolean_type value_is_null
        ScalarPhaseGroupBy ScalarResultValue) group_keys ->
    scalar_group_key_terms group_keys = Some group_terms ->
    query_expr_admissible_with_outputs
      (@QExpr_Group T generic_relname
        select_list group_keys having input)
      (scalar_select_outputs select_list).
Proof.
  intros select_list group_keys group_terms having input input_outputs
    [Hinput _] Hunique Hselect Hhaving Hkeys Hextract.
  split; [|reflexivity].
  cbn [query_expr_admissible].
  repeat split; try assumption.
  now exists group_terms.
Qed.

Lemma query_expr_admissible_with_outputs_grouping_sets :
  forall grouping_sets input input_outputs,
    query_expr_admissible_with_outputs input input_outputs ->
    query_grouping_sets_well_formed grouping_sets ->
    prop_forall
      (fun grouping_set =>
        prop_forall
          (fun item =>
            @scalar_expr_admissible T generic_relname basesort
              leaf_has_type call_has_type predicate_has_types
              rank_type boolean_type value_is_null
              ScalarPhaseSelect ScalarResultValue (fst item) /\
            scalar_expr_type (fst item) =
              type_of_attribute T (snd item))
          (fst grouping_set) /\
        prop_forall
          (@scalar_expr_admissible T generic_relname basesort
            leaf_has_type call_has_type predicate_has_types
            rank_type boolean_type value_is_null
            ScalarPhaseGroupBy ScalarResultValue)
          (snd grouping_set) /\
        exists group_terms,
          scalar_group_key_terms (snd grouping_set) = Some group_terms)
      grouping_sets ->
    query_expr_admissible_with_outputs
      (@QExpr_GroupingSets T generic_relname grouping_sets input)
      (query_grouping_sets_outputs grouping_sets).
Proof.
  intros grouping_sets input input_outputs [Hinput _] Hgroups Hbranches.
  split; cbn [query_expr_admissible query_expr_outputs]; intuition.
Qed.

Lemma query_expr_admissible_with_outputs_rank :
  forall partition_keys order_keys rank_attribute embed_rank
      input input_outputs,
    query_expr_admissible_with_outputs input input_outputs ->
    type_of_attribute T rank_attribute = rank_type ->
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
    input input_outputs [Hinput Houtputs]
    Htype Hpartition Horder Hfresh.
  split.
  - cbn [query_expr_admissible].
    repeat split; try assumption;
      unfold query_expr_sort; now rewrite Houtputs.
  - cbn [query_expr_outputs]; now rewrite Houtputs.
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
    prop_forall
      (fun item =>
        match item with
        | QueryWindowItem output function =>
            match function with
            | QueryWindowRowNumber _ =>
                type_of_attribute T output = rank_type
            | QueryWindowAggregate term
            | QueryWindowFullPartitionAggregate term =>
                leaf_has_type (type_of_attribute T output) term
            end
        end)
      items ->
    length (map (@qwi_attribute T) items) =
      Fset.cardinal (A T)
        (Fset.mk_set (A T) (map (@qwi_attribute T) items)) ->
    query_expr_admissible_with_outputs
      (@QExpr_Window T generic_relname partition_keys order_keys items input)
      (input_outputs ++ map (@qwi_attribute T) items).
Proof.
  intros partition_keys order_keys items input input_outputs
    [Hinput Houtputs] Hpartition Horder Hfresh Hitems Hunique.
  split.
  - cbn [query_expr_admissible].
    repeat split; try assumption.
    + unfold query_expr_sort; now rewrite Houtputs.
    + unfold query_expr_sort; now rewrite Houtputs.
    + rewrite Forall_forall in Hfresh |- *.
      intros item Hitem; unfold query_expr_sort.
      rewrite Houtputs; now apply Hfresh.
  - cbn [query_expr_outputs]; now rewrite Houtputs.
Qed.

Lemma query_expr_admissible_with_outputs_distinct :
  forall input input_outputs,
    query_expr_admissible_with_outputs input input_outputs ->
    query_expr_admissible_with_outputs
      (@QExpr_Distinct T generic_relname input) input_outputs.
Proof.
  intros input input_outputs [Hinput Houtputs].
  split; cbn [query_expr_admissible query_expr_outputs]; assumption.
Qed.

Lemma query_expr_admissible_with_outputs_order_by :
  forall keys input input_outputs,
    query_expr_admissible_with_outputs input input_outputs ->
    query_sort_keys_in_scope (@query_outputs_sort T input_outputs) keys ->
    query_expr_admissible_with_outputs
      (@QExpr_OrderBy T generic_relname keys input) input_outputs.
Proof.
  intros keys input input_outputs [Hinput Houtputs] Hkeys.
  split.
  - cbn [query_expr_admissible]; split; [assumption |].
    unfold query_expr_sort; now rewrite Houtputs.
  - cbn [query_expr_outputs]; exact Houtputs.
Qed.

Lemma query_expr_admissible_with_outputs_offset :
  forall count input input_outputs,
    query_expr_admissible_with_outputs input input_outputs ->
    query_expr_admissible_with_outputs
      (@QExpr_Offset T generic_relname count input) input_outputs.
Proof.
  intros count input input_outputs [Hinput Houtputs].
  split; cbn [query_expr_admissible query_expr_outputs]; assumption.
Qed.

Lemma query_expr_admissible_with_outputs_fetch :
  forall count input input_outputs,
    query_expr_admissible_with_outputs input input_outputs ->
    query_expr_admissible_with_outputs
      (@QExpr_Fetch T generic_relname count input) input_outputs.
Proof.
  intros count input input_outputs [Hinput Houtputs].
  split; cbn [query_expr_admissible query_expr_outputs]; assumption.
Qed.

End CompositionalQueryExprAdmissibility.

(** Schema conformance transports the same canonical TNull admission
    certificate; it does not introduce a weaker structural judgment. *)
Theorem query_expr_admissible_database_schema_transport :
  forall expected constraints actual query,
    database_conforms_schema expected constraints actual ->
    TNullQueryExprAdmissible (@_basesort TNull expected) query ->
    TNullQueryExprAdmissible (@_basesort TNull actual) query.
Proof.
  intros expected constraints actual query Hschema Hadmissible.
  unfold TNullQueryExprAdmissible in *.
  destruct Hadmissible as [Hadmissible [Herror Hsites]].
  split.
  - eapply query_expr_admissible_basesort_extensional.
    + intro relation.
      pose proof
        (database_conforms_schema_basesort
          expected constraints actual Hschema relation) as Hactual.
      rewrite Fset.equal_spec in Hactual |- *.
      intro attribute; symmetry; apply Hactual.
    + exact Hadmissible.
  - now split.
Qed.
