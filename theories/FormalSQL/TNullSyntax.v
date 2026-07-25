From SQLFS Require Import SqlSyntax GenericInstance Values SqlOrder Projection
  FTerms ATerms FiniteSet FTuples Env ListFacts ValueNumeric
  ValueNumericTypmod ValueFloat ValueInteger ValueString.
From Stdlib Require Import List String ZArith Floats.
From Flocq Require Import IEEE754.Bits.

Import ListNotations.
Import Tuple.

Open Scope string_scope.
Open Scope Z_scope.

Definition SelectListT := @_select_list TNull.
Definition SelectItemT := @select TNull.
Definition AggTerm := @aggterm TNull.
Definition FunTerm := @funterm TNull.
Definition SortKeyT := sort_key TNull.

Definition SelectList (items : list SelectItemT) : SelectListT :=
  @_Select_List TNull items.

Definition SelectAs (expr : AggTerm) (alias : attribute TNull) : SelectItemT :=
  @Select_As TNull expr alias.

Definition AExpr (term : FunTerm) : AggTerm :=
  @A_Expr TNull term.

Definition AAggregate
    (function : aggregate_function)
    (quantifier : aggregate_quantifier)
    (arg : FunTerm) : AggTerm :=
  @A_agg TNull (AggregateCall function quantifier) arg.

(** The generic FormalSQL [A_agg] node has one uniform child slot.  COUNT star
    is nevertheless exposed as a zero-argument term in Logos; its dedicated
    aggregate constructor ignores the private constant child. *)
Definition ACountStar : AggTerm :=
  @A_agg TNull AggregateCountStar
    (@F_Constant TNull (Value_Z (Some 0))).

Definition AScalarCall
    (operator : ValueCore.scalar_operator) (args : list AggTerm) : AggTerm :=
  @A_fun TNull operator args.

Definition Dot (attribute : attribute TNull) : FunTerm :=
  @F_Dot TNull attribute.

Definition Constant (value : value TNull) : FunTerm :=
  @F_Constant TNull value.

Definition ScalarCall
    (operator : ValueCore.scalar_operator) (args : list FunTerm) : FunTerm :=
  @F_Expr TNull operator args.

Definition projected_tuple (env : Env.env TNull) (s : SelectListT) (t : tuple TNull) :=
  projection TNull (env_t TNull env t) (@Select_List TNull s).

(** Pure select-list facts used by both exact query proofs and generated
    projection obligations.  They do not depend on a query evaluator. *)
Definition select_list_directly_selects_attr
    (select_list : SelectListT) (attribute : attribute TNull) : Prop :=
  match select_list with
  | @_Select_List _ items =>
      In
        (@Select_As TNull
          (@A_Expr TNull (@F_Dot TNull attribute)) attribute)
        items
  end.

Definition select_list_has_unique_outputs
    (select_list : SelectListT) : Prop :=
  match select_list with
  | @_Select_List _ items =>
      all_diff (map fst (map (@pair_of_select TNull) items))
  end.

Definition projection_preserves_attr
    (env : Env.env TNull) (select_list : SelectListT)
    (attribute : attribute TNull) : Prop :=
  forall row,
    attribute inS labels TNull row ->
    @dot TNull (projected_tuple env select_list row) attribute =
    @dot TNull row attribute.

Lemma direct_projection_preserves_attr :
  forall env select_list attribute,
    select_list_directly_selects_attr select_list attribute ->
    select_list_has_unique_outputs select_list ->
    projection_preserves_attr env select_list attribute.
Proof.
intros env [items] attribute Hselect Hdistinct row Hattribute.
unfold projection_preserves_attr, projected_tuple in *.
change
  (@dot TNull
    (projection TNull (env_t TNull env row)
      (@Select_List TNull (@_Select_List TNull items))) attribute =
   @dot TNull row attribute).
rewrite (@dot_projection TNull (env_t TNull env row) items attribute
  (@A_Expr TNull (@F_Dot TNull attribute)) Hselect Hdistinct).
unfold Interp.interp_aggterm, Interp.interp_funterm,
  Interp.interp_dot, env_t.
simpl.
change
  ((if attribute inS? labels TNull row
    then @dot TNull row attribute
    else Interp.interp_dot TNull env attribute) =
   @dot TNull row attribute).
rewrite Hattribute; reflexivity.
Qed.

Definition AttrZ (name : string) := Attr_Z name.
Definition AttrInt32 (name : string) := Attr_int32 name.
Definition AttrInt64 (name : string) := Attr_int64 name.
Definition AttrString (name : string) (typmod : string_typmod) :=
  Attr_string name typmod.
Definition AttrBool (name : string) := Attr_bool name.
Definition AttrFloat (name : string) := Attr_float name.
Definition AttrDouble (name : string) := Attr_double name.
Definition AttrNumeric (name : string) := Attr_numeric name.
Definition AttrDecimal (name : string) (precision scale : Z) :=
  Attr_decimal name precision scale.
Definition AttrDate (name : string) := Attr_date name.
Definition AttrTime (name : string) := Attr_time name.
Definition AttrTimestamp (name : string) (precision : Z) := Attr_timestamp name precision.
Definition AttrTimestamptz (name : string) (precision : Z) := Attr_timestamptz name precision.

Definition SortAsc := Sort_Asc.
Definition SortDesc := Sort_Desc.
Definition NullsFirst := Nulls_First.
Definition NullsLast := Nulls_Last.

Definition SortKey
    (attribute : attribute TNull)
    (direction : sort_direction)
    (nulls : null_direction) : SortKeyT :=
  @mk_sort_key TNull attribute direction nulls
    NullValues.sql_order_value_compare
    NullValues.sql_order_value_compare_opposite.

Definition SortAscNullsFirst (attribute : attribute TNull) : SortKeyT :=
  SortKey attribute SortAsc NullsFirst.

Definition SortAscNullsLast (attribute : attribute TNull) : SortKeyT :=
  SortKey attribute SortAsc NullsLast.

Definition SortDescNullsFirst (attribute : attribute TNull) : SortKeyT :=
  SortKey attribute SortDesc NullsFirst.

Definition SortDescNullsLast (attribute : attribute TNull) : SortKeyT :=
  SortKey attribute SortDesc NullsLast.

Inductive ColumnRef : Type :=
  | ZColumn : string -> ColumnRef
  | Int32Column : string -> ColumnRef
  | Int64Column : string -> ColumnRef
  | StringColumn : string -> string_typmod -> ColumnRef
  | BoolColumn : string -> ColumnRef
  | FloatColumn : string -> ColumnRef
  | DoubleColumn : string -> ColumnRef
  | NumericColumn : string -> ColumnRef
  | DecimalColumn : string -> Z -> Z -> ColumnRef
  | DateColumn : string -> ColumnRef
  | TimeColumn : string -> ColumnRef
  | TimestampColumn : string -> Z -> ColumnRef
  | TimestamptzColumn : string -> Z -> ColumnRef.

Definition ColumnAttribute (column : ColumnRef) : attribute TNull :=
  match column with
  | ZColumn name => AttrZ name
  | Int32Column name => AttrInt32 name
  | Int64Column name => AttrInt64 name
  | StringColumn name typmod => AttrString name typmod
  | BoolColumn name => AttrBool name
  | FloatColumn name => AttrFloat name
  | DoubleColumn name => AttrDouble name
  | NumericColumn name => AttrNumeric name
  | DecimalColumn name precision scale => AttrDecimal name precision scale
  | DateColumn name => AttrDate name
  | TimeColumn name => AttrTime name
  | TimestampColumn name precision => AttrTimestamp name precision
  | TimestamptzColumn name precision => AttrTimestamptz name precision
  end.

Definition DotZ (name : string) : AggTerm := AExpr (Dot (AttrZ name)).
Definition DotInt32 (name : string) : AggTerm := AExpr (Dot (AttrInt32 name)).
Definition DotInt64 (name : string) : AggTerm := AExpr (Dot (AttrInt64 name)).
Definition DotString (name : string) (typmod : string_typmod) : AggTerm :=
  AExpr (Dot (AttrString name typmod)).
Definition DotBool (name : string) : AggTerm := AExpr (Dot (AttrBool name)).
Definition DotFloat (name : string) : AggTerm := AExpr (Dot (AttrFloat name)).
Definition DotDouble (name : string) : AggTerm := AExpr (Dot (AttrDouble name)).
Definition DotNumeric (name : string) : AggTerm := AExpr (Dot (AttrNumeric name)).
Definition DotDecimal (name : string) (precision scale : Z) : AggTerm :=
  AExpr (Dot (AttrDecimal name precision scale)).
Definition DotDate (name : string) : AggTerm := AExpr (Dot (AttrDate name)).
Definition DotTime (name : string) : AggTerm := AExpr (Dot (AttrTime name)).
Definition DotTimestamp (name : string) (precision : Z) : AggTerm :=
  AExpr (Dot (AttrTimestamp name precision)).
Definition DotTimestamptz (name : string) (precision : Z) : AggTerm :=
  AExpr (Dot (AttrTimestamptz name precision)).

Definition DotColumn (column : ColumnRef) : AggTerm :=
  match column with
  | ZColumn name => DotZ name
  | Int32Column name => DotInt32 name
  | Int64Column name => DotInt64 name
  | StringColumn name typmod => DotString name typmod
  | BoolColumn name => DotBool name
  | FloatColumn name => DotFloat name
  | DoubleColumn name => DotDouble name
  | NumericColumn name => DotNumeric name
  | DecimalColumn name precision scale => DotDecimal name precision scale
  | DateColumn name => DotDate name
  | TimeColumn name => DotTime name
  | TimestampColumn name precision => DotTimestamp name precision
  | TimestamptzColumn name precision => DotTimestamptz name precision
  end.

Definition CstZ (z : Z) : AggTerm := AExpr (Constant (Value_Z (Some z))).
Definition CstInt32 (z : Z) : AggTerm :=
  AExpr (Constant (Value_int32 (int32_checked z))).
Definition CstInt64 (z : Z) : AggTerm :=
  AExpr (Constant (Value_int64 (int64_checked z))).
Definition CstString (typmod : string_typmod) (s : string) : AggTerm :=
  AExpr (Constant (Value_string
    (StringValue typmod (Some (string_explicit_cast typmod s))))).
Definition CstBool (b : bool) : AggTerm := AExpr (Constant (Value_bool (Some b))).
Definition CstFloat (f : float32) : AggTerm := AExpr (Constant (Value_float (Some f))).
Definition CstDouble (f : float64) : AggTerm := AExpr (Constant (Value_double (Some f))).
Definition Float32OfBits (bits : Z) : float32 := mk_float32 (b32_of_bits bits).
Definition Float64OfBits (bits : Z) : float64 := mk_float64 (b64_of_bits bits).
Definition CstFloatBits (bits : Z) : AggTerm := CstFloat (Float32OfBits bits).
Definition CstDoubleBits (bits : Z) : AggTerm := CstDouble (Float64OfBits bits).
Definition CstNumeric (coeff scale : Z) : AggTerm :=
  AExpr (Constant (Value_numeric (Some (numeric_of_scaled coeff scale)))).
Definition CstDecimal (precision scale coeff : Z) : AggTerm :=
  AExpr (Constant (Value_numeric
    (numeric_of_scaled_with_typmod precision scale coeff))).
Definition CstDate (date : Z) : AggTerm := AExpr (Constant (Value_date (Some date))).
Definition CstTime (time : Z) : AggTerm := AExpr (Constant (Value_time (Some time))).
Definition CstTimestamp (timestamp : Z) : AggTerm :=
  AExpr (Constant (Value_timestamp (Some timestamp))).
Definition CstTimestamptz (timestamp : Z) : AggTerm :=
  AExpr (Constant (Value_timestamptz (Some timestamp))).

Definition NullZ : AggTerm := AExpr (Constant (Value_Z None)).
Definition NullInt32 : AggTerm := AExpr (Constant (Value_int32 None)).
Definition NullInt64 : AggTerm := AExpr (Constant (Value_int64 None)).
Definition NullString (typmod : string_typmod) : AggTerm :=
  AExpr (Constant (Value_string (StringValue typmod None))).
Definition NullBool : AggTerm := AExpr (Constant (Value_bool None)).
Definition NullFloat : AggTerm := AExpr (Constant (Value_float None)).
Definition NullDouble : AggTerm := AExpr (Constant (Value_double None)).
Definition NullNumeric : AggTerm := AExpr (Constant (Value_numeric None)).
Definition NullDecimal : AggTerm := NullNumeric.
Definition NullDate : AggTerm := AExpr (Constant (Value_date None)).
Definition NullTime : AggTerm := AExpr (Constant (Value_time None)).
Definition NullTimestamp : AggTerm := AExpr (Constant (Value_timestamp None)).
Definition NullTimestamptz : AggTerm := AExpr (Constant (Value_timestamptz None)).

Definition SelectZ (name : string) : SelectItemT := SelectAs (DotZ name) (AttrZ name).
Definition SelectInt32 (name : string) : SelectItemT :=
  SelectAs (DotInt32 name) (AttrInt32 name).
Definition SelectInt64 (name : string) : SelectItemT :=
  SelectAs (DotInt64 name) (AttrInt64 name).
Definition SelectString (name : string) (typmod : string_typmod) : SelectItemT :=
  SelectAs (DotString name typmod) (AttrString name typmod).
Definition SelectBool (name : string) : SelectItemT := SelectAs (DotBool name) (AttrBool name).
Definition SelectFloat (name : string) : SelectItemT :=
  SelectAs (DotFloat name) (AttrFloat name).
Definition SelectDouble (name : string) : SelectItemT :=
  SelectAs (DotDouble name) (AttrDouble name).
Definition SelectNumeric (name : string) : SelectItemT :=
  SelectAs (DotNumeric name) (AttrNumeric name).
Definition SelectDecimal (name : string) (precision scale : Z) : SelectItemT :=
  SelectAs (DotDecimal name precision scale) (AttrDecimal name precision scale).
Definition SelectDate (name : string) : SelectItemT :=
  SelectAs (DotDate name) (AttrDate name).
Definition SelectTime (name : string) : SelectItemT :=
  SelectAs (DotTime name) (AttrTime name).
Definition SelectTimestamp (name : string) (precision : Z) : SelectItemT :=
  SelectAs (DotTimestamp name precision) (AttrTimestamp name precision).
Definition SelectTimestamptz (name : string) (precision : Z) : SelectItemT :=
  SelectAs (DotTimestamptz name precision) (AttrTimestamptz name precision).

Definition SelectColumn (column : ColumnRef) : SelectItemT :=
  SelectAs (DotColumn column) (ColumnAttribute column).

Definition SelectColumns (columns : list ColumnRef) : SelectListT :=
  SelectList (List.map SelectColumn columns).
