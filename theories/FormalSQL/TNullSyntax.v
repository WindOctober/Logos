From SQLFS Require Import SqlSyntax GenericInstance Values SqlOrder
  FTerms ATerms FTuples ValueNumeric
  ValueNumericTypmod ValueFloat ValueInteger ValueString.
From Stdlib Require Import List String ZArith Floats.
From Flocq Require Import IEEE754.Bits.

Import ListNotations.
Import Tuple.

Open Scope string_scope.
Open Scope Z_scope.

Definition AggTerm := @aggterm TNull.
Definition FunTerm := @funterm TNull.
Definition SortKeyT := sort_key TNull.

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
