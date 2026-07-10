From SQLFS Require Import SqlSyntax GenericInstance SqlAlgebra SqlOrder SqlListAlgebra Projection FTerms ATerms Formula FiniteSet FiniteBag FTuples Bool3 Env ValueDecimal ValueFloat.
From Stdlib Require Import List String ZArith Floats.
From Flocq Require Import IEEE754.Bits.

Import ListNotations.
Import Tuple.

Open Scope string_scope.
Open Scope Z_scope.

Definition Query := @query TNull relname.
Definition ListQuery := @list_query TNull relname.
Definition Formula := @sql_formula TNull Query.
Definition SelectListT := @_select_list TNull.
Definition SelectItemT := @select TNull.
Definition AggTerm := @aggterm TNull.
Definition FunTerm := @funterm TNull.
Definition SortKeyT := sort_key TNull.

Definition Table (name : string) : Query :=
  @Q_Table TNull relname (Rel name).

Definition EmptyTuple : Query :=
  @Q_Empty_Tuple TNull relname.

Definition EmptyBagRelation (attrs : list (attribute TNull)) : Query :=
  @Q_Empty_Relation TNull relname (Fset.mk_set (A TNull) attrs).

Definition SetQuery (op : set_op) (left right : Query) : Query :=
  @Q_Set TNull relname op left right.

Definition SetUnion := Union.
Definition SetUnionMax := UnionMax.
Definition SetInter := Inter.
Definition SetDiff := Diff.

Definition NaturalJoin (left right : Query) : Query :=
  @Q_NaturalJoin TNull relname left right.

Definition CrossJoin (left right : Query) : Query :=
  @Q_CrossJoin TNull relname left right.

Definition Pi (select : SelectListT) (input : Query) : Query :=
  @Q_Pi TNull relname select input.

Definition Sigma (predicate : Formula) (input : Query) : Query :=
  @Q_Sigma TNull relname predicate input.

Definition Gamma
    (select : SelectListT)
    (group_by : list AggTerm)
    (having : Formula)
    (input : Query) : Query :=
  @Q_Gamma TNull relname select group_by having input.

Definition Bag (input : Query) : ListQuery :=
  @L_Bag TNull relname input.

Definition EmptyRelation (attrs : list (attribute TNull)) : ListQuery :=
  @L_EmptyRelation TNull relname (Fset.mk_set (A TNull) attrs).

Definition OrderBy (keys : list SortKeyT) (input : ListQuery) : ListQuery :=
  @L_OrderBy TNull relname keys input.

Definition Offset (count : nat) (input : ListQuery) : ListQuery :=
  @L_Offset TNull relname count input.

Definition Fetch (count : nat) (input : ListQuery) : ListQuery :=
  @L_Fetch TNull relname count input.

Definition SelectList (items : list SelectItemT) : SelectListT :=
  @_Select_List TNull items.

Definition SelectAs (expr : AggTerm) (alias : attribute TNull) : SelectItemT :=
  @Select_As TNull expr alias.

Definition AExpr (term : FunTerm) : AggTerm :=
  @A_Expr TNull term.

Definition AAggregate (function : string) (arg : FunTerm) : AggTerm :=
  @A_agg TNull (Aggregate function) arg.

Definition ACountStar : AggTerm :=
  @A_agg TNull (Aggregate "count_star") (@F_Constant TNull (Value_Z (Some 0))).

Definition AFunction (symbol : string) (args : list AggTerm) : AggTerm :=
  @A_fun TNull (Symbol symbol) args.

Definition Dot (attribute : attribute TNull) : FunTerm :=
  @F_Dot TNull attribute.

Definition Constant (value : value TNull) : FunTerm :=
  @F_Constant TNull value.

Definition Function (symbol : string) (args : list FunTerm) : FunTerm :=
  @F_Expr TNull (Symbol symbol) args.

Definition TrueFormula : Formula :=
  @Sql_True TNull Query.

Definition Pred (predicate : string) (args : list AggTerm) : Formula :=
  @Sql_Pred TNull Query (Predicate predicate) args.

Definition And (left right : Formula) : Formula :=
  @Sql_Conj TNull Query And_F left right.

Definition Or (left right : Formula) : Formula :=
  @Sql_Conj TNull Query Or_F left right.

Definition Not (formula : Formula) : Formula :=
  @Sql_Not TNull Query formula.

Definition ExistsQuery (query : Query) : Formula :=
  @Sql_Exists TNull Query query.

Definition conj_and := And.

Definition eval_query_in_env (db : db_state) (env : Env.env TNull) (q : Query) :=
  @eval_query TNull relname
    (@_basesort TNull db)
    (@_instance TNull db)
    unknown3
    contains_nulls
    env
    q.

Definition eval_query_in_state (db : db_state) (q : Query) :=
  eval_query_in_env db nil q.

Definition eval_formula_in_env
    (db : db_state) (env : Env.env TNull) (t : tuple TNull) (f : Formula) :=
  Bool.is_true (B TNull)
    (@eval_sql_formula TNull Query
      unknown3
      contains_nulls
      (eval_query_in_env db)
      (env_t TNull env t)
      f).

Definition eval_formula_in_state (db : db_state) (t : tuple TNull) (f : Formula) :=
  eval_formula_in_env db nil t f.

Definition query_equiv (db : db_state) (q1 q2 : Query) : Prop :=
  eval_query_in_state db q1 =BE= eval_query_in_state db q2.

Definition query_satisfies (db : db_state) (q : Query) (f : Formula) : Prop :=
  forall t, t inBE eval_query_in_state db q -> eval_formula_in_state db t f = true.

Definition projected_tuple (env : Env.env TNull) (s : SelectListT) (t : tuple TNull) :=
  projection TNull (env_t TNull env t) (@Select_List TNull s).

Definition AttrZ (name : string) := Attr_Z name.
Definition AttrString (name : string) := Attr_string name.
Definition AttrBool (name : string) := Attr_bool name.
Definition AttrFloat (name : string) := Attr_float name.
Definition AttrDouble (name : string) := Attr_double name.
Definition AttrDecimal (name : string) (precision scale : Z) :=
  Attr_decimal name precision scale.
Definition AttrDate (name : string) := Attr_date name.
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
  @mk_sort_key TNull attribute direction nulls.

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
  | StringColumn : string -> ColumnRef
  | BoolColumn : string -> ColumnRef
  | FloatColumn : string -> ColumnRef
  | DoubleColumn : string -> ColumnRef
  | DecimalColumn : string -> Z -> Z -> ColumnRef
  | DateColumn : string -> ColumnRef
  | TimestampColumn : string -> Z -> ColumnRef
  | TimestamptzColumn : string -> Z -> ColumnRef.

Definition ColumnAttribute (column : ColumnRef) : attribute TNull :=
  match column with
  | ZColumn name => AttrZ name
  | StringColumn name => AttrString name
  | BoolColumn name => AttrBool name
  | FloatColumn name => AttrFloat name
  | DoubleColumn name => AttrDouble name
  | DecimalColumn name precision scale => AttrDecimal name precision scale
  | DateColumn name => AttrDate name
  | TimestampColumn name precision => AttrTimestamp name precision
  | TimestamptzColumn name precision => AttrTimestamptz name precision
  end.

Definition DotZ (name : string) : AggTerm := AExpr (Dot (AttrZ name)).
Definition DotString (name : string) : AggTerm := AExpr (Dot (AttrString name)).
Definition DotBool (name : string) : AggTerm := AExpr (Dot (AttrBool name)).
Definition DotFloat (name : string) : AggTerm := AExpr (Dot (AttrFloat name)).
Definition DotDouble (name : string) : AggTerm := AExpr (Dot (AttrDouble name)).
Definition DotDecimal (name : string) (precision scale : Z) : AggTerm :=
  AExpr (Dot (AttrDecimal name precision scale)).
Definition DotDate (name : string) : AggTerm := AExpr (Dot (AttrDate name)).
Definition DotTimestamp (name : string) (precision : Z) : AggTerm :=
  AExpr (Dot (AttrTimestamp name precision)).
Definition DotTimestamptz (name : string) (precision : Z) : AggTerm :=
  AExpr (Dot (AttrTimestamptz name precision)).

Definition DotColumn (column : ColumnRef) : AggTerm :=
  match column with
  | ZColumn name => DotZ name
  | StringColumn name => DotString name
  | BoolColumn name => DotBool name
  | FloatColumn name => DotFloat name
  | DoubleColumn name => DotDouble name
  | DecimalColumn name precision scale => DotDecimal name precision scale
  | DateColumn name => DotDate name
  | TimestampColumn name precision => DotTimestamp name precision
  | TimestamptzColumn name precision => DotTimestamptz name precision
  end.

Definition CstZ (z : Z) : AggTerm := AExpr (Constant (Value_Z (Some z))).
Definition CstString (s : string) : AggTerm := AExpr (Constant (Value_string (Some s))).
Definition CstBool (b : bool) : AggTerm := AExpr (Constant (Value_bool (Some b))).
Definition CstFloat (f : float32) : AggTerm := AExpr (Constant (Value_float (Some f))).
Definition CstDouble (f : float64) : AggTerm := AExpr (Constant (Value_double (Some f))).
Definition Float32OfBits (bits : Z) : float32 := mk_float32 (b32_of_bits bits).
Definition Float64OfBits (bits : Z) : float64 := mk_float64 (b64_of_bits bits).
Definition CstFloatBits (bits : Z) : AggTerm := CstFloat (Float32OfBits bits).
Definition CstDoubleBits (bits : Z) : AggTerm := CstDouble (Float64OfBits bits).
Definition CstDecimal (precision scale coeff : Z) : AggTerm :=
  AExpr (Constant (Value_decimal (decimal_checked precision scale coeff))).
Definition CstDate (date : Z) : AggTerm := AExpr (Constant (Value_date (Some date))).
Definition CstTimestamp (timestamp : Z) : AggTerm :=
  AExpr (Constant (Value_timestamp (Some timestamp))).
Definition CstTimestamptz (timestamp : Z) : AggTerm :=
  AExpr (Constant (Value_timestamptz (Some timestamp))).

Definition NullZ : AggTerm := AExpr (Constant (Value_Z None)).
Definition NullString : AggTerm := AExpr (Constant (Value_string None)).
Definition NullBool : AggTerm := AExpr (Constant (Value_bool None)).
Definition NullFloat : AggTerm := AExpr (Constant (Value_float None)).
Definition NullDouble : AggTerm := AExpr (Constant (Value_double None)).
Definition NullDecimal : AggTerm := AExpr (Constant (Value_decimal None)).
Definition NullDate : AggTerm := AExpr (Constant (Value_date None)).
Definition NullTimestamp : AggTerm := AExpr (Constant (Value_timestamp None)).
Definition NullTimestamptz : AggTerm := AExpr (Constant (Value_timestamptz None)).

Definition SelectZ (name : string) : SelectItemT := SelectAs (DotZ name) (AttrZ name).
Definition SelectString (name : string) : SelectItemT :=
  SelectAs (DotString name) (AttrString name).
Definition SelectBool (name : string) : SelectItemT := SelectAs (DotBool name) (AttrBool name).
Definition SelectFloat (name : string) : SelectItemT :=
  SelectAs (DotFloat name) (AttrFloat name).
Definition SelectDouble (name : string) : SelectItemT :=
  SelectAs (DotDouble name) (AttrDouble name).
Definition SelectDecimal (name : string) (precision scale : Z) : SelectItemT :=
  SelectAs (DotDecimal name precision scale) (AttrDecimal name precision scale).
Definition SelectDate (name : string) : SelectItemT :=
  SelectAs (DotDate name) (AttrDate name).
Definition SelectTimestamp (name : string) (precision : Z) : SelectItemT :=
  SelectAs (DotTimestamp name precision) (AttrTimestamp name precision).
Definition SelectTimestamptz (name : string) (precision : Z) : SelectItemT :=
  SelectAs (DotTimestamptz name precision) (AttrTimestamptz name precision).

Definition SelectColumn (column : ColumnRef) : SelectItemT :=
  SelectAs (DotColumn column) (ColumnAttribute column).

Definition SelectColumns (columns : list ColumnRef) : SelectListT :=
  SelectList (List.map SelectColumn columns).
