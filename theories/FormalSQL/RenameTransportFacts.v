(******************************************************************************)
(** TNull adapters and proof-agent facade for generic renaming transport.     **)
(******************************************************************************)

From Stdlib Require Import List String.
From SQLFS Require Export SqlRenameFacts SqlQueryRenameTransport.
From SQLFS Require Import SqlSyntax GenericInstance Values Bool3 FiniteSet FTuples
  SqlOutcome SqlQuerySyntax SqlQuerySemantics SqlQueryContexts.
From Logos.FormalSQL Require Export QueryTNullSyntax.

Import ListNotations.
Import Tuple.

(** Rename only the textual identity of a TNull attribute.  Every SQL type
    constructor and every VARCHAR/CHAR, DECIMAL, TIMESTAMP, or TIMESTAMPTZ
    modifier remains structurally unchanged. *)
Definition rename_tnull_attribute_name
    (rename_name : string -> string)
    (source : attribute TNull) : attribute TNull :=
  match source with
  | Attr_string name typmod => Attr_string (rename_name name) typmod
  | Attr_Z name => Attr_Z (rename_name name)
  | Attr_int32 name => Attr_int32 (rename_name name)
  | Attr_int64 name => Attr_int64 (rename_name name)
  | Attr_bool name => Attr_bool (rename_name name)
  | Attr_float name => Attr_float (rename_name name)
  | Attr_double name => Attr_double (rename_name name)
  | Attr_numeric name => Attr_numeric (rename_name name)
  | Attr_decimal name precision scale =>
      Attr_decimal (rename_name name) precision scale
  | Attr_date name => Attr_date (rename_name name)
  | Attr_time name => Attr_time (rename_name name)
  | Attr_timestamp name precision =>
      Attr_timestamp (rename_name name) precision
  | Attr_timestamptz name precision =>
      Attr_timestamptz (rename_name name) precision
  end.

Lemma tnull_attribute_name_renaming_type_preserving :
  forall rename_name source,
    type_of_attribute TNull
      (rename_tnull_attribute_name rename_name source) =
    type_of_attribute TNull source.
Proof.
intros rename_name source; destruct source; reflexivity.
Qed.

(** This is the typmod-sensitive adapter missing from generic [Tuple.Rcd].
    Exact value conformance, including NULL payloads and constrained textual,
    decimal, and temporal modifiers, is invariant under name-only renaming. *)
Lemma tnull_attribute_name_renaming_value_conforms :
  forall rename_name source value,
    value_conforms_attribute
      (rename_tnull_attribute_name rename_name source) value <->
    value_conforms_attribute source value.
Proof.
intros rename_name source value; destruct source; destruct value; reflexivity.
Qed.

Lemma tnull_rows_name_renaming_type_safe :
  forall rename_name rows,
    rows_rename_type_safe
      (rename_tnull_attribute_name rename_name) rows.
Proof.
intros rename_name rows row _ source _.
apply tnull_attribute_name_renaming_type_preserving.
Qed.

Theorem tnull_tuple_conforms_sort_renaming_transport :
  forall rename_name sort row,
    tuple_conforms_sort sort row ->
    attribute_rename_injective_on sort
      (rename_tnull_attribute_name rename_name) ->
    tuple_conforms_sort
      (Fset.map (A TNull) (A TNull)
        (rename_tnull_attribute_name rename_name) sort)
      (rename_tuple TNull (rename_tnull_attribute_name rename_name) row).
Proof.
intros rename_name sort row [Hlabels Hvalues] Hinjective.
assert (Hinjective_labels :
  attribute_rename_injective_on (labels TNull row)
    (rename_tnull_attribute_name rename_name)).
{
  intros left right Hleft Hright Hequal.
  apply Hinjective.
  - rewrite <- (Fset.mem_eq_2 _ _ _ Hlabels); exact Hleft.
  - rewrite <- (Fset.mem_eq_2 _ _ _ Hlabels); exact Hright.
  - exact Hequal.
}
split.
- pose proof (@rename_tuple_labels_transport TNull
    (rename_tnull_attribute_name rename_name) row) as Hrenamed_labels.
  pose proof (Fset.map_eq_s (A TNull) (A TNull)
    (rename_tnull_attribute_name rename_name)
    (labels TNull row) sort Hlabels) as Hmapped_labels.
  rewrite Fset.equal_spec; intro target.
  rewrite (Fset.mem_eq_2 _ _ _ Hrenamed_labels),
    (Fset.mem_eq_2 _ _ _ Hmapped_labels).
  reflexivity.
- intros target Htarget.
  rewrite Fset.mem_map in Htarget.
  destruct Htarget as [source [Hsource Hmember]].
  subst target.
  assert (Hmember_labels : source inS labels TNull row).
  {
    rewrite (Fset.mem_eq_2 _ _ _ Hlabels); exact Hmember.
  }
  rewrite (@rename_tuple_lookup_transport TNull
    (rename_tnull_attribute_name rename_name) row
    Hinjective_labels source Hmember_labels).
  apply (proj2
    (tnull_attribute_name_renaming_value_conforms
      rename_name source (dot TNull row source))).
  exact (Hvalues source Hmember).
Qed.

Lemma tnull_rows_renaming_firstn_transport :
  forall (rename_attribute : attribute TNull -> attribute TNull)
      count left right,
    rows_rename_equiv rename_attribute left right ->
    rows_rename_equiv rename_attribute
      (firstn count left) (firstn count right).
Proof.
exact (@rows_rename_equiv_firstn TNull).
Qed.

Lemma tnull_rows_renaming_skipn_transport :
  forall (rename_attribute : attribute TNull -> attribute TNull)
      count left right,
    rows_rename_equiv rename_attribute left right ->
    rows_rename_equiv rename_attribute
      (skipn count left) (skipn count right).
Proof.
exact (@rows_rename_equiv_skipn TNull).
Qed.

(** The generic FormalSQL relation accepts an arbitrary attribute map because
    [Tuple.Rcd] exposes only its abstract type projection.  The TNull facade is
    deliberately narrower: callers provide only a textual name map and every
    query/context entry point applies [rename_tnull_attribute_name].  Thus an
    agent cannot use this facade to change a string typmod, decimal
    precision/scale, or temporal precision while claiming alpha-renaming. *)
Definition tnull_query_rename_transport_under
    (db : db_state)
    (environment_relation : Env.env TNull -> Env.env TNull -> Prop)
    (rename_name : string -> string)
    (left right : QueryExpr) : Prop :=
  forall boolean_schedule : boolean_site -> boolean_evaluation_order,
    @query_rename_transport_under TNull relname
      (@_basesort TNull db) (@_instance TNull db) unknown3
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error
      NullValues.is_null_value boolean_schedule
      TNullLeafHasType TNullCallHasType TNullPredicateHasTypes
      type_int64 type_bool
      environment_relation (rename_tnull_attribute_name rename_name)
      left right.

(** Exact mapped-schema observations are useful at proof boundaries but are
    not themselves a full query alpha-renaming certificate: an output-only
    row adapter can satisfy them.  Use the constructor-local transport layer
    when predicates, keys, aliases, or subqueries must be certified. *)
Definition tnull_query_mapped_schema_outcome_equiv
    (db : db_state) (left_env right_env : Env.env TNull)
    (rename_name : string -> string)
    (left right : QueryExpr) : Prop :=
  forall boolean_schedule : boolean_site -> boolean_evaluation_order,
    @query_mapped_schema_outcome_equiv TNull relname
      (@_basesort TNull db) (@_instance TNull db) unknown3
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error
      NullValues.is_null_value boolean_schedule
      TNullLeafHasType TNullCallHasType TNullPredicateHasTypes
      type_int64 type_bool
      left_env right_env (rename_tnull_attribute_name rename_name)
      left right.

Lemma tnull_query_mapped_schema_outcome_equiv_mapped_schema :
  forall db left_env right_env (rename_name : string -> string) left right,
    tnull_query_mapped_schema_outcome_equiv
      db left_env right_env rename_name left right ->
    map (rename_tnull_attribute_name rename_name)
      (query_expr_outputs left) =
      query_expr_outputs right.
Proof.
intros db left_env right_env rename_name left right Hmapped.
specialize (Hmapped (fun _ => BooleanLeftFirst)).
exact (@query_mapped_schema_outcome_equiv_mapped_schema TNull relname
  (@_basesort TNull db) (@_instance TNull db) unknown3
  NullValues.interp_scalar_operator_runtime_error
  NullValues.interp_aggregate_runtime_error
  NullValues.is_null_value (fun _ => BooleanLeftFirst)
  TNullLeafHasType TNullCallHasType TNullPredicateHasTypes
  type_int64 type_bool
  left_env right_env (rename_tnull_attribute_name rename_name)
  left right Hmapped).
Qed.

Definition tnull_query_rename_context_compatible
    (db : db_state)
    (environment_relation : Env.env TNull -> Env.env TNull -> Prop)
    (rename_name : string -> string)
    (left_context right_context : query_expr_context TNull relname) : Prop :=
  forall boolean_schedule : boolean_site -> boolean_evaluation_order,
    @query_rename_context_compatible TNull relname
      (@_basesort TNull db) (@_instance TNull db) unknown3
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error
      NullValues.is_null_value boolean_schedule
      TNullLeafHasType TNullCallHasType TNullPredicateHasTypes
      type_int64 type_bool
      environment_relation (rename_tnull_attribute_name rename_name)
      left_context right_context.

(** Proof-agent entry point for arbitrary nested projection, join, grouping,
    window, ordering, and slicing contexts.  Each context pair must first be
    certified by the matching constructor-local transport theorem. *)
Theorem tnull_query_renaming_context_chain_transport :
  forall db environment_relation (rename_name : string -> string)
      left_contexts right_contexts,
    Forall2
      (tnull_query_rename_context_compatible
        db environment_relation rename_name)
      left_contexts right_contexts ->
    forall left right,
      tnull_query_rename_transport_under
        db environment_relation rename_name left right ->
      tnull_query_rename_transport_under
        db environment_relation rename_name
        (plug_query_rename_contexts left_contexts left)
        (plug_query_rename_contexts right_contexts right).
Proof.
intros db environment_relation rename_name
  left_contexts right_contexts Hcontexts left right Htransport.
intro boolean_schedule.
assert (Hcontexts_scheduled :
  Forall2
    (@query_rename_context_compatible TNull relname
      (@_basesort TNull db) (@_instance TNull db) unknown3
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error
      NullValues.is_null_value boolean_schedule
      TNullLeafHasType TNullCallHasType TNullPredicateHasTypes
      type_int64 type_bool
      environment_relation (rename_tnull_attribute_name rename_name))
    left_contexts right_contexts).
{
  induction Hcontexts; constructor.
  - now apply H.
  - exact IHHcontexts.
}
exact (@query_rename_context_chain_transport TNull relname
  (@_basesort TNull db) (@_instance TNull db) unknown3
  NullValues.interp_scalar_operator_runtime_error
  NullValues.interp_aggregate_runtime_error
  NullValues.is_null_value boolean_schedule
  TNullLeafHasType TNullCallHasType TNullPredicateHasTypes
  type_int64 type_bool
  environment_relation (rename_tnull_attribute_name rename_name)
  left_contexts right_contexts Hcontexts_scheduled
  left right (Htransport boolean_schedule)).
Qed.
