From SQLFS Require Import FTuples OrderedSet FiniteSet FiniteBag FiniteCollection
  SqlSyntax GenericInstance Values Bool3 Env SqlOutcome SqlErrorSemantics
  SchemaConstraints SqlBagAbstraction SqlQuerySemantics SqlQuerySyntax
  SqlQueryWellFormed SqlQueryContexts.
From Logos Require Import FormalSQL.QueryTNullSyntax.
From Stdlib Require Import List.

Import ListNotations.
Import Tuple.

(** Query-local bindings are a Logos composition layer, not a new SQL algebra
    operator.  Every definition and body remains an ordinary [QueryExpr]. *)
Record LocalQueryBinding : Type := MakeLocalQueryBinding {
  local_binding_relation : relname;
  local_binding_outputs : list (attribute TNull);
  local_binding_query : QueryExpr
}.

Record LocalQuerySchema : Type := MakeLocalQuerySchema {
  local_query_schema_relation : relname;
  local_query_schema_outputs : list (attribute TNull)
}.

Record BoundQuery : Type := MakeBoundQuery {
  bound_query_bindings : list LocalQueryBinding;
  bound_query_body : QueryExpr
}.

Definition BoundQueryProgram := list BoundQuery.

Definition bound_query_outputs (query : BoundQuery) : list (attribute TNull) :=
  query_expr_outputs (bound_query_body query).

Definition local_query_binding_schema
    (binding : LocalQueryBinding) : LocalQuerySchema :=
  MakeLocalQuerySchema
    (local_binding_relation binding)
    (local_binding_outputs binding).

Definition local_query_schema_relations
    (schemas : list LocalQuerySchema) : list relname :=
  map local_query_schema_relation schemas.

Definition local_query_binding_relations
    (bindings : list LocalQueryBinding) : list relname :=
  map local_binding_relation bindings.

Definition local_query_schemas_fresh
    (db : db_state) (schemas : list LocalQuerySchema) : Prop :=
  Forall
    (fun relation => ~ In relation (@_relnames TNull db))
    (local_query_schema_relations schemas).

Definition bound_query_program_binding_relations
    (program : BoundQueryProgram) : list relname :=
  flat_map
    (fun query => local_query_binding_relations (bound_query_bindings query))
    program.

Definition bound_query_boolean_sites (query : BoundQuery) : list boolean_site :=
  query_expr_boolean_sites (bound_query_body query) ++
  flat_map
    (fun binding => query_expr_boolean_sites (local_binding_query binding))
    (bound_query_bindings query).

Definition query_local_references_allowed
    (schemas : list LocalQuerySchema)
    (all_local allowed_local : list relname) (query : QueryExpr) : Prop :=
  Forall
    (fun reference =>
      let relation := fst reference in
      In relation all_local ->
      In relation allowed_local /\
      In (MakeLocalQuerySchema relation (snd reference)) schemas)
    (query_expr_table_references query).

(** Extending the set of bindings in scope cannot invalidate a reference that
    was already allowed.  The complete local-name set and exact ordered schema
    signatures remain fixed. *)
Lemma query_local_references_allowed_available_monotone :
  forall schemas all_local before after query,
    (forall relation, In relation before -> In relation after) ->
    query_local_references_allowed schemas all_local before query ->
    query_local_references_allowed schemas all_local after query.
Proof.
intros schemas all_local before after query Hincluded Hallowed.
unfold query_local_references_allowed in *.
rewrite Forall_forall in Hallowed |- *.
intros [relation outputs] Hreference; cbn in *.
specialize (Hallowed (relation, outputs) Hreference).
intro Hlocal.
destruct (Hallowed Hlocal) as [Havailable Hschema].
split; [now apply Hincluded | exact Hschema].
Qed.

Fixpoint local_query_binding_dependencies_well_formed
    (schemas : list LocalQuerySchema) (all_local available_local : list relname)
    (bindings : list LocalQueryBinding) : Prop :=
  match bindings with
  | nil => True
  | binding :: rest =>
      query_local_references_allowed schemas all_local available_local
        (local_binding_query binding) /\
      local_query_binding_dependencies_well_formed schemas all_local
        (local_binding_relation binding :: available_local) rest
  end.

(** A well-formed binding sequence remains well formed when earlier bindings
    become available.  Each newly defined head is still extended in front of
    both availability lists, so left-to-right dependency order is unchanged. *)
Lemma local_query_binding_dependencies_available_monotone :
  forall schemas all_local before after bindings,
    (forall relation, In relation before -> In relation after) ->
    local_query_binding_dependencies_well_formed
      schemas all_local before bindings ->
    local_query_binding_dependencies_well_formed
      schemas all_local after bindings.
Proof.
intros schemas all_local before after bindings.
revert before after.
induction bindings as [|binding rest IH];
  intros before after Hincluded Hwell_formed; cbn in *; [exact I|].
destruct Hwell_formed as [Hbinding Hrest]; split.
- eapply query_local_references_allowed_available_monotone;
    [exact Hincluded | exact Hbinding].
- eapply IH; [|exact Hrest].
  intros relation [Hequal | Hbefore].
  + now left.
  + right; now apply Hincluded.
Qed.

Definition bound_query_local_references_well_formed
    (schemas : list LocalQuerySchema) (query : BoundQuery) : Prop :=
  let all_local := local_query_schema_relations schemas in
  let bindings := bound_query_bindings query in
  local_query_binding_dependencies_well_formed schemas all_local nil bindings /\
  query_local_references_allowed schemas all_local
    (local_query_binding_relations bindings) (bound_query_body query).

(** Schemas are installed before any definition runs.  Dependency order is
    still enforced by the Rust importer; predeclaration merely gives ordinary
    [QExpr_Table] leaves their statically known row types. *)
Definition declare_local_query_schema
    (db : db_state) (schema : LocalQuerySchema) : db_state :=
  create_table db
    (local_query_schema_relation schema)
    (local_query_schema_outputs schema).

Fixpoint declare_local_query_schemas
    (db : db_state) (schemas : list LocalQuerySchema) : db_state :=
  match schemas with
  | nil => db
  | schema :: rest =>
      declare_local_query_schemas
        (declare_local_query_schema db schema) rest
  end.

(** Predeclaring schemas changes no table contents. *)
Lemma declare_local_query_schemas_instance_preserving :
  forall db schemas,
    @_instance TNull (declare_local_query_schemas db schemas) =
    @_instance TNull db.
Proof.
intros db schemas; revert db.
induction schemas as [|schema rest IH]; intro db; cbn; [reflexivity|].
rewrite IH.
unfold declare_local_query_schema, create_table.
reflexivity.
Qed.

(** A relation absent from every local schema retains its original sort after
    the complete predeclaration pass. *)
Lemma declare_local_query_schemas_basesort_absent :
  forall db schemas relation,
    ~ In relation (local_query_schema_relations schemas) ->
    @_basesort TNull (declare_local_query_schemas db schemas) relation =
    @_basesort TNull db relation.
Proof.
intros db schemas; revert db.
induction schemas as [|schema rest IH]; intros db relation Habsent.
- reflexivity.
- cbn [local_query_schema_relations] in Habsent.
  cbn [declare_local_query_schemas].
  rewrite (IH (declare_local_query_schema db schema) relation).
  + unfold declare_local_query_schema, create_table.
    apply (@basesort_create_table_neq TNull).
    intro Hequal; apply Habsent; left; now symmetry.
  + intro Hmember; apply Habsent; now right.
Qed.

(** A successful definition is materialized as one bag.  Later references may
    choose different list representatives of this bag, but they cannot replay
    the definition or choose a different successful outcome. *)
Definition set_local_query_binding_rows
    (db : db_state) (binding : LocalQueryBinding)
    (rows : list (tuple TNull)) : db_state :=
  @mk_state TNull
    (@_relnames TNull db)
    (@_basesort TNull db)
    (fun relation =>
      match Oset.compare ORN relation (local_binding_relation binding) with
      | Eq => @query_rows_bag TNull rows
      | _ => @_instance TNull db relation
      end).

(** Materialization updates only the instance function. *)
Lemma set_local_query_binding_rows_relnames_preserving :
  forall db binding rows,
    @_relnames TNull (set_local_query_binding_rows db binding rows) =
    @_relnames TNull db.
Proof.
reflexivity.
Qed.

Lemma set_local_query_binding_rows_basesort_preserving :
  forall db binding rows relation,
    @_basesort TNull (set_local_query_binding_rows db binding rows) relation =
    @_basesort TNull db relation.
Proof.
reflexivity.
Qed.

(** Lookup at the defined name observes exactly the newly materialized bag;
    this is the operational shadowing law for repeated writes. *)
Lemma set_local_query_binding_rows_instance_eq :
  forall db binding rows,
    @_instance TNull (set_local_query_binding_rows db binding rows)
      (local_binding_relation binding) =
    @query_rows_bag TNull rows.
Proof.
intros db binding rows.
unfold set_local_query_binding_rows; cbn [_instance].
rewrite Oset.compare_eq_refl; reflexivity.
Qed.

(** Lookup at every distinct relation is preserved by the extension. *)
Lemma set_local_query_binding_rows_instance_neq :
  forall db binding rows relation,
    relation <> local_binding_relation binding ->
    @_instance TNull (set_local_query_binding_rows db binding rows) relation =
    @_instance TNull db relation.
Proof.
intros db binding rows relation Hdistinct.
unfold set_local_query_binding_rows; cbn [_instance].
destruct (Oset.compare ORN relation (local_binding_relation binding))
  eqn:Hcompare; try reflexivity.
apply Oset.compare_eq_iff in Hcompare; contradiction.
Qed.

Definition eval_query_expr_with_schedule
    (db : db_state)
    (schedule : boolean_site -> boolean_evaluation_order)
    (env : Env.env TNull)
    (query : QueryExpr)
    (outcome : sql_outcome (list (tuple TNull))) : Prop :=
  @eval_query_expr_outcome TNull relname
    (@_basesort TNull db)
    (@_instance TNull db)
    unknown3
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error
    NullValues.is_null_value
    schedule env query outcome.

(** The ordinary table leaf used by a consumer of one local binding.  Keeping
    this constructor named makes the materialization/substitution boundary
    explicit without adding a second query language. *)
Definition local_query_binding_reference
    (binding : LocalQueryBinding) : QueryExpr :=
  @QExpr_Table TNull relname
    (local_binding_outputs binding)
    (local_binding_relation binding).

(** A concrete successful binding result represented as a query leaf.  This
    is the semantic intermediate between the one shared materialized table and
    a replayable/inlined definition.  It intentionally stores a bag, not the
    particular list representative returned while evaluating the definition. *)
Definition local_query_binding_values
    (binding : LocalQueryBinding) (rows : list (tuple TNull)) : QueryExpr :=
  @QExpr_Values TNull relname
    (local_binding_outputs binding) (@query_rows_bag TNull rows).

Definition local_query_binding_reference_well_typed
    (db : db_state) (binding : LocalQueryBinding) : Prop :=
  (@query_outputs_sort TNull (local_binding_outputs binding) =S?=
    @_basesort TNull db (local_binding_relation binding)) = true.

(** Once a successful result has been installed, the local table reference
    denotes exactly that result bag.  This is the small database-update fact
    that agents previously reconstructed by unfolding [query_table_bag]. *)
Lemma set_local_query_binding_rows_table_bag :
  forall db binding rows,
    local_query_binding_reference_well_typed db binding ->
    @query_table_bag TNull relname
      (@_basesort TNull (set_local_query_binding_rows db binding rows))
      (@_instance TNull (set_local_query_binding_rows db binding rows))
      (local_binding_outputs binding)
      (local_binding_relation binding) =
    @query_rows_bag TNull rows.
Proof.
intros db binding rows Htyped.
unfold query_table_bag, local_query_binding_reference_well_typed in *.
rewrite set_local_query_binding_rows_basesort_preserving.
rewrite Htyped.
apply set_local_query_binding_rows_instance_eq.
Qed.

(** A materialized table read and the corresponding concrete bag leaf have
    exactly the same scheduled row outcomes, including multiplicity and every
    legal list representative.  Neither leaf can invent a runtime error. *)
Lemma eval_local_query_binding_reference_values_iff :
  forall db binding rows schedule env outcome,
    local_query_binding_reference_well_typed db binding ->
    eval_query_expr_with_schedule
      (set_local_query_binding_rows db binding rows) schedule env
      (local_query_binding_reference binding) outcome <->
    eval_query_expr_with_schedule
      (set_local_query_binding_rows db binding rows) schedule env
      (local_query_binding_values binding rows) outcome.
Proof.
intros db binding rows schedule env [output | error] Htyped; split;
  intro Heval; inversion Heval; subst.
- apply EQuery_Values.
  rewrite <- (set_local_query_binding_rows_table_bag
    db binding rows Htyped); assumption.
- apply EQuery_Table.
  rewrite (set_local_query_binding_rows_table_bag
    db binding rows Htyped); assumption.
Qed.

(** EXISTS deliberately has its own demand evaluator.  For table/VALUES
    leaves it is nevertheless the same mapped row observation, so the exact
    materialized-reference substitution remains valid under EXISTS. *)
Lemma eval_local_query_binding_reference_values_exists_iff :
  forall db binding rows schedule env outcome,
    local_query_binding_reference_well_typed db binding ->
    @eval_query_exists_outcome TNull relname
      (@_basesort TNull (set_local_query_binding_rows db binding rows))
      (@_instance TNull (set_local_query_binding_rows db binding rows))
      unknown3 NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error NullValues.is_null_value
      schedule env (local_query_binding_reference binding) outcome <->
    @eval_query_exists_outcome TNull relname
      (@_basesort TNull (set_local_query_binding_rows db binding rows))
      (@_instance TNull (set_local_query_binding_rows db binding rows))
      unknown3 NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error NullValues.is_null_value
      schedule env (local_query_binding_values binding rows) outcome.
Proof.
intros db binding rows schedule env outcome Htyped; split; intro Heval;
  inversion Heval; subst; try discriminate.
- eapply EExists_Demanded; [reflexivity|].
  now apply (proj1
    (eval_local_query_binding_reference_values_iff
      db binding rows schedule env _ Htyped)).
- eapply EExists_Demanded; [reflexivity|].
  now apply (proj2
    (eval_local_query_binding_reference_values_iff
      db binding rows schedule env _ Htyped)).
Qed.

(** Demand-aware equality is what permits substitution below arbitrary query
    and scalar contexts.  In row-consuming positions it preserves the complete
    ordered/error relation; under EXISTS it preserves the dedicated target-
    eliding observation. *)
Lemma local_query_binding_reference_values_global_demand_equiv :
  forall db binding rows schedule demand,
    local_query_binding_reference_well_typed db binding ->
    @query_expr_global_demand_equiv TNull relname
      (@_basesort TNull (set_local_query_binding_rows db binding rows))
      (@_instance TNull (set_local_query_binding_rows db binding rows))
      unknown3 NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error NullValues.is_null_value
      schedule demand
      (local_query_binding_reference binding)
      (local_query_binding_values binding rows).
Proof.
intros db binding rows schedule [|] Htyped; cbn.
- split; [reflexivity|].
  intros env outcome.
  now apply eval_local_query_binding_reference_values_iff.
- intros env outcome.
  now apply eval_local_query_binding_reference_values_exists_iff.
Qed.

(** One theorem substitutes the materialized reference through every query
    context supported by FormalSQL, including occurrences nested in scalar
    subqueries.  It changes only the reference leaf; evaluation of the binding
    definition itself remains outside this theorem and is handled by the
    BoundQuery contract below. *)
Theorem local_query_binding_reference_context_substitution :
  forall db binding rows schedule
      (context : @query_expr_context TNull relname),
    local_query_binding_reference_well_typed db binding ->
    @query_expr_global_typed_outcome_equiv TNull relname
      (@_basesort TNull (set_local_query_binding_rows db binding rows))
      (@_instance TNull (set_local_query_binding_rows db binding rows))
      unknown3 NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error NullValues.is_null_value
      schedule
      (plug_query_expr_context context
        (local_query_binding_reference binding))
      (plug_query_expr_context context
        (local_query_binding_values binding rows)).
Proof.
intros db binding rows schedule context Htyped.
apply query_expr_context_global_congr.
now apply local_query_binding_reference_values_global_demand_equiv.
Qed.

Fixpoint eval_local_query_bindings_with_schedule
    (schedule : boolean_site -> boolean_evaluation_order)
    (env : Env.env TNull)
    (db : db_state)
    (bindings : list LocalQueryBinding)
    (body : QueryExpr)
    (outcome : sql_outcome (list (tuple TNull))) : Prop :=
  match bindings with
  | nil => eval_query_expr_with_schedule db schedule env body outcome
  | binding :: rest =>
      (exists error,
        eval_query_expr_with_schedule db schedule env
          (local_binding_query binding) (SqlError error) /\
        outcome = SqlError error) \/
      (exists rows,
        eval_query_expr_with_schedule db schedule env
          (local_binding_query binding) (SqlSuccess rows) /\
        eval_local_query_bindings_with_schedule schedule env
          (set_local_query_binding_rows db binding rows)
          rest body outcome)
  end.

(** A reachable body database records only successful, left-to-right
    materialization of the complete local-binding prefix.  The same
    [schedule] is used for every definition and, below, for the body.  Each
    definition is evaluated once along a derivation and its one successful
    row list is installed through [set_local_query_binding_rows], hence as a
    bag rather than as a distinguished list representative. *)
Inductive local_query_bindings_reachable_with_schedule
    (schedule : boolean_site -> boolean_evaluation_order)
    (env : Env.env TNull) :
    db_state -> list LocalQueryBinding -> db_state -> Prop :=
  | LocalQueryBindingsReachableNil :
      forall db,
        local_query_bindings_reachable_with_schedule
          schedule env db nil db
  | LocalQueryBindingsReachableCons :
      forall db binding rest rows reached,
        eval_query_expr_with_schedule db schedule env
          (local_binding_query binding) (SqlSuccess rows) ->
        local_query_bindings_reachable_with_schedule schedule env
          (set_local_query_binding_rows db binding rows) rest reached ->
        local_query_bindings_reachable_with_schedule schedule env
          db (binding :: rest) reached.

(** Binding errors are kept separate from body errors.  A head error ends the
    prefix immediately; a later error is reachable only after the head has
    succeeded and been materialized. *)
Inductive local_query_bindings_error_with_schedule
    (schedule : boolean_site -> boolean_evaluation_order)
    (env : Env.env TNull) :
    db_state -> list LocalQueryBinding -> sql_runtime_error -> Prop :=
  | LocalQueryBindingsErrorHere :
      forall db binding rest error,
        eval_query_expr_with_schedule db schedule env
          (local_binding_query binding) (SqlError error) ->
        local_query_bindings_error_with_schedule schedule env
          db (binding :: rest) error
  | LocalQueryBindingsErrorLater :
      forall db binding rest rows error,
        eval_query_expr_with_schedule db schedule env
          (local_binding_query binding) (SqlSuccess rows) ->
        local_query_bindings_error_with_schedule schedule env
          (set_local_query_binding_rows db binding rows) rest error ->
        local_query_bindings_error_with_schedule schedule env
          db (binding :: rest) error.

(** Possible body outcomes quantify only databases actually reachable by a
    successful materialization prefix.  The schedule may differ between the
    two sides of a later equivalence proof, but within each witness it is
    shared by the prefix and body.  This is the appropriate possible-outcome
    boundary; it does not require fixed-schedule body equality. *)
Definition eval_bound_query_body_possible_outcome
    (db : db_state) (schemas : list LocalQuerySchema)
    (env : Env.env TNull) (query : BoundQuery)
    (outcome : sql_outcome (list (tuple TNull))) : Prop :=
  exists schedule reached,
    local_query_bindings_reachable_with_schedule schedule env
      (declare_local_query_schemas db schemas)
      (bound_query_bindings query) reached /\
    eval_query_expr_with_schedule reached schedule env
      (bound_query_body query) outcome.

Definition eval_bound_query_possible_outcome
    (db : db_state) (schemas : list LocalQuerySchema)
    (env : Env.env TNull)
    (query : BoundQuery)
    (outcome : sql_outcome (list (tuple TNull))) : Prop :=
  exists schedule : boolean_site -> boolean_evaluation_order,
    eval_local_query_bindings_with_schedule schedule env
      (declare_local_query_schemas db schemas)
      (bound_query_bindings query)
      (bound_query_body query)
      outcome.

Definition bound_query_possible_equiv
    (db : db_state) (schemas : list LocalQuerySchema)
    (env : Env.env TNull)
    (left right : BoundQuery) : Prop :=
  bound_query_outputs left = bound_query_outputs right /\
  successful_relation_equiv (@ordered_rows_equiv TNull)
    (eval_bound_query_possible_outcome db schemas env left)
    (eval_bound_query_possible_outcome db schemas env right).

Definition bound_query_possible_outcome_equiv
    (db : db_state) (schemas : list LocalQuerySchema)
    (env : Env.env TNull)
    (left right : BoundQuery) : Prop :=
  bound_query_outputs left = bound_query_outputs right /\
  outcome_relation_equiv (@ordered_rows_equiv TNull)
    (eval_bound_query_possible_outcome db schemas env left)
    (eval_bound_query_possible_outcome db schemas env right).

(** The operational binding evaluator is exactly the disjoint choice between
    a prefix error and evaluation of the body in a successfully reachable
    database.  In particular, no later definition or body is evaluated after
    a prefix error. *)
Lemma eval_local_query_bindings_with_schedule_decompose :
  forall schedule env bindings db body outcome,
    eval_local_query_bindings_with_schedule schedule env db bindings
      body outcome <->
    (exists error,
      outcome = SqlError error /\
      local_query_bindings_error_with_schedule schedule env
        db bindings error) \/
    (exists reached,
      local_query_bindings_reachable_with_schedule schedule env
        db bindings reached /\
      eval_query_expr_with_schedule reached schedule env body outcome).
Proof.
intros schedule env bindings; induction bindings as [|binding rest IH];
  intros db body outcome.
- cbn [eval_local_query_bindings_with_schedule].
  split; intro Heval.
  + right; exists db; split; [constructor|exact Heval].
  + destruct Heval as [[error [_ Herror]] | [reached [Hreach Hbody]]].
    * inversion Herror.
    * inversion Hreach; subst; exact Hbody.
- cbn [eval_local_query_bindings_with_schedule].
  split; intro Heval.
  + destruct Heval as
      [[error [Hbinding ->]] | [rows [Hbinding Hrest]]].
    * left; exists error; split; [reflexivity|].
      now apply LocalQueryBindingsErrorHere.
    * apply (proj1 (IH
        (set_local_query_binding_rows db binding rows) body outcome))
        in Hrest.
      destruct Hrest as
        [[error [Houtcome Herror]] | [reached [Hreach Hbody]]].
      -- left; exists error; split; [exact Houtcome|].
         now apply LocalQueryBindingsErrorLater with (rows := rows).
      -- right; exists reached; split; [|exact Hbody].
         now apply LocalQueryBindingsReachableCons with (rows := rows).
  + destruct Heval as
      [[error [Houtcome Herror]] | [reached [Hreach Hbody]]].
    * subst outcome; inversion Herror; subst.
      -- left; exists error; now split.
      -- right; exists rows; split; [assumption|].
         apply (proj2 (IH
           (set_local_query_binding_rows db binding rows)
           body (SqlError error))).
         left; exists error; now split.
    * inversion Hreach; subst.
      right; exists rows; split; [assumption|].
      apply (proj2 (IH
        (set_local_query_binding_rows db binding rows) body outcome)).
      right; exists reached; now split.
Qed.

Lemma eval_bound_query_possible_outcome_decompose :
  forall db schemas env query outcome,
    eval_bound_query_possible_outcome db schemas env query outcome <->
    (exists schedule error,
      outcome = SqlError error /\
      local_query_bindings_error_with_schedule schedule env
        (declare_local_query_schemas db schemas)
        (bound_query_bindings query) error) \/
    eval_bound_query_body_possible_outcome db schemas env query outcome.
Proof.
intros db schemas env query outcome.
unfold eval_bound_query_possible_outcome,
  eval_bound_query_body_possible_outcome.
split.
- intros [schedule Heval].
  apply eval_local_query_bindings_with_schedule_decompose in Heval.
  destruct Heval as
    [[error [Houtcome Herror]] | [reached [Hreach Hbody]]].
  + left; exists schedule, error; now split.
  + right; exists schedule, reached; now split.
- intros [[schedule [error [Houtcome Herror]]]
    | [schedule [reached [Hreach Hbody]]]].
  + exists schedule.
    apply eval_local_query_bindings_with_schedule_decompose.
    left; exists error; now split.
  + exists schedule.
    apply eval_local_query_bindings_with_schedule_decompose.
    right; exists reached; now split.
Qed.

(** The ordinary possible-outcome relation for a query after local schemas
    have been declared, but without eagerly evaluating any local definition.
    This is the semantic endpoint of a CTE-inline transformation. *)
Definition eval_inlined_query_possible_outcome
    (db : db_state) (schemas : list LocalQuerySchema)
    (env : Env.env TNull) (query : QueryExpr)
    (outcome : sql_outcome (list (tuple TNull))) : Prop :=
  exists schedule,
    eval_query_expr_with_schedule
      (declare_local_query_schemas db schemas) schedule env query outcome.

Definition eval_bound_query_prefix_error_possible
    (db : db_state) (schemas : list LocalQuerySchema)
    (env : Env.env TNull) (query : BoundQuery)
    (error : sql_runtime_error) : Prop :=
  exists schedule,
    local_query_bindings_error_with_schedule schedule env
      (declare_local_query_schemas db schemas)
      (bound_query_bindings query) error.

(** Generalizes [eval_bound_query_without_bindings] to a nonempty list of
    predeclared local schemas.  With no definitions there is no
    materialization step: the BoundQuery wrapper is exactly the ordinary query
    relation in the declared database. *)
Lemma eval_bound_query_without_bindings_with_schemas :
  forall db schemas env query outcome,
    eval_bound_query_possible_outcome db schemas env
      (MakeBoundQuery nil query) outcome <->
    eval_inlined_query_possible_outcome db schemas env query outcome.
Proof.
intros db schemas env query outcome; reflexivity.
Qed.

(** A replay/inline contract isolates the genuinely semantic obligations from
    BoundQuery's prefix plumbing.

    Successful outcomes of a bound query necessarily come from a successfully
    materialized prefix and a reachable body.  Errors may instead arise in the
    prefix or in such a reachable body.  An inlined query is a sound replacement
    exactly when it transports both successful directions, preserves this
    complete error union, and both relations are inhabited.

    The contract deliberately does not assert that every CTE is replayable.
    Duplicating a definition that can error, has multiple successful bags, or
    is evaluated in a demand-sensitive context requires additional proof. *)
Definition bound_query_inline_possible_outcome_contract
    (db : db_state) (schemas : list LocalQuerySchema)
    (env : Env.env TNull) (bound : BoundQuery)
    (inlined : QueryExpr) : Prop :=
  bound_query_outputs bound = query_expr_outputs inlined /\
  (exists outcome,
    eval_bound_query_possible_outcome db schemas env bound outcome) /\
  (exists outcome,
    eval_inlined_query_possible_outcome db schemas env inlined outcome) /\
  (forall bound_rows,
    eval_bound_query_body_possible_outcome db schemas env bound
      (SqlSuccess bound_rows) ->
    exists inlined_rows,
      eval_inlined_query_possible_outcome db schemas env inlined
        (SqlSuccess inlined_rows) /\
      @ordered_rows_equiv TNull bound_rows inlined_rows) /\
  (forall inlined_rows,
    eval_inlined_query_possible_outcome db schemas env inlined
      (SqlSuccess inlined_rows) ->
    exists bound_rows,
      eval_bound_query_body_possible_outcome db schemas env bound
        (SqlSuccess bound_rows) /\
      @ordered_rows_equiv TNull bound_rows inlined_rows) /\
  (forall error,
    (eval_bound_query_prefix_error_possible db schemas env bound error \/
     eval_bound_query_body_possible_outcome db schemas env bound
       (SqlError error)) <->
    eval_inlined_query_possible_outcome db schemas env inlined
      (SqlError error)).

(** The public CTE-substitution bridge.  Once the operator-specific inline
    contract is established, binding evaluation, local-database updates,
    reference lookup, prefix/body error scheduling, and the final unbound
    wrapper are discharged here once and for all. *)
Theorem bound_query_inline_possible_outcome_contract_sound :
  forall db schemas env bound inlined,
    bound_query_inline_possible_outcome_contract
      db schemas env bound inlined ->
    bound_query_possible_outcome_equiv db schemas env
      bound (MakeBoundQuery nil inlined).
Proof.
intros db schemas env bound inlined
  [Houtputs [Hbound [Hinlined_inhabited
    [Hforward [Hbackward Herrors]]]]].
split; [exact Houtputs|].
apply outcome_relation_equiv_intro.
- exact Hbound.
- destruct Hinlined_inhabited as [outcome Houtcome].
  exists outcome.
  now apply eval_bound_query_without_bindings_with_schemas.
- intros bound_rows Houtcome.
  apply eval_bound_query_possible_outcome_decompose in Houtcome.
  destruct Houtcome as
    [[schedule [error [Himpossible _]]] | Hbody];
    [discriminate Himpossible|].
  destruct (Hforward bound_rows Hbody) as
    [inlined_rows [Hinlined Hrows]].
  exists inlined_rows; split; [|exact Hrows].
  now apply eval_bound_query_without_bindings_with_schemas.
- intros inlined_rows Houtcome.
  apply eval_bound_query_without_bindings_with_schemas in Houtcome.
  destruct (Hbackward inlined_rows Houtcome) as
    [bound_rows [Hbody Hrows]].
  exists bound_rows; split; [|exact Hrows].
  apply eval_bound_query_possible_outcome_decompose.
  now right.
- intro error; split; intro Houtcome.
  + apply eval_bound_query_possible_outcome_decompose in Houtcome.
    apply eval_bound_query_without_bindings_with_schemas.
    apply (proj1 (Herrors error)).
    destruct Houtcome as
      [[schedule [prefix_error [Hsame Hprefix]]] | Hbody].
    * inversion Hsame; subst prefix_error.
      left; now exists schedule.
    * now right.
  + apply eval_bound_query_without_bindings_with_schemas in Houtcome.
    apply (proj2 (Herrors error)) in Houtcome.
    apply eval_bound_query_possible_outcome_decompose.
    destruct Houtcome as [Hprefix | Hbody].
    * destruct Hprefix as [schedule Hprefix].
      left; exists schedule, error; now split.
    * now right.
Qed.

Definition local_query_binding_inline_possible_outcome_contract
    (db : db_state) (schemas : list LocalQuerySchema)
    (env : Env.env TNull) (binding : LocalQueryBinding)
    (body inlined : QueryExpr) : Prop :=
  bound_query_inline_possible_outcome_contract db schemas env
    (MakeBoundQuery (binding :: nil) body) inlined.

Corollary local_query_binding_inline_possible_outcome_contract_sound :
  forall db schemas env binding body inlined,
    local_query_binding_inline_possible_outcome_contract
      db schemas env binding body inlined ->
    bound_query_possible_outcome_equiv db schemas env
      (MakeBoundQuery (binding :: nil) body)
      (MakeBoundQuery nil inlined).
Proof.
intros db schemas env binding body inlined Hcontract.
now apply bound_query_inline_possible_outcome_contract_sound.
Qed.

(** A body lift keeps the local definitions literally shared and compares the
    body only after successful prefix materialization.  The body relation is
    a complete possible-outcome relation: successful row lists retain ordered
    observations, while runtime-error categories remain exact.  Since its
    witnesses include both the reachable database and the one schedule shared
    with the prefix, this contract neither assumes schedule independence nor
    demands fixed-schedule equality. *)
Definition bound_query_body_possible_outcome_lift
    (db : db_state) (schemas : list LocalQuerySchema)
    (env : Env.env TNull) (left right : BoundQuery) : Prop :=
  bound_query_bindings left = bound_query_bindings right /\
  bound_query_outputs left = bound_query_outputs right /\
  outcome_relation_equiv (@ordered_rows_equiv TNull)
    (eval_bound_query_body_possible_outcome db schemas env left)
    (eval_bound_query_body_possible_outcome db schemas env right).

Lemma bound_query_body_possible_outcome_lift_refl :
  forall db schemas env query,
    (exists outcome,
      eval_bound_query_body_possible_outcome
        db schemas env query outcome) ->
    bound_query_body_possible_outcome_lift
      db schemas env query query.
Proof.
intros db schemas env query Houtcome.
split; [reflexivity|].
split; [reflexivity|].
apply outcome_relation_equiv_refl.
- apply ordered_rows_equiv_refl.
- exact Houtcome.
Qed.

Theorem bound_query_body_possible_outcome_lift_sound :
  forall db schemas env left right,
    bound_query_body_possible_outcome_lift
      db schemas env left right ->
    bound_query_possible_outcome_equiv db schemas env left right.
Proof.
intros db schemas env [left_bindings left_body]
  [right_bindings right_body].
unfold bound_query_body_possible_outcome_lift; cbn.
intros [Hbindings [Houtputs
  [Hleft_body [Hright_body
    [Hforward [Hbackward Hbody_errors]]]]]].
subst right_bindings.
split; [exact Houtputs|].
apply outcome_relation_equiv_intro.
- destruct Hleft_body as [outcome Houtcome].
  exists outcome.
  apply eval_bound_query_possible_outcome_decompose.
  now right.
- destruct Hright_body as [outcome Houtcome].
  exists outcome.
  apply eval_bound_query_possible_outcome_decompose.
  now right.
- intros rows Hrows.
  apply eval_bound_query_possible_outcome_decompose in Hrows.
  destruct Hrows as
    [[schedule [error [Houtcome _]]] | Hbody].
  + discriminate Houtcome.
  + destruct (Hforward rows Hbody) as
      [right_rows [Hright_rows Hequiv]].
    exists right_rows; split; [|exact Hequiv].
    apply eval_bound_query_possible_outcome_decompose.
    now right.
- intros rows Hrows.
  apply eval_bound_query_possible_outcome_decompose in Hrows.
  destruct Hrows as
    [[schedule [error [Houtcome _]]] | Hbody].
  + discriminate Houtcome.
  + destruct (Hbackward rows Hbody) as
      [left_rows [Hleft_rows Hequiv]].
    exists left_rows; split; [|exact Hequiv].
    apply eval_bound_query_possible_outcome_decompose.
    now right.
- intro error; split; intro Herror;
    apply eval_bound_query_possible_outcome_decompose in Herror;
    apply eval_bound_query_possible_outcome_decompose.
  + destruct Herror as
      [[schedule [prefix_error [Houtcome Hprefix]]] | Hbody].
    * inversion Houtcome; subst prefix_error.
      left; exists schedule, error; now split.
    * right; now apply (proj1 (Hbody_errors error)).
  + destruct Herror as
      [[schedule [prefix_error [Houtcome Hprefix]]] | Hbody].
    * inversion Houtcome; subst prefix_error.
      left; exists schedule, error; now split.
    * right; now apply (proj2 (Hbody_errors error)).
Qed.

(** The composition above materializes a referenced definition once and then
    shares its successful bag.  PostgreSQL may, however, avoid evaluating a
    CTE when no consumer demands it (for example, below an untaken CASE
    branch).  Until the core evaluator carries demand traces, error-preserving
    verification must therefore prove that eager materialization is harmless
    for every accepted query that actually contains local definitions: such a
    query has a successful outcome and no error outcome.

    This is a verification boundary, not an assertion that PostgreSQL eagerly
    evaluates WITH definitions.  It keeps ordinary, error-free CTE rewrites
    available while preventing a common eagerly produced error from becoming
    a false equivalence certificate. *)
Definition bound_query_runtime_safe
    (db : db_state) (schemas : list LocalQuerySchema)
    (env : Env.env TNull)
    (query : BoundQuery) : Prop :=
  (exists rows,
    eval_bound_query_possible_outcome db schemas env query
      (SqlSuccess rows)) /\
  forall error,
    ~ eval_bound_query_possible_outcome db schemas env query
        (SqlError error).

Lemma bound_query_possible_equiv_implies_possible_outcome_equiv :
  forall db schemas env left right,
    bound_query_possible_equiv db schemas env left right ->
    bound_query_possible_outcome_equiv db schemas env left right.
Proof.
intros db schemas env left right [Houtputs Hobservations].
split; [exact Houtputs|].
unfold successful_relation_equiv, outcome_relation_equiv in *.
now apply successful_relation_equiv_implies_outcome_relation_equiv.
Qed.

Fixpoint bound_query_program_possible_equiv
    (db : db_state) (schemas : list LocalQuerySchema)
    (env : Env.env TNull)
    (left right : BoundQueryProgram) : Prop :=
  match left, right with
  | nil, nil => True
  | left_query :: left_rest, right_query :: right_rest =>
      bound_query_possible_equiv db schemas env left_query right_query /\
      bound_query_program_possible_equiv db schemas env left_rest right_rest
  | _, _ => False
  end.

Fixpoint bound_query_program_possible_outcome_equiv
    (db : db_state) (schemas : list LocalQuerySchema)
    (env : Env.env TNull)
    (left right : BoundQueryProgram) : Prop :=
  match left, right with
  | nil, nil => True
  | left_query :: left_rest, right_query :: right_rest =>
      bound_query_possible_outcome_equiv db schemas env left_query right_query /\
      bound_query_program_possible_outcome_equiv db schemas env left_rest right_rest
  | _, _ => False
  end.

Fixpoint inlined_query_program (queries : list QueryExpr) : BoundQueryProgram :=
  match queries with
  | nil => nil
  | query :: rest =>
      MakeBoundQuery nil query :: inlined_query_program rest
  end.

(** Pointwise lifting of the query-level inline contract to generated
    multi-statement programs.  Statements remain independently observed
    against the same database, schemas, and outer environment. *)
Fixpoint bound_query_program_inline_possible_outcome_contract
    (db : db_state) (schemas : list LocalQuerySchema)
    (env : Env.env TNull)
    (bound : BoundQueryProgram) (inlined : list QueryExpr) : Prop :=
  match bound, inlined with
  | nil, nil => True
  | bound_query :: bound_rest, inlined_query :: inlined_rest =>
      bound_query_inline_possible_outcome_contract
        db schemas env bound_query inlined_query /\
      bound_query_program_inline_possible_outcome_contract
        db schemas env bound_rest inlined_rest
  | _, _ => False
  end.

Theorem bound_query_program_inline_possible_outcome_contract_sound :
  forall db schemas env bound inlined,
    bound_query_program_inline_possible_outcome_contract
      db schemas env bound inlined ->
    bound_query_program_possible_outcome_equiv
      db schemas env bound (inlined_query_program inlined).
Proof.
intros db schemas env bound; induction bound as [|bound_query bound_rest IH];
  intros [|inlined_query inlined_rest] Hcontract;
  try contradiction; cbn in *; [exact I|].
destruct Hcontract as [Hquery Hrest]; split.
- now apply bound_query_inline_possible_outcome_contract_sound.
- now apply IH.
Qed.

(** Pairwise program composition of the reachable-body contract.  This list
    relation does not add statement-order effects: [BoundQueryProgram] is the
    existing collection of independently observed statements, each evaluated
    against the same explicit [db], [schemas], and [env]. *)
Fixpoint bound_query_program_body_possible_outcome_lift
    (db : db_state) (schemas : list LocalQuerySchema)
    (env : Env.env TNull)
    (left right : BoundQueryProgram) : Prop :=
  match left, right with
  | nil, nil => True
  | left_query :: left_rest, right_query :: right_rest =>
      bound_query_body_possible_outcome_lift
        db schemas env left_query right_query /\
      bound_query_program_body_possible_outcome_lift
        db schemas env left_rest right_rest
  | _, _ => False
  end.

Theorem bound_query_program_body_possible_outcome_lift_sound :
  forall db schemas env left right,
    bound_query_program_body_possible_outcome_lift
      db schemas env left right ->
    bound_query_program_possible_outcome_equiv
      db schemas env left right.
Proof.
intros db schemas env left; induction left as [|left_query left_rest IH];
  intros [|right_query right_rest] Hlift; try contradiction; cbn in *.
- exact I.
- destruct Hlift as [Hquery Hrest]; split.
  + now apply bound_query_body_possible_outcome_lift_sound.
  + now apply IH.
Qed.

Definition bound_query_materialization_safe
    (db : db_state) (schemas : list LocalQuerySchema)
    (env : Env.env TNull)
    (query : BoundQuery) : Prop :=
  match bound_query_bindings query with
  | nil => True
  | _ :: _ => bound_query_runtime_safe db schemas env query
  end.

Fixpoint bound_query_program_materialization_safe
    (db : db_state) (schemas : list LocalQuerySchema)
    (env : Env.env TNull)
    (program : BoundQueryProgram) : Prop :=
  match program with
  | nil => True
  | query :: rest =>
      bound_query_materialization_safe db schemas env query /\
      bound_query_program_materialization_safe db schemas env rest
  end.

Lemma inlined_query_program_materialization_safe :
  forall db schemas env queries,
    bound_query_program_materialization_safe db schemas env
      (inlined_query_program queries).
Proof.
intros db schemas env queries; induction queries as [|query rest IH];
  cbn [inlined_query_program bound_query_program_materialization_safe
    bound_query_materialization_safe bound_query_bindings]; auto.
Qed.

(** Only statements with local bindings cross the eager-materialization
    boundary.  An unbound statement is exactly the canonical query evaluator,
    so its ordinary successful and error outcomes require no extra safety
    premise.  Bound statements remain restricted to the materialization-safe
    fragment because PostgreSQL may skip an undemanded definition. *)
Definition bound_query_program_demand_safe_outcome_equiv
    (db : db_state) (schemas : list LocalQuerySchema)
    (env : Env.env TNull)
    (left right : BoundQueryProgram) : Prop :=
  bound_query_program_materialization_safe db schemas env left /\
  bound_query_program_materialization_safe db schemas env right /\
  bound_query_program_possible_outcome_equiv db schemas env left right.

(** Program-level end point for CTE elimination.  The inlined endpoint has no
    eager local definitions and is therefore materialization-safe by
    construction.  Safety of the original bound program remains explicit:
    the inline contract alone must not erase an error from an unused CTE. *)
Theorem bound_query_program_inline_possible_outcome_contract_demand_safe :
  forall db schemas env bound inlined,
    bound_query_program_inline_possible_outcome_contract
      db schemas env bound inlined ->
    bound_query_program_materialization_safe db schemas env bound ->
    bound_query_program_demand_safe_outcome_equiv db schemas env
      bound (inlined_query_program inlined).
Proof.
intros db schemas env bound inlined Hcontract Hsafe.
split; [exact Hsafe|].
split.
- apply inlined_query_program_materialization_safe.
- now apply bound_query_program_inline_possible_outcome_contract_sound.
Qed.

(** A possible-outcome body lift is not by itself evidence that PostgreSQL
    must evaluate an undemanded local definition.  Program clients therefore
    retain the materialization-safety premises for both endpoints explicitly. *)
Theorem bound_query_program_body_possible_outcome_lift_demand_safe :
  forall db schemas env left right,
    bound_query_program_body_possible_outcome_lift
      db schemas env left right ->
    bound_query_program_materialization_safe db schemas env left ->
    bound_query_program_materialization_safe db schemas env right ->
    bound_query_program_demand_safe_outcome_equiv
      db schemas env left right.
Proof.
intros db schemas env left right Hlift Hleft_safe Hright_safe.
split; [exact Hleft_safe|].
split; [exact Hright_safe|].
now apply bound_query_program_body_possible_outcome_lift_sound.
Qed.

Lemma bound_query_possible_equiv_runtime_safe :
  forall db schemas env left right,
    bound_query_possible_equiv db schemas env left right ->
    bound_query_runtime_safe db schemas env left /\
    bound_query_runtime_safe db schemas env right.
Proof.
intros db schemas env left right Hequiv.
destruct Hequiv as [_ Hrelation].
unfold successful_relation_equiv in Hrelation.
destruct Hrelation as
  [[left_rows Hleft_success]
    [Hleft_errors [Hright_errors [Hforward _]]]].
split.
- split; [now exists left_rows | exact Hleft_errors].
- destruct (Hforward left_rows Hleft_success) as
    [right_rows [Hright_success _]].
  split; [now exists right_rows | exact Hright_errors].
Qed.

Lemma bound_query_program_possible_equiv_materialization_safe :
  forall db schemas env left right,
    bound_query_program_possible_equiv db schemas env left right ->
    bound_query_program_materialization_safe db schemas env left /\
    bound_query_program_materialization_safe db schemas env right.
Proof.
intros db schemas env left; induction left as [|left_query left_rest IH];
  intros [|right_query right_rest] Hequiv; try contradiction; cbn in *.
- auto.
- destruct Hequiv as [Hquery Hrest].
  destruct (bound_query_possible_equiv_runtime_safe
    db schemas env left_query right_query Hquery) as
    [Hleft_query Hright_query].
  destruct (IH right_rest Hrest) as [Hleft_rest Hright_rest].
  split; split.
  + unfold bound_query_materialization_safe.
    destruct (bound_query_bindings left_query); [exact I | exact Hleft_query].
  + exact Hleft_rest.
  + unfold bound_query_materialization_safe.
    destruct (bound_query_bindings right_query); [exact I | exact Hright_query].
  + exact Hright_rest.
Qed.

Lemma bound_query_program_possible_equiv_implies_possible_outcome_equiv :
  forall db schemas env left right,
    bound_query_program_possible_equiv db schemas env left right ->
    bound_query_program_possible_outcome_equiv db schemas env left right.
Proof.
intros db schemas env left; induction left as [|left_query left_rest IH];
  intros [|right_query right_rest] Hequiv; try contradiction; cbn in *.
- exact I.
- destruct Hequiv as [Hquery Hrest]; split.
  + now apply bound_query_possible_equiv_implies_possible_outcome_equiv.
  + now apply IH.
Qed.

Lemma bound_query_program_possible_equiv_implies_demand_safe_outcome_equiv :
  forall db schemas env left right,
    bound_query_program_possible_equiv db schemas env left right ->
    bound_query_program_demand_safe_outcome_equiv
      db schemas env left right.
Proof.
intros db schemas env left right Hequiv.
destruct (bound_query_program_possible_equiv_materialization_safe
  db schemas env left right Hequiv) as
  [Hleft_safe Hright_safe].
split; [exact Hleft_safe|].
split; [exact Hright_safe|].
now apply bound_query_program_possible_equiv_implies_possible_outcome_equiv.
Qed.

Definition local_query_binding_admissible
    (db : db_state) (schemas : list LocalQuerySchema)
    (binding : LocalQueryBinding) : Prop :=
  In (local_query_binding_schema binding) schemas /\
  TNullQueryExprAdmissible (@_basesort TNull db)
    (local_binding_query binding) /\
  query_expr_contains_analysis_error (local_binding_query binding) = false /\
  query_expr_outputs (local_binding_query binding) =
    local_binding_outputs binding.

Definition bound_query_root_analysis_error_well_placed
    (query : BoundQuery) : Prop :=
  match bound_query_body query with
  | QExpr_Error _ _ => bound_query_bindings query = nil
  | _ => True
  end.

Definition bound_query_admissible
    (db : db_state) (schemas : list LocalQuerySchema)
    (query : BoundQuery) : Prop :=
  let declared := declare_local_query_schemas db schemas in
  NoDup (local_query_schema_relations schemas) /\
  local_query_schemas_fresh db schemas /\
  NoDup (local_query_binding_relations (bound_query_bindings query)) /\
  Forall (local_query_binding_admissible declared schemas)
    (bound_query_bindings query) /\
  bound_query_local_references_well_formed schemas query /\
  bound_query_root_analysis_error_well_placed query /\
  boolean_sites_well_formed (bound_query_boolean_sites query) /\
  TNullQueryExprAdmissible (@_basesort TNull declared)
    (bound_query_body query).

Definition bound_query_program_admissible
    (db : db_state) (schemas : list LocalQuerySchema)
    (program : BoundQueryProgram) : Prop :=
  NoDup (bound_query_program_binding_relations program) /\
  Forall (bound_query_admissible db schemas) program.

Lemma declare_local_query_schemas_basesort_extensional :
  forall schemas first second,
    (forall relation,
      @_basesort TNull first relation =S=
      @_basesort TNull second relation) ->
    forall relation,
      @_basesort TNull (declare_local_query_schemas first schemas) relation =S=
      @_basesort TNull (declare_local_query_schemas second schemas) relation.
Proof.
induction schemas as [|[[schema_name] schema_outputs] rest IH];
  intros first second Hequal relation; cbn.
- apply Hequal.
- apply IH; intros [candidate_name].
  unfold declare_local_query_schema, create_table, create_table_; cbn.
  destruct (string_compare candidate_name schema_name);
    [exact (Fset.equal_refl FAN (Fset.mk_set (A TNull) schema_outputs))
    | apply Hequal
    | apply Hequal].
Qed.

Lemma bound_query_admissible_database_shape_extensional :
  forall schemas first second query,
    @_relnames TNull first = @_relnames TNull second ->
    (forall relation,
      @_basesort TNull first relation =S=
      @_basesort TNull second relation) ->
    bound_query_admissible first schemas query ->
    bound_query_admissible second schemas query.
Proof.
intros schemas first second [bindings body] Hrelnames Hequal; cbn.
set (first_declared := declare_local_query_schemas first schemas).
set (second_declared := declare_local_query_schemas second schemas).
assert (Hdeclared : forall relation,
  @_basesort TNull first_declared relation =S=
  @_basesort TNull second_declared relation).
{
  intro relation; unfold first_declared, second_declared.
  now apply declare_local_query_schemas_basesort_extensional.
}
assert (Htransport : forall query,
  TNullQueryExprAdmissible (@_basesort TNull first_declared) query ->
  TNullQueryExprAdmissible (@_basesort TNull second_declared) query).
{
  intros query [Hadmissible [Herror Hsites]].
  split.
  - eapply query_expr_admissible_basesort_extensional;
      [exact Hdeclared | exact Hadmissible].
  - now split.
}
intros [Hschemas [Hfresh [Hnames [Hbindings
  [Hreferences [Hroot_error [Hsites Hbody]]]]]]].
split; [exact Hschemas|].
split.
- unfold local_query_schemas_fresh in *.
  now rewrite <- Hrelnames.
- split; [exact Hnames|].
  split.
  + rewrite Forall_forall in Hbindings |- *.
  intros binding Hbinding.
  specialize (Hbindings binding Hbinding).
  unfold local_query_binding_admissible in *.
  destruct Hbindings as [Hschema [Hquery [Herror Houtputs]]].
  split; [exact Hschema|].
  split; [now apply Htransport|].
  split; assumption.
  + split; [exact Hreferences|].
    split; [exact Hroot_error|].
    split; [exact Hsites|now apply Htransport].
Qed.

Lemma bound_query_program_admissible_database_shape_extensional :
  forall schemas first second program,
    @_relnames TNull first = @_relnames TNull second ->
    (forall relation,
      @_basesort TNull first relation =S=
      @_basesort TNull second relation) ->
    bound_query_program_admissible first schemas program ->
    bound_query_program_admissible second schemas program.
Proof.
intros schemas first second program Hrelnames Hequal.
unfold bound_query_program_admissible.
intros [Hnames Hadmissible]; split; [exact Hnames|].
rewrite Forall_forall in Hadmissible |- *.
intros query Hquery.
eapply bound_query_admissible_database_shape_extensional; eauto.
Qed.

Lemma bound_query_program_admissible_database_schema_transport :
  forall expected constraints actual schemas program,
    database_conforms_schema expected constraints actual ->
    bound_query_program_admissible expected schemas program ->
    bound_query_program_admissible actual schemas program.
Proof.
intros expected constraints actual schemas program Hschema Hadmissible.
eapply bound_query_program_admissible_database_shape_extensional.
- symmetry; exact (database_conforms_schema_relnames
    expected constraints actual Hschema).
- intro relation.
  pose proof
    (database_conforms_schema_basesort
      expected constraints actual Hschema relation) as Hactual.
  rewrite Fset.equal_spec in Hactual |- *.
  intro attribute; symmetry; apply Hactual.
- exact Hadmissible.
Qed.

(** Compatibility corollary for clients without even predeclared local
    schemas.  The generalized theorem above is the authoritative interface. *)
Lemma eval_bound_query_without_bindings :
  forall db env query outcome,
    eval_bound_query_possible_outcome db nil env
      (MakeBoundQuery nil query) outcome <->
    eval_query_expr_outcome_in_env db env query outcome.
Proof.
intros db env query outcome.
exact (eval_bound_query_without_bindings_with_schemas
  db nil env query outcome).
Qed.
