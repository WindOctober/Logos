From SQLFS Require Import FTuples OrderedSet FiniteSet FiniteBag FiniteCollection
  SqlSyntax GenericInstance Values Bool3 Env SqlOutcome SqlErrorSemantics
  SchemaConstraints SqlBagAbstraction SqlQuerySemantics SqlQuerySyntax
  SqlQueryWellFormed.
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

(** Without local bindings, the composition is exactly the canonical query
    outcome relation. *)
Lemma eval_bound_query_without_bindings :
  forall db env query outcome,
    eval_bound_query_possible_outcome db nil env
      (MakeBoundQuery nil query) outcome <->
    eval_query_expr_outcome_in_env db env query outcome.
Proof.
intros db env query outcome; reflexivity.
Qed.
