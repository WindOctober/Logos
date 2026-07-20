(************************************************************************************)
(** Structured, auditable preconditions for conditional SQL equivalence.          *)
(************************************************************************************)

From SQLFS Require Import
  SqlSyntax GenericInstance Values FTuples FiniteBag FiniteCollection
  FiniteSet ValueInteger ValueString.
From Logos.FormalSQL Require Import SchemaConstraints.
From Stdlib Require Import List String ZArith.

Import ListNotations.
Import Tuple.
Open Scope Z_scope.

(** The language deliberately contains no arbitrary [Prop], query evaluator,
    negation, or false constructor.  An agent can select useful input-domain
    restrictions, but cannot restate the equivalence goal as its premise. *)
Inductive value_precondition : Type :=
  | ValueNotNull
  | ValueZBetween (lower upper : Z)
  | ValueInt32Between (lower upper : Z)
  | ValueInt64Between (lower upper : Z)
  | ValueZNonZero
  | ValueInt32NonZero
  | ValueInt64NonZero
  | ValueStringLengthBetween (lower upper : nat).

Inductive verification_condition : Type :=
  | ConditionTrue
  | ConditionAnd
      (left right : verification_condition)
  | ConditionColumn
      (relation : relname)
      (attribute : attribute TNull)
      (condition : value_precondition)
  | ConditionRelationCardinality
      (relation : relname)
      (lower : nat)
      (upper : option nat).

Inductive precondition_source : Type :=
  | PreconditionDerived
  | PreconditionExternal.

Definition value_precondition_compatible
    (attribute : attribute TNull)
    (condition : value_precondition) : Prop :=
  match condition with
  | ValueNotNull => True
  | ValueZBetween _ _ | ValueZNonZero =>
      match attribute with Attr_Z _ => True | _ => False end
  | ValueInt32Between _ _ | ValueInt32NonZero =>
      match attribute with Attr_int32 _ => True | _ => False end
  | ValueInt64Between _ _ | ValueInt64NonZero =>
      match attribute with Attr_int64 _ => True | _ => False end
  | ValueStringLengthBetween _ _ =>
      match attribute with Attr_string _ _ => True | _ => False end
  end.

Definition value_precondition_holds
    (condition : value_precondition)
    (value : value TNull) : Prop :=
  match condition with
  | ValueNotNull => NullValues.is_null_value value = false
  | ValueZBetween lower upper =>
      match value with
      | NullValues.Value_Z (Some integer) => lower <= integer <= upper
      | _ => False
      end
  | ValueInt32Between lower upper =>
      match value with
      | NullValues.Value_int32 (Some integer) =>
          lower <= int32_value integer <= upper
      | _ => False
      end
  | ValueInt64Between lower upper =>
      match value with
      | NullValues.Value_int64 (Some integer) =>
          lower <= int64_value integer <= upper
      | _ => False
      end
  | ValueZNonZero =>
      match value with
      | NullValues.Value_Z (Some integer) => integer <> 0
      | _ => False
      end
  | ValueInt32NonZero =>
      match value with
      | NullValues.Value_int32 (Some integer) => int32_value integer <> 0
      | _ => False
      end
  | ValueInt64NonZero =>
      match value with
      | NullValues.Value_int64 (Some integer) => int64_value integer <> 0
      | _ => False
      end
  | ValueStringLengthBetween lower upper =>
      match value with
      | NullValues.Value_string (_, Some text) =>
          exists length,
            utf8_character_length text = Some length /\
            (lower <= length <= upper)%nat
      | _ => False
      end
  end.

Definition relation_declared
    (expected : db_state) (relation : relname) : Prop :=
  In relation (@_relnames TNull expected).

Definition column_condition_well_formed
    (expected : db_state)
    (relation : relname)
    (attribute : attribute TNull)
    (condition : value_precondition) : Prop :=
  relation_declared expected relation /\
  attribute inS (@_basesort TNull expected relation) /\
  value_precondition_compatible attribute condition.

Fixpoint verification_condition_well_formed
    (expected : db_state)
    (condition : verification_condition) : Prop :=
  match condition with
  | ConditionTrue => True
  | ConditionAnd first second =>
      verification_condition_well_formed expected first /\
      verification_condition_well_formed expected second
  | ConditionColumn relation attribute value_condition =>
      column_condition_well_formed
        expected relation attribute value_condition
  | ConditionRelationCardinality relation lower upper =>
      relation_declared expected relation /\
      match upper with
      | Some maximum => (lower <= maximum)%nat
      | None => True
      end
  end.

Definition column_condition_holds
    (db : db_state)
    (relation : relname)
    (attribute : attribute TNull)
    (condition : value_precondition) : Prop :=
  forall row,
    In row (instance_rows db relation) ->
    value_precondition_holds condition (dot TNull row attribute).

Definition relation_cardinality_holds
    (db : db_state)
    (relation : relname)
    (lower : nat)
    (upper : option nat) : Prop :=
  let cardinality := List.length (instance_rows db relation) in
  (lower <= cardinality)%nat /\
  match upper with
  | Some maximum => (cardinality <= maximum)%nat
  | None => True
  end.

Fixpoint verification_condition_holds
    (db : db_state)
    (condition : verification_condition) : Prop :=
  match condition with
  | ConditionTrue => True
  | ConditionAnd first second =>
      verification_condition_holds db first /\
      verification_condition_holds db second
  | ConditionColumn relation attribute value_condition =>
      column_condition_holds db relation attribute value_condition
  | ConditionRelationCardinality relation lower upper =>
      relation_cardinality_holds db relation lower upper
  end.

(** A derived condition adds no assumption: it must follow from the original
    generated input contract.  An external condition must instead be shown
    jointly satisfiable with that contract, preventing vacuous certificates. *)
Definition precondition_source_obligation
    (expected : db_state)
    (constraints : list table_constraint)
    (source : precondition_source)
    (condition : verification_condition) : Prop :=
  verification_condition_well_formed expected condition /\
  match source with
  | PreconditionDerived =>
      forall db,
        database_conforms_schema expected constraints db ->
        verification_condition_holds db condition
  | PreconditionExternal =>
      exists db,
        database_conforms_schema expected constraints db /\
        verification_condition_holds db condition
  end.

Lemma condition_true_well_formed :
  forall expected,
    verification_condition_well_formed expected ConditionTrue.
Proof.
intros; exact I.
Qed.

Lemma condition_true_holds :
  forall db,
    verification_condition_holds db ConditionTrue.
Proof.
intros; exact I.
Qed.

Lemma condition_true_is_derived :
  forall expected constraints,
    precondition_source_obligation
      expected constraints PreconditionDerived ConditionTrue.
Proof.
intros; split; [apply condition_true_well_formed |].
intros; apply condition_true_holds.
Qed.
