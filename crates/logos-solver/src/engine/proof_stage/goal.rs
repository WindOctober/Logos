//! Trusted goal generation. Bound-query safety obligations remain explicit.

use super::FORMAL_SQL_GOAL_HEADER;
use crate::core::VerificationMode;

fn condition_contract(verification_mode: VerificationMode) -> (&'static str, &'static str) {
    let condition_parameter = match verification_mode {
        VerificationMode::Conditional => "\n    (condition : verification_condition)",
        VerificationMode::SafeUnconditional | VerificationMode::OutcomeUnconditional => "",
    };
    let condition_premise = match verification_mode {
        VerificationMode::Conditional => "      verification_condition_holds db condition ->\n",
        VerificationMode::SafeUnconditional | VerificationMode::OutcomeUnconditional => "",
    };
    (condition_parameter, condition_premise)
}

fn trusted_goal_certificate(verification_mode: VerificationMode) -> &'static str {
    match verification_mode {
        VerificationMode::Conditional => {
            "
Theorem generated_precondition_certificate :
  precondition_source_obligation
    Schema.generated_schema
    Schema.generated_schema_constraints
    Problem.generated_precondition_source
    Problem.generated_precondition.
Proof.
  exact Problem.generated_precondition_valid.
Qed.

Theorem generated_equivalence_certificate :
  required_equivalence_statement Problem.generated_precondition.
Proof.
  exact Problem.generated_queries_equivalent.
Qed.
"
        }
        VerificationMode::SafeUnconditional | VerificationMode::OutcomeUnconditional => {
            "
Theorem generated_verification_certificate :
  required_verification_statement Problem.generated_verification_claim.
Proof.
  exact Problem.generated_queries_verified.
Qed.
"
        }
    }
}

pub(super) fn formal_sql_goal_module(verification_mode: VerificationMode) -> String {
    let program_equivalence = match verification_mode {
        VerificationMode::SafeUnconditional => "query_program_possible_equiv",
        VerificationMode::OutcomeUnconditional | VerificationMode::Conditional => {
            "query_program_possible_outcome_equiv"
        }
    };
    let (condition_parameter, condition_premise) = condition_contract(verification_mode);
    let unconditional_claim_contract = match verification_mode {
        VerificationMode::SafeUnconditional | VerificationMode::OutcomeUnconditional => {
            "
Definition required_countermodel_statement : Prop :=
  Witness.generated_witness_available = true /\\
  Schema.generated_schema_conforms Witness.generated_witness_db /\\
      required_query_program_admissible
        Witness.generated_witness_db
        Queries.source_query_program /\\
      required_query_program_admissible
        Witness.generated_witness_db
        Queries.target_query_program /\\
      ~ required_query_program_outcome_equiv Witness.generated_witness_db
          Queries.source_query_program
          Queries.target_query_program.

Definition required_verification_statement
    (claim : verification_claim_kind) : Prop :=
  verification_claim_goal
    claim required_equivalence_statement required_countermodel_statement.
"
        }
        VerificationMode::Conditional => "",
    };
    let trusted_certificate = trusted_goal_certificate(verification_mode);
    format!(
        "{FORMAL_SQL_GOAL_HEADER}
Definition required_query_program_equiv
    (db : db_state)
    (left right : list QueryExpr) : Prop :=
  @{program_equivalence} TNull relname
    (@_basesort TNull db)
    (@_instance TNull db)
    unknown3
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error
    required_value_is_null
    nil
    left
    right.

Definition required_query_program_outcome_equiv
    (db : db_state)
    (left right : list QueryExpr) : Prop :=
  @query_program_possible_outcome_equiv TNull relname
    (@_basesort TNull db)
    (@_instance TNull db)
    unknown3
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error
    required_value_is_null
    nil
    left
    right.

Definition required_query_program_admissible
    (db : db_state) (program : list QueryExpr) : Prop :=
  Forall
    (TNullQueryExprAdmissible (@_basesort TNull db))
    program.

Definition required_equivalence_statement{condition_parameter} : Prop :=
    Queries.source_program_output_signatures =
      map query_expr_outputs
        Queries.source_query_program /\\
    Queries.target_program_output_signatures =
      map query_expr_outputs
        Queries.target_query_program /\\
    Queries.source_program_output_signatures =
      Queries.target_program_output_signatures /\\
    (forall db : db_state,
      Schema.generated_schema_conforms db ->
{condition_premise}      required_query_program_admissible
        db Queries.source_query_program /\\
      required_query_program_admissible
        db Queries.target_query_program /\\
      required_query_program_equiv db
        Queries.source_query_program
        Queries.target_query_program).

{unconditional_claim_contract}

From LogosGenerated Require Problem.
{trusted_certificate}"
    )
}

pub(super) fn formal_sql_bound_goal_module(verification_mode: VerificationMode) -> String {
    let program_equivalence = match verification_mode {
        VerificationMode::SafeUnconditional => "bound_query_program_possible_equiv",
        VerificationMode::OutcomeUnconditional | VerificationMode::Conditional => {
            "bound_query_program_demand_safe_outcome_equiv"
        }
    };
    let (condition_parameter, condition_premise) = condition_contract(verification_mode);
    let unconditional_claim_contract = match verification_mode {
        VerificationMode::SafeUnconditional | VerificationMode::OutcomeUnconditional => {
            "
Definition required_countermodel_statement : Prop :=
  Witness.generated_witness_available = true /\\
  Schema.generated_schema_conforms Witness.generated_witness_db /\\
      required_query_program_admissible
        Witness.generated_witness_db
        Queries.source_bound_query_program /\\
      required_query_program_admissible
        Witness.generated_witness_db
        Queries.target_bound_query_program /\\
      required_query_program_materialization_safe
        Witness.generated_witness_db
        Queries.source_bound_query_program /\\
      required_query_program_materialization_safe
        Witness.generated_witness_db
        Queries.target_bound_query_program /\\
      ~ required_query_program_outcome_equiv Witness.generated_witness_db
          Queries.source_bound_query_program
          Queries.target_bound_query_program.

Definition required_verification_statement
    (claim : verification_claim_kind) : Prop :=
  verification_claim_goal
    claim required_equivalence_statement required_countermodel_statement.
"
        }
        VerificationMode::Conditional => "",
    };
    let trusted_certificate = trusted_goal_certificate(verification_mode);
    format!(
        "{FORMAL_SQL_GOAL_HEADER}
From Logos Require Import FormalSQL.QueryBindingSemantics.

Definition required_query_program_equiv
    (db : db_state)
    (left right : BoundQueryProgram) : Prop :=
  {program_equivalence}
    db Queries.generated_local_query_schemas nil left right.

Definition required_query_program_outcome_equiv
    (db : db_state)
    (left right : BoundQueryProgram) : Prop :=
  bound_query_program_possible_outcome_equiv
    db Queries.generated_local_query_schemas nil left right.

Definition required_query_program_materialization_safe
    (db : db_state) (program : BoundQueryProgram) : Prop :=
  bound_query_program_materialization_safe
    db Queries.generated_local_query_schemas nil program.

Definition required_query_program_admissible
    (db : db_state) (program : BoundQueryProgram) : Prop :=
  bound_query_program_admissible
    db Queries.generated_local_query_schemas program.

Definition required_equivalence_statement{condition_parameter} : Prop :=
    Queries.source_program_output_signatures =
      map bound_query_outputs
        Queries.source_bound_query_program /\\
    Queries.target_program_output_signatures =
      map bound_query_outputs
        Queries.target_bound_query_program /\\
    Queries.source_program_output_signatures =
      Queries.target_program_output_signatures /\\
    (forall db : db_state,
      Schema.generated_schema_conforms db ->
{condition_premise}      required_query_program_admissible
        db Queries.source_bound_query_program /\\
      required_query_program_admissible
        db Queries.target_bound_query_program /\\
      required_query_program_equiv db
        Queries.source_bound_query_program
        Queries.target_bound_query_program).

{unconditional_claim_contract}

From LogosGenerated Require Problem.
{trusted_certificate}"
    )
}
