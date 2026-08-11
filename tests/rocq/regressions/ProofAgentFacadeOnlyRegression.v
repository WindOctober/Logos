(******************************************************************************)
(** Canonical typed interfaces exported by the proof-agent facade.            **)
(******************************************************************************)

From Logos.FormalSQL Require Import ProofAgentFacade.

Check TNullScalarValueExpr.
Check TNullScalarBooleanExpr.
Check TNullQuerySelectItem.
Check TNullQuerySelectList.
Check TNullQueryGroupingSet.
Check TNullQueryExprAdmissible.
Check TNullQueryExprAdmissibleWithOutputs.

Check QExpr_Project.
Check QExpr_Filter.
Check QExpr_Group.
Check QExpr_Join.
Check QExpr_GroupingSets.

Check query_expr_filter_predicate_possible_outcome_equiv.
Check query_expr_project_select_possible_outcome_equiv.
Check query_join_rows_outcomes.
Check query_expr_join_relation_transport.
Check query_expr_join_possible_outcome_related_same_schedule.
Check query_expr_join_possible_outcome_related.
Check query_expr_group_possible_outcome_transport.
Check query_expr_group_possible_outcome_equiv_of_exact_group_bag_outcomes.
Check query_expr_group_possible_outcome_equiv_of_exact_local_outcomes.
Check query_expr_group_clauses_possible_outcome_equiv.

(** Ordered observations and their proved bag abstraction are both public. *)
Check query_expr_possible_outcome_equiv.
Check query_possible_success_bags.

(** Success-only and exact outcome modes remain separate interfaces. *)
Check query_expr_possible_equiv.
Check query_expr_possible_outcome_equiv.
