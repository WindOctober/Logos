(******************************************************************************)
(** WHERE-acceptance bridge from SQL IN to a partial-functional semijoin.    **)
(******************************************************************************)

From Stdlib Require Import List.
From SQLFS Require Import
  ATerms Bool3 Env Formula FTuples GenericInstance Projection Values.
From Logos.FormalSQL Require Import ProofAgentFacade SubqueryFacts TNullSyntax.

Import ListNotations.

(** An UNKNOWN candidate contaminates the complete SQL [IN] truth value when
    no candidate is TRUE.  The bridge below must not erase that fact. *)
Example unknown_polluted_exists_remains_unknown :
  interp_quant Bool3 Exists_F (fun truth : bool3 => truth)
    [unknown3; false3] = unknown3.
Proof. reflexivity. Qed.

(** A WHERE consumer nevertheless rejects that UNKNOWN result. *)
Example unknown_polluted_exists_is_not_accepted :
  Bool.is_true Bool3
    (interp_quant Bool3 Exists_F (fun truth : bool3 => truth)
      [unknown3; false3]) = false.
Proof. reflexivity. Qed.

Section InSemijoinCompositionRegression.

Variable env_of : TNullRow -> TNullEnvironment.
Variable select_items : list SelectItemT.
Variables
  (join : TNullRow -> TNullRow -> TNullRow)
  (accept : TNullRow -> TNullRow -> bool)
  (project emit : TNullRow -> TNullRow)
  (left right : list TNullRow).

Hypothesis row_acceptance_exact :
  forall (left_row right_row : TNullRow),
    Bool.is_true Bool3
      (@in_row_truth TNull unknown3 NullValues.is_null_value
        (env_of left_row) select_items right_row) =
    accept left_row right_row.

Hypothesis accepted_projection :
  forall left_row right_row,
    In left_row left ->
    In right_row right ->
    accept left_row right_row = true ->
    TNullRowEq (project (join left_row right_row)) (emit left_row).

Hypothesis right_match_functional :
  forall left_row,
    In left_row left ->
    (length (filter (accept left_row) right) <= 1)%nat.

(** The new [IN] bridge changes only the filter decision.  Its result feeds
    the existing partial-functional theta-join theorem without packaging a
    query-specific rewrite or weakening SQL's underlying Bool3 semantics. *)
Theorem in_acceptance_composes_with_functional_semijoin :
  TNullRowPermut
    (map project (TNullThetaJoinRows join accept left right))
    (map emit
      (filter
        (fun left_row =>
          Bool.is_true Bool3
            (@in_rows_truth TNull unknown3 NullValues.is_null_value
              (env_of left_row) select_items right))
        left)).
Proof.
  assert (Hfilter :
    filter
      (fun left_row =>
        Bool.is_true Bool3
          (@in_rows_truth TNull unknown3 NullValues.is_null_value
            (env_of left_row) select_items right))
      left =
    filter (fun left_row => existsb (accept left_row) right) left).
  {
    apply filter_ext_in.
    intros left_row _.
    apply (@in_rows_acceptance_existsb TNull
      unknown3 NullValues.is_null_value
      (env_of left_row) select_items right (accept left_row)).
    intro right_row; apply row_acceptance_exact.
  }
  rewrite Hfilter.
  eapply tnull_map_theta_join_functional_permut_filter_exists;
    eassumption.
Qed.

End InSemijoinCompositionRegression.

Print Assumptions in_rows_acceptance_existsb.
Print Assumptions in_acceptance_composes_with_functional_semijoin.
