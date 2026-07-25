From SQLFS Require Import Env GenericInstance Interp Projection.
From Logos.FormalSQL Require Import TNullSyntax ProofAgentFacade.
From Stdlib Require Import List.

Import ListNotations.

(** The projection bridge must accept arbitrary evaluator environments, not
    only two rows inserted beneath one shared outer environment. *)
Lemma projection_environment_extensionality_regression :
  forall (left_env right_env : Env.env TNull)
      (left_first left_second right_first right_second : AggTerm)
      (first_attribute second_attribute : TNullAttribute),
    Interp.interp_aggterm TNull left_env left_first =
      Interp.interp_aggterm TNull right_env right_first ->
    Interp.interp_aggterm TNull left_env left_second =
      Interp.interp_aggterm TNull right_env right_second ->
    TNullRowEq
      (Projection.projection TNull left_env
        (@Projection.Select_List TNull
          (SelectList [
            SelectAs left_first first_attribute;
            SelectAs left_second second_attribute])))
      (Projection.projection TNull right_env
        (@Projection.Select_List TNull
          (SelectList [
            SelectAs right_first first_attribute;
            SelectAs right_second second_attribute]))).
Proof.
intros left_env right_env left_first left_second right_first right_second
  first_attribute second_attribute Hfirst Hsecond.
apply tnull_projection_envs_eq_of_select_items.
constructor.
- cbn [SelectAs]. split; [reflexivity | exact Hfirst].
- constructor.
  + cbn [SelectAs]. split; [reflexivity | exact Hsecond].
  + constructor.
Qed.

Print Assumptions tnull_projection_envs_eq_of_select_items.
Print Assumptions projection_environment_extensionality_regression.
