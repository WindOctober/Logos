From SQLFS Require Import SqlSyntax GenericInstance SqlAlgebra Projection FiniteBag Bool3 FTuples OrderedSet Env Interp Partition ListFacts.
From Logos.FormalSQL Require Import TNullSyntax RewriteSpec.

Import Tuple.

(*
  Occurrence-count facts for Logos-local FormalSQL proofs.

  FormalSQL bag equality is already defined by per-tuple multiplicity.  This
  file exposes that fact through query-level names that are easier for generated
  proof scripts and proof agents to use.
*)

Definition query_occ (db : db_state) (q : Query) (t : tuple TNull) :=
  Febag.nb_occ _ t (eval_query_in_state db q).

Definition query_nonempty (db : db_state) (q : Query) : Prop :=
  exists t, t inBE eval_query_in_state db q.

Lemma query_equiv_iff_occ :
  forall db q1 q2,
    query_equiv db q1 q2 <->
    query_succeeds db q1 /\
    query_succeeds db q2 /\
    forall t, query_occ db q1 t = query_occ db q2 t.
Proof.
intros db q1 q2.
rewrite query_equiv_iff_success_and_bag_equality.
split.
- intros [Hsafe1 [Hsafe2 Hequal]].
  split; [exact Hsafe1 | split; [exact Hsafe2 |]].
  unfold query_occ.
  now rewrite Febag.nb_occ_equal in Hequal.
- intros [Hsafe1 [Hsafe2 Hocc]].
  split; [exact Hsafe1 | split; [exact Hsafe2 |]].
  rewrite Febag.nb_occ_equal.
  exact Hocc.
Qed.

Lemma pi_congr :
  forall db s q1 q2,
    query_equiv db q1 q2 ->
    query_succeeds db (Pi s q1) ->
    query_succeeds db (Pi s q2) ->
    query_equiv db (Pi s q1) (Pi s q2).
Proof.
intros db s q1 q2 Hq Hsafe1 Hsafe2.
apply query_equiv_intro; [exact Hsafe1 | exact Hsafe2 |].
apply query_equiv_implies_bag_equality in Hq.
unfold eval_query_in_state, eval_query_in_env, Pi in *.
rewrite (@eval_query_unfold TNull relname
          (@_basesort TNull db)
          (@_instance TNull db)
          unknown3
          contains_nulls
          nil
          (@Q_Pi TNull relname s q1)).
rewrite (@eval_query_unfold TNull relname
          (@_basesort TNull db)
          (@_instance TNull db)
          unknown3
          contains_nulls
          nil
          (@Q_Pi TNull relname s q2)).
rewrite 2 Febag.map_unfold.
rewrite Febag.nb_occ_equal; intro t.
rewrite 2 Febag.nb_occ_mk_bag.
apply (Oeset.nb_occ_map_eq_2_3 (OTuple TNull)).
- intros x1 x2 Hx.
  apply projection_eq.
  apply env_t_eq_2.
  exact Hx.
- intro x.
  rewrite <- 2 Febag.nb_occ_elements.
  rewrite Febag.nb_occ_equal in Hq.
  apply Hq.
Qed.

Lemma sigma_congr :
  forall db f q1 q2,
    query_equiv db q1 q2 ->
    query_succeeds db (Sigma f q1) ->
    query_succeeds db (Sigma f q2) ->
    query_equiv db (Sigma f q1) (Sigma f q2).
Proof.
intros db f q1 q2 Hq Hsafe1 Hsafe2.
apply query_equiv_intro; [exact Hsafe1 | exact Hsafe2 |].
apply query_equiv_implies_bag_equality in Hq.
unfold eval_query_in_state, Sigma, eval_query_in_env in *.
rewrite (@eval_query_unfold TNull relname
          (@_basesort TNull db)
          (@_instance TNull db)
          unknown3
          contains_nulls
          nil
          (@Q_Sigma TNull relname f q1)).
rewrite (@eval_query_unfold TNull relname
          (@_basesort TNull db)
          (@_instance TNull db)
          unknown3
          contains_nulls
          nil
          (@Q_Sigma TNull relname f q2)).
apply Febag.filter_eq.
- exact Hq.
- intros x1 x2 _ Hx.
  change (eval_formula_in_env db nil x1 f = eval_formula_in_env db nil x2 f).
  apply eval_formula_in_env_eq_tuple.
  exact Hx.
Qed.

(** Fixed-environment bag congruence is the compositional interface needed
    below [QExpr_Bag].  These laws do not introduce success assumptions or
    erase runtime errors; they only transport the pure bag result. *)
Lemma pi_eval_bag_congr :
  forall db env select_list left right,
    eval_query_in_env db env left =BE= eval_query_in_env db env right ->
    eval_query_in_env db env (Pi select_list left) =BE=
    eval_query_in_env db env (Pi select_list right).
Proof.
intros db env select_list left right Hbag.
unfold eval_query_in_env, Pi in *.
rewrite Febag.nb_occ_equal; intro output.
rewrite (@eval_query_unfold TNull relname
  (@_basesort TNull db) (@_instance TNull db) unknown3 contains_nulls env
  (@Q_Pi TNull relname select_list left)).
rewrite (@eval_query_unfold TNull relname
  (@_basesort TNull db) (@_instance TNull db) unknown3 contains_nulls env
  (@Q_Pi TNull relname select_list right)).
rewrite 2 Febag.map_unfold, 2 Febag.nb_occ_mk_bag.
apply (Oeset.nb_occ_map_eq_2_3 (OTuple TNull)).
- intros first second Hequal.
  apply projection_eq, env_t_eq_2; exact Hequal.
- intro row; rewrite <- !Febag.nb_occ_elements.
  revert row; now rewrite <- Febag.nb_occ_equal.
Qed.

Lemma sigma_eval_bag_congr :
  forall db env formula left right,
    eval_query_in_env db env left =BE= eval_query_in_env db env right ->
    eval_query_in_env db env (Sigma formula left) =BE=
    eval_query_in_env db env (Sigma formula right).
Proof.
intros db env formula left right Hbag.
unfold eval_query_in_env, Sigma in *.
rewrite (@eval_query_unfold TNull relname
  (@_basesort TNull db) (@_instance TNull db) unknown3 contains_nulls env
  (@Q_Sigma TNull relname formula left)).
rewrite (@eval_query_unfold TNull relname
  (@_basesort TNull db) (@_instance TNull db) unknown3 contains_nulls env
  (@Q_Sigma TNull relname formula right)).
apply Febag.filter_eq.
- exact Hbag.
- intros first second _ Hequal.
  apply f_equal, eval_formula_eq.
  + apply contains_nulls_eq.
  + apply env_t_eq_2; exact Hequal.
Qed.

Lemma gamma_eval_bag_congr :
  forall db env select_list group_terms having left right,
    eval_query_in_env db env left =BE= eval_query_in_env db env right ->
    eval_query_in_env db env
      (Gamma select_list group_terms having left) =BE=
    eval_query_in_env db env
      (Gamma select_list group_terms having right).
Proof.
intros db env select_list group_terms having left right Hbag.
unfold eval_query_in_env, Gamma in *.
rewrite Febag.nb_occ_equal; intro output.
rewrite (@eval_query_unfold TNull relname
  (@_basesort TNull db) (@_instance TNull db) unknown3 contains_nulls env
  (@Q_Gamma TNull relname select_list group_terms having left)).
rewrite (@eval_query_unfold TNull relname
  (@_basesort TNull db) (@_instance TNull db) unknown3 contains_nulls env
  (@Q_Gamma TNull relname select_list group_terms having right)).
rewrite 2 Febag.nb_occ_mk_bag.
apply (Oeset.nb_occ_map_eq_2_3 (OLTuple TNull)).
- intros first second Hequal.
  apply projection_eq, env_g_eq_2.
  rewrite Partition.compare_list_t; exact Hequal.
- intro group.
  rewrite 2 Oeset.nb_occ_filter.
  + apply BasicFacts.if_eq.
    * reflexivity.
    * intro Hkeep.
      apply Oeset.permut_nb_occ.
      unfold FlatData.make_groups.
      apply Partition.snd_partition_eq.
      -- intros first _ second Hequal.
         rewrite <- ListFacts.map_eq; intros attribute _.
         apply Interp.interp_aggterm_eq, env_t_eq_2; exact Hequal.
      -- apply Oeset.nb_occ_permut; intro row.
         rewrite <- !Febag.nb_occ_elements.
         revert row; now rewrite <- Febag.nb_occ_equal.
    * intros; reflexivity.
  + intros first second _ Hequal.
    apply f_equal, eval_formula_eq.
    * apply contains_nulls_eq.
    * apply (@env_g_eq_2 TNull env
        (@Group_By TNull group_terms) first second).
      rewrite Partition.compare_list_t; exact Hequal.
  + intros first second _ Hequal.
    apply f_equal, eval_formula_eq.
    * apply contains_nulls_eq.
    * apply (@env_g_eq_2 TNull env
        (@Group_By TNull group_terms) first second).
      rewrite Partition.compare_list_t; exact Hequal.
Qed.

Lemma query_satisfies_of_equiv :
  forall db q1 q2 f,
    query_equiv db q1 q2 ->
    query_satisfies db q1 f ->
    query_satisfies db q2 f.
Proof.
intros db q1 q2 f Hq Htrue t Ht.
apply Htrue.
apply query_equiv_implies_bag_equality in Hq.
change (Febag.mem _ t (eval_query_in_state db q1) = true).
rewrite (@Febag.mem_eq_2
           _ _ _
           (eval_query_in_state db q1)
           (eval_query_in_state db q2)
           Hq
           t).
exact Ht.
Qed.
