From SQLFS Require Import SqlSyntax GenericInstance SqlAlgebra Projection FiniteBag Bool3 FTuples OrderedSet Env.
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
    forall t, query_occ db q1 t = query_occ db q2 t.
Proof.
intros db q1 q2.
unfold query_equiv, query_occ.
rewrite Febag.nb_occ_equal.
split; intro H; exact H.
Qed.

Lemma pi_congr :
  forall db s q1 q2,
    query_equiv db q1 q2 ->
    query_equiv db (Pi s q1) (Pi s q2).
Proof.
intros db s q1 q2 Hq.
unfold query_equiv, eval_query_in_state, eval_query_in_env, Pi in *.
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
    query_equiv db (Sigma f q1) (Sigma f q2).
Proof.
intros db f q1 q2 Hq.
unfold query_equiv, eval_query_in_state, Sigma, eval_query_in_env in *.
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

Lemma query_satisfies_of_equiv :
  forall db q1 q2 f,
    query_equiv db q1 q2 ->
    query_satisfies db q1 f ->
    query_satisfies db q2 f.
Proof.
intros db q1 q2 f Hq Htrue t Ht.
apply Htrue.
unfold query_equiv in Hq.
change (Febag.mem _ t (eval_query_in_state db q1) = true).
rewrite (@Febag.mem_eq_2
           _ _ _
           (eval_query_in_state db q1)
           (eval_query_in_state db q2)
           Hq
           t).
exact Ht.
Qed.
