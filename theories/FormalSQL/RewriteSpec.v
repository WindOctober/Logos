From SQLFS Require Import SqlSyntax GenericInstance SqlAlgebra Projection Formula FiniteSet FiniteBag Bool3 FTuples Env ListFacts ListSort.
From Logos.FormalSQL Require Import TNullSyntax.
From Stdlib Require Import List NArith Lia.

Import Tuple.

(*
  Logos-local rewrite lemmas for FormalSQL.

  This file is intentionally outside vendor/FormalSQL.  It contains only proved
  lemmas; generated problem-specific reasoning belongs in the generated proof
  workspace, not as axioms in this library.
*)

Definition select_list_directly_preserves_attr
    (s : SelectListT) (a : attribute TNull) : Prop :=
  match s with
  | @_Select_List _ l => In (@Select_As TNull (@A_Expr TNull (@F_Dot TNull a)) a) l
  end.

Definition select_list_outputs_distinct_attrs (s : SelectListT) : Prop :=
  match s with
  | @_Select_List _ l => all_diff (map fst (map (@pair_of_select TNull) l))
  end.

Definition projection_preserves_attr_value
    (env : Env.env TNull) (s : SelectListT) (a : attribute TNull) : Prop :=
  forall t, a inS labels TNull t -> @dot TNull (projected_tuple env s t) a = @dot TNull t a.

Definition select_list_preserves_formula
    (db : db_state) (s : SelectListT) (f : Formula) : Prop :=
  forall t,
    eval_formula_in_state db (projected_tuple nil s t) f =
    eval_formula_in_state db t f.

Definition formula_implies_on_output
    (db : db_state) (q : Query) (premise conclusion : Formula) : Prop :=
  forall t,
    t inBE eval_query_in_state db q ->
    eval_formula_in_state db t premise = true ->
    eval_formula_in_state db t conclusion = true.

Lemma direct_projection_preserves_attr_value :
  forall env s a,
    select_list_directly_preserves_attr s a ->
    select_list_outputs_distinct_attrs s ->
    projection_preserves_attr_value env s a.
Proof.
intros env [l] a Hpres Hdistinct t Ha.
unfold projection_preserves_attr_value, projected_tuple in *.
change (@dot TNull (projection TNull (env_t TNull env t) (@Select_List TNull (@_Select_List TNull l))) a = @dot TNull t a).
rewrite (@dot_projection TNull (env_t TNull env t) l a (@A_Expr TNull (@F_Dot TNull a)) Hpres Hdistinct).
unfold Interp.interp_aggterm, Interp.interp_funterm, Interp.interp_dot, env_t.
simpl.
change ((if a inS? labels TNull t
         then @dot TNull t a
         else Interp.interp_dot TNull env a) = @dot TNull t a).
rewrite Ha.
apply refl_equal.
Qed.

Lemma eval_formula_in_env_eq :
  forall db env f t1 t2,
    t1 =t= t2 ->
    eval_formula_in_env db env t1 f = eval_formula_in_env db env t2 f.
Proof.
intros db env f t1 t2 Ht.
unfold eval_formula_in_env, eval_query_in_env.
apply (@is_true_eval_f_eq
  TNull relname
  (@_basesort TNull db)
  (@_instance TNull db)
  unknown3
  contains_nulls
  contains_nulls_eq
  env f t1 t2 Ht).
Qed.

Lemma selected_rows_satisfy_filter :
  forall db q f,
    formula_true_on_output db (Sigma f q) f.
Proof.
intros db q f t Ht.
unfold formula_true_on_output in *.
unfold eval_query_in_state, eval_formula_in_state, Sigma in Ht |- *.
unfold eval_query_in_env in Ht.
rewrite eval_query_unfold in Ht.
rewrite Febag.mem_filter in Ht.
- destruct (Febag.mem _ t (@eval_query TNull relname
                    (@_basesort TNull db)
                    (@_instance TNull db)
                    unknown3 contains_nulls nil q));
    simpl in Ht; [exact Ht | discriminate Ht].
- intros t1 t2 _ Ht12.
  unfold eval_formula_in_env, eval_query_in_env.
  apply (@is_true_eval_f_eq
    TNull relname
    (@_basesort TNull db)
    (@_instance TNull db)
    unknown3
    contains_nulls
    contains_nulls_eq
    nil f t1 t2 Ht12).
Qed.

Lemma formula_implies_filter_outputs :
  forall db q premise conclusion,
    formula_implies_on_output db q premise conclusion ->
    formula_true_on_output db (Sigma premise q) conclusion.
Proof.
intros db q premise conclusion Himplies t Ht.
apply Himplies.
- unfold eval_query_in_state, Sigma, eval_query_in_env in Ht |- *.
  rewrite eval_query_unfold in Ht.
  rewrite Febag.mem_filter in Ht.
  + destruct (Febag.mem _ t
        (@eval_query TNull relname
          (@_basesort TNull db)
          (@_instance TNull db)
          unknown3
          contains_nulls
          nil
          q));
      simpl in Ht; [reflexivity | discriminate Ht].
  + intros t1 t2 _ Ht12.
    unfold eval_formula_in_env, eval_query_in_env.
    apply (@is_true_eval_f_eq
      TNull relname
      (@_basesort TNull db)
      (@_instance TNull db)
      unknown3
      contains_nulls
      contains_nulls_eq
      nil premise t1 t2 Ht12).
- pose proof (selected_rows_satisfy_filter db q premise t Ht) as Hp.
  exact Hp.
Qed.

Lemma projected_filter_outputs_satisfy_preserved_predicate :
  forall db q s f,
    select_list_preserves_formula db s f ->
    formula_true_on_output db (Pi s (Sigma f q)) f.
Proof.
intros db q s f Hpres t Ht.
unfold eval_query_in_state, eval_query_in_env, Pi in Ht.
rewrite eval_query_unfold in Ht.
rewrite Febag.mem_map in Ht.
destruct Ht as [u [Htu Hu]].
pose proof (Febag.in_elements_mem _ _ _ Hu) as Hu_mem.
pose proof (selected_rows_satisfy_filter db q f u Hu_mem) as Hu_f.
unfold eval_formula_in_state.
rewrite (eval_formula_in_env_eq db nil f t (projected_tuple nil s u) Htu).
change (eval_formula_in_state db (projected_tuple nil s u) f = true).
rewrite Hpres.
exact Hu_f.
Qed.

Lemma projected_filter_outputs_satisfy_implied_predicate :
  forall db q s premise conclusion,
    select_list_preserves_formula db s conclusion ->
    formula_implies_on_output db q premise conclusion ->
    formula_true_on_output db (Pi s (Sigma premise q)) conclusion.
Proof.
intros db q s premise conclusion Hpres Himplies t Ht.
unfold eval_query_in_state, eval_query_in_env, Pi in Ht.
rewrite eval_query_unfold in Ht.
rewrite Febag.mem_map in Ht.
destruct Ht as [u [Htu Hu]].
pose proof (Febag.in_elements_mem _ _ _ Hu) as Hu_mem.
pose proof (formula_implies_filter_outputs db q premise conclusion Himplies u Hu_mem) as Hu_conclusion.
unfold eval_formula_in_state.
rewrite (eval_formula_in_env_eq db nil conclusion t (projected_tuple nil s u) Htu).
change (eval_formula_in_state db (projected_tuple nil s u) conclusion = true).
rewrite Hpres.
exact Hu_conclusion.
Qed.

Lemma eval_conj_and_true_iff :
  forall db env t p h,
    eval_formula_in_env db env t (conj_and p h) =
    (eval_formula_in_env db env t p && eval_formula_in_env db env t h)%bool.
Proof.
intros db env t p h.
unfold eval_formula_in_env, conj_and.
rewrite eval_sql_formula_unfold.
apply Bool.is_true_andb.
Qed.

Lemma redundant_conjunct_under_query_invariant :
  forall db q p h,
    formula_true_on_output db q h ->
    query_equiv db (Sigma (conj_and p h) q) (Sigma p q).
Proof.
intros db q p h Hh.
unfold query_equiv, eval_query_in_state, Sigma, eval_query_in_env.
rewrite 2 eval_query_unfold.
apply Febag.filter_eq.
- rewrite <- eval_query_unfold.
  apply Febag.equal_refl.
- intros t1 t2 Ht1 Ht12.
  assert (Ht1mem : t1 inBE eval_query_in_state db q).
  {
    unfold eval_query_in_state, eval_query_in_env.
    rewrite eval_query_unfold.
    apply Febag.nb_occ_mem.
    intro Hzero; rewrite Hzero in Ht1; lia.
  }
  change (eval_formula_in_env db nil t1 (conj_and p h) =
          eval_formula_in_env db nil t2 p).
  rewrite eval_conj_and_true_iff.
  replace (eval_formula_in_env db nil t1 h) with (eval_formula_in_state db t1 h)
    by reflexivity.
  rewrite (Hh t1).
  + rewrite Bool.Bool.andb_true_r.
    apply eval_formula_in_env_eq; assumption.
  + exact Ht1mem.
Qed.

Lemma occurrence_factor_of_andb3 :
  forall n outer_value inner_value,
    (n *
      (if match andb3 outer_value inner_value with
          | true3 => true
          | _ => false
          end
       then 1
       else 0))%N =
    (n *
      (if match inner_value with
          | true3 => true
          | _ => false
          end
       then 1
       else 0) *
      (if match outer_value with
          | true3 => true
          | _ => false
          end
       then 1
       else 0))%N.
Proof.
intros n outer_value inner_value.
destruct outer_value; destruct inner_value; cbn;
  rewrite ?N.mul_0_r, ?N.mul_0_l, ?N.mul_1_r, ?N.mul_1_l;
  reflexivity.
Qed.

Lemma sigma_sigma_merge :
  forall db q outer inner,
    query_equiv db (Sigma outer (Sigma inner q)) (Sigma (conj_and outer inner) q).
Proof.
intros db q outer inner.
unfold query_equiv, eval_query_in_state, Sigma, eval_query_in_env.
rewrite (@eval_query_unfold TNull relname
          (@_basesort TNull db)
          (@_instance TNull db)
          unknown3
          contains_nulls
          nil
          (@Q_Sigma TNull relname outer (@Q_Sigma TNull relname inner q))).
rewrite (@eval_query_unfold TNull relname
          (@_basesort TNull db)
          (@_instance TNull db)
          unknown3
          contains_nulls
          nil
          (@Q_Sigma TNull relname inner q)).
rewrite (@eval_query_unfold TNull relname
          (@_basesort TNull db)
          (@_instance TNull db)
          unknown3
          contains_nulls
          nil
          (@Q_Sigma TNull relname (conj_and outer inner) q)).
set (base := @eval_query TNull relname
              (@_basesort TNull db)
              (@_instance TNull db)
              unknown3
              contains_nulls
              nil
              q).
rewrite Febag.nb_occ_equal; intro t.
rewrite !Febag.nb_occ_filter.
- unfold conj_and.
  cbn.
  unfold interp_conj.
  symmetry; apply occurrence_factor_of_andb3.
- intros t1 t2 _ Ht12.
  unfold eval_formula_in_env, eval_query_in_env.
  apply (@is_true_eval_f_eq
    TNull relname
    (@_basesort TNull db)
    (@_instance TNull db)
    unknown3
    contains_nulls
    contains_nulls_eq
    nil (conj_and outer inner) t1 t2 Ht12).
- intros t1 t2 _ Ht12.
  unfold eval_formula_in_env, eval_query_in_env.
  apply (@is_true_eval_f_eq
    TNull relname
    (@_basesort TNull db)
    (@_instance TNull db)
    unknown3
    contains_nulls
    contains_nulls_eq
    nil inner t1 t2 Ht12).
- intros t1 t2 _ Ht12.
  unfold eval_formula_in_env, eval_query_in_env.
  apply (@is_true_eval_f_eq
    TNull relname
    (@_basesort TNull db)
    (@_instance TNull db)
    unknown3
    contains_nulls
    contains_nulls_eq
    nil outer t1 t2 Ht12).
Qed.
