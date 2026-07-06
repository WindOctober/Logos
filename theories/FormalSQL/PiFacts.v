From SQLFS Require Import SqlSyntax GenericInstance SqlAlgebra Projection FiniteSet FiniteBag Bool3 FTuples.
From Logos.FormalSQL Require Import TNullSyntax RewriteSpec OccFacts.
From Stdlib Require Import List.

Import Tuple.

(*
  Basic facts about Pi/projection-shaped algebra queries.

  These lemmas intentionally talk about the semantic output sort of a select
  list, not Coq syntactic inequality of select-list terms.  Two syntactically
  different select lists may still be semantically indistinguishable on a
  particular database instance.
*)

Definition well_sorted_database (db : db_state) : Prop :=
  forall tbl t,
    t inBE (@_instance TNull db tbl) ->
    labels TNull t =S= @_basesort TNull db tbl.

Definition select_list_sort (s : SelectListT) : Fset.set (A TNull) :=
  match s with
  | @_Select_List _ l =>
      Fset.mk_set _ (map (fun x => match x with @Select_As _ _ a => a end) l)
  end.

Lemma pi_sort :
  forall db s q,
    @sort TNull relname (@_basesort TNull db) (Pi s q) =S= select_list_sort s.
Proof.
intros db [l] q.
unfold Pi, select_list_sort.
simpl.
change
  (Fset.mk_set (A TNull)
     (map (fun x : select TNull => match x with @Select_As _ _ a => a end) l)
   =S=
   Fset.mk_set (A TNull)
     (map (fun x : select TNull => match x with @Select_As _ _ a => a end) l)).
apply Fset.equal_refl.
Qed.

Lemma pi_output_tuple_has_select_list_sort :
  forall db s q t,
    well_sorted_database db ->
    t inBE eval_query_in_state db (Pi s q) ->
    labels TNull t =S= select_list_sort s.
Proof.
intros db s q t Hdb Ht.
unfold eval_query_in_state, eval_query_in_env in Ht.
pose proof
  (@well_sorted_query
     TNull
     relname
     (@_basesort TNull db)
     (@_instance TNull db)
     unknown3
     contains_nulls
     contains_nulls_eq
     Hdb
     (Pi s q)
     nil
     t
     Ht) as Hsort.
rewrite (Fset.equal_eq_2 _ _ _ _ (pi_sort db s q)) in Hsort.
exact Hsort.
Qed.

Lemma common_pi_output_tuple_implies_same_select_list_sort :
  forall db s1 q1 s2 q2 t,
    well_sorted_database db ->
    t inBE eval_query_in_state db (Pi s1 q1) ->
    t inBE eval_query_in_state db (Pi s2 q2) ->
    select_list_sort s1 =S= select_list_sort s2.
Proof.
intros db s1 q1 s2 q2 t Hdb Hleft Hright.
pose proof (pi_output_tuple_has_select_list_sort db s1 q1 t Hdb Hleft) as Hs1.
pose proof (pi_output_tuple_has_select_list_sort db s2 q2 t Hdb Hright) as Hs2.
rewrite <- (Fset.equal_eq_1 _ _ _ _ Hs1).
exact Hs2.
Qed.

Lemma pi_sort_mismatch_not_equiv_with_witness :
  forall db s1 q1 s2 q2 t,
    well_sorted_database db ->
    t inBE eval_query_in_state db (Pi s1 q1) ->
    (select_list_sort s1 =S= select_list_sort s2 -> False) ->
    ~ query_equiv db (Pi s1 q1) (Pi s2 q2).
Proof.
intros db s1 q1 s2 q2 t Hdb Hleft Hsort_mismatch Hequiv.
assert (Hright : t inBE eval_query_in_state db (Pi s2 q2)).
{
  unfold query_equiv in Hequiv.
  change (Febag.mem _ t (eval_query_in_state db (Pi s2 q2)) = true).
  rewrite <-
    (@Febag.mem_eq_2
       _ _ _
       (eval_query_in_state db (Pi s1 q1))
       (eval_query_in_state db (Pi s2 q2))
       Hequiv
       t).
  exact Hleft.
}
apply Hsort_mismatch.
eapply common_pi_output_tuple_implies_same_select_list_sort; eauto.
Qed.

Lemma nonempty_pi_equiv_iff_sort_and_occ :
  forall db s1 q1 s2 q2,
    well_sorted_database db ->
    query_nonempty db (Pi s1 q1) ->
    query_equiv db (Pi s1 q1) (Pi s2 q2) <->
      select_list_sort s1 =S= select_list_sort s2 /\
      forall t, query_occ db (Pi s1 q1) t = query_occ db (Pi s2 q2) t.
Proof.
intros db s1 q1 s2 q2 Hdb Hnonempty.
split.
- intro Hequiv.
  split.
  + destruct Hnonempty as [t Hleft].
    assert (Hright : t inBE eval_query_in_state db (Pi s2 q2)).
    {
      unfold query_equiv in Hequiv.
      change (Febag.mem _ t (eval_query_in_state db (Pi s2 q2)) = true).
      rewrite <-
        (@Febag.mem_eq_2
           _ _ _
           (eval_query_in_state db (Pi s1 q1))
           (eval_query_in_state db (Pi s2 q2))
           Hequiv
           t).
      exact Hleft.
    }
    eapply common_pi_output_tuple_implies_same_select_list_sort; eauto.
  + intro t.
    unfold query_equiv in Hequiv.
    unfold query_occ.
    rewrite Febag.nb_occ_equal in Hequiv.
    apply Hequiv.
- intros [_ Hocc].
  unfold query_equiv, query_occ in *.
  rewrite Febag.nb_occ_equal.
  intro t.
  apply Hocc.
Qed.
