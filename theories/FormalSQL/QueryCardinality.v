(************************************************************************************)
(** Exact occurrence-count bounds for successful relational query evaluation.       *)
(************************************************************************************)

From SQLFS Require Import
  SqlSyntax GenericInstance Values FTuples FiniteBag FiniteCollection
  FiniteSet OrderedSet Bool3 Join FlatData Env Formula Projection SqlOutcome
  SqlAlgebra SqlErrorSemantics SqlQuerySyntax SqlQuerySemantics SqlBagAbstraction SqlQueryFacts
  ListFacts ListPermut Partition ValueInteger SchemaConstraints.
From Logos.FormalSQL Require Import
  SchemaCardinality TNullSyntax RewriteSpec.
From Stdlib Require Import List String ZArith Lia SetoidList SetoidPermutation
  RelationClasses Morphisms Sorting.Sorted.

Import ListNotations.
Import Tuple.

Open Scope string_scope.
Open Scope Z_scope.

(** Keep the comparison as a symbolic decision while reducing the surrounding
    concrete predicate interpreter. *)
Local Opaque Z.compare.

(** The list-level join facts below count occurrences.  They never quotient a
    list by equality and therefore retain duplicate SQL rows exactly. *)

Lemma theta_join_list_functional_length_le :
  forall (row : Type) (join : row -> row -> row)
         (accept : row -> row -> bool) left right,
    (forall left_row,
      In left_row left ->
      (List.length (filter (accept left_row) right) <= 1)%nat) ->
    (List.length (theta_join_list row join accept left right) <=
      List.length left)%nat.
Proof.
intros row join accept left.
induction left as [|left_row left IH]; intros right Hfunctional; cbn.
- lia.
- unfold d_join_list.
  rewrite length_app, length_map.
  fold (theta_join_list row join accept left right).
  pose proof (Hfunctional left_row (or_introl eq_refl)) as Hhead.
  specialize (IH right (fun row Hrow =>
    Hfunctional row (or_intror _ Hrow))).
  replace (S (List.length left)) with
    (1 + List.length left)%nat by lia.
  now apply Nat.add_le_mono.
Qed.

Lemma brute_left_join_list_length_mul :
  forall (row : Type) (join : row -> row -> row) left right,
    List.length (brute_left_join_list row join left right) =
      (List.length left * List.length right)%nat.
Proof.
intros row join left right.
unfold brute_left_join_list, theta_join_list, d_join_list.
assert (Htrue : filter (fun _ : row => true) right = right).
{
  apply ListFacts.filter_true; intros; reflexivity.
}
rewrite Htrue.
induction left as [|left_row left IH]; cbn.
- reflexivity.
- rewrite length_app, length_map, IH; lia.
Qed.

Lemma filter_brute_left_join_list_as_theta :
  forall (row : Type) (join : row -> row -> row)
         (keep : row -> bool) (accept : row -> row -> bool) left right,
    (forall left_row right_row,
      keep (join left_row right_row) = accept left_row right_row) ->
    filter keep (brute_left_join_list row join left right) =
      theta_join_list row join accept left right.
Proof.
intros row join keep accept left right Haccept.
unfold brute_left_join_list, theta_join_list, d_join_list.
assert (Htrue : filter (fun _ : row => true) right = right).
{
  apply ListFacts.filter_true; intros; reflexivity.
}
rewrite Htrue.
induction left as [|left_row left IH]; cbn.
- reflexivity.
- rewrite ListFacts.filter_app.
  rewrite ListFacts.filter_map.
  rewrite IH.
  f_equal.
  f_equal.
  apply ListFacts.filter_eq.
  intros right_row Hright.
  apply Haccept.
Qed.

Lemma theta_join_list_guard_left :
  forall (row : Type) (join : row -> row -> row)
         (guard : row -> bool) (accept : row -> row -> bool) left right,
    theta_join_list row join
      (fun left_row right_row => andb (guard left_row) (accept left_row right_row))
      left right =
    theta_join_list row join accept (filter guard left) right.
Proof.
intros row join guard accept left right.
unfold theta_join_list, d_join_list.
induction left as [|left_row left IH]; cbn.
- reflexivity.
- destruct (guard left_row) eqn:Hguard.
  + cbn; now rewrite IH.
  + cbn.
    assert (Hfalse :
      filter (fun _ : row => false) right = nil).
    {
      apply ListFacts.filter_false; intros; reflexivity.
    }
    rewrite Hfalse; cbn; exact IH.
Qed.

(** [query_same_rows_as_bag] permits an arbitrary permutation and arbitrary
    OTuple-equal representatives.  A row predicate used for bag counting must
    therefore be proper for that equality. *)
Definition tuple_predicate_proper (keep : tuple TNull -> bool) : Prop :=
  forall left right,
    Oeset.compare (OTuple TNull) left right = Eq ->
    keep left = keep right.

(** Proposition-valued row facts need the same respect for [OTuple] equality
    when they cross a bag boundary. *)
Definition tuple_property_proper (property : tuple TNull -> Prop) : Prop :=
  forall left right,
    Oeset.compare (OTuple TNull) left right = Eq ->
    (property left <-> property right).

Lemma row_attribute_present_conforms_proper :
  forall attribute,
    tuple_property_proper (row_attribute_present_conforms attribute).
Proof.
intros attribute left right Hequal.
now apply row_attribute_present_conforms_eq.
Qed.

(** Row facts crossing a bag boundary must retain presence as well as typing:
    only then does [OTuple] equality expose the selected cell. *)
Definition row_attribute_present_nonnull_conforms
    (attribute : attribute TNull) (row : tuple TNull) : Prop :=
  row_attribute_present_conforms attribute row /\
  NullValues.is_null_value (dot TNull row attribute) = false.

Lemma row_attribute_present_nonnull_conforms_proper :
  forall attribute,
    tuple_property_proper
      (row_attribute_present_nonnull_conforms attribute).
Proof.
intros attribute left right Hequal; split.
- intros [[Hpresent Htyped] Hnonnull].
  split.
  + now apply (proj1
      (row_attribute_present_conforms_eq attribute left right Hequal)).
  + rewrite <- (tuple_eq_dot_alt TNull left right Hequal attribute Hpresent).
    exact Hnonnull.
- intros [[Hpresent Htyped] Hnonnull].
  assert (Hreverse : Oeset.compare (OTuple TNull) right left = Eq).
  { now apply Oeset.compare_eq_sym. }
  split.
  + now apply (proj2
      (row_attribute_present_conforms_eq attribute left right Hequal)).
  + rewrite <- (tuple_eq_dot_alt TNull right left Hreverse attribute Hpresent).
    exact Hnonnull.
Qed.

Lemma related_permut_Forall_transport :
  forall (A B : Type) (R : A -> B -> Prop) (P : A -> Prop) (Q : B -> Prop)
         left right,
    (forall a b, R a b -> P a -> Q b) ->
    _permut R left right ->
    Forall P left ->
    Forall Q right.
Proof.
intros A B R P Q left right Hrespect Hpermut Hforall.
rewrite Forall_forall in Hforall |- *.
intros b Hb.
destruct (in_split b right Hb) as [before [after Hright]].
subst right.
destruct
  (_permut_inv_right_strong (R := R) b before after Hpermut)
  as [a [left_before [left_after [Hab [Hleft _]]]]].
apply (Hrespect a b Hab).
apply Hforall.
rewrite Hleft.
apply in_or_app; right; now left.
Qed.

(** FormalSQL's historical [_permut] relation and Stdlib's setoid
    [PermutationA] express the same one-for-one transport when the relation is
    an equivalence.  This bridge lets the query semantics reuse Stdlib's
    duplicate-freedom theorem without changing the existing bag interface. *)
Lemma related_permut_PermutationA :
  forall (A : Type) (relation : A -> A -> Prop) left right,
    Equivalence relation ->
    _permut relation left right ->
    PermutationA relation left right.
Proof.
intros A relation left right Hequivalence Hpermut.
induction Hpermut as [|first second tail before after Hrelated Htail IH].
- constructor.
- refine (@permA_trans A relation
    (first :: tail) (second :: before ++ after)
    (before ++ second :: after) _ _).
  + now apply permA_skip.
  + exact (@PermutationA_middle A relation Hequivalence before after second).
Qed.

Lemma oeset_compare_Equivalence :
  forall (A : Type) (ordered : Oeset.Rcd A),
    Equivalence
      (fun left right => Oeset.compare ordered left right = Eq).
Proof.
intros A ordered; split.
- intro value; apply Oeset.compare_eq_refl.
- intros left right; apply Oeset.compare_eq_sym.
- intros first second third Hfirst Hsecond.
  exact (Oeset.compare_eq_trans ordered first second third Hfirst Hsecond).
Qed.

Lemma oeset_sorted_NoDupA :
  forall (A : Type) (ordered : Oeset.Rcd A) rows,
    Sorted (fun left right => Oeset.compare ordered left right = Lt) rows ->
    NoDupA (fun left right => Oeset.compare ordered left right = Eq) rows.
Proof.
intros A ordered rows Hsorted.
refine
  (@SortA_NoDupA A
    (fun left right => Oeset.compare ordered left right = Eq)
    (@oeset_compare_Equivalence A ordered)
    (fun left right => Oeset.compare ordered left right = Lt)
    _ _ rows Hsorted).
- split.
  + intros value Hlt.
    pose proof (Oeset.compare_eq_refl ordered value); congruence.
  + intros first second third Hfirst Hsecond.
    exact (Oeset.compare_lt_trans ordered first second third Hfirst Hsecond).
- intros first first' Hfirst second second' Hsecond; split; intro Hlt.
  + eapply Oeset.compare_lt_eq_trans; [|exact Hsecond].
    eapply Oeset.compare_eq_lt_trans; [|exact Hlt].
    now apply Oeset.compare_eq_sym.
  + eapply Oeset.compare_lt_eq_trans; [|].
    * eapply Oeset.compare_eq_lt_trans; [exact Hfirst|exact Hlt].
    * now apply Oeset.compare_eq_sym.
Qed.

Lemma NoDupA_app_left :
  forall (A : Type) (relation : A -> A -> Prop) left right,
    NoDupA relation (left ++ right) ->
    NoDupA relation left.
Proof.
intros A relation left.
induction left as [|first left IH]; intros right Hnodup; cbn; [constructor|].
inversion Hnodup as [|? ? Hfirst Htail]; subst.
constructor.
- intros Hin.
  apply Hfirst.
  apply InA_alt in Hin as [other [Hrelated Hother]].
  apply InA_alt; exists other; split; [exact Hrelated|].
  apply in_or_app; now left.
- now apply IH with (right := right).
Qed.

Lemma NoDupA_app_right :
  forall (A : Type) (relation : A -> A -> Prop) left right,
    NoDupA relation (left ++ right) ->
    NoDupA relation right.
Proof.
intros A relation left.
induction left as [|first left IH]; intros right Hnodup; cbn in Hnodup.
- exact Hnodup.
- inversion Hnodup as [|? ? _ Htail]; subst.
  now apply IH.
Qed.

Lemma NoDupA_map_injective_on :
  forall (A : Type) (relation : A -> A -> Prop) rows
      (code : A -> nat),
    NoDupA relation rows ->
    (forall left right,
      In left rows ->
      In right rows ->
      code left = code right ->
      relation left right) ->
    NoDup (map code rows).
Proof.
intros A relation rows.
induction rows as [|first rows IH]; intros code Hnodup Hinjective; cbn.
- constructor.
- inversion Hnodup as [|? ? Hfirst Htail]; subst.
  constructor.
  + intros Hin.
    apply in_map_iff in Hin as [other [Hequal Hother]].
    apply Hfirst.
    apply InA_alt; exists other; split.
    * apply Hinjective; [now left|now right|now symmetry].
    * exact Hother.
  + apply IH; [exact Htail|].
    intros left right Hleft Hright Hequal.
    apply Hinjective; [now right|now right|exact Hequal].
Qed.

Lemma query_same_rows_as_bag_permut_elements :
  forall rows bag,
    @query_same_rows_as_bag TNull rows bag ->
    _permut
      (fun left right => Oeset.compare (OTuple TNull) left right = Eq)
      rows (Febag.elements (Fecol.CBag (CTuple TNull)) bag).
Proof.
intros rows bag Hrows.
apply Oeset.nb_occ_permut; intro row.
unfold query_same_rows_as_bag, query_rows_bag in Hrows.
rewrite Febag.nb_occ_equal in Hrows.
specialize (Hrows row).
rewrite Febag.nb_occ_mk_bag, Febag.nb_occ_elements in Hrows.
exact Hrows.
Qed.

(** Duplicate elimination is represented by a finite set embedded back into a
    bag.  Every successful list representative is therefore duplicate-free
    under semantic tuple equality, even though its representatives and order
    need not be definitionally identical to the set's element list. *)
Lemma query_distinct_bag_rows_NoDupA :
  forall input rows,
    @query_same_rows_as_bag TNull rows
      (@query_distinct_bag TNull input) ->
    NoDupA
      (fun left right => Oeset.compare (OTuple TNull) left right = Eq)
      rows.
Proof.
intros input rows Hrows.
unfold query_distinct_bag in Hrows |- *.
set (set_rows :=
  Feset.elements (Fecol.CSet (CTuple TNull))
    (Feset.mk_set (Fecol.CSet (CTuple TNull))
      (Febag.elements (Fecol.CBag (CTuple TNull)) input))).
assert (Hset :
  NoDupA
    (fun left right => Oeset.compare (OTuple TNull) left right = Eq)
    set_rows).
{
  apply oeset_sorted_NoDupA.
  unfold set_rows; apply Feset.elements_spec3.
}
pose proof
  (query_same_rows_as_bag_permut_elements rows
    (Febag.mk_bag (Fecol.CBag (CTuple TNull)) set_rows) Hrows)
  as Hrows_bag.
assert (Hbag_set :
  _permut
    (fun left right => Oeset.compare (OTuple TNull) left right = Eq)
    (Febag.elements (Fecol.CBag (CTuple TNull))
      (Febag.mk_bag (Fecol.CBag (CTuple TNull)) set_rows))
    set_rows).
{
  apply Oeset.nb_occ_permut; intro row.
  rewrite <- Febag.nb_occ_elements, Febag.nb_occ_mk_bag; reflexivity.
}
assert (Hrows_set :
  _permut
    (fun left right => Oeset.compare (OTuple TNull) left right = Eq)
    rows set_rows).
{
  eapply _permut_trans; [|exact Hrows_bag|exact Hbag_set].
  intros first second third _ _ _ Hfirst Hsecond.
  exact
    (Oeset.compare_eq_trans (OTuple TNull)
      first second third Hfirst Hsecond).
}
eapply PermutationA_preserves_NoDupA.
- apply oeset_compare_Equivalence.
- apply related_permut_PermutationA.
  + apply oeset_compare_Equivalence.
  + exact
      (@Oeset.permut_sym _ (OTuple TNull) rows set_rows Hrows_set).
- exact Hset.
Qed.

Lemma query_same_rows_as_bag_Forall_between :
  forall property first second bag,
    tuple_property_proper property ->
    @query_same_rows_as_bag TNull first bag ->
    @query_same_rows_as_bag TNull second bag ->
    Forall property first ->
    Forall property second.
Proof.
intros property first second bag Hproper Hfirst Hsecond Hforall.
pose proof (query_same_rows_as_bag_permut_elements first bag Hfirst)
  as Hfirst_permut.
pose proof (query_same_rows_as_bag_permut_elements second bag Hsecond)
  as Hsecond_permut.
assert (Helements :
  Forall property (Febag.elements (Fecol.CBag (CTuple TNull)) bag)).
{
  eapply related_permut_Forall_transport; [|exact Hfirst_permut|exact Hforall].
  intros left right Hequal Hleft.
  now apply (proj1 (Hproper left right Hequal)).
}
eapply related_permut_Forall_transport; [| |exact Helements].
- intros left right Hequal Hleft.
  now apply (proj1 (Hproper left right Hequal)).
- now apply Oeset.permut_sym.
Qed.

(** A conforming table's typed NOT NULL column remains typed and non-NULL in
    every ordered representative exposed by [QExpr_Bag].  This is the safe
    schema-to-observation bridge; it does not identify represented tuples by
    Rocq equality. *)
Theorem query_same_rows_as_conforming_table_attribute :
  forall expected constraints actual constraint attribute rows,
    database_conforms_schema expected constraints actual ->
    In constraint constraints ->
    attribute inS
      (@_basesort TNull expected (constraint_relation constraint)) ->
    In attribute (constraint_not_null constraint) ->
    @query_same_rows_as_bag TNull rows
      (@_instance TNull actual (constraint_relation constraint)) ->
    Forall (row_attribute_present_nonnull_conforms attribute) rows.
Proof.
intros expected constraints actual constraint attribute rows
  Hschema Hconstraint Hattribute Hnot_null Hrows.
eapply query_same_rows_as_bag_Forall_between with
  (first := instance_rows actual (constraint_relation constraint))
  (bag := @_instance TNull actual (constraint_relation constraint)).
- apply row_attribute_present_nonnull_conforms_proper.
- unfold instance_rows; apply query_elements_same_rows_as_bag.
- exact Hrows.
- rewrite Forall_forall; intros row Hrow.
  split.
  + pose proof
      (database_conforms_schema_rows_attribute_present
        expected constraints actual (constraint_relation constraint)
        attribute Hschema Hattribute) as Hpresent.
    unfold rows_attribute_present_conform in Hpresent.
    rewrite Forall_forall in Hpresent.
    now apply Hpresent.
  + pose proof
      (database_conforms_schema_constraints
        expected constraints actual Hschema) as Hconstraints.
    pose proof
      (schema_constraints_conform_member
        actual constraints constraint Hconstraints Hconstraint) as Htable.
    assert (Hrows_not_null :
      rows_attributes_not_null
        (constraint_not_null constraint)
        (instance_rows actual (constraint_relation constraint))).
    {
      unfold table_constraint_conforms in Htable.
      eapply rows_constraint_conform_not_null; exact Htable.
    }
    exact (Hrows_not_null row Hrow attribute Hnot_null).
Qed.

(** Lift the schema fact above directly through a successful [QExpr_Bag]
    observation of a base table.  This keeps generated proofs from repeatedly
    unpacking the bag observation and reducing the base-table evaluator. *)
Theorem query_expr_bag_table_success_rows_conform_attribute :
  forall expected constraints actual constraint attribute outputs env rows
      unknown contains_nulls symbol_runtime_error aggregate_runtime_error
      value_is_null,
    database_conforms_schema expected constraints actual ->
    In constraint constraints ->
    attribute inS
      (@_basesort TNull expected (constraint_relation constraint)) ->
    In attribute (constraint_not_null constraint) ->
    @eval_query_expr_outcome TNull relname
      (@_basesort TNull actual) (@_instance TNull actual)
      unknown contains_nulls symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (@QExpr_Bag TNull relname outputs
        (@Q_Table TNull relname (constraint_relation constraint)))
      (SqlSuccess rows) ->
    Forall (row_attribute_present_nonnull_conforms attribute) rows.
Proof.
intros expected constraints actual constraint attribute outputs env rows
  unknown contains_nulls symbol_runtime_error aggregate_runtime_error
  value_is_null Hschema Hconstraint Hattribute Hnot_null Hrows.
apply eval_query_expr_bag_success_iff in Hrows.
destruct Hrows as [bag [Hbag Hrows]].
cbn [eval_query_outcome eval_query_runtime_error eval_query] in Hbag.
inversion Hbag; subst bag.
eapply query_same_rows_as_conforming_table_attribute;
  eassumption.
Qed.

Corollary query_canonical_rows_Forall :
  forall property rows,
    tuple_property_proper property ->
    Forall property rows ->
    Forall property (@query_canonical_rows TNull rows).
Proof.
intros property rows Hproper Hforall.
unfold query_canonical_rows.
eapply related_permut_Forall_transport; [| |exact Hforall].
- intros left right Hequal Hleft.
  now apply (proj1 (Hproper left right Hequal)).
- apply query_same_rows_as_bag_permut_elements.
  unfold query_same_rows_as_bag; apply Febag.equal_refl.
Qed.

Lemma query_same_rows_as_bag_filter_length :
  forall keep rows bag,
    tuple_predicate_proper keep ->
    @query_same_rows_as_bag TNull rows bag ->
    List.length (filter keep rows) =
      List.length
        (filter keep
          (Febag.elements (Fecol.CBag (CTuple TNull)) bag)).
Proof.
intros keep rows bag Hproper Hrows.
apply _permut_length with
  (R := fun left right =>
    Oeset.compare (OTuple TNull) left right = Eq).
apply permut_filter_eq.
- intros left right _ Hequal; now apply Hproper.
- apply Oeset.nb_occ_permut; intro row.
  unfold query_same_rows_as_bag, query_rows_bag in Hrows.
  rewrite Febag.nb_occ_equal in Hrows.
  specialize (Hrows row).
  rewrite Febag.nb_occ_mk_bag, Febag.nb_occ_elements in Hrows.
  exact Hrows.
Qed.

Lemma query_same_rows_as_bag_filter_length_between :
  forall keep first second bag,
    tuple_predicate_proper keep ->
    @query_same_rows_as_bag TNull first bag ->
    @query_same_rows_as_bag TNull second bag ->
    List.length (filter keep first) = List.length (filter keep second).
Proof.
intros keep first second bag Hproper Hfirst Hsecond.
rewrite (query_same_rows_as_bag_filter_length
  keep first bag Hproper Hfirst).
symmetry.
now apply query_same_rows_as_bag_filter_length.
Qed.

Lemma query_canonical_rows_length :
  forall rows : list (tuple TNull),
    List.length (@query_canonical_rows TNull rows) = List.length rows.
Proof.
intro rows.
assert (Hproper : tuple_predicate_proper (fun _ : tuple TNull => true)).
{
  intros left right Hequal; exact eq_refl.
}
assert (Hrows : @query_same_rows_as_bag TNull rows
  (@query_rows_bag TNull rows)).
{
  unfold query_same_rows_as_bag; apply Febag.equal_refl.
}
pose proof (query_same_rows_as_bag_filter_length
  (fun _ : tuple TNull => true) rows (@query_rows_bag TNull rows)
  Hproper Hrows) as Hlength.
rewrite (ListFacts.filter_true (fun _ : tuple TNull => true) rows) in Hlength
  by (intros; reflexivity).
rewrite (ListFacts.filter_true (fun _ : tuple TNull => true)
  (Febag.elements (Fecol.CBag (CTuple TNull))
    (@query_rows_bag TNull rows))) in Hlength
  by (intros; reflexivity).
unfold query_canonical_rows.
symmetry; exact Hlength.
Qed.

Lemma row_attribute_present_conforms_join_left :
  forall attribute left right,
    row_attribute_present_conforms attribute left ->
    row_attribute_present_conforms attribute (join_tuple TNull left right).
Proof.
intros attribute left right [Hpresent Hconforms].
split.
- unfold join_tuple.
  rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)), Fset.mem_union.
  now rewrite Hpresent.
- rewrite dot_join_tuple_1; assumption.
Qed.

Lemma row_attribute_present_conforms_join_right :
  forall attribute left right,
    (attribute inS? labels TNull left) = false ->
    row_attribute_present_conforms attribute right ->
    row_attribute_present_conforms attribute (join_tuple TNull left right).
Proof.
intros attribute left right Habsent [Hpresent Hconforms].
split.
- unfold join_tuple.
  rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)), Fset.mem_union.
  now rewrite Habsent, Hpresent.
- rewrite dot_join_tuple_2; assumption.
Qed.

Lemma brute_left_join_list_Forall :
  forall (left_property right_property joined_property : tuple TNull -> Prop)
         left right,
    Forall left_property left ->
    Forall right_property right ->
    (forall left_row right_row,
      left_property left_row ->
      right_property right_row ->
      joined_property (join_tuple TNull left_row right_row)) ->
    Forall joined_property
      (brute_left_join_list (tuple TNull) (join_tuple TNull) left right).
Proof.
intros left_property right_property joined_property left right
  Hleft Hright Hjoined.
rewrite Forall_forall in Hleft, Hright |- *.
intros joined_row Hin.
unfold brute_left_join_list, theta_join_list in Hin.
apply in_flat_map in Hin as [left_row [Hleft_row Hin]].
unfold d_join_list in Hin.
apply in_map_iff in Hin as [right_row [Hrow Hright_row]].
subst joined_row.
apply filter_In in Hright_row as [Hright_row _].
apply Hjoined.
- now apply Hleft.
- now apply Hright.
Qed.

Corollary brute_left_join_list_Forall_left_attribute :
  forall attribute left right,
    rows_attribute_present_conform attribute left ->
    rows_attribute_present_conform attribute
      (brute_left_join_list (tuple TNull) (join_tuple TNull) left right).
Proof.
intros attribute left right Hleft.
unfold rows_attribute_present_conform in *.
eapply brute_left_join_list_Forall
  with (right_property := fun _ : tuple TNull => True).
- exact Hleft.
- rewrite Forall_forall; intros; exact I.
- intros left_row right_row Hrow _.
  now apply row_attribute_present_conforms_join_left.
Qed.

Corollary brute_left_join_list_Forall_right_attribute :
  forall attribute left right,
    Forall (fun row => (attribute inS? labels TNull row) = false) left ->
    rows_attribute_present_conform attribute right ->
    rows_attribute_present_conform attribute
      (brute_left_join_list (tuple TNull) (join_tuple TNull) left right).
Proof.
intros attribute left right Hleft Hright.
unfold rows_attribute_present_conform in *.
eapply brute_left_join_list_Forall; [exact Hleft|exact Hright|].
intros left_row right_row Habsent Hrow.
now apply row_attribute_present_conforms_join_right.
Qed.

Lemma direct_projection_preserves_present_conformance :
  forall env select_list attribute row,
    select_list_directly_selects_attr select_list attribute ->
    select_list_has_unique_outputs select_list ->
    row_attribute_present_conforms attribute row ->
    row_attribute_present_conforms attribute
      (projected_tuple env select_list row).
Proof.
intros env [items] attribute row Hselect Hunique [Hpresent Hconforms].
split.
- unfold projected_tuple.
  rewrite (Fset.mem_eq_2 _ _ _
    (@labels_projection TNull (env_t TNull env row) items)).
  rewrite Fset.mem_mk_set, Oset.mem_bool_true_iff, in_map_iff.
  exists (@Select_As TNull
    (@A_Expr TNull (@F_Dot TNull attribute)) attribute).
  split; [reflexivity|exact Hselect].
- pose proof
    (direct_projection_preserves_attr env (@_Select_List TNull items)
      attribute Hselect Hunique) as Hpreserves.
  unfold projection_preserves_attr in Hpreserves.
  rewrite (Hpreserves row Hpresent).
  exact Hconforms.
Qed.

(** The concrete raw Cartesian list represents exactly the cross-join bag,
    even though that bag internally chooses canonical representatives. *)
Lemma raw_cross_same_rows_as_bag :
  forall left right : list (tuple TNull),
    @query_same_rows_as_bag TNull
      (brute_left_join_list (tuple TNull) (join_tuple TNull) left right)
      (@query_cross_join_bag TNull
        (@query_rows_bag TNull left) (@query_rows_bag TNull right)).
Proof.
intros left right.
unfold query_same_rows_as_bag, query_cross_join_bag, query_rows_bag.
rewrite Febag.nb_occ_equal; intro row.
rewrite !Febag.nb_occ_mk_bag.
apply Oeset.permut_nb_occ.
unfold brute_left_join_list.
apply (theta_join_list_permut_eq
  (tuple TNull) (OTuple TNull) (join_tuple TNull)
  (join_tuple_eq_1 TNull) (join_tuple_eq_2 TNull)
  (fun _ _ : tuple TNull => true)).
- intros; reflexivity.
- apply Oeset.nb_occ_permut; intro item.
  rewrite <- Febag.nb_occ_elements, Febag.nb_occ_mk_bag; reflexivity.
- apply Oeset.nb_occ_permut; intro item.
  rewrite <- Febag.nb_occ_elements, Febag.nb_occ_mk_bag; reflexivity.
Qed.

Corollary raw_cross_filter_count_for_any_representative :
  forall keep rows left right,
    tuple_predicate_proper keep ->
    @query_same_rows_as_bag TNull rows
      (@query_cross_join_bag TNull
        (@query_rows_bag TNull left) (@query_rows_bag TNull right)) ->
    List.length (filter keep rows) =
    List.length
      (filter keep
        (brute_left_join_list (tuple TNull) (join_tuple TNull) left right)).
Proof.
intros keep rows left right Hproper Hrows.
eapply query_same_rows_as_bag_filter_length_between; eauto.
apply raw_cross_same_rows_as_bag.
Qed.

(** PostgreSQL Bool3 equality for typed INTEGER cells. *)
Lemma interp_predicate_int32_nonnull_equal :
  forall left right,
    NullValues.interp_predicate (PredicateEq)
      [NullValues.Value_int32 (Some left);
       NullValues.Value_int32 (Some right)] =
    match Z.compare (int32_value left) (int32_value right) with
    | Eq => true3
    | Lt | Gt => false3
    end.
Proof.
intros; reflexivity.
Qed.

Lemma interp_predicate_int32_null_left :
  forall right,
    NullValues.interp_predicate (PredicateEq)
      [NullValues.Value_int32 None; right] = unknown3.
Proof.
intro right; destruct right; reflexivity.
Qed.

Lemma interp_predicate_int32_null_right :
  forall left,
    NullValues.interp_predicate (PredicateEq)
      [NullValues.Value_int32 (Some left);
       NullValues.Value_int32 None] = unknown3.
Proof.
intro left; reflexivity.
Qed.

Definition postgres_int32_equal_true
    (left right : value TNull) : bool :=
  Bool.is_true (B TNull)
    (NullValues.interp_predicate (PredicateEq) [left; right]).

Lemma postgres_int32_equal_true_eq :
  forall left_name right_name left right,
    value_conforms_attribute (Attr_int32 left_name) left ->
    value_conforms_attribute (Attr_int32 right_name) right ->
    postgres_int32_equal_true left right = true ->
    left = right.
Proof.
intros left_name right_name left right Hleft Hright Htrue.
destruct (conforming_int32_value left_name left Hleft) as [left_value ->].
destruct (conforming_int32_value right_name right Hright) as [right_value ->].
destruct left_value as [left_integer|];
  destruct right_value as [right_integer|].
- unfold postgres_int32_equal_true in Htrue.
  rewrite interp_predicate_int32_nonnull_equal in Htrue.
  destruct
    (Z.compare (int32_value left_integer) (int32_value right_integer))
    eqn:Hcompare.
  + apply Z.compare_eq in Hcompare.
    rewrite (int32_ext left_integer right_integer Hcompare).
    reflexivity.
  + cbn in Htrue; discriminate.
  + cbn in Htrue; discriminate.
- unfold postgres_int32_equal_true in Htrue.
  rewrite interp_predicate_int32_null_right in Htrue.
  cbn in Htrue; discriminate.
- unfold postgres_int32_equal_true in Htrue.
  rewrite interp_predicate_int32_null_left in Htrue.
  cbn in Htrue; discriminate.
- unfold postgres_int32_equal_true in Htrue.
  rewrite interp_predicate_int32_null_left in Htrue.
  cbn in Htrue; discriminate.
Qed.

Lemma NoDup_map_constant_filter_length_le_one :
  forall (row key : Type) (key_of : row -> key) (accept : row -> bool)
         rows fixed,
    NoDup (map key_of rows) ->
    (forall row,
      In row rows -> accept row = true -> key_of row = fixed) ->
    (List.length (filter accept rows) <= 1)%nat.
Proof.
intros row key key_of accept rows fixed.
induction rows as [|first rest IH]; intros Hnodup Hconstant; cbn.
- lia.
- cbn in Hnodup.
  inversion Hnodup as [|first_key rest_keys Hfirst Hrest]; subst.
  destruct (accept first) eqn:Haccept; cbn.
  + assert (Htail : filter accept rest = nil).
    {
      destruct (filter accept rest) as [|other tail] eqn:Hfiltered;
        [reflexivity|].
      assert (Hother_filtered : In other (filter accept rest)).
      {
        rewrite Hfiltered; now left.
      }
      apply filter_In in Hother_filtered as [Hother Hother_accept].
      exfalso; apply Hfirst.
      apply in_map_iff.
      exists other; split.
      - rewrite (Hconstant first (or_introl eq_refl) Haccept).
        apply Hconstant.
        * now right.
        * exact Hother_accept.
      - exact Hother.
    }
    now rewrite Htail.
  + apply IH; [exact Hrest|].
    intros other Hother Haccepted.
    apply Hconstant; [now right|exact Haccepted].
Qed.

Lemma int32_primary_key_true_matches_at_most_one :
  forall fact_name dimension_name fact_value dimension_rows,
    value_conforms_attribute (Attr_int32 fact_name) fact_value ->
    rows_attribute_conform (Attr_int32 dimension_name) dimension_rows ->
    primary_key_conforms [Attr_int32 dimension_name] dimension_rows ->
    (List.length
      (filter
        (fun row => postgres_int32_equal_true fact_value
          (dot TNull row (Attr_int32 dimension_name)))
        dimension_rows) <= 1)%nat.
Proof.
intros fact_name dimension_name fact_value dimension_rows
  Hfact Htyped Hprimary.
pose proof
  (int32_singleton_primary_key_projection_nodup
    dimension_name dimension_rows Htyped Hprimary) as Hkeys.
assert (Hvalues :
  NoDup (map (fun row => dot TNull row (Attr_int32 dimension_name))
    dimension_rows)).
{
  eapply NoDup_map_by_key with
    (key_of := project_row [Attr_int32 dimension_name]); [exact Hkeys|].
  intros left right _ _ Hequal.
  rewrite !project_row_cons, !project_row_nil, Hequal; reflexivity.
}
eapply NoDup_map_constant_filter_length_le_one with
  (fixed := fact_value); [exact Hvalues|].
intros row Hrow Hmatch.
symmetry.
eapply postgres_int32_equal_true_eq; eauto.
Qed.

Lemma null_int32_primary_key_matches_none :
  forall dimension_name dimension_rows,
    filter
      (fun row => postgres_int32_equal_true
        (NullValues.Value_int32 None)
        (dot TNull row (Attr_int32 dimension_name)))
      dimension_rows = nil.
Proof.
intros dimension_name dimension_rows.
apply ListFacts.filter_false.
intro row.
unfold postgres_int32_equal_true.
rewrite interp_predicate_int32_null_left.
reflexivity.
Qed.

(** Partition coverage is multiplicity-preserving.  The selected group is a
    literal segment of the partition flattening, whose length equals the
    original input by [partition_permut]. *)
Lemma partition_member_length_le :
  forall (row key : Type) (OK : Oset.Rcd key) (key_of : row -> key)
         rows key_value group,
    In (key_value, group) (@Partition.partition row key OK key_of rows) ->
    (List.length group <= List.length rows)%nat.
Proof.
intros row key OK key_of rows key_value group Hin.
destruct (in_split _ _ Hin) as [before [after Hsplit]].
pose proof (@Partition.partition_permut row key OK key_of rows) as Hpermut.
pose proof (_permut_length Hpermut) as Hlength.
rewrite Hsplit, !flat_map_app in Hlength; cbn in Hlength.
rewrite !length_app in Hlength; cbn in Hlength; lia.
Qed.

Theorem query_make_groups_member_length_le :
  forall env rows group_terms group,
    In group (@query_make_groups TNull env rows group_terms) ->
    (List.length group <= List.length rows)%nat.
Proof.
intros env rows group_terms group Hin.
unfold query_make_groups in Hin.
destruct group_terms as [|term terms]; destruct rows as [|row rows];
  cbn in Hin; try contradiction.
- destruct Hin as [Hin|Hin]; [subst; cbn; lia|contradiction].
- apply in_map_iff in Hin as [[key_value selected] [Hequal Hin]].
  cbn in Hequal; subst selected.
  eapply partition_member_length_le; exact Hin.
- apply in_map_iff in Hin as [[key_value selected] [Hequal Hin]].
  cbn in Hequal; subst selected.
  eapply partition_member_length_le; exact Hin.
Qed.

Lemma query_make_groups_member_in :
  forall env rows group_terms group row,
    In group (@query_make_groups TNull env rows group_terms) ->
    In row group ->
    In row rows.
Proof.
intros env rows group_terms group row Hgroup Hrow.
unfold query_make_groups in Hgroup.
destruct group_terms as [|term terms].
- destruct rows as [|first rows].
  + cbn in Hgroup.
    destruct Hgroup as [Hgroup|Hgroup]; [subst group; contradiction|contradiction].
  + cbn [make_groups] in Hgroup.
    eapply in_map_snd_partition; eassumption.
- cbn [make_groups] in Hgroup.
  eapply in_map_snd_partition; eassumption.
Qed.

Lemma query_make_groups_member_nonempty :
  forall env rows group_terms group,
    group_terms <> nil ->
    In group (@query_make_groups TNull env rows group_terms) ->
    group <> nil.
Proof.
intros env rows group_terms group Hterms Hgroup.
unfold query_make_groups in Hgroup.
destruct group_terms as [|term terms]; [contradiction|].
cbn [make_groups] in Hgroup.
exact (in_map_snd_partition_diff_nil _ _ _ Hgroup).
Qed.

(** Partitioning reorders occurrences into disjoint key classes but never
    duplicates one.  Hence semantic tuple duplicate-freedom of the input is
    inherited by every selected class. *)
Lemma partition_member_NoDupA :
  forall (key : Type) (ordered : Oset.Rcd key)
      (key_of : tuple TNull -> key) rows key_value group,
    NoDupA
      (fun left right => Oeset.compare (OTuple TNull) left right = Eq)
      rows ->
    In (key_value, group)
      (@Partition.partition (tuple TNull) key ordered key_of rows) ->
    NoDupA
      (fun left right => Oeset.compare (OTuple TNull) left right = Eq)
      group.
Proof.
intros key ordered key_of rows key_value group Hrows Hgroup.
pose proof
  (@Partition.partition_permut (tuple TNull) key ordered key_of rows)
  as Hpartition.
assert (Hsemantic :
  _permut
    (fun left right => Oeset.compare (OTuple TNull) left right = Eq)
    rows
    (flat_map (fun item => snd item)
      (@Partition.partition (tuple TNull) key ordered key_of rows))).
{
  eapply _permut_incl; [|exact Hpartition].
  intros left right Hequal; subst right.
  apply Oeset.compare_eq_refl.
}
assert (Hflattened :
  NoDupA
    (fun left right => Oeset.compare (OTuple TNull) left right = Eq)
    (flat_map (fun item => snd item)
      (@Partition.partition (tuple TNull) key ordered key_of rows))).
{
  eapply PermutationA_preserves_NoDupA.
  - apply oeset_compare_Equivalence.
  - apply related_permut_PermutationA.
    + apply oeset_compare_Equivalence.
    + exact Hsemantic.
  - exact Hrows.
}
destruct (in_split (key_value, group) _ Hgroup)
  as [before [after Hsplit]].
rewrite Hsplit, !flat_map_app in Hflattened; cbn in Hflattened.
pose proof
  (NoDupA_app_right _ _
    (flat_map (fun item => snd item) before)
    (group ++ flat_map (fun item => snd item) after) Hflattened)
  as Htail.
exact
  (NoDupA_app_left _ _ group
    (flat_map (fun item => snd item) after) Htail).
Qed.

Lemma query_make_groups_member_NoDupA :
  forall env rows group_terms group,
    NoDupA
      (fun left right => Oeset.compare (OTuple TNull) left right = Eq)
      rows ->
    In group (@query_make_groups TNull env rows group_terms) ->
    NoDupA
      (fun left right => Oeset.compare (OTuple TNull) left right = Eq)
      group.
Proof.
intros env rows group_terms group Hrows Hgroup.
unfold query_make_groups in Hgroup.
destruct group_terms as [|term terms].
- destruct rows as [|row rows].
  + cbn in Hgroup.
    destruct Hgroup as [Hgroup|Hgroup]; [subst group; constructor|contradiction].
  + cbn [make_groups] in Hgroup.
    apply in_map_iff in Hgroup as [[key_value selected] [Hequal Hin]].
    cbn in Hequal; subst selected.
    eapply partition_member_NoDupA; eassumption.
- cbn [make_groups] in Hgroup.
  apply in_map_iff in Hgroup as [[key_value selected] [Hequal Hin]].
  cbn in Hequal; subst selected.
  eapply partition_member_NoDupA; eassumption.
Qed.

(** All rows in one query group evaluate the complete grouping-key vector to
    the same value. *)
Lemma query_make_groups_member_homogeneous :
  forall env rows group_terms group left right,
    In group (@query_make_groups TNull env rows group_terms) ->
    In left group ->
    In right group ->
    map
      (fun term => interp_aggterm TNull (env_t TNull env left) term)
      group_terms =
    map
      (fun term => interp_aggterm TNull (env_t TNull env right) term)
      group_terms.
Proof.
intros env rows group_terms group left right Hgroup Hleft Hright.
unfold query_make_groups in Hgroup.
destruct group_terms as [|term terms].
- destruct rows as [|row rows].
  + cbn in Hgroup.
    destruct Hgroup as [Hgroup|Hgroup]; [subst group; contradiction|contradiction].
  + cbn [make_groups] in Hgroup |- *.
    apply in_map_iff in Hgroup as [[key_value selected] [Hequal Hin]].
    cbn in Hequal; subst selected.
    pose proof
      (@Partition.partition_homogeneous_values
        _ _ _ _ _ _ _ Hin left Hleft) as Hleft_key.
    pose proof
      (@Partition.partition_homogeneous_values
        _ _ _ _ _ _ _ Hin right Hright) as Hright_key.
    now rewrite Hleft_key, Hright_key.
- cbn [make_groups] in Hgroup |- *.
  apply in_map_iff in Hgroup as [[key_value selected] [Hequal Hin]].
  cbn in Hequal; subst selected.
  pose proof
    (@Partition.partition_homogeneous_values
      _ _ _ _ _ _ _ Hin left Hleft) as Hleft_key.
  pose proof
    (@Partition.partition_homogeneous_values
      _ _ _ _ _ _ _ Hin right Hright) as Hright_key.
  now rewrite Hleft_key, Hright_key.
Qed.

Theorem query_distinct_group_finite_code_length_le :
  forall input distinct_rows env group_terms group
      (code : tuple TNull -> nat) domain_size,
    @query_same_rows_as_bag TNull distinct_rows
      (@query_distinct_bag TNull input) ->
    In group (@query_make_groups TNull env distinct_rows group_terms) ->
    (forall row, In row group -> (code row < domain_size)%nat) ->
    (forall left right,
      In left group ->
      In right group ->
      code left = code right ->
      Oeset.compare (OTuple TNull) left right = Eq) ->
    (List.length group <= domain_size)%nat.
Proof.
intros input distinct_rows env group_terms group code domain_size
  Hdistinct Hgroup Hrange Hinjective.
pose proof (query_distinct_bag_rows_NoDupA input distinct_rows Hdistinct)
  as Hdistinct_nodup.
pose proof
  (query_make_groups_member_NoDupA env distinct_rows group_terms group
    Hdistinct_nodup Hgroup) as Hgroup_nodup.
pose proof
  (NoDupA_map_injective_on _ _ group code Hgroup_nodup Hinjective)
  as Hcodes.
assert (Hinside : incl (map code group) (seq 0 domain_size)).
{
  intros value Hvalue.
  apply in_map_iff in Hvalue as [row [<- Hrow]].
  apply in_seq; split; [lia|now apply Hrange].
}
pose proof (NoDup_incl_length Hcodes Hinside) as Hlength.
now rewrite length_map, length_seq in Hlength.
Qed.

(** Binary-Z codes avoid ever constructing the potentially enormous finite
    domain as a [nat].  The proof converts a symbolic domain to [nat] only
    inside this generic lemma, uses the ordinary finite-sequence argument, and
    immediately transports the result back to [Z]. *)
Theorem query_distinct_group_finite_Z_code_length_le :
  forall input distinct_rows env group_terms group
      (code : tuple TNull -> Z) domain_size,
    @query_same_rows_as_bag TNull distinct_rows
      (@query_distinct_bag TNull input) ->
    In group (@query_make_groups TNull env distinct_rows group_terms) ->
    0 <= domain_size ->
    (forall row,
      In row group ->
      0 <= code row < domain_size) ->
    (forall left right,
      In left group ->
      In right group ->
      code left = code right ->
      Oeset.compare (OTuple TNull) left right = Eq) ->
    Z.of_nat (List.length group) <= domain_size.
Proof.
intros input distinct_rows env group_terms group code domain_size
  Hdistinct Hgroup Hdomain Hrange Hinjective.
pose proof (query_distinct_bag_rows_NoDupA input distinct_rows Hdistinct)
  as Hdistinct_nodup.
pose proof
  (query_make_groups_member_NoDupA env distinct_rows group_terms group
    Hdistinct_nodup Hgroup) as Hgroup_nodup.
assert (Hcodes : NoDup (map (fun row => Z.to_nat (code row)) group)).
{
  eapply NoDupA_map_injective_on; [exact Hgroup_nodup|].
  intros left right Hleft Hright Hequal.
  apply Hinjective; [exact Hleft|exact Hright|].
  apply Z2Nat.inj; [exact (proj1 (Hrange left Hleft))| |exact Hequal].
  exact (proj1 (Hrange right Hright)).
}
assert (Hinside :
  incl
    (map (fun row => Z.to_nat (code row)) group)
    (seq 0 (Z.to_nat domain_size))).
{
  intros value Hvalue.
  apply in_map_iff in Hvalue as [row [<- Hrow]].
  apply in_seq; split; [lia|].
  apply (proj1
    (Z2Nat.inj_lt (code row) domain_size
      (proj1 (Hrange row Hrow)) Hdomain)).
  exact (proj2 (Hrange row Hrow)).
}
pose proof (NoDup_incl_length Hcodes Hinside) as Hlength.
rewrite length_map, length_seq in Hlength.
apply Nat2Z.inj_le in Hlength.
rewrite Z2Nat.id in Hlength by exact Hdomain.
exact Hlength.
Qed.

(** Successful row projection emits exactly one row per input occurrence. *)
Section OutcomeLengths.

Context {T : Tuple.Rcd}.
Variable symbol_runtime_error :
  scalar_operator T -> list (option sql_runtime_error * value T) ->
  option sql_runtime_error.
Variable aggregate_runtime_error :
  aggregate T -> list (option sql_runtime_error * value T) ->
  option sql_runtime_error.

Lemma project_rows_success_length :
  forall env select_list rows output,
    @project_rows_outcome T symbol_runtime_error aggregate_runtime_error
      env select_list rows = SqlSuccess output ->
    List.length output = List.length rows.
Proof.
intros env select_list rows.
induction rows as [|row rows IH]; intro output; cbn.
- inversion 1; reflexivity.
- destruct (@eval_select_list_runtime_error T
    symbol_runtime_error aggregate_runtime_error
    (env_t T env row) select_list); [discriminate|].
  destruct (@project_rows_outcome T symbol_runtime_error
    aggregate_runtime_error env select_list rows) eqn:Htail;
    [|discriminate].
  inversion 1; subst output; cbn.
  specialize (IH l eq_refl); lia.
Qed.

Lemma project_rows_success_Forall :
  forall env select_list rows output
         (input_property output_property : tuple T -> Prop),
    Forall input_property rows ->
    (forall row,
      input_property row ->
      output_property
        (projection T (env_t T env row) (@Select_List T select_list))) ->
    @project_rows_outcome T symbol_runtime_error aggregate_runtime_error
      env select_list rows = SqlSuccess output ->
    Forall output_property output.
Proof.
intros env select_list rows.
induction rows as [|row rows IH];
  intros output input_property output_property Hrows Hproject Hout; cbn in Hout.
- inversion Hout; constructor.
- inversion Hrows as [|? ? Hrow Hrest]; subst.
  destruct (@eval_select_list_runtime_error T
    symbol_runtime_error aggregate_runtime_error
    (env_t T env row) select_list); [discriminate|].
  destruct (@project_rows_outcome T symbol_runtime_error
    aggregate_runtime_error env select_list rows) eqn:Htail;
    [|discriminate].
  inversion Hout; subst output.
  constructor.
  + now apply Hproject.
  + eapply IH; [exact Hrest|exact Hproject|reflexivity].
Qed.

Variable relname : Type.
Variable basesort : relname -> Fset.set (A T).
Variable instance : relname -> Febag.bag (Fecol.CBag (CTuple T)).
Variable unknown : Bool.b (B T).
Variable contains_nulls : tuple T -> bool.
Variable value_is_null : value T -> bool.

Lemma if_tuple_rows_success_true :
  forall (test : bool) (row : tuple T)
      (tail output : list (tuple T)),
    test = true ->
    (if test
     then SqlSuccess (row :: tail)
     else SqlSuccess tail) = SqlSuccess output ->
    output = row :: tail.
Proof.
intros test row tail output Htest Hout.
subst test; cbn in Hout; now injection Hout.
Qed.

Lemma if_tuple_rows_success_false :
  forall (test : bool) (row : tuple T)
      (tail output : list (tuple T)),
    test = false ->
    (if test
     then SqlSuccess (row :: tail)
     else SqlSuccess tail) = SqlSuccess output ->
    output = tail.
Proof.
intros test row tail output Htest Hout.
subst test; cbn in Hout; now injection Hout.
Qed.

Lemma filter_rows_success_length_le :
  forall env formula rows output,
    @eval_filter_rows_outcome T relname basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error value_is_null
      env formula rows (SqlSuccess output) ->
    (List.length output <= List.length rows)%nat.
Proof.
intros env formula rows.
induction rows as [|row rows IH]; intros output Hfilter.
- inversion Hfilter; subst; cbn; lia.
- inversion Hfilter; subst.
  match goal with
  | Htail : @eval_filter_rows_outcome _ _ _ _ _ _ _ _ _ _ _ rows ?tail |- _ =>
      destruct tail as [tail_rows|tail_error]
  end.
  + match goal with
    | Htail : @eval_filter_rows_outcome _ _ _ _ _ _ _ _ _ _ _
        ?remaining (SqlSuccess tail_rows) |- _ =>
        pose proof (IH tail_rows Htail) as Hlength
    end.
    destruct (Bool.is_true (B T) truth) eqn:Htruth.
    * pose proof (if_tuple_rows_success_true
        (Bool.is_true (B T) truth) row tail_rows output Htruth H2) as Hout.
      subst output; cbn; lia.
    * pose proof (if_tuple_rows_success_false
        (Bool.is_true (B T) truth) row tail_rows output Htruth H2) as Hout.
      subst output; cbn; lia.
  + cbn [filter_cons_outcome] in *; discriminate.
Qed.

Lemma filter_cons_outcome_success_Forall :
  forall truth row tail output (property : tuple T -> Prop),
    property row ->
    Forall property tail ->
    @filter_cons_outcome T truth row (SqlSuccess tail) = SqlSuccess output ->
    Forall property output.
Proof.
intros truth row tail output property Hrow Htail Houtput.
unfold filter_cons_outcome in Houtput.
destruct (Bool.is_true (B T) truth).
- injection Houtput as Hequal; subst output; now constructor.
- injection Houtput as Hequal; subst output; exact Htail.
Qed.

Lemma filter_rows_success_Forall :
  forall env formula rows output (property : tuple T -> Prop),
    @eval_filter_rows_outcome T relname basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error value_is_null
      env formula rows (SqlSuccess output) ->
    Forall property rows ->
    Forall property output.
Proof.
intros env formula rows.
induction rows as [|row rows IH]; intros output property Hfilter Hrows.
- inversion Hfilter; constructor.
- inversion Hrows as [|? ? Hrow Hrest]; subst.
  inversion Hfilter; subst.
  match goal with
  | Htail : @eval_filter_rows_outcome _ _ _ _ _ _ _ _ _ _ _ rows ?tail |- _ =>
      destruct tail as [tail_rows|tail_error]
  end.
  + eapply filter_cons_outcome_success_Forall.
    * exact Hrow.
    * match goal with
      | Htail : @eval_filter_rows_outcome _ _ _ _ _ _ _ _ _ _ _
          ?remaining (SqlSuccess tail_rows) |- _ =>
          exact (IH tail_rows property Htail Hrest)
      end.
    * eassumption.
  + cbn [filter_cons_outcome] in *; discriminate.
Qed.

Lemma filter_rows_success_exact_count :
  forall env formula rows output keep,
    (forall row truth,
      In row rows ->
      @eval_formula_expr_outcome T relname basesort instance unknown
        contains_nulls symbol_runtime_error aggregate_runtime_error
        value_is_null (env_t T env row) formula (SqlSuccess truth) ->
      Bool.is_true (B T) truth = keep row) ->
    @eval_filter_rows_outcome T relname basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error value_is_null
      env formula rows (SqlSuccess output) ->
    List.length output = List.length (filter keep rows).
Proof.
intros env formula rows.
induction rows as [|row rows IH]; intros output keep Hexact Hfilter.
- inversion Hfilter; reflexivity.
- inversion Hfilter; subst.
  match goal with
  | Htail : @eval_filter_rows_outcome _ _ _ _ _ _ _ _ _ _ _ rows ?tail |- _ =>
      destruct tail as [tail_rows|tail_error]
  end.
  + unfold filter_cons_outcome in *.
    pose proof (Hexact row truth (or_introl eq_refl) H3) as Hkeep.
    specialize (IH tail_rows keep
      (fun other observed Hother => Hexact other observed (or_intror _ Hother))
      H4).
    match goal with
    | H : (if Bool.is_true (B T) truth
           then SqlSuccess (row :: tail_rows)
           else SqlSuccess tail_rows) = SqlSuccess output |- _ =>
        rename H into Houtcome
    end.
    destruct (Bool.is_true (B T) truth) eqn:Htruth.
    * injection Houtcome as Houtput.
      assert (Hkeep_row : keep row = true) by exact (eq_sym Hkeep).
      subst output; cbn [filter]; rewrite Hkeep_row; cbn; lia.
    * injection Houtcome as Houtput.
      assert (Hkeep_row : keep row = false) by exact (eq_sym Hkeep).
      subst output; cbn [filter]; rewrite Hkeep_row; cbn; lia.
  + unfold filter_cons_outcome in *; discriminate.
Qed.

Lemma filter_rows_error_observable :
  forall env formula input input_rows error,
    @eval_query_expr_outcome T relname basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error value_is_null
      env input (SqlSuccess input_rows) ->
    @eval_filter_rows_outcome T relname basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error value_is_null
      env formula input_rows (SqlError error) ->
    @eval_query_expr_outcome T relname basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error value_is_null
      env (QExpr_Filter formula input) (SqlError error).
Proof.
intros env formula input input_rows error Hinput Hfilter.
eapply EQuery_FilterRows with (input_rows := input_rows).
- exact Hinput.
- exact Hfilter.
Qed.

Lemma eval_groups_success_length_le :
  forall env select_list group_terms having groups output,
    @eval_groups_outcome T relname basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error value_is_null
      env select_list group_terms having groups (SqlSuccess output) ->
    (List.length output <= List.length groups)%nat.
Proof.
intros env select_list group_terms having groups.
induction groups as [|group groups IH]; intros output Heval.
- inversion Heval; subst; cbn; lia.
- inversion Heval; subst.
  + match goal with
    | Htail : eval_groups_outcome _ _ _ _ _ _ _ _ _ _ _ groups
        (SqlSuccess output) |- _ =>
        pose proof (IH output Htail) as Hlength
    end.
    cbn; lia.
  + destruct tail as [tail_rows|tail_error].
    * unfold group_cons_outcome in H1.
      injection H1 as Houtput; subst output.
      match goal with
      | Htail : eval_groups_outcome _ _ _ _ _ _ _ _ _ _ _ groups
          (SqlSuccess tail_rows) |- _ =>
          pose proof (IH tail_rows Htail) as Hlength
      end.
      cbn; lia.
    * unfold group_cons_outcome in H1; discriminate.
Qed.

End OutcomeLengths.

(** A complete two-column INT32 key is functional when both strict equality
    predicates are true. Checking only one component would be unsound because
    neither component is unique on its own. *)
Definition postgres_int32_pair_equal_true
    (left_first left_second : value TNull)
    (right_first right_second : string)
    (row : tuple TNull) : bool :=
  andb
    (postgres_int32_equal_true left_first
      (dot TNull row (Attr_int32 right_first)))
    (postgres_int32_equal_true left_second
      (dot TNull row (Attr_int32 right_second))).

Lemma int32_composite_primary_key_true_matches_at_most_one :
  forall left_first_name left_second_name
      right_first_name right_second_name
      left_first_value left_second_value right_rows,
    value_conforms_attribute
      (Attr_int32 left_first_name) left_first_value ->
    value_conforms_attribute
      (Attr_int32 left_second_name) left_second_value ->
    rows_attribute_conform (Attr_int32 right_first_name) right_rows ->
    rows_attribute_conform (Attr_int32 right_second_name) right_rows ->
    primary_key_conforms
      [Attr_int32 right_first_name; Attr_int32 right_second_name] right_rows ->
    (List.length
      (filter
        (postgres_int32_pair_equal_true left_first_value left_second_value
          right_first_name right_second_name)
        right_rows) <= 1)%nat.
Proof.
intros left_first_name left_second_name
  right_first_name right_second_name
  left_first_value left_second_value right_rows
  Hleft_first Hleft_second Hright_first Hright_second Hprimary.
pose proof
  (int32_composite_primary_key_projection_nodup
    right_first_name right_second_name right_rows
    Hright_first Hright_second Hprimary) as Hkeys.
eapply NoDup_map_constant_filter_length_le_one with
  (key_of := project_row
    [Attr_int32 right_first_name; Attr_int32 right_second_name])
  (fixed := [left_first_value; left_second_value]); [exact Hkeys|].
intros row Hrow Hmatch.
unfold postgres_int32_pair_equal_true in Hmatch.
apply Bool.Bool.andb_true_iff in Hmatch as [Hfirst Hsecond].
rewrite !project_row_cons, project_row_nil.
f_equal.
- symmetry; eapply postgres_int32_equal_true_eq; eauto.
- f_equal; symmetry; eapply postgres_int32_equal_true_eq; eauto.
Qed.

(** A left-deep sequence of occurrence-preserving theta joins.  Each stage
    keeps at most one right occurrence for every possible left row.  This
    global formulation composes directly: no cardinality estimate, foreign
    key existence, or set quotient is hidden in the definition. *)
Definition functional_theta_stage (row : Type) : Type :=
  ((row -> row -> bool) * list row)%type.

Definition theta_stage_is_functional
    {row : Type} (stage : functional_theta_stage row) : Prop :=
  forall left_row,
    (List.length (filter (fst stage left_row) (snd stage)) <= 1)%nat.

Fixpoint functional_theta_join_chain
    (row : Type) (join : row -> row -> row)
    (left : list row) (stages : list (functional_theta_stage row))
    : list row :=
  match stages with
  | nil => left
  | (accept, right_rows) :: rest =>
      functional_theta_join_chain row join
        (theta_join_list row join accept left right_rows) rest
  end.

Theorem functional_theta_join_chain_length_le :
  forall (row : Type) (join : row -> row -> row) left stages,
    Forall theta_stage_is_functional stages ->
    (List.length (functional_theta_join_chain row join left stages) <=
      List.length left)%nat.
Proof.
intros row join left stages.
revert left.
induction stages as [|[accept right_rows] stages IH];
  intros left Hfunctional; cbn.
- apply Nat.le_refl.
- inversion Hfunctional as [|stage tail Hstage Htail]; subst.
  eapply Nat.le_trans.
  + now apply IH.
  + apply theta_join_list_functional_length_le.
    intros left_row _.
    exact (Hstage left_row).
Qed.

Lemma rows_attribute_conform_filter :
  forall attribute rows keep,
    rows_attribute_conform attribute rows ->
    rows_attribute_conform attribute (filter keep rows).
Proof.
intros attribute rows keep Hconforms row Hrow.
apply filter_In in Hrow as [Hrow _].
now apply Hconforms.
Qed.

Lemma NoDup_map_filter :
  forall (row key : Type) (key_of : row -> key) keep rows,
    NoDup (map key_of rows) ->
    NoDup (map key_of (filter keep rows)).
Proof.
intros row key key_of keep rows.
induction rows as [|first rows IH]; intros Hnodup; cbn; [constructor|].
inversion Hnodup as [|first_key rest_keys Hfirst Hrest]; subst.
destruct (keep first) eqn:Hkeep; cbn.
- constructor.
  + intros Hin.
    apply Hfirst.
    apply in_map_iff in Hin as [other [Hequal Hother]].
    apply filter_In in Hother as [Hother _].
    apply in_map_iff.
    exists other; auto.
  + now apply IH.
- now apply IH.
Qed.

Lemma primary_key_conforms_filter :
  forall primary_key rows keep,
    primary_key_conforms primary_key rows ->
    primary_key_conforms primary_key (filter keep rows).
Proof.
intros primary_key rows keep [Hnonempty [Hnonnull Hnodup]].
repeat split; [exact Hnonempty| |].
- intros row Hrow attribute Hattribute.
  apply filter_In in Hrow as [Hrow _].
  eapply Hnonnull; eauto.
- now apply NoDupA_map_filter.
Qed.

(** Fixed-first-key handoff. The caller supplies fact rows for one key value,
    then any number of functional dimension stages. Grouping cannot create
    occurrences, and the unfixed second key component ranges over at most the
    complete INT32 domain. *)
Theorem functional_chain_fixed_first_composite_int32_group_length_2_32 :
  forall first_name second_name facts keep stages fixed_first
      env group_terms group,
    rows_attribute_conform (Attr_int32 first_name) facts ->
    rows_attribute_conform (Attr_int32 second_name) facts ->
    primary_key_conforms
      [Attr_int32 first_name; Attr_int32 second_name] facts ->
    Forall
      (fun row => dot TNull row (Attr_int32 first_name) = fixed_first)
      (filter keep facts) ->
    Forall theta_stage_is_functional stages ->
    In group
      (@query_make_groups TNull env
        (functional_theta_join_chain
          (tuple TNull) (join_tuple TNull) (filter keep facts) stages)
        group_terms) ->
    Z.of_nat (List.length group) <= Z.pow 2 32.
Proof.
intros first_name second_name facts keep stages fixed_first
  env group_terms group Hfirst Hsecond Hprimary Hfixed
  Hfunctional Hgroup.
pose proof
  (query_make_groups_member_length_le env
    (functional_theta_join_chain
      (tuple TNull) (join_tuple TNull) (filter keep facts) stages)
    group_terms group Hgroup) as Hgroup_chain.
pose proof
  (functional_theta_join_chain_length_le
    (tuple TNull) (join_tuple TNull) (filter keep facts) stages Hfunctional)
  as Hchain_driver.
pose proof
  (int32_composite_primary_key_fixed_first_length
    first_name second_name (filter keep facts) fixed_first
    (rows_attribute_conform_filter _ _ _ Hfirst)
    (rows_attribute_conform_filter _ _ _ Hsecond)
    (primary_key_conforms_filter _ _ _ Hprimary)
    Hfixed) as Hdriver.
assert (Hgroup_domain : (List.length group <= int32_domain_size)%nat).
{ eapply Nat.le_trans; [exact Hgroup_chain|].
  eapply Nat.le_trans; eassumption. }
apply Nat2Z.inj_le in Hgroup_domain.
now rewrite int32_domain_size_is_two_power_32 in Hgroup_domain.
Qed.

(** Filtering a fact table and then adjoining only at-most-one dimension row at
    each stage cannot exceed the complete two-INT32 primary-key domain.  This is
    an occurrence bound: duplicates are retained, and a missing dimension match
    simply removes the corresponding fact occurrence. *)
Theorem functional_chain_composite_int32_occurrence_length_2_64 :
  forall first_name second_name facts keep stages,
    rows_attribute_conform (Attr_int32 first_name) facts ->
    rows_attribute_conform (Attr_int32 second_name) facts ->
    primary_key_conforms
      [Attr_int32 first_name; Attr_int32 second_name] facts ->
    Forall theta_stage_is_functional stages ->
    Z.of_nat
      (List.length
        (functional_theta_join_chain
          (tuple TNull) (join_tuple TNull) (filter keep facts) stages)) <=
      Z.pow 2 64.
Proof.
intros first_name second_name facts keep stages
  Hfirst Hsecond Hprimary Hfunctional.
pose proof
  (functional_theta_join_chain_length_le
    (tuple TNull) (join_tuple TNull) (filter keep facts) stages Hfunctional)
  as Hchain.
pose proof (filter_length keep facts) as Hfilter.
assert (List.length (filter keep facts) <= List.length facts)%nat as Hfilter_le
  by lia.
pose proof
  (int32_composite_primary_key_length_2_64
    first_name second_name facts Hfirst Hsecond Hprimary) as Hfacts.
apply Nat2Z.inj_le in Hchain.
apply Nat2Z.inj_le in Hfilter_le.
lia.
Qed.

(** Grouping cannot increase an individual occurrence list, so every group of
    the same functional producer inherits the complete fact-key bound. *)
Theorem functional_chain_composite_int32_group_length_2_64 :
  forall first_name second_name facts keep stages env group_terms group,
    rows_attribute_conform (Attr_int32 first_name) facts ->
    rows_attribute_conform (Attr_int32 second_name) facts ->
    primary_key_conforms
      [Attr_int32 first_name; Attr_int32 second_name] facts ->
    Forall theta_stage_is_functional stages ->
    In group
      (@query_make_groups TNull env
        (functional_theta_join_chain
          (tuple TNull) (join_tuple TNull) (filter keep facts) stages)
        group_terms) ->
    Z.of_nat (List.length group) <= Z.pow 2 64.
Proof.
intros first_name second_name facts keep stages env group_terms group
  Hfirst Hsecond Hprimary Hfunctional Hgroup.
pose proof
  (query_make_groups_member_length_le env
    (functional_theta_join_chain
      (tuple TNull) (join_tuple TNull) (filter keep facts) stages)
    group_terms group Hgroup) as Hgroup_chain.
apply Nat2Z.inj_le in Hgroup_chain.
pose proof
  (functional_chain_composite_int32_occurrence_length_2_64
    first_name second_name facts keep stages
    Hfirst Hsecond Hprimary Hfunctional) as Hchain.
eapply Z.le_trans; [exact Hgroup_chain|exact Hchain].
Qed.
