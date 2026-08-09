(************************************************************************************)
(** Exact occurrence-count bounds for successful relational query evaluation.       *)
(************************************************************************************)

From SQLFS Require Import
  SqlSyntax GenericInstance Values FTuples FiniteBag FiniteCollection
  FiniteSet OrderedSet Bool3 Join FlatData Env Formula Projection SqlOutcome
  SqlErrorSemantics SqlOrder SqlQuerySyntax SqlQuerySemantics SqlBagAbstraction SqlQueryFacts
  ListFacts ListPermut Partition ValueInteger SchemaConstraints.
From Logos.FormalSQL Require Import
  SchemaCardinality TNullSyntax.
From Stdlib Require Import List String ZArith NArith Lia SetoidList SetoidPermutation
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

(** The WHERE/HAVING decision obtained by interpreting a scalar predicate on
    row-local aggregate terms is proper for semantic tuple equality.  This is
    the reusable boundary needed by finite-bag filters; it preserves the SQL
    TRUE/non-TRUE decision without identifying FALSE with UNKNOWN as values. *)
Definition tnull_predicate_keep
    (env : Env.env TNull) (predicate : predicate TNull)
    (arguments : list (@aggterm TNull)) (row : tuple TNull) : bool :=
  Bool.is_true (B TNull)
    (interp_predicate TNull predicate
      (map (@interp_aggterm TNull (env_t TNull env row)) arguments)).

Lemma tnull_predicate_keep_proper :
  forall env predicate arguments,
    tuple_predicate_proper
      (tnull_predicate_keep env predicate arguments).
Proof.
intros env predicate arguments left right Hequal.
unfold tnull_predicate_keep.
f_equal; f_equal.
apply map_ext_in.
intros argument Hargument.
apply Interp.interp_aggterm_eq, Env.env_t_eq_2.
exact Hequal.
Qed.

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

(** Absence is a statement about a row's observable labels, not about the
    default value returned by [dot] outside that support. *)
Definition row_attribute_absent
    (attribute : attribute TNull) (row : tuple TNull) : Prop :=
  (attribute inS? labels TNull row) = false.

Lemma row_attribute_absent_proper :
  forall attribute,
    tuple_property_proper (row_attribute_absent attribute).
Proof.
intros attribute left right Hequal.
pose proof (tuple_eq_labels TNull left right Hequal) as Hlabels.
unfold row_attribute_absent.
rewrite (Fset.mem_eq_2 _ _ _ Hlabels).
tauto.
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

(** Every stored row has exactly the labels of its table sort.  Hence a label
    absent from that sort is absent from every observable representative of
    the table bag.  This core statement needs only value/schema conformance of
    the actual database; in particular, it is independent of NULL values and
    table constraints. *)
Theorem query_same_rows_as_table_absent_attribute :
  forall actual relation attribute rows,
    database_values_conform actual ->
    (attribute inS? @_basesort TNull actual relation) = false ->
    @query_same_rows_as_bag TNull rows
      (@_instance TNull actual relation) ->
    Forall (row_attribute_absent attribute) rows.
Proof.
intros actual relation attribute rows Hvalues Habsent Hrows.
eapply query_same_rows_as_bag_Forall_between with
  (first := instance_rows actual relation)
  (bag := @_instance TNull actual relation).
- apply row_attribute_absent_proper.
- unfold instance_rows; apply query_elements_same_rows_as_bag.
- exact Hrows.
- rewrite Forall_forall; intros row Hrow.
  specialize (Hvalues relation row Hrow) as [Hlabels _].
  unfold row_attribute_absent.
  rewrite (Fset.mem_eq_2 _ _ _ Hlabels).
  exact Habsent.
Qed.

(** Schema-facing form of the absence bridge.  It accepts absence in the
    expected schema and transports it to the actual table sort. *)
Theorem query_same_rows_as_conforming_table_absent_attribute :
  forall expected constraints actual relation attribute rows,
    database_conforms_schema expected constraints actual ->
    (attribute inS? @_basesort TNull expected relation) = false ->
    @query_same_rows_as_bag TNull rows
      (@_instance TNull actual relation) ->
    Forall (row_attribute_absent attribute) rows.
Proof.
intros expected constraints actual relation attribute rows
  Hschema Habsent Hrows.
eapply query_same_rows_as_table_absent_attribute.
- now apply
    (database_conforms_schema_values expected constraints actual Hschema).
- pose proof
    (database_conforms_schema_basesort
      expected constraints actual Hschema relation) as Hsort.
  rewrite (Fset.mem_eq_2 _ _ _ Hsort).
  exact Habsent.
- exact Hrows.
Qed.

(** Successful table-leaf form of the schema-facing bridge.  The explicit
    output-sort equality is the same admissibility evidence used by the table
    evaluator; no assumption is made about whether present cells are NULL. *)
Theorem query_expr_table_success_rows_absent_attribute :
  forall expected constraints actual relation attribute outputs env rows
      unknown symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule,
    database_conforms_schema expected constraints actual ->
    (attribute inS? @_basesort TNull expected relation) = false ->
    @query_outputs_sort TNull outputs =S=
      @_basesort TNull actual relation ->
    @eval_query_expr_outcome TNull relname
      (@_basesort TNull actual) (@_instance TNull actual)
      unknown symbol_runtime_error aggregate_runtime_error
      value_is_null boolean_schedule env
      (@QExpr_Table TNull relname outputs relation)
      (SqlSuccess rows) ->
    Forall (row_attribute_absent attribute) rows.
Proof.
intros expected constraints actual relation attribute outputs env rows
  unknown symbol_runtime_error aggregate_runtime_error value_is_null
  boolean_schedule
  Hschema Habsent Hsort Hrows.
apply eval_query_expr_table_success_iff in Hrows.
unfold query_table_bag in Hrows.
rewrite Hsort in Hrows.
eapply query_same_rows_as_conforming_table_absent_attribute;
  eassumption.
Qed.

(** A conforming schema guarantees that every declared table attribute is
    present and has a value of the declared SQL type in every observable row.
    This bridge is deliberately nullable-safe: it uses no table constraint and
    makes no [NOT NULL] claim. *)
Theorem query_same_rows_as_conforming_table_present_attribute :
  forall expected constraints actual relation attribute rows,
    database_conforms_schema expected constraints actual ->
    attribute inS (@_basesort TNull expected relation) ->
    @query_same_rows_as_bag TNull rows
      (@_instance TNull actual relation) ->
    Forall (row_attribute_present_conforms attribute) rows.
Proof.
intros expected constraints actual relation attribute rows
  Hschema Hattribute Hrows.
eapply query_same_rows_as_bag_Forall_between with
  (first := instance_rows actual relation)
  (bag := @_instance TNull actual relation).
- apply row_attribute_present_conforms_proper.
- unfold instance_rows; apply query_elements_same_rows_as_bag.
- exact Hrows.
- exact
    (database_conforms_schema_rows_attribute_present
      expected constraints actual relation attribute Hschema Hattribute).
Qed.

(** Lift the nullable-safe schema fact through a successful table leaf.  The
    explicit output-sort equality is the query-level evidence that the leaf
    denotes the actual table schema. *)
Theorem query_expr_table_success_rows_present_conform_attribute :
  forall expected constraints actual relation attribute outputs env rows
      unknown symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule,
    database_conforms_schema expected constraints actual ->
    attribute inS (@_basesort TNull expected relation) ->
    @query_outputs_sort TNull outputs =S=
      @_basesort TNull actual relation ->
    @eval_query_expr_outcome TNull relname
      (@_basesort TNull actual) (@_instance TNull actual)
      unknown symbol_runtime_error aggregate_runtime_error
      value_is_null boolean_schedule env
      (@QExpr_Table TNull relname outputs relation)
      (SqlSuccess rows) ->
    Forall (row_attribute_present_conforms attribute) rows.
Proof.
intros expected constraints actual relation attribute outputs env rows
  unknown symbol_runtime_error aggregate_runtime_error value_is_null
  boolean_schedule
  Hschema Hattribute Hsort Hrows.
apply eval_query_expr_table_success_iff in Hrows.
unfold query_table_bag in Hrows.
rewrite Hsort in Hrows.
eapply query_same_rows_as_conforming_table_present_attribute;
  eassumption.
Qed.

(** One-row nullable-safe specialization for generated table metadata.  As in
    the NOT NULL variant below, the generated output-sort equality is stated
    over the expected schema and transported once to the actual conforming
    database. *)
Theorem query_expr_table_success_row_present_conform_attribute_generated_sort :
  forall expected constraints actual relation attribute outputs env rows row
      unknown symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule,
    database_conforms_schema expected constraints actual ->
    attribute inS (@_basesort TNull expected relation) ->
    @_basesort TNull expected relation =S=
      @query_outputs_sort TNull outputs ->
    @eval_query_expr_outcome TNull relname
      (@_basesort TNull actual) (@_instance TNull actual)
      unknown symbol_runtime_error aggregate_runtime_error
      value_is_null boolean_schedule env
      (@QExpr_Table TNull relname outputs relation)
      (SqlSuccess rows) ->
    In row rows ->
    row_attribute_present_conforms attribute row.
Proof.
intros expected constraints actual relation attribute outputs env rows row
  unknown symbol_runtime_error aggregate_runtime_error value_is_null
  boolean_schedule
  Hschema Hattribute Hgenerated_sort Hrows Hrow.
assert (Hactual_sort :
  @query_outputs_sort TNull outputs =S= @_basesort TNull actual relation).
{
  pose proof
    (database_conforms_schema_basesort
      expected constraints actual Hschema relation) as Hdatabase_sort.
  rewrite Fset.equal_spec in Hgenerated_sort, Hdatabase_sort |- *.
  intro candidate.
  rewrite <- (Hgenerated_sort candidate).
  symmetry; exact (Hdatabase_sort candidate).
}
pose proof
  (query_expr_table_success_rows_present_conform_attribute
    expected constraints actual relation attribute outputs env rows
    unknown symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule
    Hschema Hattribute Hactual_sort Hrows) as Hall.
rewrite Forall_forall in Hall.
exact (Hall row Hrow).
Qed.

(** A conforming table's typed NOT NULL column remains typed and non-NULL in
    every ordered representative of its bag.  This is the safe
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

(** Lift the schema fact above directly through a successful [QExpr_Table]
    observation.  The resolved output order must denote the table's schema;
    this is precisely the leaf obligation imposed by query admissibility. *)
Theorem query_expr_table_success_rows_conform_attribute :
  forall expected constraints actual constraint attribute outputs env rows
      unknown symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule,
    database_conforms_schema expected constraints actual ->
    In constraint constraints ->
    attribute inS
      (@_basesort TNull expected (constraint_relation constraint)) ->
    In attribute (constraint_not_null constraint) ->
    @query_outputs_sort TNull outputs =S=
      @_basesort TNull actual (constraint_relation constraint) ->
    @eval_query_expr_outcome TNull relname
      (@_basesort TNull actual) (@_instance TNull actual)
      unknown symbol_runtime_error aggregate_runtime_error
      value_is_null boolean_schedule env
      (@QExpr_Table TNull relname outputs
        (constraint_relation constraint))
      (SqlSuccess rows) ->
    Forall (row_attribute_present_nonnull_conforms attribute) rows.
Proof.
intros expected constraints actual constraint attribute outputs env rows
  unknown symbol_runtime_error aggregate_runtime_error value_is_null
  boolean_schedule
  Hschema Hconstraint Hattribute Hnot_null Hsort Hrows.
inversion Hrows; subst.
unfold query_table_bag in *.
rewrite Hsort in *.
eapply query_same_rows_as_conforming_table_attribute;
  eassumption.
Qed.

(** Agent-facing one-row specialization of the table/schema bridge.  Generated
    table metadata describes the expected schema, whereas evaluation happens
    in the conforming actual database.  This theorem performs that basesort
    transport once and returns the exact property needed by scalar proofs; it
    neither inspects a generated query nor guesses a schema constraint. *)
Theorem query_expr_table_success_row_conform_attribute_generated_sort :
  forall expected constraints actual constraint attribute outputs env rows row
      unknown symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule,
    database_conforms_schema expected constraints actual ->
    In constraint constraints ->
    attribute inS
      (@_basesort TNull expected (constraint_relation constraint)) ->
    In attribute (constraint_not_null constraint) ->
    @_basesort TNull expected (constraint_relation constraint) =S=
      @query_outputs_sort TNull outputs ->
    @eval_query_expr_outcome TNull relname
      (@_basesort TNull actual) (@_instance TNull actual)
      unknown symbol_runtime_error aggregate_runtime_error
      value_is_null boolean_schedule env
      (@QExpr_Table TNull relname outputs
        (constraint_relation constraint))
      (SqlSuccess rows) ->
    In row rows ->
    row_attribute_present_nonnull_conforms attribute row.
Proof.
intros expected constraints actual constraint attribute outputs env rows row
  unknown symbol_runtime_error aggregate_runtime_error value_is_null
  boolean_schedule
  Hschema Hconstraint Hattribute Hnot_null Hgenerated_sort Hrows Hrow.
assert (Hactual_sort :
  @query_outputs_sort TNull outputs =S=
    @_basesort TNull actual (constraint_relation constraint)).
{
  pose proof
    (database_conforms_schema_basesort
      expected constraints actual Hschema
      (constraint_relation constraint)) as Hdatabase_sort.
  rewrite Fset.equal_spec in Hgenerated_sort, Hdatabase_sort |- *.
  intro candidate.
  rewrite <- (Hgenerated_sort candidate).
  symmetry; exact (Hdatabase_sort candidate).
}
pose proof
  (query_expr_table_success_rows_conform_attribute
    expected constraints actual constraint attribute outputs env rows
    unknown symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule
    Hschema Hconstraint Hattribute Hnot_null Hactual_sort Hrows) as Hall.
rewrite Forall_forall in Hall.
exact (Hall row Hrow).
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

(** A non-aggregate GROUP BY expression observes in the grouped environment
    exactly the value recorded for that expression in every member row's
    [query_grouping_key].  The premise that the expression is a grouping term
    is essential: arbitrary row expressions need not be constant on a group. *)
Lemma query_group_env_grouping_expression_member :
  forall env rows group_terms group row expression,
    In group (@query_make_groups TNull env rows group_terms) ->
    In row group ->
    In (A_Expr TNull expression) group_terms ->
    interp_aggterm TNull
      (env_g TNull env (@Group_By TNull group_terms) group)
      (A_Expr TNull expression) =
    interp_aggterm TNull (env_t TNull env row)
      (A_Expr TNull expression).
Proof.
intros env rows group_terms group row expression Hgroup Hrow Hexpression.
case_eq (ListSort.quicksort (OTuple TNull) group).
- intro Hsorted.
  pose proof (ListSort.length_quicksort (OTuple TNull) group) as Hlength.
  rewrite Hsorted in Hlength.
  destruct group as [|first rest]; [contradiction|discriminate Hlength].
- intros representative sorted Hsorted.
  assert (Hrepresentative : In representative group).
  {
    rewrite (ListSort.In_quicksort (OTuple TNull)), Hsorted.
    now left.
  }
  pose proof
    (query_make_groups_member_homogeneous
      env rows group_terms group representative row
      Hgroup Hrepresentative Hrow) as Hkeys.
  assert (Hexpression_value :
    interp_aggterm TNull (env_t TNull env representative)
      (A_Expr TNull expression) =
    interp_aggterm TNull (env_t TNull env row)
      (A_Expr TNull expression)).
  {
    induction group_terms as [|term terms IH] in Hkeys, Hexpression |- *.
    - contradiction.
    - cbn in Hkeys.
      injection Hkeys as Hterm Hterms.
      destruct Hexpression as [Hexpression|Hexpression].
      + now subst term.
      + now apply (IH Hexpression Hterms).
  }
  change
    (interp_funterm TNull
      (env_g TNull env (@Group_By TNull group_terms) group) expression =
     interp_funterm TNull (env_t TNull env row) expression).
  unfold env_g.
  rewrite Hsorted.
  etransitivity.
  + exact
      (Interp.interp_funterm_homogeneous_nil TNull
        (labels TNull representative) (@Group_By TNull group_terms) group
        (labels TNull representative) (@Group_Fine TNull)
        representative sorted env expression Hsorted).
  + exact Hexpression_value.
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
Variable relname : Type.
Variable basesort : relname -> Fset.set (A T).
Variable instance : relname -> Febag.bag (Fecol.CBag (CTuple T)).
Variable unknown : Bool.b (B T).
Variable symbol_runtime_error :
  scalar_operator T -> list (option sql_runtime_error * value T) ->
  option sql_runtime_error.
Variable aggregate_runtime_error :
  aggregate T -> list (option sql_runtime_error * value T) ->
  option sql_runtime_error.
Variable value_is_null : value T -> bool.
Variable boolean_schedule : boolean_site -> boolean_evaluation_order.

Lemma project_rows_success_length :
  forall env select_list rows output,
    @eval_project_rows_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule env select_list rows (SqlSuccess output) ->
    List.length output = List.length rows.
Proof.
intros env select_list rows output Heval.
destruct (eval_project_rows_success_pairs Heval)
  as [pairs [Hinput [Houtput _]]].
rewrite <- Hinput, <- Houtput, !length_map; reflexivity.
Qed.

Lemma project_rows_success_Forall :
  forall env select_list rows output
         (input_property output_property : tuple T -> Prop),
    Forall input_property rows ->
    (forall input_row output_row,
      input_property input_row ->
      @project_row_success T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env select_list input_row output_row ->
      output_property output_row) ->
    @eval_project_rows_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule env select_list rows (SqlSuccess output) ->
    Forall output_property output.
Proof.
intros env select_list rows output input_property output_property
  Hrows Hproject Hout.
destruct (eval_project_rows_success_pairs Hout)
  as [pairs [Hinput [Houtput Hpairs]]].
rewrite <- Houtput; apply Forall_map.
rewrite Forall_forall in Hrows, Hpairs |- *.
intros [input_row output_row] Hpair.
apply Hproject with (input_row := input_row).
- apply Hrows; rewrite <- Hinput.
  now apply in_map with (f := @fst (tuple T) (tuple T)) in Hpair.
- apply Hpairs in Hpair; cbn in Hpair; exact Hpair.
Qed.

(** A successful row-map query emits exactly one output occurrence for each
    occurrence in the child success selected by the parent derivation.  The
    existential child keeps the statement valid for relational, scheduled
    evaluation without asserting determinism or excluding error outcomes. *)
Lemma eval_query_expr_row_map_success_length :
  forall env outputs row_map input output,
    @eval_query_expr_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule env (QExpr_RowMap outputs row_map input)
      (SqlSuccess output) ->
    exists input_rows,
      @eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env input (SqlSuccess input_rows) /\
      List.length output = List.length input_rows.
Proof.
intros env outputs row_map input output Houtput.
apply eval_query_expr_row_map_success_iff in Houtput.
destruct Houtput as [input_rows [Hinput Hmap]].
exists input_rows; split; [exact Hinput|].
apply row_map_rows_outcome_success_map in Hmap.
subst output; now rewrite length_map.
Qed.

(** A compositional occurrence bound for every successful ordered observation
    of a query.  This contract deliberately does not claim determinism or
    runtime safety: errors remain possible outcomes, and every successful
    representative must satisfy the bound. *)
Definition query_success_length_le
    (env : Env.env T) (query : query_expr T relname) (bound : nat) : Prop :=
  forall rows,
    @eval_query_expr_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule env query (SqlSuccess rows) ->
    (List.length rows <= bound)%nat.

(** Convert the bag equality carried by a successful reset operator into the
    corresponding occurrence count.  Keeping this small bridge local to the
    cardinality theory avoids exposing canonical [Febag.elements] lists to
    operator-level proofs. *)
Lemma query_same_rows_as_bag_length_N :
  forall rows bag,
    @query_same_rows_as_bag T rows bag ->
    N.of_nat (List.length rows) =
      Febag.cardinal (Fecol.CBag (CTuple T)) bag.
Proof.
intros rows bag Hrows.
unfold query_same_rows_as_bag, query_rows_bag in Hrows.
assert (Hcardinal :
  Febag.cardinal (Fecol.CBag (CTuple T))
    (Febag.mk_bag (Fecol.CBag (CTuple T)) rows) =
  Febag.cardinal (Fecol.CBag (CTuple T)) bag).
{ now apply Febag.cardinal_eq. }
now rewrite Febag.cardinal_mk_bag in Hcardinal.
Qed.

Lemma query_same_rows_as_bag_length_le :
  forall rows bag bound,
    @query_same_rows_as_bag T rows bag ->
    (Febag.cardinal (Fecol.CBag (CTuple T)) bag <=
      N.of_nat bound)%N ->
    (List.length rows <= bound)%nat.
Proof.
intros rows bag bound Hrows Hbound.
apply (proj1 (Nat.compare_le_iff _ _)).
rewrite Nat2N.inj_compare.
apply (proj2 (N.compare_le_iff _ _)).
rewrite (query_same_rows_as_bag_length_N rows bag Hrows).
exact Hbound.
Qed.

(** A query that has no successful outcome satisfies every successful-result
    bound vacuously.  This does not erase its explicit SQL error outcome. *)
Lemma query_success_length_le_error :
  forall env outputs error bound,
    query_success_length_le env (QExpr_Error outputs error) bound.
Proof.
intros env outputs error bound rows Hrows.
apply query_error_has_no_success in Hrows; contradiction.
Qed.

(** VALUES exposes exactly its declared bag. *)
Lemma query_success_length_le_values :
  forall env outputs values bound,
    (Febag.cardinal (Fecol.CBag (CTuple T)) values <=
      N.of_nat bound)%N ->
    query_success_length_le env (QExpr_Values outputs values) bound.
Proof.
intros env outputs values bound Hbound rows Hrows.
inversion Hrows; subst.
eapply query_same_rows_as_bag_length_le; eassumption.
Qed.

(** A well-sorted table leaf turns a certified instance-bag bound into the
    uniform query-success bound.  In particular, generated fixed-witness
    cardinality facts can be consumed here without exposing any concrete row
    value or the canonical ordering of bag elements. *)
Lemma query_success_length_le_table :
  forall env outputs table bound,
    @query_outputs_sort T outputs =S= basesort table ->
    (Febag.cardinal (Fecol.CBag (CTuple T)) (instance table) <=
      N.of_nat bound)%N ->
    query_success_length_le env (QExpr_Table outputs table) bound.
Proof.
intros env outputs table bound Hsort Hbound rows Hrows.
apply eval_query_expr_table_success_iff in Hrows.
unfold query_table_bag in Hrows.
rewrite Hsort in Hrows.
pose proof
  (proj1 (@query_same_rows_as_bag_iff_bag_eq T rows (instance table)) Hrows)
  as Hbag.
unfold bag_eq, rows_bag, SqlBagAbstraction.BTupleT in Hbag.
assert (Hcardinal :
  Febag.cardinal (Fecol.CBag (CTuple T))
    (Febag.mk_bag (Fecol.CBag (CTuple T)) rows) =
  Febag.cardinal (Fecol.CBag (CTuple T)) (instance table)).
{ now apply Febag.cardinal_eq. }
rewrite Febag.cardinal_mk_bag in Hcardinal.
rewrite <- Hcardinal in Hbound.
apply (proj1 (Nat.compare_le_iff _ _)).
rewrite Nat2N.inj_compare.
apply (proj2 (N.compare_le_iff _ _)).
exact Hbound.
Qed.

(** Projection emits exactly one row per successfully projected input row, so
    it transports any successful-occurrence bound without requiring the query
    to be deterministic.  Projection errors are outside this success-only
    contract and are not erased. *)
Lemma query_success_length_le_project :
  forall env select_list input bound,
    query_success_length_le env input bound ->
    query_success_length_le env (QExpr_Project select_list input) bound.
Proof.
intros env select_list input bound Hinput output Houtput.
apply eval_query_expr_project_success_iff in Houtput.
destruct Houtput as [input_rows [Hinput_rows Hproject]].
pose proof
  (project_rows_success_length env select_list input_rows output Hproject)
  as Hlength.
rewrite Hlength.
now apply Hinput.
Qed.

(** A successful deterministic row adapter emits exactly one output
    occurrence per selected child occurrence. *)
Lemma query_success_length_le_row_map :
  forall env outputs row_map input bound,
    query_success_length_le env input bound ->
    query_success_length_le env
      (QExpr_RowMap outputs row_map input) bound.
Proof.
intros env outputs row_map input bound Hinput output Houtput.
destruct
  (eval_query_expr_row_map_success_length
    env outputs row_map input output Houtput)
  as [input_rows [Hinput_rows Hlength]].
rewrite Hlength; now apply Hinput.
Qed.

(** OFFSET subtracts the same prefix length from every successful input
    observation. *)
Lemma query_success_length_le_offset :
  forall env offset input bound,
    query_success_length_le env input bound ->
    query_success_length_le env
      (QExpr_Offset offset input) (bound - offset).
Proof.
intros env offset input bound Hinput output Houtput.
apply eval_query_expr_offset_success_iff in Houtput.
destruct Houtput as [input_rows [Hinput_rows Houtput]].
subst output.
rewrite length_skipn.
apply Nat.sub_le_mono_r.
now apply Hinput.
Qed.

(** If every successful child observation is no longer than the skipped
    prefix, every successful OFFSET observation is the empty list.  This is a
    universal statement over possible ordered results, not a claim about one
    selected execution. *)
Lemma query_offset_success_nil_of_input_length_le :
  forall env offset input,
    query_success_length_le env input offset ->
    forall output,
      @eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env (QExpr_Offset offset input) (SqlSuccess output) ->
      output = nil.
Proof.
intros env offset input Hinput output Houtput.
pose proof
  (query_success_length_le_offset env offset input offset Hinput
    output Houtput) as Hlength.
apply (proj1 (length_zero_iff_nil output)).
cbn in Hlength; lia.
Qed.

(** FETCH retains at most both the requested count and a transported child
    bound. *)
Lemma query_success_length_le_fetch :
  forall env count input bound,
    query_success_length_le env input bound ->
    query_success_length_le env
      (QExpr_Fetch count input) (Nat.min count bound).
Proof.
intros env count input bound Hinput output Houtput.
apply eval_query_expr_fetch_success_iff in Houtput.
destruct Houtput as [input_rows [Hinput_rows Houtput]].
subst output.
rewrite length_firstn.
apply Nat.min_le_compat_l.
now apply Hinput.
Qed.

(** FETCH alone supplies a count bound, even when the child has no known
    cardinality bound. *)
Lemma query_success_length_le_fetch_count :
  forall env count input,
    query_success_length_le env (QExpr_Fetch count input) count.
Proof.
intros env count input output Houtput.
apply eval_query_expr_fetch_success_iff in Houtput.
destruct Houtput as [input_rows [Hinput_rows Houtput]].
subst output.
rewrite length_firstn.
apply Nat.le_min_l.
Qed.

(** ORDER BY changes only the legal representative order, never the number of
    row occurrences. *)
Lemma query_success_length_le_order_by :
  forall env keys input bound,
    query_success_length_le env input bound ->
    query_success_length_le env (QExpr_OrderBy keys input) bound.
Proof.
intros env keys input bound Hinput output Houtput.
apply eval_query_expr_order_by_success_iff in Houtput.
destruct Houtput as [input_rows [Hinput_rows [Hsame Hordered]]].
assert (Hlength : List.length output = List.length input_rows).
{
  apply Nat2N.inj.
  rewrite (query_same_rows_as_bag_length_N output
    (query_rows_bag input_rows) Hsame).
  unfold query_rows_bag; rewrite Febag.cardinal_mk_bag; reflexivity.
}
rewrite Hlength; now apply Hinput.
Qed.

(** Finite-set construction can only remove occurrences from its source
    list.  This is the cardinality fact used by SQL DISTINCT. *)
Lemma tuple_mk_set_cardinal_le :
  forall rows : list (tuple T),
    (Feset.cardinal (Fecol.CSet (CTuple T))
      (Feset.mk_set (Fecol.CSet (CTuple T)) rows) <=
     List.length rows)%nat.
Proof.
induction rows as [|row rows IH].
- rewrite Feset.mk_set_unfold, Feset.cardinal_spec, Feset.elements_empty.
  reflexivity.
- rewrite Feset.mk_set_unfold.
  set (tail := Feset.mk_set (Fecol.CSet (CTuple T)) rows).
  assert (Hequal :
    Feset.equal (Fecol.CSet (CTuple T))
      (Feset.add (Fecol.CSet (CTuple T)) row tail)
      (Feset.union (Fecol.CSet (CTuple T))
        (Feset.singleton (Fecol.CSet (CTuple T)) row) tail) = true).
  {
    rewrite Feset.equal_spec; intro candidate.
    rewrite Feset.add_spec, Feset.mem_union, Feset.singleton_spec.
    reflexivity.
  }
  assert (Hcardinal :
    Feset.cardinal (Fecol.CSet (CTuple T))
      (Feset.add (Fecol.CSet (CTuple T)) row tail) =
    Feset.cardinal (Fecol.CSet (CTuple T))
      (Feset.union (Fecol.CSet (CTuple T))
        (Feset.singleton (Fecol.CSet (CTuple T)) row) tail)).
  {
    rewrite 2 Feset.cardinal_spec.
    now apply
      (comparelA_eq_length_eq _ _ _
        (Feset.elements_spec1 _ _ _ Hequal)).
  }
  rewrite Hcardinal.
  pose proof
    (Feset.cardinal_union_
      (Fecol.CSet (CTuple T))
      (Feset.singleton (Fecol.CSet (CTuple T)) row) tail) as Hunion.
  rewrite Feset.cardinal_singleton in Hunion.
  assert (Hle :
    (Feset.cardinal (Fecol.CSet (CTuple T))
       (Feset.union (Fecol.CSet (CTuple T))
         (Feset.singleton (Fecol.CSet (CTuple T)) row) tail) <=
     1 + Feset.cardinal (Fecol.CSet (CTuple T)) tail)%nat) by lia.
  eapply Nat.le_trans; [exact Hle|].
  unfold tail; cbn; lia.
Qed.

Lemma query_distinct_bag_cardinal_le :
  forall input,
    (Febag.cardinal (Fecol.CBag (CTuple T))
       (@query_distinct_bag T input) <=
     Febag.cardinal (Fecol.CBag (CTuple T)) input)%N.
Proof.
intro input.
unfold query_distinct_bag.
rewrite Febag.cardinal_mk_bag.
unfold Febag.cardinal.
rewrite <- Feset.cardinal_spec.
apply (proj1 (N.compare_le_iff _ _)).
rewrite <- Nat2N.inj_compare.
apply (proj2 (Nat.compare_le_iff _ _)).
apply tuple_mk_set_cardinal_le.
Qed.

Lemma query_success_length_le_distinct :
  forall env input bound,
    query_success_length_le env input bound ->
    query_success_length_le env (QExpr_Distinct input) bound.
Proof.
intros env input bound Hinput output Houtput.
apply eval_query_expr_distinct_success_iff in Houtput.
destruct Houtput as [input_rows [Hinput_rows Hsame]].
eapply Nat.le_trans; [|exact (Hinput input_rows Hinput_rows)].
apply (proj1 (Nat.compare_le_iff _ _)).
rewrite Nat2N.inj_compare.
apply (proj2 (N.compare_le_iff _ _)).
rewrite (query_same_rows_as_bag_length_N output _ Hsame).
eapply N.le_trans; [apply query_distinct_bag_cardinal_le|].
unfold rows_bag; rewrite Febag.cardinal_mk_bag; apply N.le_refl.
Qed.

(** A constructor-independent cardinality contract for SET operations.  It
    exposes only the deterministic bag transformer already defined by the
    exact semantics, including its malformed-sort empty fallback. *)
Definition query_set_cardinality_bound
    (operation : set_op) (left right : query_expr T relname)
    (left_bound right_bound output_bound : nat) : Prop :=
  forall left_bag right_bag,
    (Febag.cardinal (Fecol.CBag (CTuple T)) left_bag <=
      N.of_nat left_bound)%N ->
    (Febag.cardinal (Fecol.CBag (CTuple T)) right_bag <=
      N.of_nat right_bound)%N ->
    (Febag.cardinal (Fecol.CBag (CTuple T))
      (query_set_bag_function operation left right left_bag right_bag) <=
      N.of_nat output_bound)%N.

(** Pointwise multiplicity inclusion controls the total number of bag
    occurrences.  This is deliberately a multiset fact: unlike a finite-set
    cardinality argument, it remains valid when either SQL input contains
    duplicate rows. *)
Lemma oeset_pointwise_nb_occ_le_length :
  forall (A : Type) (ordered : Oeset.Rcd A) (left right : list A),
    (forall value,
      (Oeset.nb_occ ordered value left <=
       Oeset.nb_occ ordered value right)%N) ->
    (List.length left <= List.length right)%nat.
Proof.
intros A ordered left.
induction left as [|first left IH]; intros right Hocc; cbn; [lia|].
assert (Hpresent : Oeset.mem_bool ordered first right = true).
{
  apply Oeset.nb_occ_mem; intro Hzero.
  specialize (Hocc first).
  rewrite (Oeset.nb_occ_unfold ordered first (first :: left)),
    Oeset.compare_eq_refl, Hzero in Hocc.
  lia.
}
apply Oeset.mem_bool_true_iff in Hpresent.
destruct Hpresent as [representative [Hequal Hin]].
destruct (in_split representative right Hin) as [before [after Hright]].
subst right.
assert (Htail :
  (List.length left <= List.length (before ++ after))%nat).
{
  apply IH; intro value.
  rewrite Oeset.nb_occ_app.
  specialize (Hocc value).
  rewrite (Oeset.nb_occ_unfold ordered value (first :: left)),
    Oeset.nb_occ_app,
    (Oeset.nb_occ_unfold ordered value (representative :: after)),
    (Oeset.compare_eq_2 ordered value first representative Hequal)
    in Hocc.
  lia.
}
rewrite !length_app in *; cbn in *; lia.
Qed.

Lemma febag_cardinal_le_of_nb_occ_le :
  forall (A : Type) (ordered : Oeset.Rcd A)
      (bags : Febag.Rcd ordered) left right,
    (forall value,
      (Febag.nb_occ bags value left <=
       Febag.nb_occ bags value right)%N) ->
    (Febag.cardinal bags left <= Febag.cardinal bags right)%N.
Proof.
intros A ordered bags left right Hocc.
unfold Febag.cardinal.
apply (proj1 (N.compare_le_iff _ _)).
rewrite <- Nat2N.inj_compare.
apply (proj2 (Nat.compare_le_iff _ _)).
apply (@oeset_pointwise_nb_occ_le_length A ordered); intro value.
rewrite <- !Febag.nb_occ_elements; apply Hocc.
Qed.

Lemma febag_cardinal_union :
  forall (A : Type) (ordered : Oeset.Rcd A)
      (bags : Febag.Rcd ordered) left right,
    Febag.cardinal bags (Febag.union bags left right) =
      (Febag.cardinal bags left + Febag.cardinal bags right)%N.
Proof.
intros A ordered bags left right.
unfold Febag.cardinal.
rewrite <- Nat2N.inj_add; f_equal.
rewrite <- length_app.
apply _permut_length with
  (R := fun x y => Oeset.compare ordered x y = Eq).
apply Oeset.nb_occ_permut; intro value.
rewrite <- Febag.nb_occ_elements, Febag.nb_occ_union,
  Oeset.nb_occ_app, !Febag.nb_occ_elements.
reflexivity.
Qed.

Lemma febag_cardinal_union_max_le :
  forall (A : Type) (ordered : Oeset.Rcd A)
      (bags : Febag.Rcd ordered) left right,
    (Febag.cardinal bags (Febag.union_max bags left right) <=
      Febag.cardinal bags left + Febag.cardinal bags right)%N.
Proof.
intros A ordered bags left right.
rewrite <- febag_cardinal_union.
apply febag_cardinal_le_of_nb_occ_le; intro value.
rewrite Febag.nb_occ_union_max, Febag.nb_occ_union.
apply N.max_lub; [apply N.le_add_r|apply N.le_add_l].
Qed.

Lemma febag_cardinal_inter_le_left :
  forall (A : Type) (ordered : Oeset.Rcd A)
      (bags : Febag.Rcd ordered) left right,
    (Febag.cardinal bags (Febag.inter bags left right) <=
      Febag.cardinal bags left)%N.
Proof.
intros A ordered bags left right.
apply febag_cardinal_le_of_nb_occ_le; intro value.
rewrite Febag.nb_occ_inter; apply N.le_min_l.
Qed.

Lemma febag_cardinal_inter_le_right :
  forall (A : Type) (ordered : Oeset.Rcd A)
      (bags : Febag.Rcd ordered) left right,
    (Febag.cardinal bags (Febag.inter bags left right) <=
      Febag.cardinal bags right)%N.
Proof.
intros A ordered bags left right.
apply febag_cardinal_le_of_nb_occ_le; intro value.
rewrite Febag.nb_occ_inter; apply N.le_min_r.
Qed.

Lemma febag_cardinal_diff_le_left :
  forall (A : Type) (ordered : Oeset.Rcd A)
      (bags : Febag.Rcd ordered) left right,
    (Febag.cardinal bags (Febag.diff bags left right) <=
      Febag.cardinal bags left)%N.
Proof.
intros A ordered bags left right.
apply febag_cardinal_le_of_nb_occ_le; intro value.
rewrite Febag.nb_occ_diff; apply N.le_sub_l.
Qed.

(** Standard conservative contracts for every modeled SQL multiset
    operation.  The sort-mismatch fallback is empty and therefore satisfies
    each bound; no duplicate-freedom premise is used. *)
Lemma query_set_cardinality_bound_union :
  forall left right left_bound right_bound,
    query_set_cardinality_bound Union left right
      left_bound right_bound (left_bound + right_bound).
Proof.
intros left right left_bound right_bound left_bag right_bag Hleft Hright.
unfold query_set_bag_function.
destruct (query_expr_sort left =S?= query_expr_sort right).
- unfold query_set_bag; cbn.
  rewrite febag_cardinal_union, Nat2N.inj_add; now apply N.add_le_mono.
- unfold Febag.cardinal; rewrite Febag.elements_empty; cbn; apply N.le_0_l.
Qed.

Lemma query_set_cardinality_bound_union_max :
  forall left right left_bound right_bound,
    query_set_cardinality_bound UnionMax left right
      left_bound right_bound (left_bound + right_bound).
Proof.
intros left right left_bound right_bound left_bag right_bag Hleft Hright.
unfold query_set_bag_function.
destruct (query_expr_sort left =S?= query_expr_sort right).
- unfold query_set_bag; cbn.
  eapply N.le_trans; [apply febag_cardinal_union_max_le|].
  rewrite Nat2N.inj_add; now apply N.add_le_mono.
- unfold Febag.cardinal; rewrite Febag.elements_empty; cbn; apply N.le_0_l.
Qed.

Lemma query_set_cardinality_bound_inter :
  forall left right left_bound right_bound,
    query_set_cardinality_bound Inter left right
      left_bound right_bound (Nat.min left_bound right_bound).
Proof.
intros left right left_bound right_bound left_bag right_bag Hleft Hright.
unfold query_set_bag_function.
destruct (query_expr_sort left =S?= query_expr_sort right).
- unfold query_set_bag; cbn.
  rewrite Nat2N.inj_min.
  apply N.min_glb.
  + eapply N.le_trans; [apply febag_cardinal_inter_le_left|exact Hleft].
  + eapply N.le_trans; [apply febag_cardinal_inter_le_right|exact Hright].
- unfold Febag.cardinal; rewrite Febag.elements_empty; cbn; apply N.le_0_l.
Qed.

Lemma query_set_cardinality_bound_diff :
  forall left right left_bound right_bound,
    query_set_cardinality_bound Diff left right
      left_bound right_bound left_bound.
Proof.
intros left right left_bound right_bound left_bag right_bag Hleft Hright.
unfold query_set_bag_function.
destruct (query_expr_sort left =S?= query_expr_sort right).
- unfold query_set_bag; cbn.
  eapply N.le_trans; [apply febag_cardinal_diff_le_left|exact Hleft].
- unfold Febag.cardinal; rewrite Febag.elements_empty; cbn; apply N.le_0_l.
Qed.

Lemma query_success_length_le_set :
  forall env operation left right left_bound right_bound output_bound,
    query_success_length_le env left left_bound ->
    query_success_length_le env right right_bound ->
    query_set_cardinality_bound operation left right
      left_bound right_bound output_bound ->
    query_success_length_le env (QExpr_Set operation left right) output_bound.
Proof.
intros env operation left right left_bound right_bound output_bound
  Hleft Hright Hoperation output Houtput.
apply eval_query_expr_set_success_iff in Houtput.
destruct Houtput as
  [left_rows [right_rows [Hleft_rows [Hright_rows Hsame]]]].
eapply query_same_rows_as_bag_length_le; [exact Hsame|].
apply Hoperation.
- unfold rows_bag; rewrite Febag.cardinal_mk_bag.
  apply (proj1 (N.compare_le_iff _ _)); rewrite <- Nat2N.inj_compare.
  now apply (proj2 (Nat.compare_le_iff _ _)), Hleft.
- unfold rows_bag; rewrite Febag.cardinal_mk_bag.
  apply (proj1 (N.compare_le_iff _ _)); rewrite <- Nat2N.inj_compare.
  now apply (proj2 (Nat.compare_le_iff _ _)), Hright.
Qed.

(** Successful rank evaluation attaches exactly one value to each staged row. *)
Lemma query_rank_rows_outcome_success_length :
  forall partition_keys order_keys rank_attribute rank_value all_rows rows output,
    @query_rank_rows_outcome T value_is_null
      partition_keys order_keys rank_attribute rank_value all_rows rows =
      Some output ->
    List.length output = List.length rows.
Proof.
intros partition_keys order_keys rank_attribute rank_value all_rows rows.
induction rows as [|row rows IH]; intros output Houtput; cbn in Houtput.
- now inversion Houtput.
- destruct (query_rank_row_outcome value_is_null partition_keys order_keys
    rank_attribute rank_value all_rows row) eqn:Hrow; [|discriminate].
  destruct (query_rank_rows_outcome value_is_null partition_keys order_keys
    rank_attribute rank_value all_rows rows) eqn:Htail; [|discriminate].
  inversion Houtput; subst output; cbn; f_equal.
  now eapply IH.
Qed.

Lemma query_rank_bag_rows_length :
  forall rows : list (tuple T),
    List.length (query_rank_bag_rows (rows_bag T rows)) = List.length rows.
Proof.
intro rows; unfold query_rank_bag_rows; rewrite length_map.
apply Nat2N.inj.
change
  (Febag.cardinal (Fecol.CBag (CTuple T)) (rows_bag T rows) =
   N.of_nat (List.length rows)).
unfold rows_bag; apply Febag.cardinal_mk_bag.
Qed.

(** Successful cumulative-window evaluation likewise emits one row per legal
    ordered input occurrence.  This is only a length theorem: peer order may
    still produce multiple observable value bags for a ROWS frame. *)
Lemma query_window_rows_outcome_success_length :
  forall env partition_keys items previous position prefix rows output,
    @query_window_rows_outcome T symbol_runtime_error aggregate_runtime_error
      value_is_null env partition_keys items previous position prefix rows =
      Some (SqlSuccess output) ->
    List.length output = List.length rows.
Proof.
intros env partition_keys items previous position prefix rows.
revert previous position prefix.
induction rows as [|row rows IH];
  intros previous position prefix output Houtput; cbn in Houtput.
- now inversion Houtput.
- destruct previous as [previous_row|].
  + destruct (compare_order_keys value_is_null partition_keys previous_row row).
    all: cbn in Houtput.
    all: destruct (query_window_items_outcome symbol_runtime_error
      aggregate_runtime_error env _ _ _ items row) as [[item_row|item_error]|]
      eqn:Hitem; try discriminate.
    all: destruct (query_window_rows_outcome symbol_runtime_error
      aggregate_runtime_error value_is_null env partition_keys items
      (Some row) _ _ rows) as [[tail_rows|tail_error]|]
      eqn:Htail; try discriminate.
    all: inversion Houtput; subst output; cbn; f_equal;
      eapply IH; exact Htail.
  + destruct (query_window_items_outcome symbol_runtime_error
      aggregate_runtime_error env 1 (row :: nil) _ items row)
      as [[item_row|item_error]|] eqn:Hitem; try discriminate.
    destruct (query_window_rows_outcome symbol_runtime_error
      aggregate_runtime_error value_is_null env partition_keys items
      (Some row) 1 (row :: nil) rows) as [[tail_rows|tail_error]|]
      eqn:Htail; try discriminate.
    inversion Houtput; subst output; cbn; f_equal.
    eapply IH; exact Htail.
Qed.

(** RANK preserves the exact occurrence count of the child success used by
    the parent derivation.  Rank values and legal row order remain observable;
    only the list length is related here. *)
Lemma eval_query_expr_rank_success_length :
  forall env partition_keys order_keys rank_attribute rank_value input output,
    @eval_query_expr_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule env
      (QExpr_Rank partition_keys order_keys rank_attribute rank_value input)
      (SqlSuccess output) ->
    exists input_rows,
      @eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env input (SqlSuccess input_rows) /\
      List.length output = List.length input_rows.
Proof.
intros env partition_keys order_keys rank_attribute rank_value input output
  Houtput.
apply eval_query_expr_rank_success_iff in Houtput.
destruct Houtput as [input_rows [output_bag [Hinput [Hrank Hsame]]]].
exists input_rows; split; [exact Hinput|].
unfold query_rank_bag_relation in Hrank.
destruct Hrank as [ranked_rows [Hcompute Hbag]].
assert (Houtput_length : List.length output = List.length ranked_rows).
{
  apply Nat2N.inj.
  pose proof (query_same_rows_as_bag_length_N output output_bag Hsame) as Hout.
  assert (Hcardinal :
    Febag.cardinal (Fecol.CBag (CTuple T)) (rows_bag T ranked_rows) =
    Febag.cardinal (Fecol.CBag (CTuple T)) output_bag).
  { now apply Febag.cardinal_eq. }
  unfold rows_bag in Hcardinal; rewrite Febag.cardinal_mk_bag in Hcardinal.
  rewrite Hout; now symmetry.
}
rewrite Houtput_length.
rewrite (query_rank_rows_outcome_success_length _ _ _ _ _ _ _ Hcompute).
apply query_rank_bag_rows_length.
Qed.

(** WINDOW likewise preserves exact occurrence count while leaving peer
    ordering, frame values, runtime errors, and the Boolean schedule intact. *)
Lemma eval_query_expr_window_success_length :
  forall env partition_keys order_keys items input output,
    @eval_query_expr_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule env
      (QExpr_Window partition_keys order_keys items input)
      (SqlSuccess output) ->
    exists input_rows,
      @eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env input (SqlSuccess input_rows) /\
      List.length output = List.length input_rows.
Proof.
intros env partition_keys order_keys items input output Houtput.
apply eval_query_expr_window_success_iff in Houtput.
destruct Houtput as [input_rows [output_bag [Hinput [Hwindow Hsame]]]].
exists input_rows; split; [exact Hinput|].
unfold query_window_bag_relation in Hwindow.
destruct Hwindow as
  [ordered_rows [window_rows [Horder [Hcompute Hbag]]]].
destruct Horder as [Hordered_bag Hordered].
assert (Houtput_length : List.length output = List.length window_rows).
{
  apply Nat2N.inj.
  pose proof (query_same_rows_as_bag_length_N output output_bag Hsame) as Hout.
  assert (Hcardinal :
    Febag.cardinal (Fecol.CBag (CTuple T)) (rows_bag T window_rows) =
    Febag.cardinal (Fecol.CBag (CTuple T)) output_bag).
  { now apply Febag.cardinal_eq. }
  unfold rows_bag in Hcardinal; rewrite Febag.cardinal_mk_bag in Hcardinal.
  rewrite Hout; now symmetry.
}
assert (Hordered_length :
  List.length ordered_rows =
  List.length (query_rank_bag_rows (rows_bag T input_rows))).
{
  apply Nat2N.inj.
  rewrite (query_same_rows_as_bag_length_N ordered_rows _ Hordered_bag).
  unfold query_rows_bag, rows_bag.
  rewrite Febag.cardinal_mk_bag; reflexivity.
}
rewrite Houtput_length.
rewrite (query_window_rows_outcome_success_length
  env partition_keys items None 0 nil ordered_rows window_rows Hcompute).
rewrite Hordered_length; apply query_rank_bag_rows_length.
Qed.

Lemma query_success_length_le_rank :
  forall env partition_keys order_keys rank_attribute rank_value input bound,
    query_success_length_le env input bound ->
    query_success_length_le env
      (QExpr_Rank partition_keys order_keys rank_attribute rank_value input)
      bound.
Proof.
intros env partition_keys order_keys rank_attribute rank_value input bound
  Hinput output Houtput.
destruct
  (eval_query_expr_rank_success_length
    env partition_keys order_keys rank_attribute rank_value input output Houtput)
  as [input_rows [Hinput_rows Hlength]].
rewrite Hlength; exact (Hinput input_rows Hinput_rows).
Qed.

Lemma query_success_length_le_window :
  forall env partition_keys order_keys items input bound,
    query_success_length_le env input bound ->
    query_success_length_le env
      (QExpr_Window partition_keys order_keys items input) bound.
Proof.
intros env partition_keys order_keys items input bound Hinput output Houtput.
destruct
  (eval_query_expr_window_success_length
    env partition_keys order_keys items input output Houtput)
  as [input_rows [Hinput_rows Hlength]].
rewrite Hlength; exact (Hinput input_rows Hinput_rows).
Qed.

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
    @eval_filter_rows_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule env formula rows (SqlSuccess output) ->
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

(** Filtering only removes child occurrences.  Formula and subquery errors
    remain ordinary non-success outcomes and need no safety assumption here. *)
Lemma query_success_length_le_filter :
  forall env formula input bound,
    query_success_length_le env input bound ->
    query_success_length_le env (QExpr_Filter formula input) bound.
Proof.
intros env formula input bound Hinput output Houtput.
apply eval_query_expr_filter_success_iff in Houtput.
destruct Houtput as [input_rows [Hinput_rows Hfilter]].
eapply Nat.le_trans.
- exact (filter_rows_success_length_le env formula input_rows output Hfilter).
- now apply Hinput.
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
    @eval_filter_rows_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule env formula rows (SqlSuccess output) ->
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

(** A successful filter output satisfies every row property implied by a
    TRUE Boolean-expression observation.  Unlike [filter_rows_success_Forall], the
    property need not already hold for rejected input rows. *)
Lemma filter_rows_success_Forall_accepted :
  forall env formula rows output (property : tuple T -> Prop),
    (forall row truth,
      In row rows ->
      @eval_scalar_boolean_expr_outcome T relname basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null boolean_schedule (env_t T env row) formula (SqlSuccess truth) ->
      Bool.is_true (B T) truth = true ->
      property row) ->
    @eval_filter_rows_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule env formula rows (SqlSuccess output) ->
    Forall property output.
Proof.
intros env formula rows.
induction rows as [|row rows IH]; intros output property Hproperty Hfilter.
- inversion Hfilter; constructor.
- inversion Hfilter; subst.
  match goal with
  | Htail : @eval_filter_rows_outcome _ _ _ _ _ _ _ _ _ _ _ rows ?tail |- _ =>
      destruct tail as [tail_rows|tail_error]
  end.
  + unfold filter_cons_outcome in *.
    destruct (Bool.is_true (B T) truth) eqn:Hkeep.
    * inversion H2; subst output; constructor.
      -- eapply Hproperty; [now left|eassumption|exact Hkeep].
      -- eapply IH.
         ++ intros other observed Hother.
            apply Hproperty; now right.
         ++ eassumption.
    * inversion H2; subst output.
      eapply IH.
      -- intros other observed Hother.
         apply Hproperty; now right.
      -- eassumption.
  + cbn [filter_cons_outcome] in *; discriminate.
Qed.

Lemma filter_rows_success_exact_count :
  forall env formula rows output keep,
    (forall row truth,
      In row rows ->
      @eval_scalar_boolean_expr_outcome T relname basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null boolean_schedule (env_t T env row) formula (SqlSuccess truth) ->
      Bool.is_true (B T) truth = keep row) ->
    @eval_filter_rows_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule env formula rows (SqlSuccess output) ->
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
    @eval_query_expr_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule env input (SqlSuccess input_rows) ->
    @eval_filter_rows_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule env formula input_rows (SqlError error) ->
    @eval_query_expr_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule env (QExpr_Filter formula input) (SqlError error).
Proof.
intros env formula input input_rows error Hinput Hfilter.
eapply EQuery_FilterRows with (input_rows := input_rows).
- exact Hinput.
- exact Hfilter.
Qed.

Lemma eval_groups_success_length_le :
  forall env select_list group_terms having groups output,
    @eval_groups_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule env select_list group_terms having groups
      (SqlSuccess output) ->
    (List.length output <= List.length groups)%nat.
Proof.
intros env select_list group_terms having groups.
induction groups as [|group groups IH]; intros output Heval.
- inversion Heval; subst; cbn; lia.
- inversion Heval; subst.
  + assert (Hlength :
      (List.length output <= List.length groups)%nat).
    { eapply IH; eassumption. }
    cbn; lia.
  + destruct tail as [tail_rows|tail_error].
    * unfold group_cons_outcome in H1.
      injection H1 as Houtput; subst output.
      assert (Hlength :
        (List.length tail_rows <= List.length groups)%nat).
      { eapply IH; eassumption. }
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
