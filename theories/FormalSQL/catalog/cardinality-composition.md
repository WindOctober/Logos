# Query cardinality and compositional bounds

Route here for: row-count bounds, functional joins, filters, groups, finite images.

This focused catalog contains 137 declarations routed at declaration granularity from `CardinalityCombinators.v`, `QueryCardinality.v`. Source declarations are authoritative; every statement below is verbatim and has no proof body.

## `bag_map_cardinal`

Source: [`theories/FormalSQL/CardinalityCombinators.v:15`](../CardinalityCombinators.v#L15)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates row cardinality and compositional bounds to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `cardinality`

Search aliases: `cardinality composition`, `cardinality`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma bag_map_cardinal :
  forall (A B : Type) (OA : Oeset.Rcd A) (OB : Oeset.Rcd B)
      (CA : Fecol.Rcd OA) (CB : Fecol.Rcd OB)
      (mapping : A -> B) (bag : Febag.bag (Fecol.CBag CA)),
    Febag.cardinal (Fecol.CBag CB)
      (Febag.map (Fecol.CBag CA) (Fecol.CBag CB) mapping bag) =
    Febag.cardinal (Fecol.CBag CA) bag.
```

## `bag_filter_cardinal_le`

Source: [`theories/FormalSQL/CardinalityCombinators.v:30`](../CardinalityCombinators.v#L30)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Provides the stated reusable upper bound for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `filter`, `bag`, `cardinality`

Search aliases: `cardinality composition`, `filter`, `WHERE`, `cardinality`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma bag_filter_cardinal_le :
  forall (A : Type) (OA : Oeset.Rcd A) (CA : Fecol.Rcd OA)
      (keep : A -> bool) (bag : Febag.bag (Fecol.CBag CA)),
    (forall left right,
      (Febag.nb_occ (Fecol.CBag CA) left bag >= 1)%N ->
      Oeset.compare OA left right = Eq ->
      keep left = keep right) ->
    (Febag.cardinal (Fecol.CBag CA)
       (Febag.filter (Fecol.CBag CA) keep bag) <=
     Febag.cardinal (Fecol.CBag CA) bag)%N.
```

## `filter_filter_commute`

Source: [`theories/FormalSQL/CardinalityCombinators.v:58`](../CardinalityCombinators.v#L58)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes commutativity for the declared row cardinality and compositional bounds operator.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `filter`, `cardinality`

Search aliases: `cardinality composition`, `filter`, `WHERE`, `cardinality`

```rocq
Lemma filter_filter_commute :
  forall (A : Type) (first second : A -> bool) rows,
    filter first (filter second rows) =
    filter second (filter first rows).
```

## `flat_map_uniform_length_le`

Source: [`theories/FormalSQL/CardinalityCombinators.v:71`](../CardinalityCombinators.v#L71)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Provides the stated reusable upper bound for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `cardinality`

Search aliases: `cardinality composition`, `cardinality`

```rocq
Lemma flat_map_uniform_length_le :
  forall (A B : Type) (expand : A -> list B) rows bound,
    (forall row,
      In row rows ->
      (List.length (expand row) <= bound)%nat) ->
    (List.length (flat_map expand rows) <=
      List.length rows * bound)%nat.
```

## `flat_map_uniform_length_eq`

Source: [`theories/FormalSQL/CardinalityCombinators.v:90`](../CardinalityCombinators.v#L90)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates row cardinality and compositional bounds to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `cardinality`

Search aliases: `cardinality composition`, `cardinality`

```rocq
Lemma flat_map_uniform_length_eq :
  forall (A B : Type) (expand : A -> list B) rows bound,
    (forall row,
      In row rows ->
      List.length (expand row) = bound) ->
    List.length (flat_map expand rows) =
      (List.length rows * bound)%nat.
```

## `nonempty_groups_count_le_total_length`

Source: [`theories/FormalSQL/CardinalityCombinators.v:109`](../CardinalityCombinators.v#L109)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates row cardinality and compositional bounds to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping`, `cardinality`

Search aliases: `cardinality composition`, `GROUP BY`, `cardinality`

```rocq
Lemma nonempty_groups_count_le_total_length :
  forall (A Group : Type) (members : Group -> list A) groups,
    Forall (fun group => members group <> nil) groups ->
    (List.length groups <= List.length (flat_map members groups))%nat.
```

## `NoDupA_pairwise_filter_length_le_one`

Source: [`theories/FormalSQL/CardinalityCombinators.v:126`](../CardinalityCombinators.v#L126)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Provides the stated reusable upper bound for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `filter`, `cardinality`

Search aliases: `cardinality composition`, `filter`, `WHERE`, `cardinality`

```rocq
Lemma NoDupA_pairwise_filter_length_le_one :
  forall (A : Type) (relation : A -> A -> Prop)
      (keep : A -> bool) rows,
    NoDupA relation rows ->
    (forall left right,
      In left rows ->
      In right rows ->
      keep left = true ->
      keep right = true ->
      relation left right) ->
    (List.length (filter keep rows) <= 1)%nat.
```

## `filter_singleton_of_nonempty_length_le_one`

Source: [`theories/FormalSQL/CardinalityCombinators.v:168`](../CardinalityCombinators.v#L168)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Provides the stated reusable upper bound for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `filter`, `cardinality`

Search aliases: `cardinality composition`, `filter`, `WHERE`, `cardinality`

```rocq
Lemma filter_singleton_of_nonempty_length_le_one :
  forall (A : Type) (keep : A -> bool) rows,
    (exists row, In row rows /\ keep row = true) ->
    (List.length (filter keep rows) <= 1)%nat ->
    exists row, filter keep rows = [row].
```

## `map_theta_join_total_functional`

Source: [`theories/FormalSQL/CardinalityCombinators.v:191`](../CardinalityCombinators.v#L191)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Identifies the exact projected join list with the pointwise mapped left input under total and at-most-one matching.

Applicability: Use to replace a projected total-functional join by the exact mapped left list; duplicate left occurrences and list order are preserved.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `join`, `cardinality`

Search aliases: `cardinality composition`, `join`, `cardinality`

```rocq
Lemma map_theta_join_total_functional :
  forall (A B : Type)
      (join : A -> A -> A) (accept : A -> A -> bool)
      (project : A -> B) (emit : A -> B) left right,
    (forall left_row right_row,
      project (join left_row right_row) = emit left_row) ->
    (forall left_row,
      In left_row left ->
      exists right_row,
        In right_row right /\ accept left_row right_row = true) ->
    (forall left_row,
      In left_row left ->
      (List.length (filter (accept left_row) right) <= 1)%nat) ->
    map project (theta_join_list A join accept left right) = map emit left.
```

## `map_theta_join_functional_permut_filter_exists`

Source: [`theories/FormalSQL/CardinalityCombinators.v:228`](../CardinalityCombinators.v#L228)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the map theta join functional permut filter exists law for join cardinality, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join cardinality.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `filter`, `join`, `cardinality`

Search aliases: `cardinality composition`, `join`, `filter`, `WHERE`, `cardinality`

```rocq
Lemma map_theta_join_functional_permut_filter_exists :
  forall (A B : Type) (OB : Oeset.Rcd B)
      (join : A -> A -> A) (accept : A -> A -> bool)
      (project emit : A -> B) left right,
    (forall left_row right_row,
      In left_row left ->
      In right_row right ->
      accept left_row right_row = true ->
      Oeset.compare OB (project (join left_row right_row))
        (emit left_row) = Eq) ->
    (forall left_row,
      In left_row left ->
      (List.length (filter (accept left_row) right) <= 1)%nat) ->
    Oeset.permut OB
      (map project (theta_join_list A join accept left right))
      (map emit
        (filter
          (fun left_row => existsb (accept left_row) right) left)).
```

## `anti_filter_empty_of_total_match`

Source: [`theories/FormalSQL/CardinalityCombinators.v:301`](../CardinalityCombinators.v#L301)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the exact empty-input or empty-result law for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `filter`, `cardinality`

Search aliases: `cardinality composition`, `filter`, `WHERE`, `cardinality`

```rocq
Lemma anti_filter_empty_of_total_match :
  forall (A B : Type) (accept : A -> B -> bool) left right,
    (forall left_row,
      In left_row left ->
      exists right_row,
        In right_row right /\ accept left_row right_row = true) ->
    filter
      (fun left_row => negb (existsb (accept left_row) right)) left = nil.
```

## `map_left_join_total_functional`

Source: [`theories/FormalSQL/CardinalityCombinators.v:323`](../CardinalityCombinators.v#L323)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Identifies the exact projected join list with the pointwise mapped left input under total and at-most-one matching.

Applicability: Use to replace a projected total-functional join by the exact mapped left list; duplicate left occurrences and list order are preserved.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `join`, `cardinality`

Search aliases: `cardinality composition`, `join`, `cardinality`

```rocq
Lemma map_left_join_total_functional :
  forall (A B : Type)
      (join : A -> A -> A) (accept : A -> A -> bool)
      (project : A -> B) (emit : A -> B) (pad : A -> A) left right,
    (forall left_row right_row,
      project (join left_row right_row) = emit left_row) ->
    (forall left_row,
      In left_row left -> project (pad left_row) = emit left_row) ->
    (forall left_row,
      In left_row left ->
      exists right_row,
        In right_row right /\ accept left_row right_row = true) ->
    (forall left_row,
      In left_row left ->
      (List.length (filter (accept left_row) right) <= 1)%nat) ->
    map project (theta_join_list A join accept left right) ++
      map project
        (map pad
          (filter
            (fun left_row => negb (existsb (accept left_row) right)) left)) =
    map emit left.
```

## `map_left_join_functional_permut`

Source: [`theories/FormalSQL/CardinalityCombinators.v:359`](../CardinalityCombinators.v#L359)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Identifies a projected at-most-one LEFT JOIN with the mapped left input up to semantic permutation, retaining unmatched and duplicate left occurrences without a total-match premise.

Applicability: Use when each left occurrence has zero or one accepted right occurrence and matched and padded rows project to the same direct left result; semantic permutation preserves duplicate left rows.

Important premises: Retain both matched and padded projection equalities and the per-left at-most-one bound.  No foreign-key totality premise is required; the conclusion is occurrence-preserving permutation.

Cross-index: `join`, `cardinality`

Search aliases: `cardinality composition`, `functional LEFT JOIN`, `at-most-one match`, `nullable unmatched key`, `left multiplicity`, `join`, `cardinality`

```rocq
Lemma map_left_join_functional_permut :
  forall (A B : Type) (OB : Oeset.Rcd B)
      (join : A -> A -> A) (accept : A -> A -> bool)
      (project : A -> B) (emit : A -> B) (pad : A -> A) left right,
    (forall left_row right_row,
      Oeset.compare OB (project (join left_row right_row))
        (emit left_row) = Eq) ->
    (forall left_row,
      In left_row left ->
      Oeset.compare OB (project (pad left_row)) (emit left_row) = Eq) ->
    (forall left_row,
      In left_row left ->
      (List.length (filter (accept left_row) right) <= 1)%nat) ->
    Oeset.permut OB
      (map project
        (theta_join_list A join accept left right ++
         map pad
           (filter
             (fun left_row => negb (existsb (accept left_row) right)) left)))
      (map emit left).
```

## `map_left_join_functional_branch_permut`

Source: [`theories/FormalSQL/CardinalityCombinators.v:441`](../CardinalityCombinators.v#L441)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the map left join functional branch permut law for join cardinality, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join cardinality.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `join`, `cardinality`

Search aliases: `cardinality composition`, `join`, `cardinality`

```rocq
Lemma map_left_join_functional_branch_permut :
  forall (A B : Type) (OB : Oeset.Rcd B)
      (join : A -> A -> A) (accept : A -> A -> bool)
      (project matched_emit unmatched_emit : A -> B)
      (pad : A -> A) left right,
    (forall left_row right_row,
      In left_row left ->
      In right_row right ->
      accept left_row right_row = true ->
      Oeset.compare OB (project (join left_row right_row))
        (matched_emit left_row) = Eq) ->
    (forall left_row,
      In left_row left ->
      Oeset.compare OB (project (pad left_row))
        (unmatched_emit left_row) = Eq) ->
    (forall left_row,
      In left_row left ->
      (List.length (filter (accept left_row) right) <= 1)%nat) ->
    Oeset.permut OB
      (map project
        (theta_join_list A join accept left right ++
         map pad
           (filter
             (fun left_row => negb (existsb (accept left_row) right)) left)))
      (map
        (fun left_row =>
          if existsb (accept left_row) right
          then matched_emit left_row
          else unmatched_emit left_row)
        left).
```

## `NoDupA_map_preimage`

Source: [`theories/FormalSQL/CardinalityCombinators.v:543`](../CardinalityCombinators.v#L543)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes the displayed duplicate-freedom property for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `cardinality`

Search aliases: `cardinality composition`, `cardinality`

```rocq
Lemma NoDupA_map_preimage :
  forall (A B : Type) (relation : B -> B -> Prop)
      (project : A -> B) rows,
    NoDupA relation (map project rows) ->
    NoDupA
      (fun left right => relation (project left) (project right)) rows.
```

## `NoDupA_map_of_reflection`

Source: [`theories/FormalSQL/CardinalityCombinators.v:569`](../CardinalityCombinators.v#L569)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes the displayed duplicate-freedom property for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `cardinality`

Search aliases: `cardinality composition`, `cardinality`

```rocq
Lemma NoDupA_map_of_reflection :
  forall (A B : Type) (source_relation : A -> A -> Prop)
      (target_relation : B -> B -> Prop) (project : A -> B) rows,
    NoDupA source_relation rows ->
    (forall left right,
      In left rows ->
      In right rows ->
      target_relation (project left) (project right) ->
      source_relation left right) ->
    NoDupA target_relation (map project rows).
```

## `NoDupA_flat_map_filter_map_functional_reflection`

Source: [`theories/FormalSQL/CardinalityCombinators.v:603`](../CardinalityCombinators.v#L603)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes the displayed duplicate-freedom property for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `filter`, `cardinality`

Search aliases: `cardinality composition`, `filter`, `WHERE`, `cardinality`

```rocq
Lemma NoDupA_flat_map_filter_map_functional_reflection :
  forall (Left Right Output : Type)
      (source_relation : Left -> Left -> Prop)
      (target_relation : Output -> Output -> Prop)
      (accept : Left -> Right -> bool)
      (emit : Left -> Right -> Output)
      left right,
    NoDupA source_relation left ->
    (forall left_row,
      In left_row left ->
      (List.length (filter (accept left_row) right) <= 1)%nat) ->
    (forall left_first left_second right_first right_second,
      In left_first left -> In left_second left ->
      In right_first right -> In right_second right ->
      accept left_first right_first = true ->
      accept left_second right_second = true ->
      target_relation
        (emit left_first right_first) (emit left_second right_second) ->
      source_relation left_first left_second) ->
    NoDupA target_relation
      (flat_map
        (fun left_row =>
          map (emit left_row) (filter (accept left_row) right)) left).
```

## `NoDupA_map_iff_NoDup_on`

Source: [`theories/FormalSQL/CardinalityCombinators.v:670`](../CardinalityCombinators.v#L670)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for row cardinality and compositional bounds.

Applicability: Use in either direction to invert or construct a goal about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `cardinality`

Search aliases: `cardinality composition`, `cardinality`

```rocq
Lemma NoDupA_map_iff_NoDup_on :
  forall (A Code : Type) (relation : A -> A -> Prop)
      (code : A -> Code) rows,
    (forall left right,
      In left rows ->
      In right rows ->
      (relation left right <-> code left = code right)) ->
    (NoDupA relation rows <-> NoDup (map code rows)).
```

## `NoDupA_finite_image_length_le`

Source: [`theories/FormalSQL/CardinalityCombinators.v:718`](../CardinalityCombinators.v#L718)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Provides the stated reusable upper bound for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `cardinality`

Search aliases: `cardinality composition`, `cardinality`

```rocq
Theorem NoDupA_finite_image_length_le :
  forall (A Code : Type) (relation : A -> A -> Prop)
      (code : A -> Code) rows domain,
    NoDupA relation rows ->
    (forall row, In row rows -> In (code row) domain) ->
    (forall left right,
      In left rows ->
      In right rows ->
      (relation left right <-> code left = code right)) ->
    (List.length rows <= List.length domain)%nat.
```

## `NoDupA_finite_product_code_length_le`

Source: [`theories/FormalSQL/CardinalityCombinators.v:744`](../CardinalityCombinators.v#L744)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Provides the stated reusable upper bound for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `cardinality`

Search aliases: `cardinality composition`, `cardinality`

```rocq
Corollary NoDupA_finite_product_code_length_le :
  forall (A Left Right : Type) (relation : A -> A -> Prop)
      (left_code : A -> Left) (right_code : A -> Right)
      rows left_domain right_domain,
    NoDupA relation rows ->
    (forall row, In row rows -> In (left_code row) left_domain) ->
    (forall row, In row rows -> In (right_code row) right_domain) ->
    (forall left right,
      In left rows ->
      In right rows ->
      (relation left right <->
       (left_code left, right_code left) =
       (left_code right, right_code right))) ->
    (List.length rows <=
      List.length left_domain * List.length right_domain)%nat.
```

## `NoDupA_finite_option_code_length_le`

Source: [`theories/FormalSQL/CardinalityCombinators.v:777`](../CardinalityCombinators.v#L777)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Provides the stated reusable upper bound for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `cardinality`

Search aliases: `cardinality composition`, `cardinality`

```rocq
Corollary NoDupA_finite_option_code_length_le :
  forall (A Code : Type) (relation : A -> A -> Prop)
      (code : A -> option Code) rows domain,
    NoDupA relation rows ->
    (forall row,
      In row rows ->
      match code row with
      | None => True
      | Some value => In value domain
      end) ->
    (forall left right,
      In left rows ->
      In right rows ->
      (relation left right <-> code left = code right)) ->
    (List.length rows <= S (List.length domain))%nat.
```

## `oeset_nb_occ_le_length`

Source: [`theories/FormalSQL/CardinalityCombinators.v:814`](../CardinalityCombinators.v#L814)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates row cardinality and compositional bounds to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `cardinality`

Search aliases: `cardinality composition`, `cardinality`, `multiplicity`

```rocq
Lemma oeset_nb_occ_le_length :
  forall (A : Type) (ordered : Oeset.Rcd A) value rows,
    (Oeset.nb_occ ordered value rows <=
      N.of_nat (List.length rows))%N.
```

## `instance_row_multiplicity_le_length`

Source: [`theories/FormalSQL/CardinalityCombinators.v:839`](../CardinalityCombinators.v#L839)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates row cardinality and compositional bounds to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `cardinality`

Search aliases: `cardinality composition`, `cardinality`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Corollary instance_row_multiplicity_le_length :
  forall db relation row,
    (Febag.nb_occ
      (Fecol.CBag (CTuple TNull)) row
      (@_instance TNull db relation) <=
     N.of_nat (List.length (instance_rows db relation)))%N.
```

## `instance_row_positive_multiplicity_nonempty`

Source: [`theories/FormalSQL/CardinalityCombinators.v:852`](../CardinalityCombinators.v#L852)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the exact empty-input or empty-result law for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `cardinality`

Search aliases: `cardinality composition`, `cardinality`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Corollary instance_row_positive_multiplicity_nonempty :
  forall db relation row,
    (0 < Febag.nb_occ
      (Fecol.CBag (CTuple TNull)) row
      (@_instance TNull db relation))%N ->
    instance_rows db relation <> nil.
```

## `theta_join_list_degree_length_le`

Source: [`theories/FormalSQL/CardinalityCombinators.v:871`](../CardinalityCombinators.v#L871)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Provides the stated reusable upper bound for join cardinality.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join cardinality.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `join`, `cardinality`

Search aliases: `cardinality composition`, `join`, `cardinality`

```rocq
Lemma theta_join_list_degree_length_le :
  forall (row : Type) (join : row -> row -> row)
      (accept : row -> row -> bool) left right bound,
    (forall left_row,
      In left_row left ->
      (List.length (filter (accept left_row) right) <= bound)%nat) ->
    (List.length (theta_join_list row join accept left right) <=
      List.length left * bound)%nat.
```

## `theta_join_list_length_le_product`

Source: [`theories/FormalSQL/CardinalityCombinators.v:890`](../CardinalityCombinators.v#L890)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Provides the stated reusable upper bound for join cardinality.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join cardinality.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `join`, `cardinality`

Search aliases: `cardinality composition`, `join`, `cardinality`

```rocq
Corollary theta_join_list_length_le_product :
  forall (row : Type) (join : row -> row -> row)
      (accept : row -> row -> bool) left right,
    (List.length (theta_join_list row join accept left right) <=
      List.length left * List.length right)%nat.
```

## `filter_theta_join_list_degree_length_le`

Source: [`theories/FormalSQL/CardinalityCombinators.v:904`](../CardinalityCombinators.v#L904)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Provides the stated reusable upper bound for join cardinality.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join cardinality.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `filter`, `join`, `cardinality`

Search aliases: `cardinality composition`, `join`, `filter`, `WHERE`, `cardinality`

```rocq
Corollary filter_theta_join_list_degree_length_le :
  forall (row : Type) (join : row -> row -> row)
      (accept : row -> row -> bool) (keep : row -> bool)
      left right bound,
    (forall left_row,
      In left_row left ->
      (List.length (filter (accept left_row) right) <= bound)%nat) ->
    (List.length
      (filter keep (theta_join_list row join accept left right)) <=
      List.length left * bound)%nat.
```

## `expansion_pipeline_length_le`

Source: [`theories/FormalSQL/CardinalityCombinators.v:944`](../CardinalityCombinators.v#L944)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Provides the stated reusable upper bound for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `cardinality`

Search aliases: `cardinality composition`, `cardinality`

```rocq
Theorem expansion_pipeline_length_le :
  forall (A : Type) stages bounds rows,
    @expansion_pipeline_bounds A stages bounds ->
    (List.length (expansion_pipeline A stages rows) <=
      List.length rows * multiply_bounds bounds)%nat.
```

## `partition_flatten_length`

Source: [`theories/FormalSQL/CardinalityCombinators.v:968`](../CardinalityCombinators.v#L968)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates row cardinality and compositional bounds to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `cardinality`

Search aliases: `cardinality composition`, `cardinality`

```rocq
Lemma partition_flatten_length :
  forall (A Key : Type) (ordered : Oset.Rcd Key)
      (key_of : A -> Key) rows,
    List.length
      (flat_map snd (@Partition.partition A Key ordered key_of rows)) =
    List.length rows.
```

## `partition_group_count_le`

Source: [`theories/FormalSQL/CardinalityCombinators.v:983`](../CardinalityCombinators.v#L983)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the partition group count upper-bound law for row cardinality and compositional bounds, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `grouping`, `cardinality`

Search aliases: `cardinality composition`, `GROUP BY`, `cardinality`

```rocq
Theorem partition_group_count_le :
  forall (A Key : Type) (ordered : Oset.Rcd Key)
      (key_of : A -> Key) rows,
    (List.length (@Partition.partition A Key ordered key_of rows) <=
      List.length rows)%nat.
```

## `theta_join_list_functional_length_le`

Source: [`theories/FormalSQL/QueryCardinality.v:28`](../QueryCardinality.v#L28)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Provides the stated reusable upper bound for join cardinality.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join cardinality.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `join`, `cardinality`

Search aliases: `cardinality composition`, `join`, `cardinality`

```rocq
Lemma theta_join_list_functional_length_le :
  forall (row : Type) (join : row -> row -> row)
         (accept : row -> row -> bool) left right,
    (forall left_row,
      In left_row left ->
      (List.length (filter (accept left_row) right) <= 1)%nat) ->
    (List.length (theta_join_list row join accept left right) <=
      List.length left)%nat.
```

## `brute_left_join_list_length_mul`

Source: [`theories/FormalSQL/QueryCardinality.v:51`](../QueryCardinality.v#L51)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates join cardinality to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join cardinality.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `join`, `cardinality`

Search aliases: `cardinality composition`, `join`, `cardinality`

```rocq
Lemma brute_left_join_list_length_mul :
  forall (row : Type) (join : row -> row -> row) left right,
    List.length (brute_left_join_list row join left right) =
      (List.length left * List.length right)%nat.
```

## `filter_brute_left_join_list_as_theta`

Source: [`theories/FormalSQL/QueryCardinality.v:68`](../QueryCardinality.v#L68)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Bridges the two displayed representations of join cardinality.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join cardinality.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `filter`, `join`, `cardinality`

Search aliases: `cardinality composition`, `join`, `filter`, `WHERE`, `cardinality`

```rocq
Lemma filter_brute_left_join_list_as_theta :
  forall (row : Type) (join : row -> row -> row)
         (keep : row -> bool) (accept : row -> row -> bool) left right,
    (forall left_row right_row,
      keep (join left_row right_row) = accept left_row right_row) ->
    filter keep (brute_left_join_list row join left right) =
      theta_join_list row join accept left right.
```

## `theta_join_list_guard_left`

Source: [`theories/FormalSQL/QueryCardinality.v:95`](../QueryCardinality.v#L95)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the theta join list guard left law for join cardinality, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join cardinality.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `join`, `cardinality`

Search aliases: `cardinality composition`, `join`, `cardinality`

```rocq
Lemma theta_join_list_guard_left :
  forall (row : Type) (join : row -> row -> row)
         (guard : row -> bool) (accept : row -> row -> bool) left right,
    theta_join_list row join
      (fun left_row right_row => andb (guard left_row) (accept left_row right_row))
      left right =
    theta_join_list row join accept (filter guard left) right.
```

## `tnull_predicate_keep_proper`

Source: [`theories/FormalSQL/QueryCardinality.v:137`](../QueryCardinality.v#L137)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the tnull predicate keep proper law for row cardinality and compositional bounds, in the exact direction displayed by the declaration.

Applicability: Use to orient, transport, or compose a semantic relation about row cardinality and compositional bounds.

Important premises: supply the declared equivalence/properness relation.

Cross-index: `cardinality`, `scalar`

Search aliases: `cardinality composition`, `predicate`, `Bool3`, `cardinality`, `equivalence`, `congruence`

```rocq
Lemma tnull_predicate_keep_proper :
  forall env predicate arguments,
    tuple_predicate_proper
      (tnull_predicate_keep env predicate arguments).
```

## `row_attribute_present_conforms_proper`

Source: [`theories/FormalSQL/QueryCardinality.v:158`](../QueryCardinality.v#L158)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the row attribute present conforms proper law for row cardinality and compositional bounds, in the exact direction displayed by the declaration.

Applicability: Use to orient, transport, or compose a semantic relation about row cardinality and compositional bounds.

Important premises: keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `cardinality`, `schema`

Search aliases: `cardinality composition`, `schema conformance`, `typing`, `cardinality`, `equivalence`, `congruence`

```rocq
Lemma row_attribute_present_conforms_proper :
  forall attribute,
    tuple_property_proper (row_attribute_present_conforms attribute).
```

## `row_attribute_absent_proper`

Source: [`theories/FormalSQL/QueryCardinality.v:172`](../QueryCardinality.v#L172)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the row attribute absent proper law for row cardinality and compositional bounds, in the exact direction displayed by the declaration.

Applicability: Use to orient, transport, or compose a semantic relation about row cardinality and compositional bounds.

Important premises: keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `cardinality`, `schema`

Search aliases: `cardinality composition`, `schema conformance`, `typing`, `cardinality`, `equivalence`, `congruence`

```rocq
Lemma row_attribute_absent_proper :
  forall attribute,
    tuple_property_proper (row_attribute_absent attribute).
```

## `row_attribute_present_nonnull_conforms_proper`

Source: [`theories/FormalSQL/QueryCardinality.v:190`](../QueryCardinality.v#L190)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the row attribute present nonnull conforms proper law for row cardinality and compositional bounds, in the exact direction displayed by the declaration.

Applicability: Use to orient, transport, or compose a semantic relation about row cardinality and compositional bounds.

Important premises: keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `cardinality`, `schema`

Search aliases: `cardinality composition`, `schema conformance`, `typing`, `cardinality`, `equivalence`, `congruence`

```rocq
Lemma row_attribute_present_nonnull_conforms_proper :
  forall attribute,
    tuple_property_proper
      (row_attribute_present_nonnull_conforms attribute).
```

## `related_permut_Forall_transport`

Source: [`theories/FormalSQL/QueryCardinality.v:212`](../QueryCardinality.v#L212)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Transports the displayed hypotheses and conclusion for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `cardinality`

Search aliases: `cardinality composition`, `cardinality`

```rocq
Lemma related_permut_Forall_transport :
  forall (A B : Type) (R : A -> B -> Prop) (P : A -> Prop) (Q : B -> Prop)
         left right,
    (forall a b, R a b -> P a -> Q b) ->
    _permut R left right ->
    Forall P left ->
    Forall Q right.
```

## `related_permut_PermutationA`

Source: [`theories/FormalSQL/QueryCardinality.v:238`](../QueryCardinality.v#L238)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the related permut permutation a law for row cardinality and compositional bounds, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `cardinality`

Search aliases: `cardinality composition`, `cardinality`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma related_permut_PermutationA :
  forall (A : Type) (relation : A -> A -> Prop) left right,
    Equivalence relation ->
    _permut relation left right ->
    PermutationA relation left right.
```

## `oeset_compare_Equivalence`

Source: [`theories/FormalSQL/QueryCardinality.v:254`](../QueryCardinality.v#L254)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the oeset compare equivalence law for row cardinality and compositional bounds, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `cardinality`

Search aliases: `cardinality composition`, `cardinality`

```rocq
Lemma oeset_compare_Equivalence :
  forall (A : Type) (ordered : Oeset.Rcd A),
    Equivalence
      (fun left right => Oeset.compare ordered left right = Eq).
```

## `oeset_sorted_NoDupA`

Source: [`theories/FormalSQL/QueryCardinality.v:266`](../QueryCardinality.v#L266)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes the displayed duplicate-freedom property for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `cardinality`

Search aliases: `cardinality composition`, `cardinality`

```rocq
Lemma oeset_sorted_NoDupA :
  forall (A : Type) (ordered : Oeset.Rcd A) rows,
    Sorted (fun left right => Oeset.compare ordered left right = Lt) rows ->
    NoDupA (fun left right => Oeset.compare ordered left right = Eq) rows.
```

## `NoDupA_app_left`

Source: [`theories/FormalSQL/QueryCardinality.v:292`](../QueryCardinality.v#L292)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes the displayed duplicate-freedom property for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `cardinality`

Search aliases: `cardinality composition`, `cardinality`

```rocq
Lemma NoDupA_app_left :
  forall (A : Type) (relation : A -> A -> Prop) left right,
    NoDupA relation (left ++ right) ->
    NoDupA relation left.
```

## `NoDupA_app_right`

Source: [`theories/FormalSQL/QueryCardinality.v:309`](../QueryCardinality.v#L309)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes the displayed duplicate-freedom property for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `cardinality`

Search aliases: `cardinality composition`, `cardinality`

```rocq
Lemma NoDupA_app_right :
  forall (A : Type) (relation : A -> A -> Prop) left right,
    NoDupA relation (left ++ right) ->
    NoDupA relation right.
```

## `NoDupA_map_injective_on`

Source: [`theories/FormalSQL/QueryCardinality.v:321`](../QueryCardinality.v#L321)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Recovers source equality from the declared row cardinality and compositional bounds representation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `cardinality`

Search aliases: `cardinality composition`, `cardinality`

```rocq
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
```

## `query_same_rows_as_bag_permut_elements`

Source: [`theories/FormalSQL/QueryCardinality.v:348`](../QueryCardinality.v#L348)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Bridges the two displayed representations of row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `cardinality`

Search aliases: `cardinality composition`, `cardinality`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_same_rows_as_bag_permut_elements :
  forall rows bag,
    @query_same_rows_as_bag TNull rows bag ->
    _permut
      (fun left right => Oeset.compare (OTuple TNull) left right = Eq)
      rows (Febag.elements (Fecol.CBag (CTuple TNull)) bag).
```

## `query_distinct_bag_rows_NoDupA`

Source: [`theories/FormalSQL/QueryCardinality.v:368`](../QueryCardinality.v#L368)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes the displayed duplicate-freedom property for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `cardinality`

Search aliases: `cardinality composition`, `DISTINCT`, `duplicate elimination`, `cardinality`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_distinct_bag_rows_NoDupA :
  forall input rows,
    @query_same_rows_as_bag TNull rows
      (@query_distinct_bag TNull input) ->
    NoDupA
      (fun left right => Oeset.compare (OTuple TNull) left right = Eq)
      rows.
```

## `query_same_rows_as_bag_Forall_between`

Source: [`theories/FormalSQL/QueryCardinality.v:424`](../QueryCardinality.v#L424)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Bridges the two displayed representations of row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `cardinality`

Search aliases: `cardinality composition`, `cardinality`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_same_rows_as_bag_Forall_between :
  forall property first second bag,
    tuple_property_proper property ->
    @query_same_rows_as_bag TNull first bag ->
    @query_same_rows_as_bag TNull second bag ->
    Forall property first ->
    Forall property second.
```

## `query_same_rows_as_table_absent_attribute`

Source: [`theories/FormalSQL/QueryCardinality.v:455`](../QueryCardinality.v#L455)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Bridges the two displayed representations of row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `cardinality`, `schema`

Search aliases: `cardinality composition`, `schema conformance`, `typing`, `cardinality`

```rocq
Theorem query_same_rows_as_table_absent_attribute :
  forall actual relation attribute rows,
    database_values_conform actual ->
    (attribute inS? @_basesort TNull actual relation) = false ->
    @query_same_rows_as_bag TNull rows
      (@_instance TNull actual relation) ->
    Forall (row_attribute_absent attribute) rows.
```

## `query_same_rows_as_conforming_table_absent_attribute`

Source: [`theories/FormalSQL/QueryCardinality.v:479`](../QueryCardinality.v#L479)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Bridges the two displayed representations of row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `cardinality`, `schema`

Search aliases: `cardinality composition`, `schema conformance`, `typing`, `cardinality`

```rocq
Theorem query_same_rows_as_conforming_table_absent_attribute :
  forall expected constraints actual relation attribute rows,
    database_conforms_schema expected constraints actual ->
    (attribute inS? @_basesort TNull expected relation) = false ->
    @query_same_rows_as_bag TNull rows
      (@_instance TNull actual relation) ->
    Forall (row_attribute_absent attribute) rows.
```

## `query_expr_table_success_rows_absent_attribute`

Source: [`theories/FormalSQL/QueryCardinality.v:503`](../QueryCardinality.v#L503)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Inverts or constructs the successful evaluation branch for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `cardinality`, `schema`

Search aliases: `cardinality composition`, `schema conformance`, `typing`, `cardinality`

```rocq
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
```

## `query_same_rows_as_conforming_table_present_attribute`

Source: [`theories/FormalSQL/QueryCardinality.v:534`](../QueryCardinality.v#L534)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Bridges the two displayed representations of row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `cardinality`, `schema`

Search aliases: `cardinality composition`, `schema conformance`, `typing`, `cardinality`

```rocq
Theorem query_same_rows_as_conforming_table_present_attribute :
  forall expected constraints actual relation attribute rows,
    database_conforms_schema expected constraints actual ->
    attribute inS (@_basesort TNull expected relation) ->
    @query_same_rows_as_bag TNull rows
      (@_instance TNull actual relation) ->
    Forall (row_attribute_present_conforms attribute) rows.
```

## `query_expr_table_success_rows_present_conform_attribute`

Source: [`theories/FormalSQL/QueryCardinality.v:558`](../QueryCardinality.v#L558)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Inverts or constructs the successful evaluation branch for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `cardinality`, `schema`

Search aliases: `cardinality composition`, `schema conformance`, `typing`, `cardinality`

```rocq
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
```

## `query_expr_table_success_row_present_conform_attribute_generated_sort`

Source: [`theories/FormalSQL/QueryCardinality.v:589`](../QueryCardinality.v#L589)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Inverts or constructs the successful evaluation branch for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `cardinality`, `schema`

Search aliases: `cardinality composition`, `schema conformance`, `typing`, `cardinality`

```rocq
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
```

## `query_same_rows_as_conforming_table_attribute`

Source: [`theories/FormalSQL/QueryCardinality.v:635`](../QueryCardinality.v#L635)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Bridges the two displayed representations of row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `cardinality`, `schema`

Search aliases: `cardinality composition`, `schema conformance`, `typing`, `cardinality`

```rocq
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
```

## `query_expr_table_success_rows_conform_attribute`

Source: [`theories/FormalSQL/QueryCardinality.v:683`](../QueryCardinality.v#L683)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Inverts or constructs the successful evaluation branch for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `cardinality`, `schema`

Search aliases: `cardinality composition`, `schema conformance`, `typing`, `cardinality`

```rocq
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
```

## `query_expr_table_success_row_conform_attribute_generated_sort`

Source: [`theories/FormalSQL/QueryCardinality.v:719`](../QueryCardinality.v#L719)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Inverts or constructs the successful evaluation branch for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `cardinality`, `schema`

Search aliases: `cardinality composition`, `schema conformance`, `typing`, `cardinality`

```rocq
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
```

## `query_canonical_rows_Forall`

Source: [`theories/FormalSQL/QueryCardinality.v:767`](../QueryCardinality.v#L767)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the query canonical rows forall law for row cardinality and compositional bounds, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `cardinality`

Search aliases: `cardinality composition`, `cardinality`

```rocq
Corollary query_canonical_rows_Forall :
  forall property rows,
    tuple_property_proper property ->
    Forall property rows ->
    Forall property (@query_canonical_rows TNull rows).
```

## `query_same_rows_as_bag_filter_length`

Source: [`theories/FormalSQL/QueryCardinality.v:782`](../QueryCardinality.v#L782)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates row cardinality and compositional bounds to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `filter`, `bag`, `cardinality`

Search aliases: `cardinality composition`, `filter`, `WHERE`, `cardinality`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_same_rows_as_bag_filter_length :
  forall keep rows bag,
    tuple_predicate_proper keep ->
    @query_same_rows_as_bag TNull rows bag ->
    List.length (filter keep rows) =
      List.length
        (filter keep
          (Febag.elements (Fecol.CBag (CTuple TNull)) bag)).
```

## `query_same_rows_as_bag_filter_length_between`

Source: [`theories/FormalSQL/QueryCardinality.v:805`](../QueryCardinality.v#L805)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates row cardinality and compositional bounds to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `filter`, `bag`, `cardinality`

Search aliases: `cardinality composition`, `filter`, `WHERE`, `cardinality`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_same_rows_as_bag_filter_length_between :
  forall keep first second bag,
    tuple_predicate_proper keep ->
    @query_same_rows_as_bag TNull first bag ->
    @query_same_rows_as_bag TNull second bag ->
    List.length (filter keep first) = List.length (filter keep second).
```

## `query_canonical_rows_length`

Source: [`theories/FormalSQL/QueryCardinality.v:819`](../QueryCardinality.v#L819)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates row cardinality and compositional bounds to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `grouping`, `cardinality`

Search aliases: `cardinality composition`, `GROUP BY`, `cardinality`

```rocq
Lemma query_canonical_rows_length :
  forall rows : list (tuple TNull),
    List.length (@query_canonical_rows TNull rows) = List.length rows.
```

## `row_attribute_present_conforms_join_left`

Source: [`theories/FormalSQL/QueryCardinality.v:846`](../QueryCardinality.v#L846)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the row attribute present conforms join left law for join cardinality, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join cardinality.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `join`, `cardinality`, `schema`

Search aliases: `cardinality composition`, `join`, `schema conformance`, `typing`, `cardinality`

```rocq
Lemma row_attribute_present_conforms_join_left :
  forall attribute left right,
    row_attribute_present_conforms attribute left ->
    row_attribute_present_conforms attribute (join_tuple TNull left right).
```

## `row_attribute_present_conforms_join_right`

Source: [`theories/FormalSQL/QueryCardinality.v:859`](../QueryCardinality.v#L859)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the row attribute present conforms join right law for join cardinality, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join cardinality.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `join`, `cardinality`, `schema`

Search aliases: `cardinality composition`, `join`, `schema conformance`, `typing`, `cardinality`

```rocq
Lemma row_attribute_present_conforms_join_right :
  forall attribute left right,
    (attribute inS? labels TNull left) = false ->
    row_attribute_present_conforms attribute right ->
    row_attribute_present_conforms attribute (join_tuple TNull left right).
```

## `brute_left_join_list_Forall`

Source: [`theories/FormalSQL/QueryCardinality.v:873`](../QueryCardinality.v#L873)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the brute left join list forall law for join cardinality, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join cardinality.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `join`, `cardinality`

Search aliases: `cardinality composition`, `join`, `cardinality`

```rocq
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
```

## `brute_left_join_list_Forall_left_attribute`

Source: [`theories/FormalSQL/QueryCardinality.v:900`](../QueryCardinality.v#L900)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the brute left join list forall left attribute law for join cardinality, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join cardinality.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `join`, `cardinality`, `schema`

Search aliases: `cardinality composition`, `join`, `schema conformance`, `typing`, `cardinality`

```rocq
Corollary brute_left_join_list_Forall_left_attribute :
  forall attribute left right,
    rows_attribute_present_conform attribute left ->
    rows_attribute_present_conform attribute
      (brute_left_join_list (tuple TNull) (join_tuple TNull) left right).
```

## `brute_left_join_list_Forall_right_attribute`

Source: [`theories/FormalSQL/QueryCardinality.v:916`](../QueryCardinality.v#L916)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the brute left join list forall right attribute law for join cardinality, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join cardinality.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `join`, `cardinality`, `schema`

Search aliases: `cardinality composition`, `join`, `schema conformance`, `typing`, `cardinality`

```rocq
Corollary brute_left_join_list_Forall_right_attribute :
  forall attribute left right,
    Forall (fun row => (attribute inS? labels TNull row) = false) left ->
    rows_attribute_present_conform attribute right ->
    rows_attribute_present_conform attribute
      (brute_left_join_list (tuple TNull) (join_tuple TNull) left right).
```

## `raw_cross_same_rows_as_bag`

Source: [`theories/FormalSQL/QueryCardinality.v:932`](../QueryCardinality.v#L932)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Bridges the two displayed representations of join cardinality.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join cardinality.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `join`, `bag`, `cardinality`

Search aliases: `cardinality composition`, `join`, `cross product`, `CROSS JOIN`, `cardinality`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma raw_cross_same_rows_as_bag :
  forall left right : list (tuple TNull),
    @query_same_rows_as_bag TNull
      (brute_left_join_list (tuple TNull) (join_tuple TNull) left right)
      (@query_cross_join_bag TNull
        (@query_rows_bag TNull left) (@query_rows_bag TNull right)).
```

## `raw_cross_filter_count_for_any_representative`

Source: [`theories/FormalSQL/QueryCardinality.v:956`](../QueryCardinality.v#L956)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the raw cross filter count for any representative law for join cardinality, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join cardinality.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `filter`, `join`, `cardinality`

Search aliases: `cardinality composition`, `join`, `cross product`, `CROSS JOIN`, `filter`, `WHERE`, `cardinality`

```rocq
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
```

## `interp_predicate_int32_nonnull_equal`

Source: [`theories/FormalSQL/QueryCardinality.v:973`](../QueryCardinality.v#L973)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the interp predicate int32 nonnull equal law for row cardinality and compositional bounds, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `cardinality`, `scalar`

Search aliases: `cardinality composition`, `predicate`, `Bool3`, `INTEGER`, `int32`, `cardinality`

```rocq
Lemma interp_predicate_int32_nonnull_equal :
  forall left right,
    NullValues.interp_predicate (PredicateEq)
      [NullValues.Value_int32 (Some left);
       NullValues.Value_int32 (Some right)] =
    match Z.compare (int32_value left) (int32_value right) with
    | Eq => true3
    | Lt | Gt => false3
    end.
```

## `interp_predicate_int32_null_left`

Source: [`theories/FormalSQL/QueryCardinality.v:986`](../QueryCardinality.v#L986)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `cardinality`, `scalar`

Search aliases: `cardinality composition`, `NULL`, `UNKNOWN`, `three-valued logic`, `predicate`, `Bool3`, `INTEGER`, `int32`, `cardinality`

```rocq
Lemma interp_predicate_int32_null_left :
  forall right,
    NullValues.interp_predicate (PredicateEq)
      [NullValues.Value_int32 None; right] = unknown3.
```

## `interp_predicate_int32_null_right`

Source: [`theories/FormalSQL/QueryCardinality.v:994`](../QueryCardinality.v#L994)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `cardinality`, `scalar`

Search aliases: `cardinality composition`, `NULL`, `UNKNOWN`, `three-valued logic`, `predicate`, `Bool3`, `INTEGER`, `int32`, `cardinality`

```rocq
Lemma interp_predicate_int32_null_right :
  forall left,
    NullValues.interp_predicate (PredicateEq)
      [NullValues.Value_int32 (Some left);
       NullValues.Value_int32 None] = unknown3.
```

## `postgres_int32_equal_true_eq`

Source: [`theories/FormalSQL/QueryCardinality.v:1008`](../QueryCardinality.v#L1008)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the postgres int32 equal true equality law for row cardinality and compositional bounds, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `cardinality`, `scalar`

Search aliases: `cardinality composition`, `INTEGER`, `int32`, `cardinality`

```rocq
Lemma postgres_int32_equal_true_eq :
  forall left_name right_name left right,
    value_conforms_attribute (Attr_int32 left_name) left ->
    value_conforms_attribute (Attr_int32 right_name) right ->
    postgres_int32_equal_true left right = true ->
    left = right.
```

## `NoDup_map_constant_filter_length_le_one`

Source: [`theories/FormalSQL/QueryCardinality.v:1041`](../QueryCardinality.v#L1041)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Provides the stated reusable upper bound for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `filter`, `cardinality`

Search aliases: `cardinality composition`, `filter`, `WHERE`, `cardinality`

```rocq
Lemma NoDup_map_constant_filter_length_le_one :
  forall (row key : Type) (key_of : row -> key) (accept : row -> bool)
         rows fixed,
    NoDup (map key_of rows) ->
    (forall row,
      In row rows -> accept row = true -> key_of row = fixed) ->
    (List.length (filter accept rows) <= 1)%nat.
```

## `int32_primary_key_true_matches_at_most_one`

Source: [`theories/FormalSQL/QueryCardinality.v:1079`](../QueryCardinality.v#L1079)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the int32 primary key true matches at most one law for row cardinality and compositional bounds, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `cardinality`, `schema`, `scalar`

Search aliases: `cardinality composition`, `INTEGER`, `int32`, `integrity constraint`, `key`, `cardinality`

```rocq
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
```

## `null_int32_primary_key_matches_none`

Source: [`theories/FormalSQL/QueryCardinality.v:1111`](../QueryCardinality.v#L1111)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses; keep schema/integrity conformance premises explicit.

Cross-index: `cardinality`, `schema`, `scalar`

Search aliases: `cardinality composition`, `NULL`, `UNKNOWN`, `three-valued logic`, `INTEGER`, `int32`, `integrity constraint`, `key`, `cardinality`

```rocq
Lemma null_int32_primary_key_matches_none :
  forall dimension_name dimension_rows,
    filter
      (fun row => postgres_int32_equal_true
        (NullValues.Value_int32 None)
        (dot TNull row (Attr_int32 dimension_name)))
      dimension_rows = nil.
```

## `partition_member_length_le`

Source: [`theories/FormalSQL/QueryCardinality.v:1130`](../QueryCardinality.v#L1130)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Provides the stated reusable upper bound for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `cardinality`

Search aliases: `cardinality composition`, `cardinality`

```rocq
Lemma partition_member_length_le :
  forall (row key : Type) (OK : Oset.Rcd key) (key_of : row -> key)
         rows key_value group,
    In (key_value, group) (@Partition.partition row key OK key_of rows) ->
    (List.length group <= List.length rows)%nat.
```

## `query_make_groups_member_length_le`

Source: [`theories/FormalSQL/QueryCardinality.v:1144`](../QueryCardinality.v#L1144)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Provides the stated reusable upper bound for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping`, `cardinality`

Search aliases: `cardinality composition`, `GROUP BY`, `cardinality`

```rocq
Theorem query_make_groups_member_length_le :
  forall env rows group_terms group,
    In group (@query_make_groups TNull env rows group_terms) ->
    (List.length group <= List.length rows)%nat.
```

## `query_make_groups_member_in`

Source: [`theories/FormalSQL/QueryCardinality.v:1162`](../QueryCardinality.v#L1162)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates membership or occurrence evidence to row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping`, `cardinality`

Search aliases: `cardinality composition`, `GROUP BY`, `cardinality`

```rocq
Lemma query_make_groups_member_in :
  forall env rows group_terms group row,
    In group (@query_make_groups TNull env rows group_terms) ->
    In row group ->
    In row rows.
```

## `query_make_groups_member_nonempty`

Source: [`theories/FormalSQL/QueryCardinality.v:1180`](../QueryCardinality.v#L1180)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the exact empty-input or empty-result law for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping`, `cardinality`

Search aliases: `cardinality composition`, `GROUP BY`, `cardinality`

```rocq
Lemma query_make_groups_member_nonempty :
  forall env rows group_terms group,
    group_terms <> nil ->
    In group (@query_make_groups TNull env rows group_terms) ->
    group <> nil.
```

## `partition_member_NoDupA`

Source: [`theories/FormalSQL/QueryCardinality.v:1196`](../QueryCardinality.v#L1196)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes the displayed duplicate-freedom property for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `cardinality`

Search aliases: `cardinality composition`, `cardinality`

```rocq
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
```

## `query_make_groups_member_NoDupA`

Source: [`theories/FormalSQL/QueryCardinality.v:1249`](../QueryCardinality.v#L1249)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes the displayed duplicate-freedom property for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping`, `cardinality`

Search aliases: `cardinality composition`, `GROUP BY`, `cardinality`

```rocq
Lemma query_make_groups_member_NoDupA :
  forall env rows group_terms group,
    NoDupA
      (fun left right => Oeset.compare (OTuple TNull) left right = Eq)
      rows ->
    In group (@query_make_groups TNull env rows group_terms) ->
    NoDupA
      (fun left right => Oeset.compare (OTuple TNull) left right = Eq)
      group.
```

## `query_make_groups_member_homogeneous`

Source: [`theories/FormalSQL/QueryCardinality.v:1277`](../QueryCardinality.v#L1277)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates membership or occurrence evidence to row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping`, `cardinality`

Search aliases: `cardinality composition`, `GROUP BY`, `cardinality`

```rocq
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
```

## `query_group_env_grouping_expression_member`

Source: [`theories/FormalSQL/QueryCardinality.v:1321`](../QueryCardinality.v#L1321)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates membership or occurrence evidence to row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping`, `cardinality`

Search aliases: `cardinality composition`, `GROUP BY`, `cardinality`

```rocq
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
```

## `query_distinct_group_finite_code_length_le`

Source: [`theories/FormalSQL/QueryCardinality.v:1377`](../QueryCardinality.v#L1377)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Provides the stated reusable upper bound for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping`, `cardinality`

Search aliases: `cardinality composition`, `GROUP BY`, `DISTINCT`, `duplicate elimination`, `cardinality`

```rocq
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
```

## `query_distinct_group_finite_Z_code_length_le`

Source: [`theories/FormalSQL/QueryCardinality.v:1415`](../QueryCardinality.v#L1415)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Provides the stated reusable upper bound for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping`, `cardinality`

Search aliases: `cardinality composition`, `GROUP BY`, `DISTINCT`, `duplicate elimination`, `cardinality`

```rocq
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
```

## `project_rows_success_length`

Source: [`theories/FormalSQL/QueryCardinality.v:1484`](../QueryCardinality.v#L1484)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates row cardinality and compositional bounds to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `projection`, `cardinality`

Search aliases: `cardinality composition`, `projection`, `SELECT list`, `cardinality`

```rocq
Lemma project_rows_success_length :
  forall env select_list rows output,
    @eval_project_rows_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule env select_list rows (SqlSuccess output) ->
    List.length output = List.length rows.
```

## `project_rows_success_Forall`

Source: [`theories/FormalSQL/QueryCardinality.v:1497`](../QueryCardinality.v#L1497)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Inverts or constructs the successful evaluation branch for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `projection`, `cardinality`

Search aliases: `cardinality composition`, `projection`, `SELECT list`, `cardinality`

```rocq
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
```

## `eval_query_expr_row_map_success_length`

Source: [`theories/FormalSQL/QueryCardinality.v:1529`](../QueryCardinality.v#L1529)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates row cardinality and compositional bounds to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `projection`, `cardinality`

Search aliases: `cardinality composition`, `projection`, `SELECT list`, `cardinality`

```rocq
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
```

## `query_same_rows_as_bag_length_N`

Source: [`theories/FormalSQL/QueryCardinality.v:1565`](../QueryCardinality.v#L1565)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates row cardinality and compositional bounds to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `cardinality`

Search aliases: `cardinality composition`, `cardinality`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_same_rows_as_bag_length_N :
  forall rows bag,
    @query_same_rows_as_bag T rows bag ->
    N.of_nat (List.length rows) =
      Febag.cardinal (Fecol.CBag (CTuple T)) bag.
```

## `query_same_rows_as_bag_length_le`

Source: [`theories/FormalSQL/QueryCardinality.v:1581`](../QueryCardinality.v#L1581)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Provides the stated reusable upper bound for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `cardinality`

Search aliases: `cardinality composition`, `cardinality`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_same_rows_as_bag_length_le :
  forall rows bag bound,
    @query_same_rows_as_bag T rows bag ->
    (Febag.cardinal (Fecol.CBag (CTuple T)) bag <=
      N.of_nat bound)%N ->
    (List.length rows <= bound)%nat.
```

## `query_success_length_le_error`

Source: [`theories/FormalSQL/QueryCardinality.v:1598`](../QueryCardinality.v#L1598)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Provides the stated reusable upper bound for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `cardinality`

Search aliases: `cardinality composition`, `runtime outcome`, `runtime safety`, `error propagation`, `cardinality`

```rocq
Lemma query_success_length_le_error :
  forall env outputs error bound,
    query_success_length_le env (QExpr_Error outputs error) bound.
```

## `query_success_length_le_values`

Source: [`theories/FormalSQL/QueryCardinality.v:1607`](../QueryCardinality.v#L1607)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Provides the stated reusable upper bound for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `cardinality`

Search aliases: `cardinality composition`, `cardinality`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_success_length_le_values :
  forall env outputs values bound,
    (Febag.cardinal (Fecol.CBag (CTuple T)) values <=
      N.of_nat bound)%N ->
    query_success_length_le env (QExpr_Values outputs values) bound.
```

## `query_success_length_le_table`

Source: [`theories/FormalSQL/QueryCardinality.v:1622`](../QueryCardinality.v#L1622)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Provides the stated reusable upper bound for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `cardinality`

Search aliases: `cardinality composition`, `cardinality`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_success_length_le_table :
  forall env outputs table bound,
    @query_outputs_sort T outputs =S= basesort table ->
    (Febag.cardinal (Fecol.CBag (CTuple T)) (instance table) <=
      N.of_nat bound)%N ->
    query_success_length_le env (QExpr_Table outputs table) bound.
```

## `query_success_length_le_project`

Source: [`theories/FormalSQL/QueryCardinality.v:1654`](../QueryCardinality.v#L1654)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Provides the stated reusable upper bound for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `projection`, `cardinality`

Search aliases: `cardinality composition`, `projection`, `SELECT list`, `cardinality`

```rocq
Lemma query_success_length_le_project :
  forall env select_list input bound,
    query_success_length_le env input bound ->
    query_success_length_le env (QExpr_Project select_list input) bound.
```

## `query_success_length_le_row_map`

Source: [`theories/FormalSQL/QueryCardinality.v:1671`](../QueryCardinality.v#L1671)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Provides the stated reusable upper bound for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `projection`, `cardinality`

Search aliases: `cardinality composition`, `projection`, `SELECT list`, `cardinality`

```rocq
Lemma query_success_length_le_row_map :
  forall env outputs row_map input bound,
    query_success_length_le env input bound ->
    query_success_length_le env
      (QExpr_RowMap outputs row_map input) bound.
```

## `query_success_length_le_offset`

Source: [`theories/FormalSQL/QueryCardinality.v:1687`](../QueryCardinality.v#L1687)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Provides the stated reusable upper bound for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain exact order whenever the declaration observes it.

Cross-index: `ordered`, `cardinality`

Search aliases: `cardinality composition`, `OFFSET`, `cardinality`

```rocq
Lemma query_success_length_le_offset :
  forall env offset input bound,
    query_success_length_le env input bound ->
    query_success_length_le env
      (QExpr_Offset offset input) (bound - offset).
```

## `query_offset_success_nil_of_input_length_le`

Source: [`theories/FormalSQL/QueryCardinality.v:1706`](../QueryCardinality.v#L1706)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Provides the stated reusable upper bound for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain exact order whenever the declaration observes it.

Cross-index: `ordered`, `cardinality`

Search aliases: `cardinality composition`, `OFFSET`, `cardinality`

```rocq
Lemma query_offset_success_nil_of_input_length_le :
  forall env offset input,
    query_success_length_le env input offset ->
    forall output,
      @eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env (QExpr_Offset offset input) (SqlSuccess output) ->
      output = nil.
```

## `query_success_length_le_fetch`

Source: [`theories/FormalSQL/QueryCardinality.v:1725`](../QueryCardinality.v#L1725)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Provides the stated reusable upper bound for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain exact order whenever the declaration observes it.

Cross-index: `ordered`, `cardinality`

Search aliases: `cardinality composition`, `FETCH`, `LIMIT`, `cardinality`

```rocq
Lemma query_success_length_le_fetch :
  forall env count input bound,
    query_success_length_le env input bound ->
    query_success_length_le env
      (QExpr_Fetch count input) (Nat.min count bound).
```

## `query_success_length_le_fetch_count`

Source: [`theories/FormalSQL/QueryCardinality.v:1742`](../QueryCardinality.v#L1742)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Provides the stated reusable upper bound for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: retain exact order whenever the declaration observes it.

Cross-index: `ordered`, `cardinality`

Search aliases: `cardinality composition`, `FETCH`, `LIMIT`, `cardinality`

```rocq
Lemma query_success_length_le_fetch_count :
  forall env count input,
    query_success_length_le env (QExpr_Fetch count input) count.
```

## `query_success_length_le_order_by`

Source: [`theories/FormalSQL/QueryCardinality.v:1756`](../QueryCardinality.v#L1756)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Provides the stated reusable upper bound for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain exact order whenever the declaration observes it.

Cross-index: `ordered`, `cardinality`

Search aliases: `cardinality composition`, `ORDER BY`, `ordered observation`, `cardinality`

```rocq
Lemma query_success_length_le_order_by :
  forall env keys input bound,
    query_success_length_le env input bound ->
    query_success_length_le env (QExpr_OrderBy keys input) bound.
```

## `tuple_mk_set_cardinal_le`

Source: [`theories/FormalSQL/QueryCardinality.v:1776`](../QueryCardinality.v#L1776)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Provides the stated reusable upper bound for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `cardinality`

Search aliases: `cardinality composition`, `cardinality`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma tuple_mk_set_cardinal_le :
  forall rows : list (tuple T),
    (Feset.cardinal (Fecol.CSet (CTuple T))
      (Feset.mk_set (Fecol.CSet (CTuple T)) rows) <=
     List.length rows)%nat.
```

## `query_distinct_bag_cardinal_le`

Source: [`theories/FormalSQL/QueryCardinality.v:1824`](../QueryCardinality.v#L1824)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Provides the stated reusable upper bound for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `cardinality`

Search aliases: `cardinality composition`, `DISTINCT`, `duplicate elimination`, `cardinality`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_distinct_bag_cardinal_le :
  forall input,
    (Febag.cardinal (Fecol.CBag (CTuple T))
       (@query_distinct_bag T input) <=
     Febag.cardinal (Fecol.CBag (CTuple T)) input)%N.
```

## `query_success_length_le_distinct`

Source: [`theories/FormalSQL/QueryCardinality.v:1841`](../QueryCardinality.v#L1841)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Provides the stated reusable upper bound for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `cardinality`

Search aliases: `cardinality composition`, `DISTINCT`, `duplicate elimination`, `cardinality`

```rocq
Lemma query_success_length_le_distinct :
  forall env input bound,
    query_success_length_le env input bound ->
    query_success_length_le env (QExpr_Distinct input) bound.
```

## `oeset_pointwise_nb_occ_le_length`

Source: [`theories/FormalSQL/QueryCardinality.v:1877`](../QueryCardinality.v#L1877)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates row cardinality and compositional bounds to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `cardinality`

Search aliases: `cardinality composition`, `cardinality`, `multiplicity`

```rocq
Lemma oeset_pointwise_nb_occ_le_length :
  forall (A : Type) (ordered : Oeset.Rcd A) (left right : list A),
    (forall value,
      (Oeset.nb_occ ordered value left <=
       Oeset.nb_occ ordered value right)%N) ->
    (List.length left <= List.length right)%nat.
```

## `febag_cardinal_le_of_nb_occ_le`

Source: [`theories/FormalSQL/QueryCardinality.v:1914`](../QueryCardinality.v#L1914)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Provides the stated reusable upper bound for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `cardinality`

Search aliases: `cardinality composition`, `cardinality`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma febag_cardinal_le_of_nb_occ_le :
  forall (A : Type) (ordered : Oeset.Rcd A)
      (bags : Febag.Rcd ordered) left right,
    (forall value,
      (Febag.nb_occ bags value left <=
       Febag.nb_occ bags value right)%N) ->
    (Febag.cardinal bags left <= Febag.cardinal bags right)%N.
```

## `febag_cardinal_union`

Source: [`theories/FormalSQL/QueryCardinality.v:1931`](../QueryCardinality.v#L1931)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates row cardinality and compositional bounds to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `cardinality`

Search aliases: `cardinality composition`, `cardinality`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma febag_cardinal_union :
  forall (A : Type) (ordered : Oeset.Rcd A)
      (bags : Febag.Rcd ordered) left right,
    Febag.cardinal bags (Febag.union bags left right) =
      (Febag.cardinal bags left + Febag.cardinal bags right)%N.
```

## `febag_cardinal_union_max_le`

Source: [`theories/FormalSQL/QueryCardinality.v:1949`](../QueryCardinality.v#L1949)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates row cardinality and compositional bounds to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `cardinality`

Search aliases: `cardinality composition`, `cardinality`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma febag_cardinal_union_max_le :
  forall (A : Type) (ordered : Oeset.Rcd A)
      (bags : Febag.Rcd ordered) left right,
    (Febag.cardinal bags (Febag.union_max bags left right) <=
      Febag.cardinal bags left + Febag.cardinal bags right)%N.
```

## `febag_cardinal_inter_le_left`

Source: [`theories/FormalSQL/QueryCardinality.v:1962`](../QueryCardinality.v#L1962)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates row cardinality and compositional bounds to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `cardinality`

Search aliases: `cardinality composition`, `cardinality`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma febag_cardinal_inter_le_left :
  forall (A : Type) (ordered : Oeset.Rcd A)
      (bags : Febag.Rcd ordered) left right,
    (Febag.cardinal bags (Febag.inter bags left right) <=
      Febag.cardinal bags left)%N.
```

## `febag_cardinal_inter_le_right`

Source: [`theories/FormalSQL/QueryCardinality.v:1973`](../QueryCardinality.v#L1973)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates row cardinality and compositional bounds to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `cardinality`

Search aliases: `cardinality composition`, `cardinality`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma febag_cardinal_inter_le_right :
  forall (A : Type) (ordered : Oeset.Rcd A)
      (bags : Febag.Rcd ordered) left right,
    (Febag.cardinal bags (Febag.inter bags left right) <=
      Febag.cardinal bags right)%N.
```

## `febag_cardinal_diff_le_left`

Source: [`theories/FormalSQL/QueryCardinality.v:1984`](../QueryCardinality.v#L1984)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates row cardinality and compositional bounds to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `cardinality`

Search aliases: `cardinality composition`, `cardinality`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma febag_cardinal_diff_le_left :
  forall (A : Type) (ordered : Oeset.Rcd A)
      (bags : Febag.Rcd ordered) left right,
    (Febag.cardinal bags (Febag.diff bags left right) <=
      Febag.cardinal bags left)%N.
```

## `query_set_cardinality_bound_union`

Source: [`theories/FormalSQL/QueryCardinality.v:1998`](../QueryCardinality.v#L1998)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates SQL bag/set operations to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `cardinality`

Search aliases: `cardinality composition`, `set operation`, `UNION`, `cardinality`

```rocq
Lemma query_set_cardinality_bound_union :
  forall left right left_bound right_bound,
    query_set_cardinality_bound Union left right
      left_bound right_bound (left_bound + right_bound).
```

## `query_set_cardinality_bound_union_max`

Source: [`theories/FormalSQL/QueryCardinality.v:2011`](../QueryCardinality.v#L2011)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates SQL bag/set operations to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `cardinality`

Search aliases: `cardinality composition`, `set operation`, `UNION`, `cardinality`

```rocq
Lemma query_set_cardinality_bound_union_max :
  forall left right left_bound right_bound,
    query_set_cardinality_bound UnionMax left right
      left_bound right_bound (left_bound + right_bound).
```

## `query_set_cardinality_bound_inter`

Source: [`theories/FormalSQL/QueryCardinality.v:2025`](../QueryCardinality.v#L2025)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates SQL bag/set operations to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `cardinality`

Search aliases: `cardinality composition`, `set operation`, `INTERSECT`, `cardinality`

```rocq
Lemma query_set_cardinality_bound_inter :
  forall left right left_bound right_bound,
    query_set_cardinality_bound Inter left right
      left_bound right_bound (Nat.min left_bound right_bound).
```

## `query_set_cardinality_bound_diff`

Source: [`theories/FormalSQL/QueryCardinality.v:2041`](../QueryCardinality.v#L2041)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for SQL bag/set operations.

Applicability: Use in either direction to invert or construct a goal about SQL bag/set operations.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `cardinality`

Search aliases: `cardinality composition`, `set operation`, `EXCEPT`, `cardinality`

```rocq
Lemma query_set_cardinality_bound_diff :
  forall left right left_bound right_bound,
    query_set_cardinality_bound Diff left right
      left_bound right_bound left_bound.
```

## `query_success_length_le_set`

Source: [`theories/FormalSQL/QueryCardinality.v:2054`](../QueryCardinality.v#L2054)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Provides the stated reusable upper bound for SQL bag/set operations.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `cardinality`

Search aliases: `cardinality composition`, `set operation`, `cardinality`

```rocq
Lemma query_success_length_le_set :
  forall env operation left right left_bound right_bound output_bound,
    query_success_length_le env left left_bound ->
    query_success_length_le env right right_bound ->
    query_set_cardinality_bound operation left right
      left_bound right_bound output_bound ->
    query_success_length_le env (QExpr_Set operation left right) output_bound.
```

## `query_rank_rows_outcome_success_length`

Source: [`theories/FormalSQL/QueryCardinality.v:2078`](../QueryCardinality.v#L2078)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates row cardinality and compositional bounds to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `outcome`, `runtime`, `cardinality`

Search aliases: `cardinality composition`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `cardinality`

```rocq
Lemma query_rank_rows_outcome_success_length :
  forall partition_keys order_keys rank_attribute rank_value all_rows rows output,
    @query_rank_rows_outcome T value_is_null
      partition_keys order_keys rank_attribute rank_value all_rows rows =
      Some output ->
    List.length output = List.length rows.
```

## `query_rank_bag_rows_length`

Source: [`theories/FormalSQL/QueryCardinality.v:2096`](../QueryCardinality.v#L2096)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates row cardinality and compositional bounds to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `cardinality`

Search aliases: `cardinality composition`, `cardinality`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_rank_bag_rows_length :
  forall rows : list (tuple T),
    List.length (query_rank_bag_rows (rows_bag T rows)) = List.length rows.
```

## `query_window_rows_outcome_success_length`

Source: [`theories/FormalSQL/QueryCardinality.v:2111`](../QueryCardinality.v#L2111)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates row cardinality and compositional bounds to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `outcome`, `runtime`, `cardinality`

Search aliases: `cardinality composition`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `cardinality`

```rocq
Lemma query_window_rows_outcome_success_length :
  forall env partition_keys items previous position prefix rows output,
    @query_window_rows_outcome T symbol_runtime_error aggregate_runtime_error
      value_is_null env partition_keys items previous position prefix rows =
      Some (SqlSuccess output) ->
    List.length output = List.length rows.
```

## `eval_query_expr_rank_success_length`

Source: [`theories/FormalSQL/QueryCardinality.v:2149`](../QueryCardinality.v#L2149)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates row cardinality and compositional bounds to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain exact order whenever the declaration observes it.

Cross-index: `ordered`, `cardinality`

Search aliases: `cardinality composition`, `window`, `PARTITION BY`, `cardinality`

```rocq
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
```

## `eval_query_expr_window_success_length`

Source: [`theories/FormalSQL/QueryCardinality.v:2187`](../QueryCardinality.v#L2187)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates row cardinality and compositional bounds to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain exact order whenever the declaration observes it.

Cross-index: `ordered`, `cardinality`

Search aliases: `cardinality composition`, `window`, `PARTITION BY`, `cardinality`

```rocq
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
```

## `query_success_length_le_rank`

Source: [`theories/FormalSQL/QueryCardinality.v:2234`](../QueryCardinality.v#L2234)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Provides the stated reusable upper bound for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain exact order whenever the declaration observes it.

Cross-index: `ordered`, `cardinality`

Search aliases: `cardinality composition`, `window`, `PARTITION BY`, `cardinality`

```rocq
Lemma query_success_length_le_rank :
  forall env partition_keys order_keys rank_attribute rank_value input bound,
    query_success_length_le env input bound ->
    query_success_length_le env
      (QExpr_Rank partition_keys order_keys rank_attribute rank_value input)
      bound.
```

## `query_success_length_le_window`

Source: [`theories/FormalSQL/QueryCardinality.v:2250`](../QueryCardinality.v#L2250)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Provides the stated reusable upper bound for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain exact order whenever the declaration observes it.

Cross-index: `ordered`, `cardinality`

Search aliases: `cardinality composition`, `window`, `PARTITION BY`, `cardinality`

```rocq
Lemma query_success_length_le_window :
  forall env partition_keys order_keys items input bound,
    query_success_length_le env input bound ->
    query_success_length_le env
      (QExpr_Window partition_keys order_keys items input) bound.
```

## `if_tuple_rows_success_true`

Source: [`theories/FormalSQL/QueryCardinality.v:2264`](../QueryCardinality.v#L2264)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Inverts or constructs the successful evaluation branch for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `cardinality`

Search aliases: `cardinality composition`, `cardinality`

```rocq
Lemma if_tuple_rows_success_true :
  forall (test : bool) (row : tuple T)
      (tail output : list (tuple T)),
    test = true ->
    (if test
     then SqlSuccess (row :: tail)
     else SqlSuccess tail) = SqlSuccess output ->
    output = row :: tail.
```

## `if_tuple_rows_success_false`

Source: [`theories/FormalSQL/QueryCardinality.v:2277`](../QueryCardinality.v#L2277)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Inverts or constructs the successful evaluation branch for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `cardinality`

Search aliases: `cardinality composition`, `cardinality`

```rocq
Lemma if_tuple_rows_success_false :
  forall (test : bool) (row : tuple T)
      (tail output : list (tuple T)),
    test = false ->
    (if test
     then SqlSuccess (row :: tail)
     else SqlSuccess tail) = SqlSuccess output ->
    output = tail.
```

## `filter_rows_success_length_le`

Source: [`theories/FormalSQL/QueryCardinality.v:2290`](../QueryCardinality.v#L2290)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Provides the stated reusable upper bound for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `filter`, `cardinality`

Search aliases: `cardinality composition`, `filter`, `WHERE`, `cardinality`

```rocq
Lemma filter_rows_success_length_le :
  forall env formula rows output,
    @eval_filter_rows_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule env formula rows (SqlSuccess output) ->
    (List.length output <= List.length rows)%nat.
```

## `query_success_length_le_filter`

Source: [`theories/FormalSQL/QueryCardinality.v:2322`](../QueryCardinality.v#L2322)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Provides the stated reusable upper bound for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `filter`, `cardinality`

Search aliases: `cardinality composition`, `filter`, `WHERE`, `cardinality`

```rocq
Lemma query_success_length_le_filter :
  forall env formula input bound,
    query_success_length_le env input bound ->
    query_success_length_le env (QExpr_Filter formula input) bound.
```

## `filter_cons_outcome_success_Forall`

Source: [`theories/FormalSQL/QueryCardinality.v:2335`](../QueryCardinality.v#L2335)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Inverts or constructs the successful evaluation branch for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `outcome`, `runtime`, `filter`, `cardinality`

Search aliases: `cardinality composition`, `filter`, `WHERE`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `cardinality`

```rocq
Lemma filter_cons_outcome_success_Forall :
  forall truth row tail output (property : tuple T -> Prop),
    property row ->
    Forall property tail ->
    @filter_cons_outcome T truth row (SqlSuccess tail) = SqlSuccess output ->
    Forall property output.
```

## `filter_rows_success_Forall`

Source: [`theories/FormalSQL/QueryCardinality.v:2349`](../QueryCardinality.v#L2349)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Inverts or constructs the successful evaluation branch for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `filter`, `cardinality`

Search aliases: `cardinality composition`, `filter`, `WHERE`, `cardinality`

```rocq
Lemma filter_rows_success_Forall :
  forall env formula rows output (property : tuple T -> Prop),
    @eval_filter_rows_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule env formula rows (SqlSuccess output) ->
    Forall property rows ->
    Forall property output.
```

## `filter_rows_success_Forall_accepted`

Source: [`theories/FormalSQL/QueryCardinality.v:2380`](../QueryCardinality.v#L2380)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Inverts or constructs the successful evaluation branch for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `filter`, `cardinality`

Search aliases: `cardinality composition`, `filter`, `WHERE`, `cardinality`

```rocq
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
```

## `filter_rows_success_exact_count`

Source: [`theories/FormalSQL/QueryCardinality.v:2417`](../QueryCardinality.v#L2417)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Inverts or constructs the successful evaluation branch for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `filter`, `cardinality`

Search aliases: `cardinality composition`, `filter`, `WHERE`, `cardinality`

```rocq
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
```

## `filter_rows_error_observable`

Source: [`theories/FormalSQL/QueryCardinality.v:2458`](../QueryCardinality.v#L2458)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `filter`, `cardinality`

Search aliases: `cardinality composition`, `filter`, `WHERE`, `runtime outcome`, `runtime safety`, `error propagation`, `cardinality`

```rocq
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
```

## `eval_groups_success_length_le`

Source: [`theories/FormalSQL/QueryCardinality.v:2476`](../QueryCardinality.v#L2476)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Provides the stated reusable upper bound for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping`, `cardinality`

Search aliases: `cardinality composition`, `GROUP BY`, `cardinality`

```rocq
Lemma eval_groups_success_length_le :
  forall env select_list group_terms having groups output,
    @eval_groups_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule env select_list group_terms having groups
      (SqlSuccess output) ->
    (List.length output <= List.length groups)%nat.
```

## `int32_composite_primary_key_true_matches_at_most_one`

Source: [`theories/FormalSQL/QueryCardinality.v:2517`](../QueryCardinality.v#L2517)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the int32 composite primary key true matches at most one law for row cardinality and compositional bounds, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `cardinality`, `schema`, `scalar`

Search aliases: `cardinality composition`, `INTEGER`, `int32`, `integrity constraint`, `key`, `cardinality`

```rocq
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
```

## `functional_theta_join_chain_length_le`

Source: [`theories/FormalSQL/QueryCardinality.v:2579`](../QueryCardinality.v#L2579)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Provides the stated reusable upper bound for join cardinality.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join cardinality.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `join`, `cardinality`

Search aliases: `cardinality composition`, `join`, `cardinality`

```rocq
Theorem functional_theta_join_chain_length_le :
  forall (row : Type) (join : row -> row -> row) left stages,
    Forall theta_stage_is_functional stages ->
    (List.length (functional_theta_join_chain row join left stages) <=
      List.length left)%nat.
```

## `rows_attribute_conform_filter`

Source: [`theories/FormalSQL/QueryCardinality.v:2598`](../QueryCardinality.v#L2598)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the rows attribute conform filter law for row cardinality and compositional bounds, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `filter`, `cardinality`, `schema`

Search aliases: `cardinality composition`, `filter`, `WHERE`, `schema conformance`, `typing`, `cardinality`

```rocq
Lemma rows_attribute_conform_filter :
  forall attribute rows keep,
    rows_attribute_conform attribute rows ->
    rows_attribute_conform attribute (filter keep rows).
```

## `NoDup_map_filter`

Source: [`theories/FormalSQL/QueryCardinality.v:2608`](../QueryCardinality.v#L2608)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes the displayed duplicate-freedom property for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `filter`, `cardinality`

Search aliases: `cardinality composition`, `filter`, `WHERE`, `cardinality`

```rocq
Lemma NoDup_map_filter :
  forall (row key : Type) (key_of : row -> key) keep rows,
    NoDup (map key_of rows) ->
    NoDup (map key_of (filter keep rows)).
```

## `primary_key_conforms_filter`

Source: [`theories/FormalSQL/QueryCardinality.v:2628`](../QueryCardinality.v#L2628)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the primary key conforms filter law for row cardinality and compositional bounds, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `filter`, `cardinality`, `schema`

Search aliases: `cardinality composition`, `filter`, `WHERE`, `integrity constraint`, `key`, `cardinality`

```rocq
Lemma primary_key_conforms_filter :
  forall primary_key rows keep,
    primary_key_conforms primary_key rows ->
    primary_key_conforms primary_key (filter keep rows).
```
