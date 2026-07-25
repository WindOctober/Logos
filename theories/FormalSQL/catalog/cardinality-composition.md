# Query cardinality and compositional bounds

Route here for: row-count bounds, functional joins, filters, groups, finite images.

This focused catalog contains 101 declarations routed at declaration granularity from `CardinalityCombinators.v`, `QueryCardinality.v`. Source declarations are authoritative; every statement below is verbatim and has no proof body.

## `bag_map_cardinal`

Source: [`theories/FormalSQL/CardinalityCombinators.v:15`](../CardinalityCombinators.v#L15)

Purpose/direction: Relates row cardinality and compositional bounds to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 52), `cardinality` (rank 36)

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

Purpose/direction: Provides the stated reusable upper bound for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `filter` (rank 46), `bag` (rank 52), `cardinality` (rank 36)

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

Purpose/direction: Establishes commutativity for the declared row cardinality and compositional bounds operator.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `filter` (rank 46), `cardinality` (rank 36)

Search aliases: `cardinality composition`, `filter`, `WHERE`, `cardinality`

```rocq
Lemma filter_filter_commute :
  forall (A : Type) (first second : A -> bool) rows,
    filter first (filter second rows) =
    filter second (filter first rows).
```

## `flat_map_uniform_length_le`

Source: [`theories/FormalSQL/CardinalityCombinators.v:71`](../CardinalityCombinators.v#L71)

Purpose/direction: Provides the stated reusable upper bound for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `cardinality` (rank 24)

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

## `nonempty_groups_count_le_total_length`

Source: [`theories/FormalSQL/CardinalityCombinators.v:90`](../CardinalityCombinators.v#L90)

Purpose/direction: Relates row cardinality and compositional bounds to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping` (rank 52), `cardinality` (rank 28)

Search aliases: `cardinality composition`, `GROUP BY`, `cardinality`

```rocq
Lemma nonempty_groups_count_le_total_length :
  forall (A Group : Type) (members : Group -> list A) groups,
    Forall (fun group => members group <> nil) groups ->
    (List.length groups <= List.length (flat_map members groups))%nat.
```

## `NoDupA_pairwise_filter_length_le_one`

Source: [`theories/FormalSQL/CardinalityCombinators.v:107`](../CardinalityCombinators.v#L107)

Purpose/direction: Provides the stated reusable upper bound for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `filter` (rank 46), `cardinality` (rank 24)

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

Source: [`theories/FormalSQL/CardinalityCombinators.v:149`](../CardinalityCombinators.v#L149)

Purpose/direction: Provides the stated reusable upper bound for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `filter` (rank 46), `cardinality` (rank 24)

Search aliases: `cardinality composition`, `filter`, `WHERE`, `cardinality`

```rocq
Lemma filter_singleton_of_nonempty_length_le_one :
  forall (A : Type) (keep : A -> bool) rows,
    (exists row, In row rows /\ keep row = true) ->
    (List.length (filter keep rows) <= 1)%nat ->
    exists row, filter keep rows = [row].
```

## `map_theta_join_total_functional`

Source: [`theories/FormalSQL/CardinalityCombinators.v:172`](../CardinalityCombinators.v#L172)

Purpose/direction: Identifies the exact projected join list with the pointwise mapped left input under total and at-most-one matching.

Applicability: Use to replace a projected total-functional join by the exact mapped left list; duplicate left occurrences and list order are preserved.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `join` (rank 38), `cardinality` (rank 36)

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

Source: [`theories/FormalSQL/CardinalityCombinators.v:209`](../CardinalityCombinators.v#L209)

Purpose/direction: States the map theta join functional permut filter exists law for join cardinality, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join cardinality.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `filter` (rank 46), `join` (rank 42), `cardinality` (rank 36)

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

Source: [`theories/FormalSQL/CardinalityCombinators.v:282`](../CardinalityCombinators.v#L282)

Purpose/direction: States the exact empty-input or empty-result law for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `filter` (rank 46), `cardinality` (rank 36)

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

Source: [`theories/FormalSQL/CardinalityCombinators.v:304`](../CardinalityCombinators.v#L304)

Purpose/direction: Identifies the exact projected join list with the pointwise mapped left input under total and at-most-one matching.

Applicability: Use to replace a projected total-functional join by the exact mapped left list; duplicate left occurrences and list order are preserved.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `join` (rank 38), `cardinality` (rank 36)

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

Source: [`theories/FormalSQL/CardinalityCombinators.v:340`](../CardinalityCombinators.v#L340)

Purpose/direction: Identifies a projected at-most-one LEFT JOIN with the mapped left input up to semantic permutation, retaining unmatched and duplicate left occurrences without a total-match premise.

Applicability: Use when each left occurrence has zero or one accepted right occurrence and matched and padded rows project to the same direct left result; semantic permutation preserves duplicate left rows.

Important premises: Retain both matched and padded projection equalities and the per-left at-most-one bound.  No foreign-key totality premise is required; the conclusion is occurrence-preserving permutation.

Cross-index: `join` (rank 10), `cardinality` (rank 36)

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

## `NoDupA_map_preimage`

Source: [`theories/FormalSQL/CardinalityCombinators.v:419`](../CardinalityCombinators.v#L419)

Purpose/direction: Establishes the displayed duplicate-freedom property for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `cardinality` (rank 36)

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

Source: [`theories/FormalSQL/CardinalityCombinators.v:445`](../CardinalityCombinators.v#L445)

Purpose/direction: Establishes the displayed duplicate-freedom property for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `cardinality` (rank 36)

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

Source: [`theories/FormalSQL/CardinalityCombinators.v:479`](../CardinalityCombinators.v#L479)

Purpose/direction: Establishes the displayed duplicate-freedom property for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `filter` (rank 46), `cardinality` (rank 36)

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

Source: [`theories/FormalSQL/CardinalityCombinators.v:546`](../CardinalityCombinators.v#L546)

Purpose/direction: Gives necessary and sufficient conditions for row cardinality and compositional bounds.

Applicability: Use in either direction to invert or construct a goal about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `cardinality` (rank 36)

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

Source: [`theories/FormalSQL/CardinalityCombinators.v:594`](../CardinalityCombinators.v#L594)

Purpose/direction: Provides the stated reusable upper bound for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `cardinality` (rank 22)

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

Source: [`theories/FormalSQL/CardinalityCombinators.v:620`](../CardinalityCombinators.v#L620)

Purpose/direction: Provides the stated reusable upper bound for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `cardinality` (rank 23)

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

Source: [`theories/FormalSQL/CardinalityCombinators.v:653`](../CardinalityCombinators.v#L653)

Purpose/direction: Provides the stated reusable upper bound for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `cardinality` (rank 23)

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

Source: [`theories/FormalSQL/CardinalityCombinators.v:690`](../CardinalityCombinators.v#L690)

Purpose/direction: Relates row cardinality and compositional bounds to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 52), `cardinality` (rank 28)

Search aliases: `cardinality composition`, `cardinality`, `multiplicity`

```rocq
Lemma oeset_nb_occ_le_length :
  forall (A : Type) (ordered : Oeset.Rcd A) value rows,
    (Oeset.nb_occ ordered value rows <=
      N.of_nat (List.length rows))%N.
```

## `instance_row_multiplicity_le_length`

Source: [`theories/FormalSQL/CardinalityCombinators.v:715`](../CardinalityCombinators.v#L715)

Purpose/direction: Relates row cardinality and compositional bounds to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 51), `cardinality` (rank 27)

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

Source: [`theories/FormalSQL/CardinalityCombinators.v:728`](../CardinalityCombinators.v#L728)

Purpose/direction: States the exact empty-input or empty-result law for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 51), `cardinality` (rank 35)

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

Source: [`theories/FormalSQL/CardinalityCombinators.v:747`](../CardinalityCombinators.v#L747)

Purpose/direction: Provides the stated reusable upper bound for join cardinality.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join cardinality.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `join` (rank 42), `cardinality` (rank 24)

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

Source: [`theories/FormalSQL/CardinalityCombinators.v:766`](../CardinalityCombinators.v#L766)

Purpose/direction: Provides the stated reusable upper bound for join cardinality.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join cardinality.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `join` (rank 41), `cardinality` (rank 23)

Search aliases: `cardinality composition`, `join`, `cardinality`

```rocq
Corollary theta_join_list_length_le_product :
  forall (row : Type) (join : row -> row -> row)
      (accept : row -> row -> bool) left right,
    (List.length (theta_join_list row join accept left right) <=
      List.length left * List.length right)%nat.
```

## `filter_theta_join_list_degree_length_le`

Source: [`theories/FormalSQL/CardinalityCombinators.v:780`](../CardinalityCombinators.v#L780)

Purpose/direction: Provides the stated reusable upper bound for join cardinality.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join cardinality.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `filter` (rank 45), `join` (rank 41), `cardinality` (rank 23)

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

Source: [`theories/FormalSQL/CardinalityCombinators.v:820`](../CardinalityCombinators.v#L820)

Purpose/direction: Provides the stated reusable upper bound for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `cardinality` (rank 22)

Search aliases: `cardinality composition`, `cardinality`

```rocq
Theorem expansion_pipeline_length_le :
  forall (A : Type) stages bounds rows,
    @expansion_pipeline_bounds A stages bounds ->
    (List.length (expansion_pipeline A stages rows) <=
      List.length rows * multiply_bounds bounds)%nat.
```

## `partition_flatten_length`

Source: [`theories/FormalSQL/CardinalityCombinators.v:844`](../CardinalityCombinators.v#L844)

Purpose/direction: Relates row cardinality and compositional bounds to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `cardinality` (rank 28)

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

Source: [`theories/FormalSQL/CardinalityCombinators.v:859`](../CardinalityCombinators.v#L859)

Purpose/direction: States the partition group count upper-bound law for row cardinality and compositional bounds, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `grouping` (rank 50), `cardinality` (rank 34)

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

Purpose/direction: Provides the stated reusable upper bound for join cardinality.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join cardinality.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `join` (rank 42), `cardinality` (rank 24)

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

Purpose/direction: Relates join cardinality to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join cardinality.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `join` (rank 42), `cardinality` (rank 28)

Search aliases: `cardinality composition`, `join`, `cardinality`

```rocq
Lemma brute_left_join_list_length_mul :
  forall (row : Type) (join : row -> row -> row) left right,
    List.length (brute_left_join_list row join left right) =
      (List.length left * List.length right)%nat.
```

## `filter_brute_left_join_list_as_theta`

Source: [`theories/FormalSQL/QueryCardinality.v:68`](../QueryCardinality.v#L68)

Purpose/direction: Bridges the two displayed representations of join cardinality.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join cardinality.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `filter` (rank 46), `join` (rank 42), `cardinality` (rank 36)

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

Purpose/direction: States the theta join list guard left law for join cardinality, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join cardinality.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `join` (rank 42), `cardinality` (rank 36)

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

Purpose/direction: States the tnull predicate keep proper law for row cardinality and compositional bounds, in the exact direction displayed by the declaration.

Applicability: Use to orient, transport, or compose a semantic relation about row cardinality and compositional bounds.

Important premises: supply the declared equivalence/properness relation.

Cross-index: `cardinality` (rank 36), `scalar` (rank 52)

Search aliases: `cardinality composition`, `predicate`, `Bool3`, `cardinality`, `equivalence`, `congruence`

```rocq
Lemma tnull_predicate_keep_proper :
  forall env predicate arguments,
    tuple_predicate_proper
      (tnull_predicate_keep env predicate arguments).
```

## `row_attribute_present_conforms_proper`

Source: [`theories/FormalSQL/QueryCardinality.v:158`](../QueryCardinality.v#L158)

Purpose/direction: States the row attribute present conforms proper law for row cardinality and compositional bounds, in the exact direction displayed by the declaration.

Applicability: Use to orient, transport, or compose a semantic relation about row cardinality and compositional bounds.

Important premises: keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `cardinality` (rank 36), `schema` (rank 52)

Search aliases: `cardinality composition`, `schema conformance`, `typing`, `cardinality`, `equivalence`, `congruence`

```rocq
Lemma row_attribute_present_conforms_proper :
  forall attribute,
    tuple_property_proper (row_attribute_present_conforms attribute).
```

## `row_attribute_absent_proper`

Source: [`theories/FormalSQL/QueryCardinality.v:172`](../QueryCardinality.v#L172)

Purpose/direction: States the row attribute absent proper law for row cardinality and compositional bounds, in the exact direction displayed by the declaration.

Applicability: Use to orient, transport, or compose a semantic relation about row cardinality and compositional bounds.

Important premises: keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `cardinality` (rank 36), `schema` (rank 52)

Search aliases: `cardinality composition`, `schema conformance`, `typing`, `cardinality`, `equivalence`, `congruence`

```rocq
Lemma row_attribute_absent_proper :
  forall attribute,
    tuple_property_proper (row_attribute_absent attribute).
```

## `row_attribute_present_nonnull_conforms_proper`

Source: [`theories/FormalSQL/QueryCardinality.v:190`](../QueryCardinality.v#L190)

Purpose/direction: States the row attribute present nonnull conforms proper law for row cardinality and compositional bounds, in the exact direction displayed by the declaration.

Applicability: Use to orient, transport, or compose a semantic relation about row cardinality and compositional bounds.

Important premises: keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `cardinality` (rank 36), `schema` (rank 52)

Search aliases: `cardinality composition`, `schema conformance`, `typing`, `cardinality`, `equivalence`, `congruence`

```rocq
Lemma row_attribute_present_nonnull_conforms_proper :
  forall attribute,
    tuple_property_proper
      (row_attribute_present_nonnull_conforms attribute).
```

## `related_permut_Forall_transport`

Source: [`theories/FormalSQL/QueryCardinality.v:212`](../QueryCardinality.v#L212)

Purpose/direction: Transports the displayed hypotheses and conclusion for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `cardinality` (rank 36)

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

Purpose/direction: States the related permut permutation a law for row cardinality and compositional bounds, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 44), `cardinality` (rank 36)

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

Purpose/direction: States the oeset compare equivalence law for row cardinality and compositional bounds, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `cardinality` (rank 36)

Search aliases: `cardinality composition`, `cardinality`

```rocq
Lemma oeset_compare_Equivalence :
  forall (A : Type) (ordered : Oeset.Rcd A),
    Equivalence
      (fun left right => Oeset.compare ordered left right = Eq).
```

## `oeset_sorted_NoDupA`

Source: [`theories/FormalSQL/QueryCardinality.v:266`](../QueryCardinality.v#L266)

Purpose/direction: Establishes the displayed duplicate-freedom property for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `cardinality` (rank 36)

Search aliases: `cardinality composition`, `cardinality`

```rocq
Lemma oeset_sorted_NoDupA :
  forall (A : Type) (ordered : Oeset.Rcd A) rows,
    Sorted (fun left right => Oeset.compare ordered left right = Lt) rows ->
    NoDupA (fun left right => Oeset.compare ordered left right = Eq) rows.
```

## `NoDupA_app_left`

Source: [`theories/FormalSQL/QueryCardinality.v:292`](../QueryCardinality.v#L292)

Purpose/direction: Establishes the displayed duplicate-freedom property for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `cardinality` (rank 36)

Search aliases: `cardinality composition`, `cardinality`

```rocq
Lemma NoDupA_app_left :
  forall (A : Type) (relation : A -> A -> Prop) left right,
    NoDupA relation (left ++ right) ->
    NoDupA relation left.
```

## `NoDupA_app_right`

Source: [`theories/FormalSQL/QueryCardinality.v:309`](../QueryCardinality.v#L309)

Purpose/direction: Establishes the displayed duplicate-freedom property for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `cardinality` (rank 36)

Search aliases: `cardinality composition`, `cardinality`

```rocq
Lemma NoDupA_app_right :
  forall (A : Type) (relation : A -> A -> Prop) left right,
    NoDupA relation (left ++ right) ->
    NoDupA relation right.
```

## `NoDupA_map_injective_on`

Source: [`theories/FormalSQL/QueryCardinality.v:321`](../QueryCardinality.v#L321)

Purpose/direction: Recovers source equality from the declared row cardinality and compositional bounds representation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `cardinality` (rank 36)

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

Purpose/direction: Bridges the two displayed representations of row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 44), `cardinality` (rank 36)

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

Purpose/direction: Establishes the displayed duplicate-freedom property for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 52), `cardinality` (rank 36)

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

Purpose/direction: Bridges the two displayed representations of row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 52), `cardinality` (rank 36)

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

Purpose/direction: Bridges the two displayed representations of row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `cardinality` (rank 34), `schema` (rank 50)

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

Purpose/direction: Bridges the two displayed representations of row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `cardinality` (rank 34), `schema` (rank 4)

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

Purpose/direction: Inverts or constructs the successful evaluation branch for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `cardinality` (rank 34), `schema` (rank 0)

Search aliases: `cardinality composition`, `schema conformance`, `typing`, `cardinality`

```rocq
Theorem query_expr_table_success_rows_absent_attribute :
  forall expected constraints actual relation attribute outputs env rows
      unknown symbol_runtime_error aggregate_runtime_error value_is_null,
    database_conforms_schema expected constraints actual ->
    (attribute inS? @_basesort TNull expected relation) = false ->
    @query_outputs_sort TNull outputs =S=
      @_basesort TNull actual relation ->
    @eval_query_expr_outcome TNull relname
      (@_basesort TNull actual) (@_instance TNull actual)
      unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (@QExpr_Table TNull relname outputs relation)
      (SqlSuccess rows) ->
    Forall (row_attribute_absent attribute) rows.
```

## `query_same_rows_as_conforming_table_present_attribute`

Source: [`theories/FormalSQL/QueryCardinality.v:532`](../QueryCardinality.v#L532)

Purpose/direction: Bridges the two displayed representations of row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `cardinality` (rank 34), `schema` (rank 6)

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

Source: [`theories/FormalSQL/QueryCardinality.v:556`](../QueryCardinality.v#L556)

Purpose/direction: Inverts or constructs the successful evaluation branch for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `cardinality` (rank 34), `schema` (rank 2)

Search aliases: `cardinality composition`, `schema conformance`, `typing`, `cardinality`

```rocq
Theorem query_expr_table_success_rows_present_conform_attribute :
  forall expected constraints actual relation attribute outputs env rows
      unknown symbol_runtime_error aggregate_runtime_error value_is_null,
    database_conforms_schema expected constraints actual ->
    attribute inS (@_basesort TNull expected relation) ->
    @query_outputs_sort TNull outputs =S=
      @_basesort TNull actual relation ->
    @eval_query_expr_outcome TNull relname
      (@_basesort TNull actual) (@_instance TNull actual)
      unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (@QExpr_Table TNull relname outputs relation)
      (SqlSuccess rows) ->
    Forall (row_attribute_present_conforms attribute) rows.
```

## `query_same_rows_as_conforming_table_attribute`

Source: [`theories/FormalSQL/QueryCardinality.v:585`](../QueryCardinality.v#L585)

Purpose/direction: Bridges the two displayed representations of row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `cardinality` (rank 34), `schema` (rank 50)

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

Source: [`theories/FormalSQL/QueryCardinality.v:633`](../QueryCardinality.v#L633)

Purpose/direction: Inverts or constructs the successful evaluation branch for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `cardinality` (rank 34), `schema` (rank 50)

Search aliases: `cardinality composition`, `schema conformance`, `typing`, `cardinality`

```rocq
Theorem query_expr_table_success_rows_conform_attribute :
  forall expected constraints actual constraint attribute outputs env rows
      unknown symbol_runtime_error aggregate_runtime_error value_is_null,
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
      value_is_null env
      (@QExpr_Table TNull relname outputs
        (constraint_relation constraint))
      (SqlSuccess rows) ->
    Forall (row_attribute_present_nonnull_conforms attribute) rows.
```

## `query_canonical_rows_Forall`

Source: [`theories/FormalSQL/QueryCardinality.v:662`](../QueryCardinality.v#L662)

Purpose/direction: States the query canonical rows forall law for row cardinality and compositional bounds, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `cardinality` (rank 35)

Search aliases: `cardinality composition`, `cardinality`

```rocq
Corollary query_canonical_rows_Forall :
  forall property rows,
    tuple_property_proper property ->
    Forall property rows ->
    Forall property (@query_canonical_rows TNull rows).
```

## `query_same_rows_as_bag_filter_length`

Source: [`theories/FormalSQL/QueryCardinality.v:677`](../QueryCardinality.v#L677)

Purpose/direction: Relates row cardinality and compositional bounds to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `filter` (rank 46), `bag` (rank 52), `cardinality` (rank 28)

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

Source: [`theories/FormalSQL/QueryCardinality.v:700`](../QueryCardinality.v#L700)

Purpose/direction: Relates row cardinality and compositional bounds to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `filter` (rank 46), `bag` (rank 52), `cardinality` (rank 28)

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

Source: [`theories/FormalSQL/QueryCardinality.v:714`](../QueryCardinality.v#L714)

Purpose/direction: Relates row cardinality and compositional bounds to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `grouping` (rank 16), `cardinality` (rank 28)

Search aliases: `cardinality composition`, `GROUP BY`, `cardinality`

```rocq
Lemma query_canonical_rows_length :
  forall rows : list (tuple TNull),
    List.length (@query_canonical_rows TNull rows) = List.length rows.
```

## `row_attribute_present_conforms_join_left`

Source: [`theories/FormalSQL/QueryCardinality.v:741`](../QueryCardinality.v#L741)

Purpose/direction: States the row attribute present conforms join left law for join cardinality, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join cardinality.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `join` (rank 42), `cardinality` (rank 36), `schema` (rank 52)

Search aliases: `cardinality composition`, `join`, `schema conformance`, `typing`, `cardinality`

```rocq
Lemma row_attribute_present_conforms_join_left :
  forall attribute left right,
    row_attribute_present_conforms attribute left ->
    row_attribute_present_conforms attribute (join_tuple TNull left right).
```

## `row_attribute_present_conforms_join_right`

Source: [`theories/FormalSQL/QueryCardinality.v:754`](../QueryCardinality.v#L754)

Purpose/direction: States the row attribute present conforms join right law for join cardinality, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join cardinality.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `join` (rank 42), `cardinality` (rank 36), `schema` (rank 52)

Search aliases: `cardinality composition`, `join`, `schema conformance`, `typing`, `cardinality`

```rocq
Lemma row_attribute_present_conforms_join_right :
  forall attribute left right,
    (attribute inS? labels TNull left) = false ->
    row_attribute_present_conforms attribute right ->
    row_attribute_present_conforms attribute (join_tuple TNull left right).
```

## `brute_left_join_list_Forall`

Source: [`theories/FormalSQL/QueryCardinality.v:768`](../QueryCardinality.v#L768)

Purpose/direction: States the brute left join list forall law for join cardinality, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join cardinality.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `join` (rank 42), `cardinality` (rank 36)

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

Source: [`theories/FormalSQL/QueryCardinality.v:795`](../QueryCardinality.v#L795)

Purpose/direction: States the brute left join list forall left attribute law for join cardinality, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join cardinality.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `join` (rank 41), `cardinality` (rank 35), `schema` (rank 51)

Search aliases: `cardinality composition`, `join`, `schema conformance`, `typing`, `cardinality`

```rocq
Corollary brute_left_join_list_Forall_left_attribute :
  forall attribute left right,
    rows_attribute_present_conform attribute left ->
    rows_attribute_present_conform attribute
      (brute_left_join_list (tuple TNull) (join_tuple TNull) left right).
```

## `brute_left_join_list_Forall_right_attribute`

Source: [`theories/FormalSQL/QueryCardinality.v:811`](../QueryCardinality.v#L811)

Purpose/direction: States the brute left join list forall right attribute law for join cardinality, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join cardinality.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `join` (rank 41), `cardinality` (rank 35), `schema` (rank 51)

Search aliases: `cardinality composition`, `join`, `schema conformance`, `typing`, `cardinality`

```rocq
Corollary brute_left_join_list_Forall_right_attribute :
  forall attribute left right,
    Forall (fun row => (attribute inS? labels TNull row) = false) left ->
    rows_attribute_present_conform attribute right ->
    rows_attribute_present_conform attribute
      (brute_left_join_list (tuple TNull) (join_tuple TNull) left right).
```

## `direct_projection_preserves_present_conformance`

Source: [`theories/FormalSQL/QueryCardinality.v:825`](../QueryCardinality.v#L825)

Purpose/direction: Shows that the indicated operator preserves the displayed row cardinality and compositional bounds property.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `projection` (rank 52), `cardinality` (rank 36)

Search aliases: `cardinality composition`, `projection`, `SELECT list`, `cardinality`

```rocq
Lemma direct_projection_preserves_present_conformance :
  forall env select_list attribute row,
    select_list_directly_selects_attr select_list attribute ->
    select_list_has_unique_outputs select_list ->
    row_attribute_present_conforms attribute row ->
    row_attribute_present_conforms attribute
      (projected_tuple env select_list row).
```

## `raw_cross_same_rows_as_bag`

Source: [`theories/FormalSQL/QueryCardinality.v:852`](../QueryCardinality.v#L852)

Purpose/direction: Bridges the two displayed representations of join cardinality.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join cardinality.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `join` (rank 52), `bag` (rank 52), `cardinality` (rank 36)

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

Source: [`theories/FormalSQL/QueryCardinality.v:876`](../QueryCardinality.v#L876)

Purpose/direction: States the raw cross filter count for any representative law for join cardinality, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join cardinality.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `filter` (rank 45), `join` (rank 51), `cardinality` (rank 35)

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

Source: [`theories/FormalSQL/QueryCardinality.v:893`](../QueryCardinality.v#L893)

Purpose/direction: States the interp predicate int32 nonnull equal law for row cardinality and compositional bounds, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `cardinality` (rank 22), `scalar` (rank 52)

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

Source: [`theories/FormalSQL/QueryCardinality.v:906`](../QueryCardinality.v#L906)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `cardinality` (rank 22), `scalar` (rank 52)

Search aliases: `cardinality composition`, `NULL`, `UNKNOWN`, `three-valued logic`, `predicate`, `Bool3`, `INTEGER`, `int32`, `cardinality`

```rocq
Lemma interp_predicate_int32_null_left :
  forall right,
    NullValues.interp_predicate (PredicateEq)
      [NullValues.Value_int32 None; right] = unknown3.
```

## `interp_predicate_int32_null_right`

Source: [`theories/FormalSQL/QueryCardinality.v:914`](../QueryCardinality.v#L914)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `cardinality` (rank 22), `scalar` (rank 52)

Search aliases: `cardinality composition`, `NULL`, `UNKNOWN`, `three-valued logic`, `predicate`, `Bool3`, `INTEGER`, `int32`, `cardinality`

```rocq
Lemma interp_predicate_int32_null_right :
  forall left,
    NullValues.interp_predicate (PredicateEq)
      [NullValues.Value_int32 (Some left);
       NullValues.Value_int32 None] = unknown3.
```

## `postgres_int32_equal_true_eq`

Source: [`theories/FormalSQL/QueryCardinality.v:928`](../QueryCardinality.v#L928)

Purpose/direction: States the postgres int32 equal true equality law for row cardinality and compositional bounds, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `cardinality` (rank 22), `scalar` (rank 52)

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

Source: [`theories/FormalSQL/QueryCardinality.v:961`](../QueryCardinality.v#L961)

Purpose/direction: Provides the stated reusable upper bound for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `filter` (rank 46), `cardinality` (rank 24)

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

Source: [`theories/FormalSQL/QueryCardinality.v:999`](../QueryCardinality.v#L999)

Purpose/direction: States the int32 primary key true matches at most one law for row cardinality and compositional bounds, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `cardinality` (rank 22), `schema` (rank 38), `scalar` (rank 52)

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

Source: [`theories/FormalSQL/QueryCardinality.v:1031`](../QueryCardinality.v#L1031)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses; keep schema/integrity conformance premises explicit.

Cross-index: `cardinality` (rank 22), `schema` (rank 38), `scalar` (rank 52)

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

Source: [`theories/FormalSQL/QueryCardinality.v:1050`](../QueryCardinality.v#L1050)

Purpose/direction: Provides the stated reusable upper bound for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `cardinality` (rank 24)

Search aliases: `cardinality composition`, `cardinality`

```rocq
Lemma partition_member_length_le :
  forall (row key : Type) (OK : Oset.Rcd key) (key_of : row -> key)
         rows key_value group,
    In (key_value, group) (@Partition.partition row key OK key_of rows) ->
    (List.length group <= List.length rows)%nat.
```

## `query_make_groups_member_length_le`

Source: [`theories/FormalSQL/QueryCardinality.v:1064`](../QueryCardinality.v#L1064)

Purpose/direction: Provides the stated reusable upper bound for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping` (rank 40), `cardinality` (rank 22)

Search aliases: `cardinality composition`, `GROUP BY`, `cardinality`

```rocq
Theorem query_make_groups_member_length_le :
  forall env rows group_terms group,
    In group (@query_make_groups TNull env rows group_terms) ->
    (List.length group <= List.length rows)%nat.
```

## `query_make_groups_member_in`

Source: [`theories/FormalSQL/QueryCardinality.v:1082`](../QueryCardinality.v#L1082)

Purpose/direction: Relates membership or occurrence evidence to row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping` (rank 42), `cardinality` (rank 36)

Search aliases: `cardinality composition`, `GROUP BY`, `cardinality`

```rocq
Lemma query_make_groups_member_in :
  forall env rows group_terms group row,
    In group (@query_make_groups TNull env rows group_terms) ->
    In row group ->
    In row rows.
```

## `query_make_groups_member_nonempty`

Source: [`theories/FormalSQL/QueryCardinality.v:1100`](../QueryCardinality.v#L1100)

Purpose/direction: States the exact empty-input or empty-result law for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping` (rank 42), `cardinality` (rank 36)

Search aliases: `cardinality composition`, `GROUP BY`, `cardinality`

```rocq
Lemma query_make_groups_member_nonempty :
  forall env rows group_terms group,
    group_terms <> nil ->
    In group (@query_make_groups TNull env rows group_terms) ->
    group <> nil.
```

## `partition_member_NoDupA`

Source: [`theories/FormalSQL/QueryCardinality.v:1116`](../QueryCardinality.v#L1116)

Purpose/direction: Establishes the displayed duplicate-freedom property for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `cardinality` (rank 36)

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

Source: [`theories/FormalSQL/QueryCardinality.v:1169`](../QueryCardinality.v#L1169)

Purpose/direction: Establishes the displayed duplicate-freedom property for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping` (rank 42), `cardinality` (rank 36)

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

Source: [`theories/FormalSQL/QueryCardinality.v:1197`](../QueryCardinality.v#L1197)

Purpose/direction: Relates membership or occurrence evidence to row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping` (rank 42), `cardinality` (rank 36)

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

Source: [`theories/FormalSQL/QueryCardinality.v:1241`](../QueryCardinality.v#L1241)

Purpose/direction: Relates membership or occurrence evidence to row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping` (rank 48), `cardinality` (rank 36)

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

Source: [`theories/FormalSQL/QueryCardinality.v:1297`](../QueryCardinality.v#L1297)

Purpose/direction: Provides the stated reusable upper bound for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping` (rank 50), `cardinality` (rank 22)

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

Source: [`theories/FormalSQL/QueryCardinality.v:1335`](../QueryCardinality.v#L1335)

Purpose/direction: Provides the stated reusable upper bound for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping` (rank 50), `cardinality` (rank 22)

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

Source: [`theories/FormalSQL/QueryCardinality.v:1398`](../QueryCardinality.v#L1398)

Purpose/direction: Relates row cardinality and compositional bounds to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `projection` (rank 52), `cardinality` (rank 28)

Search aliases: `cardinality composition`, `projection`, `SELECT list`, `cardinality`

```rocq
Lemma project_rows_success_length :
  forall env select_list rows output,
    @project_rows_outcome T symbol_runtime_error aggregate_runtime_error
      env select_list rows = SqlSuccess output ->
    List.length output = List.length rows.
```

## `project_rows_success_Forall`

Source: [`theories/FormalSQL/QueryCardinality.v:1417`](../QueryCardinality.v#L1417)

Purpose/direction: Inverts or constructs the successful evaluation branch for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `projection` (rank 52), `cardinality` (rank 36)

Search aliases: `cardinality composition`, `projection`, `SELECT list`, `cardinality`

```rocq
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
```

## `if_tuple_rows_success_true`

Source: [`theories/FormalSQL/QueryCardinality.v:1452`](../QueryCardinality.v#L1452)

Purpose/direction: Inverts or constructs the successful evaluation branch for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `cardinality` (rank 36)

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

Source: [`theories/FormalSQL/QueryCardinality.v:1465`](../QueryCardinality.v#L1465)

Purpose/direction: Inverts or constructs the successful evaluation branch for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `cardinality` (rank 36)

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

Source: [`theories/FormalSQL/QueryCardinality.v:1478`](../QueryCardinality.v#L1478)

Purpose/direction: Provides the stated reusable upper bound for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `filter` (rank 46), `cardinality` (rank 24)

Search aliases: `cardinality composition`, `filter`, `WHERE`, `cardinality`

```rocq
Lemma filter_rows_success_length_le :
  forall env formula rows output,
    @eval_filter_rows_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env formula rows (SqlSuccess output) ->
    (List.length output <= List.length rows)%nat.
```

## `filter_cons_outcome_success_Forall`

Source: [`theories/FormalSQL/QueryCardinality.v:1508`](../QueryCardinality.v#L1508)

Purpose/direction: Inverts or constructs the successful evaluation branch for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `outcome` (rank 52), `runtime` (rank 52), `filter` (rank 46), `cardinality` (rank 36)

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

Source: [`theories/FormalSQL/QueryCardinality.v:1522`](../QueryCardinality.v#L1522)

Purpose/direction: Inverts or constructs the successful evaluation branch for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `filter` (rank 46), `cardinality` (rank 36)

Search aliases: `cardinality composition`, `filter`, `WHERE`, `cardinality`

```rocq
Lemma filter_rows_success_Forall :
  forall env formula rows output (property : tuple T -> Prop),
    @eval_filter_rows_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env formula rows (SqlSuccess output) ->
    Forall property rows ->
    Forall property output.
```

## `filter_rows_success_Forall_accepted`

Source: [`theories/FormalSQL/QueryCardinality.v:1553`](../QueryCardinality.v#L1553)

Purpose/direction: Inverts or constructs the successful evaluation branch for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `filter` (rank 46), `cardinality` (rank 36)

Search aliases: `cardinality composition`, `filter`, `WHERE`, `cardinality`

```rocq
Lemma filter_rows_success_Forall_accepted :
  forall env formula rows output (property : tuple T -> Prop),
    (forall row truth,
      In row rows ->
      @eval_formula_expr_outcome T relname basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null (env_t T env row) formula (SqlSuccess truth) ->
      Bool.is_true (B T) truth = true ->
      property row) ->
    @eval_filter_rows_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env formula rows (SqlSuccess output) ->
    Forall property output.
```

## `filter_rows_success_exact_count`

Source: [`theories/FormalSQL/QueryCardinality.v:1590`](../QueryCardinality.v#L1590)

Purpose/direction: Inverts or constructs the successful evaluation branch for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `filter` (rank 46), `cardinality` (rank 36)

Search aliases: `cardinality composition`, `filter`, `WHERE`, `cardinality`

```rocq
Lemma filter_rows_success_exact_count :
  forall env formula rows output keep,
    (forall row truth,
      In row rows ->
      @eval_formula_expr_outcome T relname basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null (env_t T env row) formula (SqlSuccess truth) ->
      Bool.is_true (B T) truth = keep row) ->
    @eval_filter_rows_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env formula rows (SqlSuccess output) ->
    List.length output = List.length (filter keep rows).
```

## `filter_rows_error_observable`

Source: [`theories/FormalSQL/QueryCardinality.v:1631`](../QueryCardinality.v#L1631)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime` (rank 52), `filter` (rank 46), `cardinality` (rank 36)

Search aliases: `cardinality composition`, `filter`, `WHERE`, `runtime outcome`, `runtime safety`, `error propagation`, `cardinality`

```rocq
Lemma filter_rows_error_observable :
  forall env formula input input_rows error,
    @eval_query_expr_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env input (SqlSuccess input_rows) ->
    @eval_filter_rows_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env formula input_rows (SqlError error) ->
    @eval_query_expr_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env (QExpr_Filter formula input) (SqlError error).
```

## `eval_groups_success_length_le`

Source: [`theories/FormalSQL/QueryCardinality.v:1649`](../QueryCardinality.v#L1649)

Purpose/direction: Provides the stated reusable upper bound for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping` (rank 52), `cardinality` (rank 24)

Search aliases: `cardinality composition`, `GROUP BY`, `cardinality`

```rocq
Lemma eval_groups_success_length_le :
  forall env select_list group_terms having groups output,
    @eval_groups_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env select_list group_terms having groups (SqlSuccess output) ->
    (List.length output <= List.length groups)%nat.
```

## `int32_composite_primary_key_true_matches_at_most_one`

Source: [`theories/FormalSQL/QueryCardinality.v:1689`](../QueryCardinality.v#L1689)

Purpose/direction: States the int32 composite primary key true matches at most one law for row cardinality and compositional bounds, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `cardinality` (rank 22), `schema` (rank 38), `scalar` (rank 52)

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

Source: [`theories/FormalSQL/QueryCardinality.v:1751`](../QueryCardinality.v#L1751)

Purpose/direction: Provides the stated reusable upper bound for join cardinality.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join cardinality.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `join` (rank 40), `cardinality` (rank 22)

Search aliases: `cardinality composition`, `join`, `cardinality`

```rocq
Theorem functional_theta_join_chain_length_le :
  forall (row : Type) (join : row -> row -> row) left stages,
    Forall theta_stage_is_functional stages ->
    (List.length (functional_theta_join_chain row join left stages) <=
      List.length left)%nat.
```

## `rows_attribute_conform_filter`

Source: [`theories/FormalSQL/QueryCardinality.v:1770`](../QueryCardinality.v#L1770)

Purpose/direction: States the rows attribute conform filter law for row cardinality and compositional bounds, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `filter` (rank 46), `cardinality` (rank 36), `schema` (rank 52)

Search aliases: `cardinality composition`, `filter`, `WHERE`, `schema conformance`, `typing`, `cardinality`

```rocq
Lemma rows_attribute_conform_filter :
  forall attribute rows keep,
    rows_attribute_conform attribute rows ->
    rows_attribute_conform attribute (filter keep rows).
```

## `NoDup_map_filter`

Source: [`theories/FormalSQL/QueryCardinality.v:1780`](../QueryCardinality.v#L1780)

Purpose/direction: Establishes the displayed duplicate-freedom property for row cardinality and compositional bounds.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `filter` (rank 46), `cardinality` (rank 36)

Search aliases: `cardinality composition`, `filter`, `WHERE`, `cardinality`

```rocq
Lemma NoDup_map_filter :
  forall (row key : Type) (key_of : row -> key) keep rows,
    NoDup (map key_of rows) ->
    NoDup (map key_of (filter keep rows)).
```

## `primary_key_conforms_filter`

Source: [`theories/FormalSQL/QueryCardinality.v:1800`](../QueryCardinality.v#L1800)

Purpose/direction: States the primary key conforms filter law for row cardinality and compositional bounds, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `filter` (rank 46), `cardinality` (rank 36), `schema` (rank 38)

Search aliases: `cardinality composition`, `filter`, `WHERE`, `integrity constraint`, `key`, `cardinality`

```rocq
Lemma primary_key_conforms_filter :
  forall primary_key rows keep,
    primary_key_conforms primary_key rows ->
    primary_key_conforms primary_key (filter keep rows).
```

## `functional_chain_fixed_first_composite_int32_group_length_2_32`

Source: [`theories/FormalSQL/QueryCardinality.v:1817`](../QueryCardinality.v#L1817)

Purpose/direction: Relates row cardinality and compositional bounds to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping` (rank 50), `cardinality` (rank 20), `scalar` (rank 50)

Search aliases: `cardinality composition`, `GROUP BY`, `INTEGER`, `int32`, `cardinality`

```rocq
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
```

## `functional_chain_composite_int32_occurrence_length_2_64`

Source: [`theories/FormalSQL/QueryCardinality.v:1865`](../QueryCardinality.v#L1865)

Purpose/direction: Relates row cardinality and compositional bounds to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 50), `cardinality` (rank 20), `scalar` (rank 50)

Search aliases: `cardinality composition`, `INTEGER`, `int32`, `cardinality`, `multiplicity`

```rocq
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
```

## `functional_chain_composite_int32_group_length_2_64`

Source: [`theories/FormalSQL/QueryCardinality.v:1897`](../QueryCardinality.v#L1897)

Purpose/direction: Relates row cardinality and compositional bounds to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about row cardinality and compositional bounds.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping` (rank 50), `cardinality` (rank 20), `scalar` (rank 50)

Search aliases: `cardinality composition`, `GROUP BY`, `INTEGER`, `int32`, `cardinality`

```rocq
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
```
