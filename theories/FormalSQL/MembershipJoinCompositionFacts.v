(** Correlation-preserving membership/EXISTS composition. *)

Set Implicit Arguments.

From Stdlib Require Import List Lia.
From SQLFS Require Import
  ATerms Bool3 Env FiniteBag FiniteCollection FiniteSet Formula FTuples
  GenericInstance ListPermut OrderedSet Projection SqlBagAbstraction
  SqlErrorSemantics SqlOutcome SqlQueryContexts SqlQueryFacts
  SqlQuerySemantics SqlQuerySyntax Values.
From Logos.FormalSQL Require Import
  GroupedFilterOutcomeFacts MembershipCompositionFacts OrderedQueryFacts
  SubqueryFacts.

Import ListNotations.
Import Tuple.
