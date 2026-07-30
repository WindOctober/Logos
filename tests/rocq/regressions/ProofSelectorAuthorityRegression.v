From Logos Require Import FormalSQL.VerificationConditions.

(** A source-level selector whose type can be shadowed is not authoritative.
    The two coercions below reproduce the namespace attack that used to let a
    lexical [VerificationCountermodel] selector elaborate as equivalence. *)
Inductive counterfeit_claim_kind : Type :=
  | CounterfeitClaim.

Definition trusted_claim_to_counterfeit
    (_ : Logos.FormalSQL.VerificationConditions.verification_claim_kind)
    : counterfeit_claim_kind :=
  CounterfeitClaim.
Coercion trusted_claim_to_counterfeit :
  Logos.FormalSQL.VerificationConditions.verification_claim_kind >->
  counterfeit_claim_kind.

Definition counterfeit_to_trusted_claim
    (_ : counterfeit_claim_kind)
    : Logos.FormalSQL.VerificationConditions.verification_claim_kind :=
  Logos.FormalSQL.VerificationConditions.VerificationEquivalence.
Coercion counterfeit_to_trusted_claim :
  counterfeit_claim_kind >->
  Logos.FormalSQL.VerificationConditions.verification_claim_kind.

Definition verification_claim_kind := counterfeit_claim_kind.

Definition legacy_shadowable_claim : verification_claim_kind :=
  Logos.FormalSQL.VerificationConditions.VerificationCountermodel.

Definition legacy_observed_claim :
    Logos.FormalSQL.VerificationConditions.verification_claim_kind :=
  legacy_shadowable_claim.

Example legacy_selector_can_be_reinterpreted :
  legacy_observed_claim =
    Logos.FormalSQL.VerificationConditions.VerificationEquivalence.
Proof. reflexivity. Qed.

(** The repaired declaration fixes the trusted type by its absolute logical
    name. Rocq therefore uses the direct typing derivation and cannot insert
    the counterfeit round trip. *)
Definition hardened_claim :
    Logos.FormalSQL.VerificationConditions.verification_claim_kind :=
  Logos.FormalSQL.VerificationConditions.VerificationCountermodel.

Definition hardened_observed_claim :
    Logos.FormalSQL.VerificationConditions.verification_claim_kind :=
  hardened_claim.

Example fully_qualified_selector_preserves_constructor :
  hardened_observed_claim =
    Logos.FormalSQL.VerificationConditions.VerificationCountermodel.
Proof. reflexivity. Qed.
