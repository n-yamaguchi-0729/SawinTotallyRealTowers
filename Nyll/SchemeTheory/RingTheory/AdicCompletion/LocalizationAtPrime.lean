/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Adic completion commutes with localization at a maximal ideal

For a maximal ideal `Q` of a commutative ring `S`, localization at `Q`
identifies every finite quotient `S ⧸ Q ^ n` with the corresponding quotient
of `Localization.AtPrime Q` by the `n`-th power of its maximal ideal.  We prove
that these finite-level equivalences commute with the power transition maps and
lift them to an equivalence of adic completions.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe uS

variable {S : Type uS} [CommRing S]

section AtPrime

variable (Q : Ideal S) [Q.IsMaximal]

local notation "S_Q" => Localization.AtPrime Q
local notation "m_Q" => IsLocalRing.maximalIdeal S_Q

/-- The finite-level localization equivalences commute with the transition maps
between powers of the maximal ideals. -/
theorem localizationAtPrimeQuotientPowEquiv_factorPow
    {m n : ℕ} (hmn : m ≤ n) (x : S ⧸ Q ^ n) :
    Ideal.Quotient.factorPow m_Q hmn
        (IsLocalization.AtPrime.equivQuotMaximalIdealPow Q S_Q n x) =
      IsLocalization.AtPrime.equivQuotMaximalIdealPow Q S_Q m
        (Ideal.Quotient.factorPow Q hmn x) := by
  induction x using Quotient.inductionOn' with
  | _ x =>
      change Ideal.Quotient.factorPow m_Q hmn
          (IsLocalization.AtPrime.equivQuotMaximalIdealPow Q S_Q n
            (Ideal.Quotient.mk (Q ^ n) x)) =
        IsLocalization.AtPrime.equivQuotMaximalIdealPow Q S_Q m
          (Ideal.Quotient.factorPow Q hmn (Ideal.Quotient.mk (Q ^ n) x))
      rw [IsLocalization.AtPrime.equivQuotMaximalIdealPow_apply_mk,
        Ideal.Quotient.factor_mk,
        Ideal.Quotient.factor_mk,
        IsLocalization.AtPrime.equivQuotMaximalIdealPow_apply_mk]

/-- Naturality of the inverse finite-level localization equivalences. -/
theorem localizationAtPrimeQuotientPowEquiv_symm_factorPow
    {m n : ℕ} (hmn : m ≤ n) (x : S_Q ⧸ m_Q ^ n) :
    Ideal.Quotient.factorPow Q hmn
        ((IsLocalization.AtPrime.equivQuotMaximalIdealPow Q S_Q n).symm x) =
      (IsLocalization.AtPrime.equivQuotMaximalIdealPow Q S_Q m).symm
        (Ideal.Quotient.factorPow m_Q hmn x) := by
  apply (IsLocalization.AtPrime.equivQuotMaximalIdealPow Q S_Q m).injective
  rw [AlgEquiv.apply_symm_apply,
    ← localizationAtPrimeQuotientPowEquiv_factorPow Q hmn
      ((IsLocalization.AtPrime.equivQuotMaximalIdealPow Q S_Q n).symm x),
    AlgEquiv.apply_symm_apply]

private theorem factorPow_evalₐ
    {R : Type*} [CommRing R] (I : Ideal R)
    {m n : ℕ} (hmn : m ≤ n) (x : AdicCompletion I R) :
    Ideal.Quotient.factorPow I hmn (AdicCompletion.evalₐ I n x) =
      AdicCompletion.evalₐ I m x := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
    (AdicCompletion.evalₐ I n x)
  have hn : AdicCompletion.eval I R n x =
      Ideal.Quotient.mk (I ^ n • ⊤ : Ideal R) a := by
    rw [← AdicCompletion.factor_evalₐ_eq_eval I x (by simp), ← ha,
      Ideal.Quotient.factor_mk]
  have hm : AdicCompletion.eval I R m x =
      Ideal.Quotient.mk (I ^ m • ⊤ : Ideal R) a := by
    calc
      AdicCompletion.eval I R m x =
          AdicCompletion.transitionMap I R hmn
            (AdicCompletion.eval I R n x) :=
        (AdicCompletion.transitionMap_comp_eval_apply I R hmn x).symm
      _ = Ideal.Quotient.mk (I ^ m • ⊤ : Ideal R) a := by
        rw [hn]
        rfl
  calc
    Ideal.Quotient.factorPow I hmn (AdicCompletion.evalₐ I n x) =
        Ideal.Quotient.mk (I ^ m) a := by
      rw [← ha, Ideal.Quotient.factor_mk]
    _ = AdicCompletion.evalₐ I m x := by
      rw [← AdicCompletion.factor_eval_eq_evalₐ I x (by simp), hm]
      rfl

private noncomputable def completionToAtPrimeQuotientRingHom (n : ℕ) :
    AdicCompletion Q S →+* S_Q ⧸ m_Q ^ n :=
  (IsLocalization.AtPrime.equivQuotMaximalIdealPow Q S_Q n).toRingEquiv.toRingHom.comp
    (AdicCompletion.evalₐ Q n).toRingHom

private theorem completionToAtPrimeQuotientRingHom_compatible :
    ∀ {m n : ℕ} (hmn : m ≤ n),
      (Ideal.Quotient.factorPow m_Q hmn).comp
          (completionToAtPrimeQuotientRingHom Q n) =
        completionToAtPrimeQuotientRingHom Q m := by
  intro m n hmn
  ext x
  change Ideal.Quotient.factorPow m_Q hmn
      (IsLocalization.AtPrime.equivQuotMaximalIdealPow Q S_Q n
        (AdicCompletion.evalₐ Q n x)) =
    IsLocalization.AtPrime.equivQuotMaximalIdealPow Q S_Q m
      (AdicCompletion.evalₐ Q m x)
  rw [localizationAtPrimeQuotientPowEquiv_factorPow Q hmn,
    factorPow_evalₐ Q hmn]

private noncomputable def completionToAtPrimeRingHom :
    AdicCompletion Q S →+* AdicCompletion m_Q S_Q :=
  AdicCompletion.liftRingHom m_Q
    (completionToAtPrimeQuotientRingHom Q)
    (completionToAtPrimeQuotientRingHom_compatible Q)

@[simp]
private theorem evalₐ_completionToAtPrimeRingHom
    (n : ℕ) (x : AdicCompletion Q S) :
    AdicCompletion.evalₐ m_Q n (completionToAtPrimeRingHom Q x) =
      IsLocalization.AtPrime.equivQuotMaximalIdealPow Q S_Q n
        (AdicCompletion.evalₐ Q n x) := by
  unfold completionToAtPrimeRingHom
  rw [AdicCompletion.evalₐ_liftRingHom]
  rfl

private noncomputable def atPrimeCompletionToQuotientRingHom (n : ℕ) :
    AdicCompletion m_Q S_Q →+* S ⧸ Q ^ n :=
  (IsLocalization.AtPrime.equivQuotMaximalIdealPow Q S_Q n).symm.toRingEquiv.toRingHom.comp
    (AdicCompletion.evalₐ m_Q n).toRingHom

private theorem atPrimeCompletionToQuotientRingHom_compatible :
    ∀ {m n : ℕ} (hmn : m ≤ n),
      (Ideal.Quotient.factorPow Q hmn).comp
          (atPrimeCompletionToQuotientRingHom Q n) =
        atPrimeCompletionToQuotientRingHom Q m := by
  intro m n hmn
  ext x
  change Ideal.Quotient.factorPow Q hmn
      ((IsLocalization.AtPrime.equivQuotMaximalIdealPow Q S_Q n).symm
        (AdicCompletion.evalₐ m_Q n x)) =
    (IsLocalization.AtPrime.equivQuotMaximalIdealPow Q S_Q m).symm
      (AdicCompletion.evalₐ m_Q m x)
  rw [localizationAtPrimeQuotientPowEquiv_symm_factorPow Q hmn,
    factorPow_evalₐ m_Q hmn]

private noncomputable def completionFromAtPrimeRingHom :
    AdicCompletion m_Q S_Q →+* AdicCompletion Q S :=
  AdicCompletion.liftRingHom Q
    (atPrimeCompletionToQuotientRingHom Q)
    (atPrimeCompletionToQuotientRingHom_compatible Q)

@[simp]
private theorem evalₐ_completionFromAtPrimeRingHom
    (n : ℕ) (x : AdicCompletion m_Q S_Q) :
    AdicCompletion.evalₐ Q n (completionFromAtPrimeRingHom Q x) =
      (IsLocalization.AtPrime.equivQuotMaximalIdealPow Q S_Q n).symm
        (AdicCompletion.evalₐ m_Q n x) := by
  unfold completionFromAtPrimeRingHom
  rw [AdicCompletion.evalₐ_liftRingHom]
  rfl

private theorem completionToAtPrime_comp_fromAtPrime :
    (completionToAtPrimeRingHom Q).comp (completionFromAtPrimeRingHom Q) =
      RingHom.id (AdicCompletion m_Q S_Q) := by
  apply RingHom.ext
  intro x
  apply AdicCompletion.ext_evalₐ
  intro n
  simp

private theorem completionFromAtPrime_comp_toAtPrime :
    (completionFromAtPrimeRingHom Q).comp (completionToAtPrimeRingHom Q) =
      RingHom.id (AdicCompletion Q S) := by
  apply RingHom.ext
  intro x
  apply AdicCompletion.ext_evalₐ
  intro n
  simp

/-- Completion at a maximal ideal is canonically equivalent, as a ring, to
completion of its localization at the local maximal ideal. -/
noncomputable def adicCompletionLocalizationAtPrimeRingEquiv :
    AdicCompletion Q S ≃+* AdicCompletion m_Q S_Q :=
  RingEquiv.ofRingHom
    (completionToAtPrimeRingHom Q)
    (completionFromAtPrimeRingHom Q)
    (completionToAtPrime_comp_fromAtPrime Q)
    (completionFromAtPrime_comp_toAtPrime Q)

@[simp]
theorem evalₐ_adicCompletionLocalizationAtPrimeRingEquiv
    (n : ℕ) (x : AdicCompletion Q S) :
    AdicCompletion.evalₐ m_Q n
        (adicCompletionLocalizationAtPrimeRingEquiv Q x) =
      IsLocalization.AtPrime.equivQuotMaximalIdealPow Q S_Q n
        (AdicCompletion.evalₐ Q n x) :=
  evalₐ_completionToAtPrimeRingHom Q n x

@[simp]
theorem evalₐ_adicCompletionLocalizationAtPrimeRingEquiv_symm
    (n : ℕ) (x : AdicCompletion m_Q S_Q) :
    AdicCompletion.evalₐ Q n
        ((adicCompletionLocalizationAtPrimeRingEquiv Q).symm x) =
      (IsLocalization.AtPrime.equivQuotMaximalIdealPow Q S_Q n).symm
        (AdicCompletion.evalₐ m_Q n x) :=
  evalₐ_completionFromAtPrimeRingHom Q n x

/-- The canonical algebra equivalence over `S`: completion at `Q` agrees with
completion of `Localization.AtPrime Q` at its maximal ideal. -/
noncomputable def adicCompletionLocalizationAtPrimeAlgEquiv :
    AdicCompletion Q S ≃ₐ[S] AdicCompletion m_Q S_Q :=
  AlgEquiv.ofRingEquiv
    (f := adicCompletionLocalizationAtPrimeRingEquiv Q) (fun x => by
      apply AdicCompletion.ext_evalₐ
      intro n
      simp [AdicCompletion.algebraMap_apply])

@[simp]
theorem evalₐ_adicCompletionLocalizationAtPrimeAlgEquiv
    (n : ℕ) (x : AdicCompletion Q S) :
    AdicCompletion.evalₐ m_Q n
        (adicCompletionLocalizationAtPrimeAlgEquiv Q x) =
      IsLocalization.AtPrime.equivQuotMaximalIdealPow Q S_Q n
        (AdicCompletion.evalₐ Q n x) :=
  evalₐ_adicCompletionLocalizationAtPrimeRingEquiv Q n x

end AtPrime

end EtaleFundamentalGroups

end
