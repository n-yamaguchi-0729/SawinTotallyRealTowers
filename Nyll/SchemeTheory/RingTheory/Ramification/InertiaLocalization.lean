/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Ring.Action.Group
import Mathlib.RingTheory.Ideal.Pointwise
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Defs
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Individual inertia automorphisms on the literal prime localization

The native inertia-to-stabilizer theorem supplies preservation of the prime,
then the native local-ring equivalence extends the original automorphism.
Its coefficient formula proves compatibility with the original base map.
Native localization extensionality and maximal-ideal contraction prove that
its residue action is the identity. No group action on the localization is
introduced, and no valuation or finiteness hypothesis is required.
-/

noncomputable section

open scoped Pointwise

namespace SchemeTheory

universe u v

private theorem inertia_comap_eq
    (B : Type u) [CommRing B] (Q : Ideal B) (σ : B ≃+* B)
    (hσ : ∀ b : B, σ b - b ∈ Q) : Q = Q.comap σ.toRingHom := by
  have hI : σ ∈ Q.inertia (B ≃+* B) := hσ
  have hInv : σ⁻¹ ∈ Q.inertia (B ≃+* B) := (Q.inertia (B ≃+* B)).inv_mem hI
  have hstab : σ⁻¹ • Q = Q := Q.inertia_le_stabilizer hInv
  exact hstab.symm.trans (Ideal.pointwise_smul_eq_comap (a := σ⁻¹) Q)

/-- Extend an actual inertia automorphism to the literal localization at Q. -/
def inertiaLocalizationRingEquiv
    (B : Type u) [CommRing B] (Q : Ideal B) [Q.IsPrime] (σ : B ≃+* B)
    (hσ : ∀ b : B, σ b - b ∈ Q) :
    Localization.AtPrime Q ≃+* Localization.AtPrime Q :=
  Localization.localRingEquiv Q Q σ (inertia_comap_eq B Q σ hσ)

/-- The native localization extension has the original value on coefficients. -/
theorem inertiaLocalizationRingEquiv_algebraMap
    (B : Type u) [CommRing B] (Q : Ideal B) [Q.IsPrime] (σ : B ≃+* B)
    (hσ : ∀ b : B, σ b - b ∈ Q) (b : B) :
    inertiaLocalizationRingEquiv B Q σ hσ (algebraMap B (Localization.AtPrime Q) b) =
      algebraMap B (Localization.AtPrime Q) (σ b) :=
  Localization.localRingHom_to_map Q Q σ.toRingHom (inertia_comap_eq B Q σ hσ) b

/-- A commuting original ring map remains fixed after localization. This
interface uses the literal ring map and its supplied commutation proof, so
no extra base-algebra action is opened at a dense Galois boundary. -/
theorem inertiaLocalizationRingEquiv_comp_baseMap
    (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    (Q : Ideal B) [Q.IsPrime] (σ : B ≃+* B)
    (hσ : ∀ b : B, σ b - b ∈ Q) (f : A →+* B)
    (hf : σ.toRingHom.comp f = f) :
    (inertiaLocalizationRingEquiv B Q σ hσ).toRingHom.comp
        ((algebraMap B (Localization.AtPrime Q)).comp f) =
      (algebraMap B (Localization.AtPrime Q)).comp f := by
  apply RingHom.ext
  intro a
  exact (inertiaLocalizationRingEquiv_algebraMap B Q σ hσ (f a)).trans
    (congrArg (algebraMap B (Localization.AtPrime Q)) (RingHom.congr_fun hf a))

/-- The extended individual inertia automorphism acts trivially on the actual
residue field of the prime localization. Prime Q need not be maximal in B. -/
theorem inertiaLocalizationRingEquiv_comp_residue
    (B : Type u) [CommRing B] (Q : Ideal B) [Q.IsPrime] (σ : B ≃+* B)
    (hσ : ∀ b : B, σ b - b ∈ Q) :
    (IsLocalRing.residue (Localization.AtPrime Q)).comp
        (inertiaLocalizationRingEquiv B Q σ hσ).toRingHom =
      IsLocalRing.residue (Localization.AtPrime Q) := by
  apply IsLocalization.ringHom_ext Q.primeCompl
  apply RingHom.ext
  intro b
  let T := Localization.AtPrime Q
  have hm : algebraMap B T (σ b - b) ∈ IsLocalRing.maximalIdeal T :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff T Q (σ b - b)).mpr (hσ b)
  have heq : IsLocalRing.residue T (algebraMap B T (σ b)) =
      IsLocalRing.residue T (algebraMap B T b) := by
    apply Ideal.Quotient.eq.mpr
    rw [← map_sub]
    exact hm
  exact (congrArg (IsLocalRing.residue T)
    (inertiaLocalizationRingEquiv_algebraMap B Q σ hσ b)).trans heq

end SchemeTheory
