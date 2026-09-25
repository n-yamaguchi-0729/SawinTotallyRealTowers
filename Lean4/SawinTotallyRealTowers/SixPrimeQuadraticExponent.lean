/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.SixPrimeQuadraticCompositum
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.FieldTheory.Normal.Defs
import Mathlib.GroupTheory.OrderOfElement

set_option autoImplicit false

/-!
# Exponent two in the five-field quadratic compositum

Restriction to the two factors of a compositum is jointly injective.
An exponent bound on both Galois groups therefore holds on their
compositum. Each of the five chosen quadratic fields has Galois group
of order two, so every automorphism of their finite compositum squares
to the identity. Its degree is not used in this argument.
-/

universe u v

namespace ClassFieldTower.Sawin

private theorem galois_pow_eq_one_sup
    {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω]
    (E F : FiniteGaloisIntermediateField K Ω) (n : ℕ)
    (hE : ∀ σ : E ≃ₐ[K] E, σ ^ n = 1)
    (hF : ∀ σ : F ≃ₐ[K] F, σ ^ n = 1) :
    ∀ σ : (E ⊔ F : FiniteGaloisIntermediateField K Ω) ≃ₐ[K]
      (E ⊔ F : FiniteGaloisIntermediateField K Ω), σ ^ n = 1 := by
  let S : IntermediateField K Ω := E.toIntermediateField ⊔ F.toIntermediateField
  let A : IntermediateField K S :=
    IntermediateField.restrict (show E.toIntermediateField ≤ S from le_sup_left)
  let B : IntermediateField K S :=
    IntermediateField.restrict (show F.toIntermediateField ≤ S from le_sup_right)
  let eA : E ≃ₐ[K] A :=
    IntermediateField.restrictAlgEquiv (show E.toIntermediateField ≤ S from le_sup_left)
  let eB : F ≃ₐ[K] B :=
    IntermediateField.restrictAlgEquiv (show F.toIntermediateField ≤ S from le_sup_right)
  let : Normal K A := Normal.of_algEquiv eA
  let : Normal K B := Normal.of_algEquiv eB
  change ∀ σ : S ≃ₐ[K] S, σ ^ n = 1
  intro σ
  have hFixA : σ ^ n ∈ A.fixingSubgroup := by
    rw [← IntermediateField.restrictNormalHom_ker]
    change (AlgEquiv.restrictNormalHom A) (σ ^ n) = 1
    rw [map_pow]
    apply (AlgEquiv.autCongr eA).symm.injective
    rw [map_pow, map_one]
    exact hE ((AlgEquiv.autCongr eA).symm ((AlgEquiv.restrictNormalHom A) σ))
  have hFixB : σ ^ n ∈ B.fixingSubgroup := by
    rw [← IntermediateField.restrictNormalHom_ker]
    change (AlgEquiv.restrictNormalHom B) (σ ^ n) = 1
    rw [map_pow]
    apply (AlgEquiv.autCongr eB).symm.injective
    rw [map_pow, map_one]
    exact hF ((AlgEquiv.autCongr eB).symm ((AlgEquiv.restrictNormalHom B) σ))
  have hSup : A ⊔ B = ⊤ := by
    apply IntermediateField.lift_injective S
    rw [IntermediateField.lift_sup, IntermediateField.lift_restrict,
      IntermediateField.lift_restrict, IntermediateField.lift_top]
  have hFix : σ ^ n ∈ (A ⊔ B).fixingSubgroup := by
    rw [IntermediateField.fixingSubgroup_sup]
    exact ⟨hFixA, hFixB⟩
  rw [hSup, IntermediateField.fixingSubgroup_top] at hFix
  exact Subgroup.mem_bot.mp hFix

/-- Every automorphism of the actual five-quadratic-field compositum
has square equal to the identity. -/
theorem sawinQuadraticCompositum_galois_sq_eq_one
    (σ : sawinQuadraticCompositum ≃ₐ[ℚ] sawinQuadraticCompositum) : σ ^ 2 = 1 := by
  have hAll : ∀ τ : sawinQuadraticCompositum ≃ₐ[ℚ] sawinQuadraticCompositum,
      τ ^ 2 = 1 := by
    apply Finset.sup_induction
      (p := fun E : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ) ↦
        ∀ τ : E ≃ₐ[ℚ] E, τ ^ 2 = 1)
    · intro τ
      apply (AlgEquiv.autCongr (IntermediateField.botEquiv ℚ (AlgebraicClosure ℚ))).injective
      exact Subsingleton.elim _ _
    · intro E hE F hF
      exact galois_pow_eq_one_sup E F 2 hE hF
    · intro i _hi τ
      let : IsGalois ℚ (sawinQuadraticLayer i).toIntermediateField :=
        (sawinQuadraticLayer i).isGalois
      have hCard : Nat.card (sawinQuadraticLayer i ≃ₐ[ℚ] sawinQuadraticLayer i) = 2 :=
        (IsGalois.card_aut_eq_finrank ℚ (sawinQuadraticLayer i)).trans
          (quadraticClosure_finrank
            (sawinQuadraticRadicand i : ℚ) (sawinQuadraticRadicand_nonsquare i))
      rw [← hCard]
      exact pow_card_eq_one'
  exact hAll σ

end ClassFieldTower.Sawin
