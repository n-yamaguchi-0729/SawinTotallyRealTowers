/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Algebra.Notation.Indicator
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Subgroup character vectors with a prescribed failure of the full action

As in the normal-basis character eigenvector construction, inverse-character
coefficients weight the actual canonical normal basis. Here the coefficients
are supported only on a subgroup. This vector transforms by the character
on that subgroup, while an automorphism outside it moves the support away
from the identity. Its identity coordinate distinguishes the two vectors.
Neither a characteristic restriction nor normality of the subgroup is needed.
-/

noncomputable section

namespace LocalFieldTheory.DiscreteValuationField

open scoped BigOperators

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- The inverse-character weighted normal-basis sum supported on `Δ`. -/
def normalBasisSubgroupCharacterVector (Δ : Subgroup Gal(L/K))
    (χ : Gal(L/K) →* Kˣ) : L :=
  ∑ δ : Gal(L/K),
    (Δ : Set Gal(L/K)).indicator (fun τ => (((χ τ)⁻¹ : Kˣ) : K)) δ •
      IsGalois.normalBasis K L δ

/-- The coefficients are exactly the inverse character on the subgroup
and zero outside it. -/
theorem normalBasisSubgroupCharacterVector_repr (Δ : Subgroup Gal(L/K))
    (χ : Gal(L/K) →* Kˣ) (δ : Gal(L/K)) :
    (IsGalois.normalBasis K L).repr (normalBasisSubgroupCharacterVector Δ χ) δ =
      (Δ : Set Gal(L/K)).indicator (fun τ => (((χ τ)⁻¹ : Kˣ) : K)) δ := by
  classical
  exact congrFun ((IsGalois.normalBasis K L).repr_sum_self
    ((Δ : Set Gal(L/K)).indicator (fun τ => (((χ τ)⁻¹ : Kˣ) : K)))) δ

private theorem map_normalBasisSubgroupCharacterVector (Δ : Subgroup Gal(L/K))
    (χ : Gal(L/K) →* Kˣ) (σ : Gal(L/K)) :
    σ (normalBasisSubgroupCharacterVector Δ χ) =
      ∑ δ : Gal(L/K),
        (Δ : Set Gal(L/K)).indicator (fun τ => (((χ τ)⁻¹ : Kˣ) : K)) δ •
          IsGalois.normalBasis K L (σ * δ) := by
  classical
  unfold normalBasisSubgroupCharacterVector
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro δ _hδ
  rw [map_smul, IsGalois.normalBasis_apply δ,
    IsGalois.normalBasis_apply (σ * δ), AlgEquiv.mul_apply]

/-- Left translation by a subgroup element multiplies the supported vector
by the restricted character. -/
theorem normalBasisSubgroupCharacterVector_eigen (Δ : Subgroup Gal(L/K))
    (χ : Gal(L/K) →* Kˣ) (σ : Δ) :
    (σ : Gal(L/K)) (normalBasisSubgroupCharacterVector Δ χ) =
      (χ (σ : Gal(L/K)) : K) • normalBasisSubgroupCharacterVector Δ χ := by
  classical
  let c : Gal(L/K) → K :=
    (Δ : Set Gal(L/K)).indicator (fun τ => (((χ τ)⁻¹ : Kˣ) : K))
  have hcoeff (δ : Gal(L/K)) :
      c δ = (χ (σ : Gal(L/K)) : K) * c ((σ : Gal(L/K)) * δ) := by
    by_cases hδ : δ ∈ Δ
    · have hσδ : (σ : Gal(L/K)) * δ ∈ Δ := Δ.mul_mem σ.property hδ
      dsimp only [c]
      rw [Set.indicator_of_mem hδ, Set.indicator_of_mem hσδ]
      symm
      rw [χ.map_mul, mul_inv_rev, Units.val_mul,
        mul_left_comm (χ (σ : Gal(L/K)) : K), Units.mul_inv, mul_one]
    · have hσδ : (σ : Gal(L/K)) * δ ∉ Δ :=
        fun h => hδ ((Δ.mul_mem_cancel_left σ.property).mp h)
      dsimp only [c]
      rw [Set.indicator_of_notMem hδ, Set.indicator_of_notMem hσδ, mul_zero]
  calc
    (σ : Gal(L/K)) (normalBasisSubgroupCharacterVector Δ χ) =
        ∑ δ : Gal(L/K), c δ • IsGalois.normalBasis K L ((σ : Gal(L/K)) * δ) :=
      map_normalBasisSubgroupCharacterVector Δ χ (σ : Gal(L/K))
    _ = ∑ δ : Gal(L/K),
        (χ (σ : Gal(L/K)) : K) •
          (c ((σ : Gal(L/K)) * δ) •
            IsGalois.normalBasis K L ((σ : Gal(L/K)) * δ)) := by
      apply Finset.sum_congr rfl
      intro δ _hδ
      rw [hcoeff δ, smul_smul]
    _ = ∑ δ : Gal(L/K),
        (χ (σ : Gal(L/K)) : K) • (c δ • IsGalois.normalBasis K L δ) :=
      Function.Bijective.sum_comp (Group.mulLeft_bijective (σ : Gal(L/K)))
        (fun δ : Gal(L/K) =>
          (χ (σ : Gal(L/K)) : K) • (c δ • IsGalois.normalBasis K L δ))
    _ = (χ (σ : Gal(L/K)) : K) • normalBasisSubgroupCharacterVector Δ χ :=
      Finset.smul_sum.symm

/-- An automorphism outside the subgroup cannot have the prescribed
character action on this vector: the identity coordinate becomes zero. -/
theorem normalBasisSubgroupCharacterVector_not_eigen (Δ : Subgroup Gal(L/K))
    (χ : Gal(L/K) →* Kˣ) (g : Gal(L/K)) (hg : g ∉ Δ) :
    g (normalBasisSubgroupCharacterVector Δ χ) ≠
      (χ g : K) • normalBasisSubgroupCharacterVector Δ χ := by
  classical
  have hcoord : (IsGalois.normalBasis K L).repr
      (normalBasisSubgroupCharacterVector Δ χ) 1 = (1 : K) := by
    rw [normalBasisSubgroupCharacterVector_repr, Set.indicator_of_mem Δ.one_mem,
      map_one, inv_one, Units.val_one]
  have hmoved : (IsGalois.normalBasis K L).repr
      (g (normalBasisSubgroupCharacterVector Δ χ)) 1 = (0 : K) := by
    rw [map_normalBasisSubgroupCharacterVector, map_sum, Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro δ _hδ
    by_cases hδ : δ ∈ Δ
    · have hne : g * δ ≠ 1 := by
        intro h
        apply hg
        rw [mul_eq_one_iff_eq_inv.mp h]
        exact Δ.inv_mem hδ
      rw [map_smul, Finsupp.smul_apply, Module.Basis.repr_self_apply,
        ite_eq_right hne, smul_zero]
    · rw [Set.indicator_of_notMem hδ, zero_smul, map_zero, Finsupp.zero_apply]
  intro h
  have hrepr := congrArg (fun x : L => (IsGalois.normalBasis K L).repr x 1) h
  rw [hmoved, map_smul, Finsupp.smul_apply, hcoord, smul_eq_mul, mul_one] at hrepr
  exact (χ g).ne_zero hrepr.symm

/-- The actual canonical normal basis supplies a nonzero restricted-character
eigenvector on which any specified automorphism outside the subgroup fails
to act by the full character. -/
theorem exists_nonzero_subgroupCharacterEigenvector_not_eigen
    (Δ : Subgroup Gal(L/K)) (χ : Gal(L/K) →* Kˣ)
    (g : Gal(L/K)) (hg : g ∉ Δ) :
    ∃ b : L, b ≠ 0 ∧
      (∀ δ : Δ, (δ : Gal(L/K)) b = (χ (δ : Gal(L/K)) : K) • b) ∧
      g b ≠ (χ g : K) • b := by
  have hne := normalBasisSubgroupCharacterVector_not_eigen Δ χ g hg
  refine ⟨normalBasisSubgroupCharacterVector Δ χ, ?_,
    normalBasisSubgroupCharacterVector_eigen Δ χ, hne⟩
  intro hzero
  apply hne
  rw [hzero, map_zero, smul_zero]

end LocalFieldTheory.DiscreteValuationField
