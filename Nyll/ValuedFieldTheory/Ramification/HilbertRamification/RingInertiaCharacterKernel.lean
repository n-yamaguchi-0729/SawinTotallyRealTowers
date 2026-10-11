/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Ring.Action.Basic
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.RingInertiaCharacter
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Tactic.Ring

/-!
# The principal-unit kernel of the inertia character

Characterizes triviality of the DVR inertia character by principal-unit multipliers on all ring
elements. It defines the corresponding inertia subgroup and identifies it with the character
kernel.
-/

noncomputable section

namespace RamificationTheory.HilbertRamification.DiscreteValuationRing

open IsLocalRing

universe u v

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (G : Type v) [Group G] [MulSemiringAction G R]

/-- The character kernel is exactly the actual principal-unit action on all
ring elements. The ratios and their residue-one property are constructed. -/
theorem inertiaResidueCharacter_eq_one_iff
    (σ : (maximalIdeal R).inertia G) :
    inertiaResidueCharacter R G σ = 1 ↔
      ∀ x : R, ∃ a : Rˣ,
        (σ : G) • x = x * (a : R) ∧ residue R (a : R) = 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  let c : Rˣ := uniformizerRatioUnit R G π hπ (σ : G)
  let f : Rˣ →* (ResidueField R)ˣ := Units.map (residue R).toMonoidHom
  have hc : π * (c : R) = (σ : G) • π := uniformizerRatioUnit_spec R G π hπ (σ : G)
  constructor
  · intro hσ x
    rw [inertiaResidueCharacter_eq_uniformizer R G π hπ] at hσ
    change f c = 1 at hσ
    by_cases hx : x = 0
    · subst x
      refine ⟨1, ?_, ?_⟩
      · rw [smul_zero, zero_mul]
      · exact map_one (residue R)
    · obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hπ
      let gu : Rˣ := Units.map
        (MulSemiringAction.toRingHom G R (σ : G)).toMonoidHom u
      let a : Rˣ := u⁻¹ * gu * c ^ n
      have hua : u * a = gu * c ^ n := by
        dsimp only [a]
        rw [← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
      refine ⟨a, ?_, ?_⟩
      · calc
          (σ : G) • x = ((σ : G) • (u : R)) * (π * (c : R)) ^ n := by
            rw [hu, smul_mul', smul_pow', hc]
          _ = π ^ n * ((gu * c ^ n : Rˣ) : R) := by
            change ((σ : G) • (u : R)) * (π * (c : R)) ^ n =
              π ^ n * (((σ : G) • (u : R)) * (c : R) ^ n)
            rw [mul_pow]
            ring
          _ = π ^ n * ((u * a : Rˣ) : R) :=
            congrArg (fun b : Rˣ => π ^ n * (b : R)) hua.symm
          _ = x * (a : R) := by
            rw [hu]
            change π ^ n * ((u : R) * (a : R)) = ((u : R) * π ^ n) * (a : R)
            ring
      · have hgu : f gu = f u := inertia_residueUnits_fixed R G σ u
        have ha : f a = 1 := by
          dsimp only [a]
          rw [map_mul, map_mul, map_inv, map_pow, hgu, hσ, one_pow,
            inv_mul_cancel, mul_one]
        exact congrArg (fun b : (ResidueField R)ˣ => (b : ResidueField R)) ha
  · intro h
    obtain ⟨a, ha, hres⟩ := h π
    have hac : a = c := by
      apply Units.ext
      exact mul_left_cancel₀ hπ.ne_zero (ha.symm.trans hc.symm)
    rw [inertiaResidueCharacter_eq_uniformizer R G π hπ]
    change f c = 1
    rw [← hac]
    apply Units.ext
    exact hres

/-- Actual principal-unit inertia, with its literal ring-element predicate. -/
def principalUnitInertia : Subgroup ((maximalIdeal R).inertia G) :=
  ((inertiaResidueCharacter R G).ker).copy
    {σ | ∀ x : R, ∃ a : Rˣ,
      (σ : G) • x = x * (a : R) ∧ residue R (a : R) = 1}
    (Set.ext (fun σ => (inertiaResidueCharacter_eq_one_iff R G σ).symm))

theorem principalUnitInertia_eq_character_ker :
    principalUnitInertia R G = (inertiaResidueCharacter R G).ker :=
  Subgroup.copy_eq _ _ _

end RamificationTheory.HilbertRamification.DiscreteValuationRing

end
