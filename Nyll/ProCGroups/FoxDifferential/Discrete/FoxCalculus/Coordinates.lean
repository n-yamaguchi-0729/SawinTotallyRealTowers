/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Discrete.FoxCalculus.Boundary

/-!
# Fox differential: discrete — fox calculus — coordinates

The principal declarations in this module are:

- `relativeFreeFoxCoordinatesLinearEquivDifferential`
  The linear equivalence between pushed-forward Fox coordinates and the universal differential
  module of a finite-rank free group.
- `relativeDifferentialToFreeFoxCoordinates_comp_relativeFreeFoxCoordinatesLinearMap`
  The coordinate map is a left inverse to the coordinate-to-differential map.
- `relativeFreeFoxCoordinatesLinearMap_comp_relativeDifferentialToFreeFoxCoordinates`
  The coordinate-to-differential map is a left inverse to the differential-to-coordinate map.
-/

namespace FoxDifferential

noncomputable section

namespace FoxCalculus

open scoped BigOperators

universe u v


variable {H : Type v} [Group H]
variable (X : Type u)

variable [DecidableEq X]
variable (ψ : FreeGroup X →* H)

variable [Fintype X]

/-- The coordinate map is a left inverse to the coordinate-to-differential map. -/
theorem relativeDifferentialToFreeFoxCoordinates_comp_relativeFreeFoxCoordinatesLinearMap :
    (relativeDifferentialToFreeFoxCoordinates (H := H) X ψ).comp
        (relativeFreeFoxCoordinatesLinearMap (H := H) X ψ) =
      LinearMap.id := by
  apply LinearMap.ext
  intro a
  rw [LinearMap.comp_apply]
  change relativeDifferentialToFreeFoxCoordinates (H := H) X ψ
      (∑ y : X, a y • universalDifferential ψ (FreeGroup.of y)) = a
  rw [map_sum]
  simp only [map_smul, relativeDifferentialToFreeFoxCoordinates_d]
  funext x
  change ((∑ y : X,
      a y • relativeFreeGroupFoxDerivative (H := H) X ψ (FreeGroup.of y)) :
      RelativeFreeFoxCoordinates (H := H) X) x = a x
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single x]
  · simp only [relativeFreeGroupFoxDerivative_of, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul,
      mul_one]
  · intro y _ hy
    have hxy : x ≠ y := fun h => hy h.symm
    simp only [relativeFreeGroupFoxDerivative_of, Pi.smul_apply, Pi.single_eq_of_ne hxy,
        smul_eq_mul, mul_zero]
  · simp only [Finset.mem_univ, not_true_eq_false, relativeFreeGroupFoxDerivative_of, Pi.smul_apply,
  Pi.single_eq_same, smul_eq_mul, mul_one, IsEmpty.forall_iff]

/-- The coordinate-to-differential map is a left inverse to the differential-to-coordinate map. -/
theorem relativeFreeFoxCoordinatesLinearMap_comp_relativeDifferentialToFreeFoxCoordinates :
    (relativeFreeFoxCoordinatesLinearMap (H := H) X ψ).comp
        (relativeDifferentialToFreeFoxCoordinates (H := H) X ψ) =
      LinearMap.id := by
  apply hom_ext ψ
  intro w
  change relativeFreeFoxCoordinatesLinearMap (H := H) X ψ
      (relativeDifferentialToFreeFoxCoordinates (H := H) X ψ
        (universalDifferential ψ w)) = universalDifferential ψ w
  rw [relativeDifferentialToFreeFoxCoordinates_d,
    relativeFreeFoxCoordinatesLinearMap_derivative]

/--
The linear equivalence between pushed-forward Fox coordinates and the universal differential
module of a finite-rank free group.
-/
def relativeFreeFoxCoordinatesLinearEquivDifferential :
    RelativeFreeFoxCoordinates (H := H) X ≃ₗ[GroupRing H] DifferentialModule ψ := by
  refine LinearEquiv.ofLinearMap
    (relativeFreeFoxCoordinatesLinearMap (H := H) X ψ)
    (relativeDifferentialToFreeFoxCoordinates (H := H) X ψ)
    ?_ ?_
  · exact relativeFreeFoxCoordinatesLinearMap_comp_relativeDifferentialToFreeFoxCoordinates
      (H := H) X ψ
  · exact relativeDifferentialToFreeFoxCoordinates_comp_relativeFreeFoxCoordinatesLinearMap
      (H := H) X ψ

end FoxCalculus

end

end FoxDifferential
