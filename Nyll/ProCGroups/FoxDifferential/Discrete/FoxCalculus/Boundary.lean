/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Common.FoxBoundary
import Nyll.ProCGroups.FoxDifferential.Discrete.DifferentialModule.Boundary
import Nyll.ProCGroups.FoxDifferential.Discrete.FoxCalculus.Universal

/-!
# Fox differential: discrete — fox calculus — boundary

The principal declarations in this module are:

- `relativeFreeGroupFoxBoundary`
  The pushed-forward Fox boundary \(a \mapsto \sum_x a_x (\psi(x) - 1)\).
- `relativeFreeGroupFoxBoundary_apply`
  The relative free-group Fox boundary is evaluated on canonical generators and then extended
  linearly to the coordinate module.
- `relativeFreeGroupFoxBoundary_single`
  The relative Fox boundary sends a coordinate basis vector to the corresponding augmentation
  generator.
- `toGroupRing_comp_relativeFreeFoxCoordinatesLinearMap`
  Composing the universal boundary with the coordinate-to-differential map gives the pushed-forward
  Fox boundary.
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

/-- The pushed-forward Fox boundary \(a \mapsto \sum_x a_x (\psi(x) - 1)\). -/
def relativeFreeGroupFoxBoundary :
    RelativeFreeFoxCoordinates (H := H) X →ₗ[GroupRing H] GroupRing H :=
  { toFun := fun a =>
      ∑ x : X, a x * augmentationGenerator H (ψ (FreeGroup.of x))
    map_add' := by
      intro a b
      simp only [Pi.add_apply, augmentationGenerator_eq_groupRingBoundary, add_mul,
          Finset.sum_add_distrib]
    map_smul' := by
      intro r a
      simp only [Pi.smul_apply, smul_eq_mul, augmentationGenerator_eq_groupRingBoundary, mul_assoc,
  RingHom.id_apply, Finset.mul_sum]}

omit [DecidableEq X] in
/--
The relative free-group Fox boundary is evaluated on canonical generators and then extended
linearly to the coordinate module.
-/
theorem relativeFreeGroupFoxBoundary_apply
    (a : RelativeFreeFoxCoordinates (H := H) X) :
    relativeFreeGroupFoxBoundary (H := H) X ψ a =
      ∑ x : X, a x * augmentationGenerator H (ψ (FreeGroup.of x)) :=
  rfl

/--
The relative Fox boundary sends a coordinate basis vector to the corresponding augmentation
generator.
-/
@[simp]
theorem relativeFreeGroupFoxBoundary_single (x : X) :
    relativeFreeGroupFoxBoundary (H := H) X ψ
        (Pi.single x (1 : GroupRing H)) =
      augmentationGenerator H (ψ (FreeGroup.of x)) := by
  rw [relativeFreeGroupFoxBoundary_apply]
  rw [Finset.sum_eq_single x]
  · simp only [Pi.single_eq_same, augmentationGenerator_eq_groupRingBoundary, one_mul]
  · intro y _ hy
    simp only [Pi.single_eq_of_ne hy, augmentationGenerator_eq_groupRingBoundary, zero_mul]
  · simp only [Finset.mem_univ, not_true_eq_false, Pi.single_eq_same,
      augmentationGenerator_eq_groupRingBoundary,
  one_mul, IsEmpty.forall_iff]

omit [DecidableEq X] in
/--
Composing the universal boundary with the coordinate-to-differential map gives the
pushed-forward Fox boundary.
-/
theorem toGroupRing_comp_relativeFreeFoxCoordinatesLinearMap :
    (toGroupRing ψ).comp
        (relativeFreeFoxCoordinatesLinearMap (H := H) X ψ) =
      relativeFreeGroupFoxBoundary (H := H) X ψ := by
  apply LinearMap.ext
  intro a
  change
    toGroupRing ψ
        (∑ x : X, a x • universalDifferential ψ (FreeGroup.of x)) =
      ∑ x : X, a x * augmentationGenerator H (ψ (FreeGroup.of x))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro x _hx
  rw [map_smul, toGroupRing_d]
  rfl

/--
Relative Fox fundamental formula, also known as the Fox--Euler formula: \(\psi(w) - 1 = \sum_x
(\partial w/\partial x) (\psi(x) - 1)\).
-/
theorem relativeFreeGroupFoxDerivative_fundamental_formula (w : FreeGroup X) :
    groupRingBoundary ψ w =
      ∑ x : X,
        relativeFreeGroupFoxDerivative (H := H) X ψ w x *
          augmentationGenerator H (ψ (FreeGroup.of x)) := by
  have h :=
    LinearMap.congr_fun
      (toGroupRing_comp_relativeFreeFoxCoordinatesLinearMap (H := H) X ψ)
      (relativeFreeGroupFoxDerivative (H := H) X ψ w)
  rw [LinearMap.comp_apply, relativeFreeFoxCoordinatesLinearMap_derivative,
    toGroupRing_d] at h
  simpa [relativeFreeGroupFoxBoundary] using h

/-- Fox boundary form of the relative Fox fundamental formula. -/
theorem relativeFreeGroupFoxBoundary_derivative (w : FreeGroup X) :
    relativeFreeGroupFoxBoundary (H := H) X ψ
        (relativeFreeGroupFoxDerivative (H := H) X ψ w) =
      groupRingBoundary ψ w := by
  simpa [relativeFreeGroupFoxBoundary_apply] using
    (relativeFreeGroupFoxDerivative_fundamental_formula (H := H) X ψ w).symm

/--
Conditional relative Fox boundary formula. Any differential map on a free group with the
standard coordinate values satisfies the relative Fox boundary formula.
-/
theorem relativeFreeGroupFoxBoundary_of_crossedHom
    (delta : DifferentialHom ψ (RelativeFreeFoxCoordinates (H := H) X))
    (hbasis :
      ∀ x : X, delta (FreeGroup.of x) = Pi.single x (1 : GroupRing H))
    (w : FreeGroup X) :
    relativeFreeGroupFoxBoundary (H := H) X ψ (delta w) = groupRingBoundary ψ w := by
  have hdelta_eq : delta = relativeFreeGroupFoxHom (H := H) X ψ :=
    relativeFreeGroupFoxHom_unique (H := H) X ψ delta hbasis
  rw [hdelta_eq]
  exact relativeFreeGroupFoxBoundary_derivative (H := H) X ψ w

/--
Conditional relative Fox fundamental formula. The Fox-Euler sum computed from any differential
map with standard coordinate values is \([\psi(w)]-1\).
-/
theorem relativeFreeGroupFoxDerivative_fundamental_formula_of_crossedHom
    (delta : DifferentialHom ψ (RelativeFreeFoxCoordinates (H := H) X))
    (hbasis :
      ∀ x : X, delta (FreeGroup.of x) = Pi.single x (1 : GroupRing H))
    (w : FreeGroup X) :
    groupRingBoundary ψ w =
      ∑ x : X, delta w x * augmentationGenerator H (ψ (FreeGroup.of x)) := by
  simpa [relativeFreeGroupFoxBoundary_apply] using
    (relativeFreeGroupFoxBoundary_of_crossedHom (H := H) X ψ delta hbasis w).symm

/-- Explicit \(\psi(w)-1\) version of the conditional relative Fox-Euler formula. -/
theorem relativeFreeGroupFoxDerivative_euler_formula_of_crossedHom
    (delta : DifferentialHom ψ (RelativeFreeFoxCoordinates (H := H) X))
    (hbasis :
      ∀ x : X, delta (FreeGroup.of x) = Pi.single x (1 : GroupRing H))
    (w : FreeGroup X) :
    (MonoidAlgebra.of ℤ H (ψ w) : GroupRing H) - 1 =
      ∑ x : X, delta w x * augmentationGenerator H (ψ (FreeGroup.of x)) := by
  simpa [groupRingBoundary] using
    relativeFreeGroupFoxDerivative_fundamental_formula_of_crossedHom
      (H := H) X ψ delta hbasis w

/-- Explicit \(\psi(w)-1\) version of the relative Fox--Euler formula. -/
theorem relativeFreeGroupFoxDerivative_euler_formula (w : FreeGroup X) :
    (MonoidAlgebra.of ℤ H (ψ w) : GroupRing H) - 1 =
      ∑ x : X,
        relativeFreeGroupFoxDerivative (H := H) X ψ w x *
          augmentationGenerator H (ψ (FreeGroup.of x)) := by
  simpa [groupRingBoundary] using
    relativeFreeGroupFoxDerivative_fundamental_formula (H := H) X ψ w

end FoxCalculus

end

end FoxDifferential
