/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.FiniteStage.SourceBoundary

/-!
# Fox differential: completed — finite stage — source derivative vector

The principal declarations in this module are:

- `foxAlgebraicStageSourceDerivativeVector`
  Source-valued derivative vector of a source quotient element.
- `foxAlgebraicStageSourceGroupAlgebraDerivativeVector`
  Source-valued derivative vector of an arbitrary source group-algebra element.
- `foxAlgebraicStageSourceDerivativeVector_apply`
  The finite-stage source derivative vector evaluates the source word at the chosen coordinate.
- `foxAlgebraicStageSourceGroupAlgebraDerivativeVector_apply`
  The finite-stage source group-algebra derivative vector is evaluated coordinatewise in the source
  finite quotient.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u

variable {X : Type u} [DecidableEq X]
variable (N : Subgroup (FreeGroup X)) [N.Normal] (n : ℕ)

/-- Source-valued derivative vector of a source quotient element. -/
def foxAlgebraicStageSourceDerivativeVector
    (q : FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) :
    foxAlgebraicStageSourceCoordinateVector (X := X) N n :=
  fun i =>
    foxAlgebraicStageSourceGroupAlgebraDerivative (X := X) N n i
      (MonoidAlgebra.of (ModNCompletedCoeff n)
        (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) q)

omit [N.Normal] in
/-- The finite-stage source derivative vector evaluates the source word at the chosen coordinate. -/
@[simp]
theorem foxAlgebraicStageSourceDerivativeVector_apply
    (q : FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
    (i : X) :
    foxAlgebraicStageSourceDerivativeVector (X := X) N n q i =
      foxAlgebraicStageSourceGroupAlgebraDerivative (X := X) N n i
        (MonoidAlgebra.of (ModNCompletedCoeff n)
          (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) q) :=
  rfl

/-- Source-valued derivative vector of an arbitrary source group-algebra element. -/
def foxAlgebraicStageSourceGroupAlgebraDerivativeVector :
    foxAlgebraicStageSourceGroupAlgebra (X := X) N n →ₗ[ModNCompletedCoeff n]
      foxAlgebraicStageSourceCoordinateVector (X := X) N n where
  toFun x := fun i => foxAlgebraicStageSourceGroupAlgebraDerivative (X := X) N n i x
  map_add' := by
    intro x y
    funext i
    simp only [map_add, Pi.add_apply]
  map_smul' := by
    intro a x
    funext i
    simp only [map_smul, RingHom.id_apply, Pi.smul_apply]

omit [N.Normal] in
/--
The finite-stage source group-algebra derivative vector is evaluated coordinatewise in the
source finite quotient.
-/
@[simp]
theorem foxAlgebraicStageSourceGroupAlgebraDerivativeVector_apply
    (x : foxAlgebraicStageSourceGroupAlgebra (X := X) N n) (i : X) :
    foxAlgebraicStageSourceGroupAlgebraDerivativeVector (X := X) N n x i =
      foxAlgebraicStageSourceGroupAlgebraDerivative (X := X) N n i x :=
  rfl

omit [N.Normal] in
/-- The source boundary of the source-valued derivative of a source quotient element is \(q-1\). -/
theorem foxAlgebraicStageSourceFoxBoundary_sourceDerivativeVector
    [Fintype X]
    (q : FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) :
    foxAlgebraicStageSourceFoxBoundary (X := X) N n
        (foxAlgebraicStageSourceDerivativeVector (X := X) N n q) =
      MonoidAlgebra.of (ModNCompletedCoeff n)
        (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) q - 1 := by
  rw [foxAlgebraicStageSourceFoxBoundary_apply]
  exact (foxAlgebraicStageSourceGroupAlgebraDerivative_of_quotient_fundamental_formula
    (X := X) (N := N) (n := n) q).symm

omit [N.Normal] in
/--
The source boundary of the source-valued derivative of a group-algebra element is the usual
source augmentation formula.
-/
theorem foxAlgebraicStageSourceFoxBoundary_sourceGroupAlgebraDerivativeVector
    [Fintype X]
    (x : foxAlgebraicStageSourceGroupAlgebra (X := X) N n) :
    foxAlgebraicStageSourceFoxBoundary (X := X) N n
        (foxAlgebraicStageSourceGroupAlgebraDerivativeVector (X := X) N n x) =
      x -
        algebraMap (ModNCompletedCoeff n)
          (foxAlgebraicStageSourceGroupAlgebra (X := X) N n)
          (foxCommutatorPowerSourceGroupAlgebraAugmentation
            (F := FreeGroup X) N n x) := by
  rw [foxAlgebraicStageSourceFoxBoundary_apply]
  exact (foxAlgebraicStageSourceGroupAlgebraDerivative_groupAlgebra_fundamental_formula
    (X := X) (N := N) (n := n) x).symm

omit [DecidableEq X] in
/-- The source-to-target coordinate map commutes with source scalar multiplication. -/
theorem foxAlgebraicStageCoordinateSourceToTarget_smul_source
    (a : foxAlgebraicStageSourceGroupAlgebra (X := X) N n)
    (v : foxAlgebraicStageSourceCoordinateVector (X := X) N n) :
    foxAlgebraicStageCoordinateSourceToTarget (X := X) N n (a • v) =
      foxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N n a •
        foxAlgebraicStageCoordinateSourceToTarget (X := X) N n v := by
  funext i
  rw [foxAlgebraicStageCoordinateSourceToTarget_apply]
  simp only [Pi.smul_apply, foxAlgebraicStageCoordinateSourceToTarget_apply]
  change
    foxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N n (a * v i) =
      foxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N n a *
        foxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N n (v i)
  rw [RingHom.map_mul]

/--
Applying source-to-target coordinates to a source derivative vector gives the target-valued
finite derivative vector.
-/
theorem foxAlgebraicStageCoordinateSourceToTarget_sourceDerivativeVector
    (q : FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) :
    foxAlgebraicStageCoordinateSourceToTarget (X := X) N n
        (foxAlgebraicStageSourceDerivativeVector (X := X) N n q) =
      foxAlgebraicStageQuotientDerivativeVector (X := X) N n q := by
  funext i
  rw [foxAlgebraicStageCoordinateSourceToTarget_apply,
    foxAlgebraicStageSourceDerivativeVector_apply]
  rw [foxAlgebraicStageSourceGroupAlgebraDerivative_map_of_quotient,
    foxAlgebraicStageGroupAlgebraDerivative_of_quotient]
  rfl

/--
Applying source-to-target coordinates to the group-algebra source derivative vector gives the
coordinatewise target group-algebra derivative.
-/
theorem foxAlgebraicStageCoordinateSourceToTarget_sourceGroupAlgebraDerivativeVector
    (x : foxAlgebraicStageSourceGroupAlgebra (X := X) N n) :
    foxAlgebraicStageCoordinateSourceToTarget (X := X) N n
        (foxAlgebraicStageSourceGroupAlgebraDerivativeVector (X := X) N n x) =
      fun i => foxAlgebraicStageGroupAlgebraDerivative (X := X) N n i x := by
  funext i
  rw [foxAlgebraicStageCoordinateSourceToTarget_apply,
    foxAlgebraicStageSourceGroupAlgebraDerivativeVector_apply]
  exact foxAlgebraicStageSourceGroupAlgebraDerivative_map
    (X := X) (N := N) (n := n) i x

end

end FoxDifferential
