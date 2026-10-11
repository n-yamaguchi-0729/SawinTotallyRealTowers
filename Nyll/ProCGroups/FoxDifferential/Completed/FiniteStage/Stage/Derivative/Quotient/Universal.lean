/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.FiniteStage.Stage.Derivative.Quotient.Basic

/-!
# Fox differential: stage — derivative — quotient — universal

The principal declarations in this module are:

- `foxAlgebraicStageQuotientDerivativeVectorLinearMap`
  The linear map from the quotient universal crossed-differential module representing the descended
  finite-stage Fox derivative vector.
- `foxAlgebraicStageQuotientDerivativeVectorLinearMap_universal`
  The quotient derivative-vector linear map evaluates on the universal differential as the descended
  finite-stage Fox derivative vector.
- `existsUnique_foxAlgebraicStageQuotientDerivativeVectorLinearMap`
  Existence and uniqueness of the linear map representing the descended finite-stage Fox derivative
  vector on the finite source quotient.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u

variable {X : Type u} [DecidableEq X]
variable (N : Subgroup (FreeGroup X)) [N.Normal] (n : ℕ)

/--
The linear map from the quotient universal crossed-differential module representing the
descended finite-stage Fox derivative vector.
-/
def foxAlgebraicStageQuotientDerivativeVectorLinearMap :
    CrossedDifferentialModule (foxAlgebraicStageQuotientCoefficient (X := X) N n) →ₗ[
      foxAlgebraicStageTargetGroupAlgebra (X := X) N n]
      foxAlgebraicStageCoordinateVector (X := X) N n :=
  crossedHomModuleLift
    (A := foxAlgebraicStageCoordinateVector (X := X) N n)
    (foxAlgebraicStageQuotientCoefficient (X := X) N n)
    (foxAlgebraicStageQuotientDerivativeVector (X := X) N n)

/--
The quotient derivative-vector linear map evaluates on the universal differential as the
descended finite-stage Fox derivative vector.
-/
@[simp]
theorem foxAlgebraicStageQuotientDerivativeVectorLinearMap_universal
    (q : FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) :
    foxAlgebraicStageQuotientDerivativeVectorLinearMap (X := X) N n
        (universalCrossedDifferential (foxAlgebraicStageQuotientCoefficient (X := X) N n) q) =
      foxAlgebraicStageQuotientDerivativeVector (X := X) N n q := by
  exact crossedHomModuleLift_universal
    (A := foxAlgebraicStageCoordinateVector (X := X) N n)
    (foxAlgebraicStageQuotientCoefficient (X := X) N n)
    (foxAlgebraicStageQuotientDerivativeVector (X := X) N n) q

/--
Existence and uniqueness of the linear map representing the descended finite-stage Fox
derivative vector on the finite source quotient.
-/
theorem existsUnique_foxAlgebraicStageQuotientDerivativeVectorLinearMap :
    ∃! f :
        CrossedDifferentialModule (foxAlgebraicStageQuotientCoefficient (X := X) N n) →ₗ[
          foxAlgebraicStageTargetGroupAlgebra (X := X) N n]
          foxAlgebraicStageCoordinateVector (X := X) N n,
      ∀ q : FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n,
        f (universalCrossedDifferential (foxAlgebraicStageQuotientCoefficient (X := X) N n) q) =
          foxAlgebraicStageQuotientDerivativeVector (X := X) N n q := by
  exact existsUnique_crossedHomModuleLift
    (A := foxAlgebraicStageCoordinateVector (X := X) N n)
    (foxAlgebraicStageQuotientCoefficient (X := X) N n)
    (foxAlgebraicStageQuotientDerivativeVector (X := X) N n)



end

end FoxDifferential
