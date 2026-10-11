/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.FiniteStage.PrimePower.Derivative.Source.Fundamental
import Nyll.ProCGroups.FoxDifferential.Completed.FiniteStage.PrimePower.Derivative.Source.GroupLike
import Nyll.ProCGroups.FoxDifferential.Completed.FiniteStage.PrimePower.Derivative.Source.Mul
import Nyll.ProCGroups.FoxDifferential.Completed.FiniteStage.PrimePower.Derivative.Source.SpecialValues

/-!
# Fox differential: prime power — derivative — on group — coefficient

The principal declarations in this module are:

- `foxAlgebraicStageTargetPrimePowerCompletedCoefficientHom`
  The completed target coefficient homomorphism is associated to the quotient
  \(\mathrm{FreeGroup}(X) \to F/N\). It sends a word to the corresponding group-like element of the
  prime-power completed group algebra of the target quotient.
- `foxAlgebraicStageTargetPrimePowerCompletedCoefficientHom_apply`
  The finite Fox-stage target coefficient homomorphism into the prime-power completed coefficients
  is evaluated by the corresponding finite-stage coefficient map.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u v

variable (ℓ : ℕ) [Fact (0 < ℓ)]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]


variable {X : Type u} [DecidableEq X]
variable (N : Subgroup (FreeGroup X)) [N.Normal] (n : ℕ)


/--
The completed target coefficient homomorphism is associated to the quotient
\(\mathrm{FreeGroup}(X) \to F/N\). It sends a word to the corresponding group-like element of
the prime-power completed group algebra of the target quotient.
-/
def foxAlgebraicStageTargetPrimePowerCompletedCoefficientHom
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (foxAlgebraicStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (foxAlgebraicStageTargetQuotient (X := X) N)] :
    FreeGroup X →*
      PrimePowerCompletedGroupAlgebra ℓ (foxAlgebraicStageTargetQuotient (X := X) N) where
  toFun w :=
    primePowerCompletedGroupAlgebraOf (ell := ℓ)
      (H := foxAlgebraicStageTargetQuotient (X := X) N) (QuotientGroup.mk' N w)
  map_one' := by
    simp only [QuotientGroup.mk'_apply, QuotientGroup.mk_one, primePowerCompletedGroupAlgebraOf_one]
  map_mul' u v := by
    rw [← primePowerCompletedGroupAlgebraOf_mul (ell := ℓ)
      (H := foxAlgebraicStageTargetQuotient (X := X) N)]
    rfl

omit [DecidableEq X] [Fact (0 < ℓ)] in
/--
The finite Fox-stage target coefficient homomorphism into the prime-power completed coefficients
is evaluated by the corresponding finite-stage coefficient map.
-/
@[simp]
theorem foxAlgebraicStageTargetPrimePowerCompletedCoefficientHom_apply
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (foxAlgebraicStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (foxAlgebraicStageTargetQuotient (X := X) N)] (w : FreeGroup X) :
    foxAlgebraicStageTargetPrimePowerCompletedCoefficientHom (ℓ := ℓ) (X := X) N w =
      primePowerCompletedGroupAlgebraOf (ell := ℓ)
        (H := foxAlgebraicStageTargetQuotient (X := X) N) (QuotientGroup.mk' N w) := rfl




end

end FoxDifferential
