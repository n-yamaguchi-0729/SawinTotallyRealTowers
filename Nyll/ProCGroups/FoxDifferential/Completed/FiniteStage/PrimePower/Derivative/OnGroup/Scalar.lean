/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.FiniteStage.PrimePower.Derivative.OnGroup.Coefficient

/-!
# Fox differential: prime power — derivative — on group — scalar

The principal declarations in this module are:

- `primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTargetOnGroup`
  The dense group-level form of the completed-target Fox derivative. This is the completed-target
  derivative evaluated on group-like elements of the source completed group algebra.
- `primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTargetOnGroup_apply`
  The Fox derivative from the prime-power completed group algebra to the completed target is
  evaluated on group elements by the corresponding finite-stage formula.
- `primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTargetOnGroup_of`
  On a free generator, the group-level completed-target Fox derivative has the expected Kronecker
  generator value.
- `primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTargetOnGroup_unique`
  The group-level completed-target Fox derivative is the unique crossed homomorphism with its
  standard Kronecker values on free generators.
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
The dense group-level form of the completed-target Fox derivative. This is the completed-target
derivative evaluated on group-like elements of the source completed group algebra.
-/
def primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTargetOnGroup
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (foxAlgebraicStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (foxAlgebraicStageTargetQuotient (X := X) N)]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (i : X) :
    ScalarCrossedHom
      (foxAlgebraicStageTargetPrimePowerCompletedCoefficientHom (ℓ := ℓ) (X := X) N)
      (PrimePowerCompletedGroupAlgebra ℓ
        (foxAlgebraicStageTargetQuotient (X := X) N)) where
  toFun w := primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
      (ℓ := ℓ) (X := X) N hfinite i
      (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X) w)
  map_mul' := by
    intro u v
    simpa only [scalarCrossedAction_apply,
      foxAlgebraicStageTargetPrimePowerCompletedCoefficientHom_apply, smul_eq_mul]
      using primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget_of_mul
        (ℓ := ℓ) (X := X) N hfinite i u v

omit [Fact (0 < ℓ)] in
/--
The Fox derivative from the prime-power completed group algebra to the completed target is
evaluated on group elements by the corresponding finite-stage formula.
-/
@[simp]
theorem primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTargetOnGroup_apply
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (foxAlgebraicStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (foxAlgebraicStageTargetQuotient (X := X) N)]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (i : X) (w : FreeGroup X) :
    primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTargetOnGroup
        (ℓ := ℓ) (X := X) N hfinite i w =
      primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
        (ℓ := ℓ) (X := X) N hfinite i
        (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X) w) := rfl

omit [Fact (0 < ℓ)] in
/--
On a free generator, the group-level completed-target Fox derivative has the expected Kronecker
generator value.
-/
@[simp 900]
theorem primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTargetOnGroup_of
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (foxAlgebraicStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (foxAlgebraicStageTargetQuotient (X := X) N)]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (i j : X) :
    primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTargetOnGroup
        (ℓ := ℓ) (X := X) N hfinite i (FreeGroup.of j) =
      ((Pi.single i
        (1 : PrimePowerCompletedGroupAlgebra ℓ
          (foxAlgebraicStageTargetQuotient (X := X) N))) :
        X → PrimePowerCompletedGroupAlgebra ℓ
          (foxAlgebraicStageTargetQuotient (X := X) N)) j := by
  apply (primePowerCompletedGroupAlgebraSystem ℓ
    (foxAlgebraicStageTargetQuotient (X := X) N)).ext
  intro k
  rw [primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTargetOnGroup_apply]
  change primePowerCompletedGroupAlgebraProjection
      (ℓ := ℓ) (G := foxAlgebraicStageTargetQuotient (X := X) N) k
      (primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
        (ℓ := ℓ) (X := X) N hfinite i
        (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X)
          (FreeGroup.of j))) =
    primePowerCompletedGroupAlgebraProjection
      (ℓ := ℓ) (G := foxAlgebraicStageTargetQuotient (X := X) N) k
      (((Pi.single i
        (1 : PrimePowerCompletedGroupAlgebra ℓ
          (foxAlgebraicStageTargetQuotient (X := X) N))) :
        X → PrimePowerCompletedGroupAlgebra ℓ
          (foxAlgebraicStageTargetQuotient (X := X) N)) j)
  rw [ppCompletedGAFoxDerivToTarget_generator_proj]
  by_cases hji : j = i
  · subst j
    simp only [Pi.single_eq_same, map_one, InverseSystem.projection_apply,
      coe_one_primePowerCompletedGroupAlgebra, Pi.one_apply]
    rfl
  · have hij : i ≠ j := by
      exact Ne.symm hji
    simp only [ne_eq, hij, not_false_eq_true, Pi.single_eq_of_ne, map_zero, hji,
        InverseSystem.projection_apply,
      coe_zero_primePowerCompletedGroupAlgebra, Pi.zero_apply]
    rfl

omit [Fact (0 < ℓ)] in
/--
The group-level completed-target Fox derivative is the unique crossed homomorphism with its
standard Kronecker values on free generators.
-/
theorem primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTargetOnGroup_unique
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (foxAlgebraicStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (foxAlgebraicStageTargetQuotient (X := X) N)]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (i : X)
    (delta : ScalarCrossedHom
      (foxAlgebraicStageTargetPrimePowerCompletedCoefficientHom (ℓ := ℓ) (X := X) N)
      (PrimePowerCompletedGroupAlgebra ℓ
        (foxAlgebraicStageTargetQuotient (X := X) N)))
    (hbasis : ∀ j : X, delta (FreeGroup.of j) =
      ((Pi.single i
        (1 : PrimePowerCompletedGroupAlgebra ℓ
          (foxAlgebraicStageTargetQuotient (X := X) N))) :
        X → PrimePowerCompletedGroupAlgebra ℓ
          (foxAlgebraicStageTargetQuotient (X := X) N)) j) :
    delta =
      primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTargetOnGroup
        (ℓ := ℓ) (X := X) N hfinite i := by
  let basisValue : X →
      PrimePowerCompletedGroupAlgebra ℓ (foxAlgebraicStageTargetQuotient (X := X) N) :=
    fun j =>
      ((Pi.single i
        (1 : PrimePowerCompletedGroupAlgebra ℓ
          (foxAlgebraicStageTargetQuotient (X := X) N))) :
        X → PrimePowerCompletedGroupAlgebra ℓ
          (foxAlgebraicStageTargetQuotient (X := X) N)) j
  have hdelta_free := freeCrossedHomWithCoeff_unique
    (A := PrimePowerCompletedGroupAlgebra ℓ
      (foxAlgebraicStageTargetQuotient (X := X) N))
    (foxAlgebraicStageTargetPrimePowerCompletedCoefficientHom (ℓ := ℓ) (X := X) N)
    basisValue delta hbasis
  have hcompleted_free := freeCrossedHomWithCoeff_unique
    (A := PrimePowerCompletedGroupAlgebra ℓ
      (foxAlgebraicStageTargetQuotient (X := X) N))
    (foxAlgebraicStageTargetPrimePowerCompletedCoefficientHom (ℓ := ℓ) (X := X) N)
    basisValue
    (primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTargetOnGroup
      (ℓ := ℓ) (X := X) N hfinite i)
    (by
      intro j
      exact primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTargetOnGroup_of
        (ℓ := ℓ) (X := X) N hfinite i j)
  exact hdelta_free.trans hcompleted_free.symm

omit [Fact (0 < ℓ)] in
/--
Existence and uniqueness of the completed-target Fox crossed homomorphism on group-like source
elements.
-/
theorem existsUnique_ppCompletedGAFoxDerivToTargetOnGroup
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (foxAlgebraicStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (foxAlgebraicStageTargetQuotient (X := X) N)]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (i : X) :
    ∃! delta : ScalarCrossedHom
        (foxAlgebraicStageTargetPrimePowerCompletedCoefficientHom (ℓ := ℓ) (X := X) N)
        (PrimePowerCompletedGroupAlgebra ℓ
          (foxAlgebraicStageTargetQuotient (X := X) N)),
      ∀ j : X, delta (FreeGroup.of j) =
        ((Pi.single i
          (1 : PrimePowerCompletedGroupAlgebra ℓ
            (foxAlgebraicStageTargetQuotient (X := X) N))) :
          X → PrimePowerCompletedGroupAlgebra ℓ
            (foxAlgebraicStageTargetQuotient (X := X) N)) j := by
  refine ⟨primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTargetOnGroup
    (ℓ := ℓ) (X := X) N hfinite i, ?_, ?_⟩
  · exact primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTargetOnGroup_of
      (ℓ := ℓ) (X := X) N hfinite i
  · intro delta hdelta
    exact primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTargetOnGroup_unique
      (ℓ := ℓ) (X := X) N hfinite i delta hdelta




end

end FoxDifferential
