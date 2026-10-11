/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.FiniteStage.PrimePower.Derivative.OnGroup.Scalar

/-!
# Fox differential: prime power — derivative — on group — vector

The principal declarations in this module are:

- `primePowerCompletedGroupAlgebraFreeFoxDerivativeVectorToCompletedTargetOnGroup`
  The dense group-level completed-target Fox derivative vector. It evaluates the completed-target
  derivative vector on group-like elements of the source completed group algebra.
- `primePowerCompletedGAFreeFoxDerivativeVectorToCompletedTargetOnGroup_apply`
  The prime-power completed-group-algebra Fox-derivative vector is evaluated on group elements by
  the corresponding completed-target finite-stage formula.
- `primePowerCompletedGAFreeFoxDerivativeVectorToCompletedTargetOnGroup_of`
  On a free generator, the completed-target derivative vector has the corresponding standard basis
  vector as its value.
- `primePowerCompletedGAFreeFoxDerivativeVectorToCompletedTargetOnGroup_unique`
  The completed-target Fox derivative vector is the unique crossed homomorphism with standard basis
  values.
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
The dense group-level completed-target Fox derivative vector. It evaluates the completed-target
derivative vector on group-like elements of the source completed group algebra.
-/
def primePowerCompletedGroupAlgebraFreeFoxDerivativeVectorToCompletedTargetOnGroup
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (foxAlgebraicStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (foxAlgebraicStageTargetQuotient (X := X) N)]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a))) :
    ScalarCrossedHom
      (foxAlgebraicStageTargetPrimePowerCompletedCoefficientHom (ℓ := ℓ) (X := X) N)
      (X → PrimePowerCompletedGroupAlgebra ℓ
        (foxAlgebraicStageTargetQuotient (X := X) N)) where
  toFun w := fun i =>
    primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTargetOnGroup
      (ℓ := ℓ) (X := X) N hfinite i w
  map_mul' := by
    intro u v
    funext i
    change
      primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTargetOnGroup
          (ℓ := ℓ) (X := X) N hfinite i (u * v) =
        primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTargetOnGroup
            (ℓ := ℓ) (X := X) N hfinite i u +
          foxAlgebraicStageTargetPrimePowerCompletedCoefficientHom
              (ℓ := ℓ) (X := X) N u •
            primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTargetOnGroup
              (ℓ := ℓ) (X := X) N hfinite i v
    exact ScalarCrossedHom.map_mul
      (primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTargetOnGroup
        (ℓ := ℓ) (X := X) N hfinite i) u v

omit [Fact (0 < ℓ)] in
/--
The prime-power completed-group-algebra Fox-derivative vector is evaluated on group elements by
the corresponding completed-target finite-stage formula.
-/
@[simp]
theorem primePowerCompletedGAFreeFoxDerivativeVectorToCompletedTargetOnGroup_apply
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (foxAlgebraicStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (foxAlgebraicStageTargetQuotient (X := X) N)]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (w : FreeGroup X) (i : X) :
    primePowerCompletedGroupAlgebraFreeFoxDerivativeVectorToCompletedTargetOnGroup
        (ℓ := ℓ) (X := X) N hfinite w i =
      primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTargetOnGroup
        (ℓ := ℓ) (X := X) N hfinite i w := rfl

omit [Fact (0 < ℓ)] in
/--
On a free generator, the completed-target derivative vector has the corresponding standard basis
vector as its value.
-/
@[simp 900]
theorem primePowerCompletedGAFreeFoxDerivativeVectorToCompletedTargetOnGroup_of
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (foxAlgebraicStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (foxAlgebraicStageTargetQuotient (X := X) N)]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (j : X) :
    primePowerCompletedGroupAlgebraFreeFoxDerivativeVectorToCompletedTargetOnGroup
        (ℓ := ℓ) (X := X) N hfinite (FreeGroup.of j) =
      Pi.single j
        (1 : PrimePowerCompletedGroupAlgebra ℓ
          (foxAlgebraicStageTargetQuotient (X := X) N)) := by
  funext i
  rw [primePowerCompletedGAFreeFoxDerivativeVectorToCompletedTargetOnGroup_apply,
    primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTargetOnGroup_of]
  by_cases hji : j = i
  · subst j
    simp only [Pi.single_eq_same]
  · have hij : i ≠ j := by
      exact Ne.symm hji
    simp only [ne_eq, hji, not_false_eq_true, Pi.single_eq_of_ne, hij]

omit [Fact (0 < ℓ)] in
/--
The completed-target Fox derivative vector is the unique crossed homomorphism with standard
basis values.
-/
theorem primePowerCompletedGAFreeFoxDerivativeVectorToCompletedTargetOnGroup_unique
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (foxAlgebraicStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (foxAlgebraicStageTargetQuotient (X := X) N)]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (delta : ScalarCrossedHom
      (foxAlgebraicStageTargetPrimePowerCompletedCoefficientHom (ℓ := ℓ) (X := X) N)
      (X → PrimePowerCompletedGroupAlgebra ℓ
        (foxAlgebraicStageTargetQuotient (X := X) N)))
    (hbasis : ∀ j : X, delta (FreeGroup.of j) =
      Pi.single j
        (1 : PrimePowerCompletedGroupAlgebra ℓ
          (foxAlgebraicStageTargetQuotient (X := X) N))) :
    delta =
      primePowerCompletedGroupAlgebraFreeFoxDerivativeVectorToCompletedTargetOnGroup
        (ℓ := ℓ) (X := X) N hfinite := by
  have hdelta_free := freeCrossedHomWithCoeff_unique
    (A := X → PrimePowerCompletedGroupAlgebra ℓ
      (foxAlgebraicStageTargetQuotient (X := X) N))
    (foxAlgebraicStageTargetPrimePowerCompletedCoefficientHom (ℓ := ℓ) (X := X) N)
    (fun j : X =>
      Pi.single j
        (1 : PrimePowerCompletedGroupAlgebra ℓ
          (foxAlgebraicStageTargetQuotient (X := X) N)))
    delta hbasis
  have hcompleted_free := freeCrossedHomWithCoeff_unique
    (A := X → PrimePowerCompletedGroupAlgebra ℓ
      (foxAlgebraicStageTargetQuotient (X := X) N))
    (foxAlgebraicStageTargetPrimePowerCompletedCoefficientHom (ℓ := ℓ) (X := X) N)
    (fun j : X =>
      Pi.single j
        (1 : PrimePowerCompletedGroupAlgebra ℓ
          (foxAlgebraicStageTargetQuotient (X := X) N)))
    (primePowerCompletedGroupAlgebraFreeFoxDerivativeVectorToCompletedTargetOnGroup
      (ℓ := ℓ) (X := X) N hfinite)
    (primePowerCompletedGAFreeFoxDerivativeVectorToCompletedTargetOnGroup_of
      (ℓ := ℓ) (X := X) N hfinite)
  exact hdelta_free.trans hcompleted_free.symm

omit [Fact (0 < ℓ)] in
/-- Existence and uniqueness of the completed-target Fox derivative-vector crossed homomorphism. -/
theorem existsUnique_primePowerCompletedGAFreeFoxDerivativeVectorToCompletedTargetOnGroup
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (foxAlgebraicStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (foxAlgebraicStageTargetQuotient (X := X) N)]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a))) :
    ∃! delta : ScalarCrossedHom
        (foxAlgebraicStageTargetPrimePowerCompletedCoefficientHom (ℓ := ℓ) (X := X) N)
        (X → PrimePowerCompletedGroupAlgebra ℓ
          (foxAlgebraicStageTargetQuotient (X := X) N)),
      ∀ j : X, delta (FreeGroup.of j) =
        Pi.single j
          (1 : PrimePowerCompletedGroupAlgebra ℓ
            (foxAlgebraicStageTargetQuotient (X := X) N)) := by
  refine ⟨primePowerCompletedGroupAlgebraFreeFoxDerivativeVectorToCompletedTargetOnGroup
    (ℓ := ℓ) (X := X) N hfinite, ?_, ?_⟩
  · exact primePowerCompletedGAFreeFoxDerivativeVectorToCompletedTargetOnGroup_of
      (ℓ := ℓ) (X := X) N hfinite
  · intro delta hdelta
    exact primePowerCompletedGAFreeFoxDerivativeVectorToCompletedTargetOnGroup_unique
      (ℓ := ℓ) (X := X) N hfinite delta hdelta




end

end FoxDifferential
