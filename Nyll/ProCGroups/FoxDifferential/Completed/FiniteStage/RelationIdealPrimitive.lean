/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.FiniteStage.SourceDerivativeVector

/-!
# Fox differential: completed — finite stage — relation ideal primitive

The principal declarations in this module are:

- `foxAlgebraicStageSourceBoundaryPrimitive`
  An element of the source finite group algebra has a relation-compatible source Fox primitive if it
  is the source boundary of a vector whose target projection lies in the finite relation-boundary
  submodule.
- `foxAlgebraicStageSourceBoundaryPrimitiveSubmodule`
  Source-boundary primitives form a left submodule of the source group algebra.
- `foxAlgebraicStageSourceBoundaryPrimitive_zero`
  The zero source-boundary primitive.
- `foxAlgebraicStageSourceBoundaryPrimitive_add`
  Source-boundary primitives are closed under addition.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u

variable {X : Type u} [DecidableEq X]
variable (N : Subgroup (FreeGroup X)) [N.Normal] (n : ℕ)

/--
An element of the source finite group algebra has a relation-compatible source Fox primitive if
it is the source boundary of a vector whose target projection lies in the finite
relation-boundary submodule.
-/
def foxAlgebraicStageSourceBoundaryPrimitive [Fintype X]
    (x : foxAlgebraicStageSourceGroupAlgebra (X := X) N n) : Prop :=
  ∃ p : foxAlgebraicStageSourceCoordinateVector (X := X) N n,
    foxAlgebraicStageSourceFoxBoundary (X := X) N n p = x ∧
      foxAlgebraicStageCoordinateSourceToTarget (X := X) N n p ∈
        foxAlgebraicStageRelationBoundarySubmodule (X := X) N n

/-- The zero source-boundary primitive. -/
theorem foxAlgebraicStageSourceBoundaryPrimitive_zero [Fintype X] :
    foxAlgebraicStageSourceBoundaryPrimitive (X := X) N n 0 := by
  refine ⟨0, ?_, ?_⟩
  · simp only [foxAlgebraicStageSourceFoxBoundary_apply, Pi.zero_apply, QuotientGroup.mk'_apply,
  MonoidAlgebra.of_apply, zero_mul, Finset.sum_const_zero]
  · exact (foxAlgebraicStageRelationBoundarySubmodule (X := X) N n).zero_mem

/-- Source-boundary primitives are closed under addition. -/
theorem foxAlgebraicStageSourceBoundaryPrimitive_add [Fintype X]
    {x y : foxAlgebraicStageSourceGroupAlgebra (X := X) N n}
    (hx : foxAlgebraicStageSourceBoundaryPrimitive (X := X) N n x)
    (hy : foxAlgebraicStageSourceBoundaryPrimitive (X := X) N n y) :
    foxAlgebraicStageSourceBoundaryPrimitive (X := X) N n (x + y) := by
  rcases hx with ⟨px, hpx, hpxrel⟩
  rcases hy with ⟨py, hpy, hpyrel⟩
  refine ⟨px + py, ?_, ?_⟩
  · rw [map_add, hpx, hpy]
  · rw [map_add]
    exact (foxAlgebraicStageRelationBoundarySubmodule (X := X) N n).add_mem hpxrel hpyrel

/-- Source-boundary primitives are closed under negation. -/
theorem foxAlgebraicStageSourceBoundaryPrimitive_neg [Fintype X]
    {x : foxAlgebraicStageSourceGroupAlgebra (X := X) N n}
    (hx : foxAlgebraicStageSourceBoundaryPrimitive (X := X) N n x) :
    foxAlgebraicStageSourceBoundaryPrimitive (X := X) N n (-x) := by
  rcases hx with ⟨p, hp, hprel⟩
  refine ⟨-p, ?_, ?_⟩
  · rw [map_neg, hp]
  · rw [map_neg]
    exact (foxAlgebraicStageRelationBoundarySubmodule (X := X) N n).neg_mem hprel

/-- Source-boundary primitives are closed under subtraction. -/
theorem foxAlgebraicStageSourceBoundaryPrimitive_sub [Fintype X]
    {x y : foxAlgebraicStageSourceGroupAlgebra (X := X) N n}
    (hx : foxAlgebraicStageSourceBoundaryPrimitive (X := X) N n x)
    (hy : foxAlgebraicStageSourceBoundaryPrimitive (X := X) N n y) :
    foxAlgebraicStageSourceBoundaryPrimitive (X := X) N n (x - y) := by
  simpa [sub_eq_add_neg] using
    foxAlgebraicStageSourceBoundaryPrimitive_add (X := X) N n hx
      (foxAlgebraicStageSourceBoundaryPrimitive_neg (X := X) N n hy)

/-- Source-boundary primitives are closed under left multiplication by source coefficients. -/
theorem foxAlgebraicStageSourceBoundaryPrimitive_smul [Fintype X]
    (a : foxAlgebraicStageSourceGroupAlgebra (X := X) N n)
    {x : foxAlgebraicStageSourceGroupAlgebra (X := X) N n}
    (hx : foxAlgebraicStageSourceBoundaryPrimitive (X := X) N n x) :
    foxAlgebraicStageSourceBoundaryPrimitive (X := X) N n (a • x) := by
  rcases hx with ⟨p, hp, hprel⟩
  refine ⟨a • p, ?_, ?_⟩
  · rw [map_smul, hp]
  · rw [foxAlgebraicStageCoordinateSourceToTarget_smul_source]
    exact (foxAlgebraicStageRelationBoundarySubmodule (X := X) N n).smul_mem
      (foxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N n a) hprel

/-- Source-boundary primitives form a left submodule of the source group algebra. -/
def foxAlgebraicStageSourceBoundaryPrimitiveSubmodule [Fintype X] :
    Submodule (foxAlgebraicStageSourceGroupAlgebra (X := X) N n)
      (foxAlgebraicStageSourceGroupAlgebra (X := X) N n) where
  carrier := {x | foxAlgebraicStageSourceBoundaryPrimitive (X := X) N n x}
  zero_mem' := foxAlgebraicStageSourceBoundaryPrimitive_zero (X := X) N n
  add_mem' := by
    intro x y hx hy
    exact foxAlgebraicStageSourceBoundaryPrimitive_add (X := X) N n hx hy
  smul_mem' := by
    intro a x hx
    exact foxAlgebraicStageSourceBoundaryPrimitive_smul (X := X) N n a hx

/--
The source-boundary primitive submodule has exactly the finite-stage source-boundary primitive
elements as its underlying set.
-/
@[simp]
theorem foxAlgebraicStageSourceBoundaryPrimitiveSubmodule_coe [Fintype X] :
    ((foxAlgebraicStageSourceBoundaryPrimitiveSubmodule (X := X) N n :
      Submodule (foxAlgebraicStageSourceGroupAlgebra (X := X) N n)
        (foxAlgebraicStageSourceGroupAlgebra (X := X) N n)) :
        Set (foxAlgebraicStageSourceGroupAlgebra (X := X) N n)) =
      {x | foxAlgebraicStageSourceBoundaryPrimitive (X := X) N n x} :=
  rfl

/-- The source primitive attached to a finite relation q. -/
def foxAlgebraicStageRelationAugmentationPrimitiveVector
    (q : foxAlgebraicStageRelationGroup (X := X) N n) :
    foxAlgebraicStageSourceCoordinateVector (X := X) N n :=
  foxAlgebraicStageSourceDerivativeVector (X := X) N n q.1

/-- The source boundary of the primitive vector for q is the augmentation generator \(q-1\). -/
theorem foxAlgebraicStageSourceFoxBoundary_relationAugmentationPrimitiveVector
    [Fintype X]
    (q : foxAlgebraicStageRelationGroup (X := X) N n) :
    foxAlgebraicStageSourceFoxBoundary (X := X) N n
        (foxAlgebraicStageRelationAugmentationPrimitiveVector (X := X) N n q) =
      foxAlgebraicStageRelationAugmentationGenerator (X := X) N n q := by
  rw [foxAlgebraicStageRelationAugmentationPrimitiveVector,
    foxAlgebraicStageSourceFoxBoundary_sourceDerivativeVector,
    foxAlgebraicStageRelationAugmentationGenerator]

/-- The target projection of the primitive vector for q is the finite relation boundary of q. -/
theorem foxAlgebraicStageCoordinateSourceToTarget_relationAugmentationPrimitiveVector
    (q : foxAlgebraicStageRelationGroup (X := X) N n) :
    foxAlgebraicStageCoordinateSourceToTarget (X := X) N n
        (foxAlgebraicStageRelationAugmentationPrimitiveVector (X := X) N n q) =
      foxAlgebraicStageRelationBoundaryAddMonoidHom (X := X) N n (Additive.ofMul q) := by
  rw [foxAlgebraicStageRelationAugmentationPrimitiveVector,
    foxAlgebraicStageCoordinateSourceToTarget_sourceDerivativeVector,
    foxAlgebraicStageRelationBoundaryAddMonoidHom_of]

/-- Relation augmentation generators have relation-compatible source Fox primitives. -/
theorem foxAlgebraicStageSourceBoundaryPrimitive_relationAugmentationGenerator
    [Fintype X]
    (q : foxAlgebraicStageRelationGroup (X := X) N n) :
    foxAlgebraicStageSourceBoundaryPrimitive (X := X) N n
      (foxAlgebraicStageRelationAugmentationGenerator (X := X) N n q) := by
  refine ⟨foxAlgebraicStageRelationAugmentationPrimitiveVector (X := X) N n q, ?_, ?_⟩
  · exact foxAlgebraicStageSourceFoxBoundary_relationAugmentationPrimitiveVector
      (X := X) N n q
  · rw [foxAlgebraicStageCoordinateSourceToTarget_relationAugmentationPrimitiveVector]
    exact foxAlgebraicStageRelationBoundaryRange_subset_relationBoundarySubmodule
      (X := X) N n
      ((mem_foxAlgebraicStageRelationBoundaryRange_iff
        (X := X) (N := N) (n := n)).2
        ⟨Additive.ofMul q, rfl⟩)


/--
Left multiplication of a relation augmentation generator by a source quotient basis element has
an explicit relation-compatible source primitive.
-/
theorem foxAlgebraicStageSourceBoundaryPrimitive_sourceBasis_mul_relationAugmentationGenerator
    [Fintype X]
    (s : FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
    (q : foxAlgebraicStageRelationGroup (X := X) N n) :
    foxAlgebraicStageSourceBoundaryPrimitive (X := X) N n
      (MonoidAlgebra.of (ModNCompletedCoeff n)
          (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) s *
        foxAlgebraicStageRelationAugmentationGenerator (X := X) N n q) := by
  simpa [Algebra.smul_def] using
    foxAlgebraicStageSourceBoundaryPrimitive_smul (X := X) N n
      (MonoidAlgebra.of (ModNCompletedCoeff n)
        (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) s)
      (foxAlgebraicStageSourceBoundaryPrimitive_relationAugmentationGenerator (X := X) N n q)

/--
Source primitive for the right basis multiple \((q - 1)s\); the primitive is
\(D_{\mathrm{src}}(q s) - D_{\mathrm{src}}(s)\).
-/
def foxAlgebraicStageRelationAugmentationRightBasisPrimitiveVector
    (q : foxAlgebraicStageRelationGroup (X := X) N n)
    (s : FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) :
    foxAlgebraicStageSourceCoordinateVector (X := X) N n :=
  foxAlgebraicStageSourceDerivativeVector (X := X) N n (q.1 * s) -
    foxAlgebraicStageSourceDerivativeVector (X := X) N n s

/-- The source boundary of \(D_{\mathrm{src}}(q s) - D_{\mathrm{src}}(s)\) is \((q - 1)s\). -/
theorem foxAlgebraicStageSourceFoxBoundary_relationAugmentationRightBasisPrimitiveVector
    [Fintype X]
    (q : foxAlgebraicStageRelationGroup (X := X) N n)
    (s : FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) :
    foxAlgebraicStageSourceFoxBoundary (X := X) N n
        (foxAlgebraicStageRelationAugmentationRightBasisPrimitiveVector (X := X) N n q s) =
      foxAlgebraicStageRelationAugmentationGenerator (X := X) N n q *
        MonoidAlgebra.of (ModNCompletedCoeff n)
          (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) s := by
  rw [foxAlgebraicStageRelationAugmentationRightBasisPrimitiveVector, map_sub,
    foxAlgebraicStageSourceFoxBoundary_sourceDerivativeVector,
    foxAlgebraicStageSourceFoxBoundary_sourceDerivativeVector,
    foxAlgebraicStageRelationAugmentationGenerator]
  rw [map_mul, sub_mul, one_mul]
  abel

/--
The target projection of \(D_{\mathrm{src}}(q s) - D_{\mathrm{src}}(s)\) is the relation
boundary of \(q\).
-/
theorem foxAlgebraicStageCoordinateSourceToTarget_relationAugmentationRightBasisPrimitiveVector
    (q : foxAlgebraicStageRelationGroup (X := X) N n)
    (s : FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) :
    foxAlgebraicStageCoordinateSourceToTarget (X := X) N n
        (foxAlgebraicStageRelationAugmentationRightBasisPrimitiveVector (X := X) N n q s) =
      foxAlgebraicStageRelationBoundaryAddMonoidHom (X := X) N n (Additive.ofMul q) := by
  rw [foxAlgebraicStageRelationAugmentationRightBasisPrimitiveVector, map_sub,
    foxAlgebraicStageCoordinateSourceToTarget_sourceDerivativeVector,
    foxAlgebraicStageCoordinateSourceToTarget_sourceDerivativeVector,
    foxAlgebraicStageRelationBoundaryAddMonoidHom_of,
    ScalarCrossedHom.map_mul
      (foxAlgebraicStageQuotientDerivativeVector (X := X) N n),
    foxAlgebraicStageQuotientCoefficient_relation_eq_one]
  simp only [one_smul, add_sub_cancel_right]

/--
Right multiplication of a relation augmentation generator by a source quotient basis element has
an explicit relation-compatible source primitive.
-/
theorem foxAlgebraicStageSourceBoundaryPrimitive_relationAugmentationGenerator_mul_sourceBasis
    [Fintype X]
    (q : foxAlgebraicStageRelationGroup (X := X) N n)
    (s : FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) :
    foxAlgebraicStageSourceBoundaryPrimitive (X := X) N n
      (foxAlgebraicStageRelationAugmentationGenerator (X := X) N n q *
        MonoidAlgebra.of (ModNCompletedCoeff n)
          (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) s) := by
  refine ⟨foxAlgebraicStageRelationAugmentationRightBasisPrimitiveVector (X := X) N n q s, ?_, ?_⟩
  · exact foxAlgebraicStageSourceFoxBoundary_relationAugmentationRightBasisPrimitiveVector
      (X := X) N n q s
  · rw [foxAlgebraicStageCoordinateSourceToTarget_relationAugmentationRightBasisPrimitiveVector]
    exact foxAlgebraicStageRelationBoundaryRange_subset_relationBoundarySubmodule
      (X := X) N n
      ((mem_foxAlgebraicStageRelationBoundaryRange_iff
        (X := X) (N := N) (n := n)).2
        ⟨Additive.ofMul q, rfl⟩)

/-- The left source-submodule generated by the relation augmentation generators. -/
def foxAlgebraicStageRelationAugmentationLeftSubmodule :
    Submodule (foxAlgebraicStageSourceGroupAlgebra (X := X) N n)
      (foxAlgebraicStageSourceGroupAlgebra (X := X) N n) :=
  Submodule.span (foxAlgebraicStageSourceGroupAlgebra (X := X) N n)
    (Set.range (foxAlgebraicStageRelationAugmentationGenerator (X := X) N n))

/-- The left relation-augmentation submodule is contained in the primitive submodule. -/
theorem foxAlgebraicStageRelationAugmentationLeftSubmodule_le_primitiveSubmodule
    [Fintype X] :
    foxAlgebraicStageRelationAugmentationLeftSubmodule (X := X) N n ≤
      foxAlgebraicStageSourceBoundaryPrimitiveSubmodule (X := X) N n := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨q, rfl⟩
  exact foxAlgebraicStageSourceBoundaryPrimitive_relationAugmentationGenerator
    (X := X) N n q

/--
Membership in the left relation-augmentation submodule gives a relation-compatible source
primitive.
-/
theorem foxAlgebraicStageSourceBoundaryPrimitive_of_mem_relationAugmentationLeftSubmodule
    [Fintype X]
    {x : foxAlgebraicStageSourceGroupAlgebra (X := X) N n}
    (hx : x ∈ foxAlgebraicStageRelationAugmentationLeftSubmodule (X := X) N n) :
    foxAlgebraicStageSourceBoundaryPrimitive (X := X) N n x :=
  foxAlgebraicStageRelationAugmentationLeftSubmodule_le_primitiveSubmodule (X := X) N n hx

end

end FoxDifferential
