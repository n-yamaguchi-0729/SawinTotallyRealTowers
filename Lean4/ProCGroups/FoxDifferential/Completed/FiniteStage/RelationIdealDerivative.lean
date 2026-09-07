import ProCGroups.FoxDifferential.Completed.FiniteStage.SourceBoundary

set_option autoImplicit false

/-!
# Fox differential: completed — finite stage — relation ideal derivative

The principal declarations in this module are:

- `foxAlgebraicStageGroupAlgebraDerivativeVector`
  The vector of target-valued finite Fox derivatives of a source group-algebra element.
- `foxAlgebraicStageGroupAlgebraDerivativeVector_apply`
  The finite-stage group-algebra derivative vector is evaluated coordinatewise in the target finite
  quotient.
- `foxAlgebraicStageGroupAlgebraDerivativeVector_zero`
  The finite-stage group-algebra derivative vector sends \(0\) to \(0\).
- `foxAlgebraicStageGroupAlgebraDerivativeVector_add`
  The finite-stage group-algebra derivative vector preserves addition.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u

variable {X : Type u} [DecidableEq X]
variable (N : Subgroup (FreeGroup X)) [N.Normal] (n : ℕ)

/-- The vector of target-valued finite Fox derivatives of a source group-algebra element. -/
def foxAlgebraicStageGroupAlgebraDerivativeVector
    (x : foxAlgebraicStageSourceGroupAlgebra (X := X) N n) :
    foxAlgebraicStageCoordinateVector (X := X) N n :=
  fun i => foxAlgebraicStageGroupAlgebraDerivative (X := X) N n i x

/--
The finite-stage group-algebra derivative vector is evaluated coordinatewise in the target
finite quotient.
-/
@[simp]
theorem foxAlgebraicStageGroupAlgebraDerivativeVector_apply
    (x : foxAlgebraicStageSourceGroupAlgebra (X := X) N n) (i : X) :
    foxAlgebraicStageGroupAlgebraDerivativeVector (X := X) N n x i =
      foxAlgebraicStageGroupAlgebraDerivative (X := X) N n i x :=
  rfl

/-- The finite-stage group-algebra derivative vector sends \(0\) to \(0\). -/
@[simp]
theorem foxAlgebraicStageGroupAlgebraDerivativeVector_zero :
    foxAlgebraicStageGroupAlgebraDerivativeVector (X := X) N n 0 = 0 := by
  funext i
  simp only [foxAlgebraicStageGroupAlgebraDerivativeVector_apply, map_zero, Pi.zero_apply]

/-- The finite-stage group-algebra derivative vector preserves addition. -/
@[simp]
theorem foxAlgebraicStageGroupAlgebraDerivativeVector_add
    (x y : foxAlgebraicStageSourceGroupAlgebra (X := X) N n) :
    foxAlgebraicStageGroupAlgebraDerivativeVector (X := X) N n (x + y) =
      foxAlgebraicStageGroupAlgebraDerivativeVector (X := X) N n x +
        foxAlgebraicStageGroupAlgebraDerivativeVector (X := X) N n y := by
  funext i
  simp only [foxAlgebraicStageGroupAlgebraDerivativeVector, map_add, Pi.add_apply]

/-- The finite-stage group-algebra derivative vector preserves negation. -/
@[simp]
theorem foxAlgebraicStageGroupAlgebraDerivativeVector_neg
    (x : foxAlgebraicStageSourceGroupAlgebra (X := X) N n) :
    foxAlgebraicStageGroupAlgebraDerivativeVector (X := X) N n (-x) =
      -foxAlgebraicStageGroupAlgebraDerivativeVector (X := X) N n x := by
  funext i
  simp only [foxAlgebraicStageGroupAlgebraDerivativeVector_apply, map_neg, Pi.neg_apply]

/-- The finite-stage group-algebra derivative vector preserves subtraction. -/
@[simp]
theorem foxAlgebraicStageGroupAlgebraDerivativeVector_sub
    (x y : foxAlgebraicStageSourceGroupAlgebra (X := X) N n) :
    foxAlgebraicStageGroupAlgebraDerivativeVector (X := X) N n (x - y) =
      foxAlgebraicStageGroupAlgebraDerivativeVector (X := X) N n x -
        foxAlgebraicStageGroupAlgebraDerivativeVector (X := X) N n y := by
  funext i
  simp only [foxAlgebraicStageGroupAlgebraDerivativeVector, map_sub, Pi.sub_apply]

/-- Product rule for the vector of target-valued derivatives. -/
theorem foxAlgebraicStageGroupAlgebraDerivativeVector_mul
    (x y : foxAlgebraicStageSourceGroupAlgebra (X := X) N n) :
    foxAlgebraicStageGroupAlgebraDerivativeVector (X := X) N n (x * y) =
      (algebraMap (ModNCompletedCoeff n)
        (foxAlgebraicStageTargetGroupAlgebra (X := X) N n)
        (foxCommutatorPowerSourceGroupAlgebraAugmentation
          (F := FreeGroup X) N n y)) •
        foxAlgebraicStageGroupAlgebraDerivativeVector (X := X) N n x +
    foxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N n x •
        foxAlgebraicStageGroupAlgebraDerivativeVector (X := X) N n y := by
  funext i
  simp only [foxAlgebraicStageGroupAlgebraDerivativeVector,
      foxAlgebraicStageGroupAlgebraDerivative_mul,
  Algebra.smul_def, MonoidAlgebra.coe_algebraMap, Algebra.algebraMap_self, RingHom.coe_id,
      Function.comp_apply, id_eq,
  Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/--
The derivative vector of a relation augmentation generator is the corresponding relation
boundary vector.
-/
theorem foxAlgebraicStageGroupAlgebraDerivativeVector_relationAugmentationGenerator
    (q : foxAlgebraicStageRelationGroup (X := X) N n) :
    foxAlgebraicStageGroupAlgebraDerivativeVector (X := X) N n
        (foxAlgebraicStageRelationAugmentationGenerator (X := X) N n q) =
      foxAlgebraicStageRelationBoundaryAddMonoidHom (X := X) N n (Additive.ofMul q) := by
  funext i
  rw [foxAlgebraicStageGroupAlgebraDerivativeVector_apply,
    foxAlgebraicStageRelationBoundaryAddMonoidHom_of]
  rw [foxAlgebraicStageRelationAugmentationGenerator, map_sub,
    foxAlgebraicStageGroupAlgebraDerivative_of_quotient,
    foxAlgebraicStageGroupAlgebraDerivative_one, sub_zero]
  rfl

omit [DecidableEq X] in
/-- Relation augmentation generators have zero source augmentation. -/
theorem foxAlgebraicStageRelationAugmentationGenerator_sourceAugmentation_eq_zero
    (q : foxAlgebraicStageRelationGroup (X := X) N n) :
    foxCommutatorPowerSourceGroupAlgebraAugmentation
        (F := FreeGroup X) N n
        (foxAlgebraicStageRelationAugmentationGenerator (X := X) N n q) = 0 := by
  rw [foxAlgebraicStageRelationAugmentationGenerator, map_sub, map_one,
    foxCommutatorPowerSourceGroupAlgebraAugmentation_of_quotient]
  simp only [sub_self]

omit [DecidableEq X] in
/-- Relation augmentation generators have zero target image. -/
theorem foxAlgebraicStageRelationAugmentationGenerator_groupAlgebraMap_eq_zero
    (q : foxAlgebraicStageRelationGroup (X := X) N n) :
    foxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N n
        (foxAlgebraicStageRelationAugmentationGenerator (X := X) N n q) = 0 := by
  exact
    (mem_foxAlgebraicStageGroupAlgebraMapKernelIdeal (X := X) (N := N) (n := n)).1
      (foxAlgebraicStageRelationAugmentationGenerator_mem_groupAlgebraMapKernel
        (X := X) N n q)

/--
The derivative vector of every element of the finite relation augmentation ideal lies in the
relation-boundary submodule; such elements have zero target image and zero augmentation.
-/
theorem foxAlgebraicStageGADeriv_mem_relBoundarySubmodule_of_mem_relAugIdeal
    {x : foxAlgebraicStageSourceGroupAlgebra (X := X) N n}
    (hx : x ∈ foxAlgebraicStageRelationAugmentationIdeal (X := X) N n) :
    foxAlgebraicStageGroupAlgebraDerivativeVector (X := X) N n x ∈
      foxAlgebraicStageRelationBoundarySubmodule (X := X) N n := by
  let P : foxAlgebraicStageSourceGroupAlgebra (X := X) N n → Prop := fun z =>
    foxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N n z = 0 ∧
      foxCommutatorPowerSourceGroupAlgebraAugmentation (F := FreeGroup X) N n z = 0 ∧
        foxAlgebraicStageGroupAlgebraDerivativeVector (X := X) N n z ∈
          foxAlgebraicStageRelationBoundarySubmodule (X := X) N n
  have hP : P x := by
    change x ∈ Submodule.span (foxAlgebraicStageSourceGroupAlgebra (X := X) N n)
        (Set.range (foxAlgebraicStageRelationAugmentationGenerator (X := X) N n)) at hx
    refine Submodule.span_induction (p := fun z _ => P z) ?hgen ?hzero ?hadd ?hsmul hx
    · rintro z ⟨q, rfl⟩
      refine ⟨?_, ?_, ?_⟩
      · exact foxAlgebraicStageRelationAugmentationGenerator_groupAlgebraMap_eq_zero
          (X := X) N n q
      · exact foxAlgebraicStageRelationAugmentationGenerator_sourceAugmentation_eq_zero
          (X := X) N n q
      · rw [foxAlgebraicStageGroupAlgebraDerivativeVector_relationAugmentationGenerator]
        exact foxAlgebraicStageRelationBoundaryAddMonoidHom_mem_relationBoundarySubmodule
          (X := X) N n (Additive.ofMul q)
    · refine ⟨?_, ?_, ?_⟩
      · simp only [map_zero]
      · simp only [map_zero]
      · simp only [foxAlgebraicStageGroupAlgebraDerivativeVector_zero, zero_mem]
    · intro a b _ _ ha hb
      rcases ha with ⟨ha_map, ha_aug, ha_der⟩
      rcases hb with ⟨hb_map, hb_aug, hb_der⟩
      refine ⟨?_, ?_, ?_⟩
      · rw [map_add, ha_map, hb_map, add_zero]
      · rw [map_add, ha_aug, hb_aug, add_zero]
      · rw [foxAlgebraicStageGroupAlgebraDerivativeVector_add]
        exact (foxAlgebraicStageRelationBoundarySubmodule (X := X) N n).add_mem ha_der hb_der
    · intro a z _ hz
      rcases hz with ⟨hz_map, hz_aug, hz_der⟩
      refine ⟨?_, ?_, ?_⟩
      · change foxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N n (a * z) = 0
        rw [RingHom.map_mul, hz_map, mul_zero]
      · change foxCommutatorPowerSourceGroupAlgebraAugmentation
            (F := FreeGroup X) N n (a * z) = 0
        rw [map_mul, hz_aug, mul_zero]
      · have hderivative :
            foxAlgebraicStageGroupAlgebraDerivativeVector (X := X) N n (a * z) =
              foxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N n a •
                foxAlgebraicStageGroupAlgebraDerivativeVector (X := X) N n z := by
          rw [foxAlgebraicStageGroupAlgebraDerivativeVector_mul]
          rw [hz_aug]
          rw [map_zero, zero_smul, zero_add]
        change foxAlgebraicStageGroupAlgebraDerivativeVector (X := X) N n (a * z) ∈
          foxAlgebraicStageRelationBoundarySubmodule (X := X) N n
        rw [hderivative]
        exact (foxAlgebraicStageRelationBoundarySubmodule (X := X) N n).smul_mem _ hz_der
  exact hP.2.2

/-- Differentiating the source Fox boundary recovers the coordinatewise source-to-target image. -/
theorem foxAlgebraicStageGroupAlgebraDerivativeVector_sourceFoxBoundary
    [Fintype X]
    (a : foxAlgebraicStageSourceCoordinateVector (X := X) N n) :
    foxAlgebraicStageGroupAlgebraDerivativeVector (X := X) N n
        (foxAlgebraicStageSourceFoxBoundary (X := X) N n a) =
      foxAlgebraicStageCoordinateSourceToTarget (X := X) N n a := by
  funext j
  rw [foxAlgebraicStageGroupAlgebraDerivativeVector_apply,
    foxAlgebraicStageSourceFoxBoundary_apply,
    foxAlgebraicStageCoordinateSourceToTarget_apply]
  have hgen_aug (i : X) :
      foxCommutatorPowerSourceGroupAlgebraAugmentation
          (F := FreeGroup X) N n
          (MonoidAlgebra.of (ModNCompletedCoeff n)
              (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
              (QuotientGroup.mk'
                (foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
                (FreeGroup.of i)) - 1) = 0 := by
    rw [map_sub, map_one, foxCommutatorPowerSourceGroupAlgebraAugmentation_of_quotient]
    simp only [sub_self]
  have hgen_derivative (i : X) :
      foxAlgebraicStageGroupAlgebraDerivative (X := X) N n j
          (MonoidAlgebra.of (ModNCompletedCoeff n)
              (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
              (QuotientGroup.mk'
                (foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
                (FreeGroup.of i)) - 1) =
        (Pi.single i (1 : foxAlgebraicStageTargetGroupAlgebra (X := X) N n) :
          X → foxAlgebraicStageTargetGroupAlgebra (X := X) N n) j := by
    rw [map_sub, foxAlgebraicStageGroupAlgebraDerivative_of,
      foxAlgebraicStageGroupAlgebraDerivative_one, sub_zero]
    simp only [foxAlgebraicStageDerivative, foxAlgebraicStageDerivativeVector_of]
  calc
    foxAlgebraicStageGroupAlgebraDerivative (X := X) N n j
        (∑ i : X,
          a i *
            (MonoidAlgebra.of (ModNCompletedCoeff n)
              (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
              (QuotientGroup.mk'
                (foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
                (FreeGroup.of i)) - 1))
        =
      ∑ i : X,
        foxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N n (a i) *
          ((Pi.single i (1 : foxAlgebraicStageTargetGroupAlgebra (X := X) N n) :
            X → foxAlgebraicStageTargetGroupAlgebra (X := X) N n) j) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [foxAlgebraicStageGroupAlgebraDerivative_mul]
        rw [hgen_aug i, zero_smul, zero_add, hgen_derivative i]
    _ = foxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N n (a j) := by
        rw [Finset.sum_eq_single j]
        · simp only [Pi.single_eq_same, mul_one]
        · intro i _ hij
          rw [Pi.single_eq_of_ne hij.symm]
          simp only [mul_zero]
        · simp only [Finset.mem_univ, not_true_eq_false, Pi.single_eq_same, mul_one,
            IsEmpty.forall_iff]

/--
The source-boundary relation-ideal reduction is a theorem: if the source boundary of a lift is
in the relation ideal, differentiating that boundary gives the desired relation-boundary vector.
-/
theorem foxAlgebraicStageSourceBoundaryRelationIdealReduction_of_relationIdeal_derivatives
    [Fintype X] :
    foxAlgebraicStageSourceBoundaryRelationIdealReduction (X := X) N n := by
  intro a ha
  have hderivative :=
    foxAlgebraicStageGADeriv_mem_relBoundarySubmodule_of_mem_relAugIdeal
      (X := X) N n (x := foxAlgebraicStageSourceFoxBoundary (X := X) N n a) ha
  rw [foxAlgebraicStageGroupAlgebraDerivativeVector_sourceFoxBoundary (X := X) N n a] at hderivative
  exact hderivative

/--
Differentiation of the relation augmentation ideal gives finite-stage relation-boundary module
exactness.
-/
theorem foxAlgebraicStageRelationBoundaryModuleExact_of_relationIdeal_derivatives
    [Fintype X] :
    foxAlgebraicStageRelationBoundaryModuleExact (X := X) N n :=
  foxAlgebraicStageRelationBoundaryModuleExact_of_sourceBoundaryRelReduction
    (X := X) N n
    (foxAlgebraicStageSourceBoundaryRelationIdealReduction_of_relationIdeal_derivatives
      (X := X) N n)

/-- The relation-ideal derivative identity gives finite-stage coordinate coverage. -/
theorem foxAlgebraicStageBoundaryCyclesCoveredBySourceKernel_of_relationIdeal_derivatives
    [Fintype X] :
    foxAlgebraicStageBoundaryCyclesCoveredBySourceKernel (X := X) N n :=
  foxAlgebraicStageBoundaryCyclesCoveredBySourceKernel_of_relationBoundaryModuleExact
    (X := X) N n
    (foxAlgebraicStageRelationBoundaryModuleExact_of_relationIdeal_derivatives (X := X) N n)

/-- The relation-ideal derivative identity gives finite-stage semidirect coverage. -/
theorem foxAlgebraicStageSemiBoundaryCyclesCovered_of_relDeriv
    [Fintype X] :
    foxAlgebraicStageSemidirectBoundaryCyclesCoveredBySourceKernel (X := X) N n :=
  (foxAlgebraicStageSemidirectBoundaryCyclesCoveredBySourceKernel_iff
    (X := X) (N := N) (n := n)).2
    (foxAlgebraicStageBoundaryCyclesCoveredBySourceKernel_of_relationIdeal_derivatives
      (X := X) N n)

end

end FoxDifferential
