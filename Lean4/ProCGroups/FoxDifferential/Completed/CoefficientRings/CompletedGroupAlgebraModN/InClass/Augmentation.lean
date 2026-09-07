import ProCGroups.FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraModN.InClass.StageCoeffMap

set_option autoImplicit false

/-!
# Fox differential: coefficient rings — mod-\(n\) completed group algebra — in class — augmentation

The principal declarations in this module are:

- `modNCompletedGroupAlgebraStageAugmentationInClass`
  The augmentation on one class-restricted residue-coefficient finite stage.
- `modNCompletedGroupAlgebraStageAugmentationInClass_of`
  The class-indexed finite-stage \(n\)-modular augmentation sends every group-like basis element to
  \(1\).
- `modNCompletedGroupAlgebraStageAugmentationInClass_single`
  The class-indexed finite-stage \(n\)-modular augmentation sends a singleton basis element to its
  coefficient.
- `modNCompletedGroupAlgebraStageAugmentationInClass_compatible`
  Class-indexed finite-stage \(n\)-modular augmentations are compatible with group-quotient
  transition maps.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u

variable (n : ℕ) [Fact (0 < n)]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The augmentation on one class-restricted residue-coefficient finite stage. -/
def modNCompletedGroupAlgebraStageAugmentationInClass
    (C : ProCGroups.FiniteGroupClass.{u}) (U : CompletedGroupAlgebraIndexInClass G C) :
    ModNCompletedGroupAlgebraStageInClass n G C U →+* ModNCompletedCoeff n :=
  MonoidAlgebra.lift (ModNCompletedCoeff n) (ModNCompletedCoeff n)
    (CompletedGroupAlgebraQuotientInClass G C U)
    (1 : CompletedGroupAlgebraQuotientInClass G C U →* ModNCompletedCoeff n)

omit [Fact (0 < n)] in
/--
The class-indexed finite-stage \(n\)-modular augmentation sends every group-like basis element
to \(1\).
-/
@[simp]
theorem modNCompletedGroupAlgebraStageAugmentationInClass_of
    (C : ProCGroups.FiniteGroupClass.{u}) (U : CompletedGroupAlgebraIndexInClass G C)
    (q : CompletedGroupAlgebraQuotientInClass G C U) :
    modNCompletedGroupAlgebraStageAugmentationInClass n G C U
        (MonoidAlgebra.of (ModNCompletedCoeff n) _ q) = 1 := by
  change
    MonoidAlgebra.lift (ModNCompletedCoeff n) (ModNCompletedCoeff n)
        (CompletedGroupAlgebraQuotientInClass G C U)
        (1 : CompletedGroupAlgebraQuotientInClass G C U →*
          ModNCompletedCoeff n)
        (MonoidAlgebra.single q 1) = 1
  rw [MonoidAlgebra.lift_single, MonoidHom.one_apply, one_smul]

omit [Fact (0 < n)] in
/--
The class-indexed finite-stage \(n\)-modular augmentation sends a singleton basis element to its
coefficient.
-/
@[simp]
theorem modNCompletedGroupAlgebraStageAugmentationInClass_single
    (C : ProCGroups.FiniteGroupClass.{u}) (U : CompletedGroupAlgebraIndexInClass G C)
    (q : CompletedGroupAlgebraQuotientInClass G C U) (a : ModNCompletedCoeff n) :
    modNCompletedGroupAlgebraStageAugmentationInClass n G C U
        (MonoidAlgebra.single q a) = a := by
  change
    MonoidAlgebra.lift (ModNCompletedCoeff n) (ModNCompletedCoeff n)
        (CompletedGroupAlgebraQuotientInClass G C U)
        (1 : CompletedGroupAlgebraQuotientInClass G C U →*
          ModNCompletedCoeff n)
        (MonoidAlgebra.single q a) = a
  rw [MonoidAlgebra.lift_single, MonoidHom.one_apply, smul_eq_mul, mul_one]

omit [Fact (0 < n)] in
/--
Class-indexed finite-stage \(n\)-modular augmentations are compatible with group-quotient
transition maps.
-/
@[simp 900]
theorem modNCompletedGroupAlgebraStageAugmentationInClass_compatible
    (C : ProCGroups.FiniteGroupClass.{u})
    {U V : CompletedGroupAlgebraIndexInClass G C} (hUV : U ≤ V) :
    (modNCompletedGroupAlgebraStageAugmentationInClass n G C U).comp
        (modNCompletedGroupAlgebraTransitionInClass n G C hUV) =
      modNCompletedGroupAlgebraStageAugmentationInClass n G C V := by
  apply RingHom.ext
  intro x
  induction x using MonoidAlgebra.induction_linear with
  | zero =>
      simp only [map_zero]
  | add x y hx hy =>
      simp only [map_add, hx, hy]
  | single q a =>
      erw [RingHom.comp_apply,
        modNCompletedGroupAlgebraTransitionInClass_single]
      unfold modNCompletedGroupAlgebraStageAugmentationInClass
      erw [MonoidAlgebra.lift_single, MonoidAlgebra.lift_single]
      change a • (1 : ModNCompletedCoeff n) = a • (1 : ModNCompletedCoeff n)
      rfl

omit [Fact (0 < n)] in
/--
Composing the class-indexed finite-stage \(n\)-modular augmentation with the dense stage map
gives the ordinary \(n\)-modular group-algebra augmentation.
-/
@[simp 900]
theorem modNCompletedGroupAlgebraStageAugmentationInClass_comp_stageMap
    (C : ProCGroups.FiniteGroupClass.{u}) (U : CompletedGroupAlgebraIndexInClass G C) :
    (modNCompletedGroupAlgebraStageAugmentationInClass n G C U).comp
        (modNCompletedGroupAlgebraStageMapInClass n G C U) =
      MonoidAlgebra.lift (ModNCompletedCoeff n) (ModNCompletedCoeff n) G
        (1 : G →* ModNCompletedCoeff n) := by
  apply RingHom.ext
  intro x
  induction x using MonoidAlgebra.induction_linear with
  | zero =>
      simp only [map_zero]
  | add x y hx hy =>
      simp only [map_add, hx, hy]
  | single g a =>
      erw [RingHom.comp_apply]
      unfold modNCompletedGroupAlgebraStageMapInClass
      erw [MonoidAlgebra.mapDomainRingHom_apply,
        MonoidAlgebra.mapDomain_single]
      unfold modNCompletedGroupAlgebraStageAugmentationInClass
      erw [MonoidAlgebra.lift_single, MonoidAlgebra.lift_single]
      change a * (1 : ModNCompletedCoeff n) = a * (1 : ModNCompletedCoeff n)
      rfl

omit [Fact (0 < n)] in
/--
Stage augmentations commute with coefficient reduction on class-restricted finite quotient
stages.
-/
@[simp 900]
theorem modNCompletedGroupAlgebraStageAugmentationInClass_comp_stageCoeffMap
    (C : ProCGroups.FiniteGroupClass.{u}) (U : CompletedGroupAlgebraIndexInClass G C)
    {m : ℕ} (hnm : n ∣ m) :
    (modNCompletedGroupAlgebraStageAugmentationInClass n G C U).comp
        (modNCompletedGroupAlgebraStageCoeffMapInClass
          (n := n) (m := m) (G := G) C U hnm) =
      (modNCompletedCoeffMap (n := n) (m := m) hnm).comp
        (modNCompletedGroupAlgebraStageAugmentationInClass m G C U) := by
  apply RingHom.ext
  intro x
  induction x using MonoidAlgebra.induction_linear with
  | zero =>
      simp only [map_zero]
  | add x y hx hy =>
      simp only [map_add, hx, hy]
  | single q a =>
      rw [RingHom.comp_apply, RingHom.comp_apply,
        modNCompletedGroupAlgebraStageCoeffMapInClass_single_apply,
        modNCompletedGroupAlgebraStageAugmentationInClass_single,
        modNCompletedGroupAlgebraStageAugmentationInClass_single]

end

end FoxDifferential
