/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.Continuous.Universal.NaturalTopology
import Nyll.ProCGroups.FoxDifferential.Completed.ProCIntegerCoefficients.AugmentationIdeal.Kernel

/-!
# Fox differential: completed — continuous — universal — augmentation quotient

The principal declarations in this module are:

- `zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard`
  The algebraic product \(I(\ker \psi)I(G)\) inside the algebraic standard source augmentation
  ideal.
- `zcCompletedGroupAlgebraStandardAugmentationIdealProjection`
  Projection of the algebraic standard augmentation ideal to a finite augmentation stage.
- `zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard_generator_mem`
  A generator \((n-1)s\) lies in the algebraic product \(I(\ker \psi)I(G)\).
- `zcCompletedGroupAlgebraStandardAugmentationIdealProjection_val`
  The value of the augmentation-ideal projection is the value of the corresponding finite-stage
  projection.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.ProC

universe u

section KernelAugmentationQuotient

variable (C : ProCGroups.FiniteGroupClass.{u})
variable {G H : Type u}
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/--
The algebraic product \(I(\ker \psi)I(G)\) inside the algebraic standard source augmentation
ideal.
-/
def zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard
    (psi : ContinuousMonoidHom G H) :
    Submodule (ZCCompletedGroupAlgebra C G)
      (zcCompletedGroupAlgebraStandardAugmentationIdeal C G) :=
  Submodule.span (ZCCompletedGroupAlgebra C G)
    (Set.range fun p :
      ProfiniteKernelSubgroup psi × zcCompletedGroupAlgebraStandardAugmentationIdeal C G =>
        (zcGroupLike C G p.1.1 - 1) • p.2)

omit [IsTopologicalGroup H] in
/-- A generator \((n-1)s\) lies in the algebraic product \(I(\ker \psi)I(G)\). -/
theorem zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard_generator_mem
    (psi : ContinuousMonoidHom G H) (n : ProfiniteKernelSubgroup psi)
    (s : zcCompletedGroupAlgebraStandardAugmentationIdeal C G) :
    (zcGroupLike C G n.1 - 1) • s ∈
      zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi :=
  Submodule.subset_span (Set.mem_range_self (n, s))

/-- Projection of the algebraic standard augmentation ideal to a finite augmentation stage. -/
def zcCompletedGroupAlgebraStandardAugmentationIdealProjection
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (i : ZCCompletedGroupAlgebraIndex C G) :
    zcCompletedGroupAlgebraStandardAugmentationIdeal C G →
      zcCompletedGroupAlgebraStageAugmentationIdeal C G i := by
  intro x
  let xAug : ZCCompletedGroupAlgebraAugmentationIdeal C G :=
    ⟨x, zcCompletedGroupAlgebraStandardAugmentationIdeal_le_augmentationIdeal C G x.2⟩
  exact zcCompletedGroupAlgebraAugmentationIdealProjection C G i xAug

/--
The value of the augmentation-ideal projection is the value of the corresponding finite-stage
projection.
-/
@[simp]
theorem zcCompletedGroupAlgebraStandardAugmentationIdealProjection_val
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (i : ZCCompletedGroupAlgebraIndex C G)
    (x : zcCompletedGroupAlgebraStandardAugmentationIdeal C G) :
    ((zcCompletedGroupAlgebraStandardAugmentationIdealProjection C i x :
      ZCCompletedGroupAlgebraStage C G i)) =
      zcCompletedGroupAlgebraProjection C G i x :=
  rfl

/-- The standard augmentation-ideal projection is continuous. -/
theorem continuous_zcCompletedGroupAlgebraStandardAugmentationIdealProjection
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (i : ZCCompletedGroupAlgebraIndex C G) :
    Continuous (zcCompletedGroupAlgebraStandardAugmentationIdealProjection C i) := by
  have hval : Continuous (fun x : zcCompletedGroupAlgebraStandardAugmentationIdeal C G =>
      zcCompletedGroupAlgebraProjection C G i (x : ZCCompletedGroupAlgebra C G)) :=
    (continuous_zcCompletedGroupAlgebraProjection C G i).comp continuous_subtype_val
  exact Continuous.subtype_mk hval
    (fun x => (zcCompletedGroupAlgebraStandardAugmentationIdealProjection C i x).2)

/--
On a finite coefficient stage, the identity crossed-differential boundary is a left inverse to
the additive lift from the finite augmentation ideal.
-/
theorem zcCompletedGAStageAugmentationIdeal_identityBoundary_monoidAlgebraToIdentity
    (i : ZCCompletedGroupAlgebraIndex C G)
    (x : zcCompletedGroupAlgebraStageAugmentationIdeal C G i) :
    identityCrossedDifferentialBoundary
        (monoidAlgebraToIdentityCrossedDifferentialModule
          (S := ModNCompletedCoeff i.1.modulus)
          (G := CompletedGroupAlgebraQuotientInClass G C i.2)
          (x : ZCCompletedGroupAlgebraStage C G i)) =
      (x : ZCCompletedGroupAlgebraStage C G i) := by
  let : Fact (0 < i.1.modulus) := ⟨i.1.positive⟩
  have hxaug :
      (MonoidAlgebra.lift
          (ModNCompletedCoeff i.1.modulus)
          (ModNCompletedCoeff i.1.modulus)
          (CompletedGroupAlgebraQuotientInClass G C i.2)
          (1 : CompletedGroupAlgebraQuotientInClass G C i.2 →* ModNCompletedCoeff i.1.modulus))
          (x : ZCCompletedGroupAlgebraStage C G i) = 0 := by
    simpa [modNCompletedGroupAlgebraStageAugmentationInClass] using
      (mem_zcCompletedGroupAlgebraStageAugmentationIdeal_iff
        (C := C) (H := G) (i := i) (x := (x : ZCCompletedGroupAlgebraStage C G i))).1 x.2
  exact
    idCrossedDiffBoundary_monoidAlgebraToModule_of_augmentation_eq_zero
      (S := ModNCompletedCoeff i.1.modulus)
      (G := CompletedGroupAlgebraQuotientInClass G C i.2)
      (a := (x : ZCCompletedGroupAlgebraStage C G i))
      hxaug

/-- The finite-stage augmentation-ideal projection is compatible with zero. -/
@[simp]
theorem zcCompletedGroupAlgebraStandardAugmentationIdealProjection_zero
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (i : ZCCompletedGroupAlgebraIndex C G) :
    zcCompletedGroupAlgebraStandardAugmentationIdealProjection C i
        (0 : zcCompletedGroupAlgebraStandardAugmentationIdeal C G) = 0 := by
  apply Subtype.ext
  simp only [zcCompletedGroupAlgebraStandardAugmentationIdealProjection_val, ZeroMemClass.coe_zero,
  zcCompletedGroupAlgebraProjection_zero]

/-- The finite-stage augmentation-ideal projection is compatible with addition. -/
@[simp]
theorem zcCompletedGroupAlgebraStandardAugmentationIdealProjection_add
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (i : ZCCompletedGroupAlgebraIndex C G)
    (x y : zcCompletedGroupAlgebraStandardAugmentationIdeal C G) :
    zcCompletedGroupAlgebraStandardAugmentationIdealProjection C i (x + y) =
      zcCompletedGroupAlgebraStandardAugmentationIdealProjection C i x +
        zcCompletedGroupAlgebraStandardAugmentationIdealProjection C i y := by
  apply Subtype.ext
  simp only [zcCompletedGroupAlgebraStandardAugmentationIdealProjection_val, Submodule.coe_add,
  zcCompletedGroupAlgebraProjection_add]

/-- The finite-stage augmentation-ideal projection is compatible with scalar multiplication. -/
@[simp]
theorem zcCompletedGroupAlgebraStandardAugmentationIdealProjection_smul
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (i : ZCCompletedGroupAlgebraIndex C G)
    (a : ZCCompletedGroupAlgebra C G)
    (x : zcCompletedGroupAlgebraStandardAugmentationIdeal C G) :
    zcCompletedGroupAlgebraStandardAugmentationIdealProjection C i (a • x) =
      zcCompletedGroupAlgebraProjection C G i a •
        zcCompletedGroupAlgebraStandardAugmentationIdealProjection C i x := by
  apply Subtype.ext
  change zcCompletedGroupAlgebraProjection C G i (a * (x : ZCCompletedGroupAlgebra C G)) =
    zcCompletedGroupAlgebraProjection C G i a *
      zcCompletedGroupAlgebraProjection C G i (x : ZCCompletedGroupAlgebra C G)
  rw [zcCompletedGroupAlgebraProjection_mul]

/--
The finite-stage projection of the standard augmentation ideal, as a semilinear map over the
completed group-algebra projection.
-/
def zcCompletedGroupAlgebraStandardAugmentationIdealProjectionLinear
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (i : ZCCompletedGroupAlgebraIndex C G) :
    zcCompletedGroupAlgebraStandardAugmentationIdeal C G →ₛₗ[
      zcCompletedGroupAlgebraProjectionRingHom C G i]
      zcCompletedGroupAlgebraStageAugmentationIdeal C G i where
  toFun := zcCompletedGroupAlgebraStandardAugmentationIdealProjection C i
  map_add' := by
    intro x y
    exact zcCompletedGroupAlgebraStandardAugmentationIdealProjection_add C i x y
  map_smul' := by
    intro a x
    exact zcCompletedGroupAlgebraStandardAugmentationIdealProjection_smul C i a x

/--
The linear finite-stage projection of the standard completed augmentation ideal has the same value
as its underlying projection.
-/
@[simp]
theorem zcCompletedGroupAlgebraStandardAugmentationIdealProjectionLinear_apply
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (i : ZCCompletedGroupAlgebraIndex C G)
    (x : zcCompletedGroupAlgebraStandardAugmentationIdeal C G) :
    zcCompletedGroupAlgebraStandardAugmentationIdealProjectionLinear C i x =
      zcCompletedGroupAlgebraStandardAugmentationIdealProjection C i x :=
  rfl

/-- The finite-stage augmentation-ideal projection is compatible with subtraction. -/
@[simp]
theorem zcCompletedGroupAlgebraStandardAugmentationIdealProjection_sub
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (i : ZCCompletedGroupAlgebraIndex C G)
    (x y : zcCompletedGroupAlgebraStandardAugmentationIdeal C G) :
    zcCompletedGroupAlgebraStandardAugmentationIdealProjection C i (x - y) =
      zcCompletedGroupAlgebraStandardAugmentationIdealProjection C i x -
        zcCompletedGroupAlgebraStandardAugmentationIdealProjection C i y := by
  simpa using
    map_sub (zcCompletedGroupAlgebraStandardAugmentationIdealProjectionLinear C i) x y

/-- The product of all finite-stage projections of the standard completed augmentation ideal. -/
def zcCompletedGroupAlgebraStandardAugmentationIdealProjectionProduct
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C] :
    zcCompletedGroupAlgebraStandardAugmentationIdeal C G →
      ∀ i : ZCCompletedGroupAlgebraIndex C G,
        zcCompletedGroupAlgebraStageAugmentationIdeal C G i :=
  fun x i => zcCompletedGroupAlgebraStandardAugmentationIdealProjection C i x

/--
Evaluating the product of standard augmentation-ideal projections at `i` returns the projection at
`i`.
-/
@[simp]
theorem zcCompletedGroupAlgebraStandardAugmentationIdealProjectionProduct_apply
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (x : zcCompletedGroupAlgebraStandardAugmentationIdeal C G)
    (i : ZCCompletedGroupAlgebraIndex C G) :
    zcCompletedGroupAlgebraStandardAugmentationIdealProjectionProduct C x i =
      zcCompletedGroupAlgebraStandardAugmentationIdealProjection C i x :=
  rfl

/-- Finite-stage projections separate points of the standard completed augmentation ideal. -/
theorem zcCompletedGroupAlgebraStandardAugmentationIdealProjectionProduct_injective
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C] :
    Function.Injective
      (zcCompletedGroupAlgebraStandardAugmentationIdealProjectionProduct C (G := G)) := by
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  funext i
  exact congrArg Subtype.val (congrFun hxy i)

/--
Extensionality for standard completed augmentation ideal elements by finite-stage projections.
-/
theorem zcCompletedGroupAlgebraStandardAugmentationIdealProjection_ext
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    {x y : zcCompletedGroupAlgebraStandardAugmentationIdeal C G}
    (h : ∀ i : ZCCompletedGroupAlgebraIndex C G,
      zcCompletedGroupAlgebraStandardAugmentationIdealProjection C i x =
      zcCompletedGroupAlgebraStandardAugmentationIdealProjection C i y) :
    x = y :=
  zcCompletedGroupAlgebraStandardAugmentationIdealProjectionProduct_injective C
    (by
      funext i
      exact h i)

/--
Every finite standard augmentation stage is hit by the completed standard augmentation ideal
projection.
-/
theorem zcCompletedGroupAlgebraStandardAugmentationIdealProjection_surjective
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (i : ZCCompletedGroupAlgebraIndex C G) :
    Function.Surjective
      (zcCompletedGroupAlgebraStandardAugmentationIdealProjection C i) := by
  intro x
  rcases zcCompletedGroupAlgebraStageAugmentationIdeal_mem_projection_standard
      (C := C) (H := G) i x with
    ⟨y, hy, hproj⟩
  refine ⟨⟨y, hy⟩, ?_⟩
  apply Subtype.ext
  simpa [zcCompletedGroupAlgebraStandardAugmentationIdealProjection_val] using hproj

/--
The finite-stage product \(I(\ker)\,I(G/U)\) attached to the open-image quotient at a source
stage.
-/
def zcCompletedGroupAlgebraOpenImageKernelAugmentationIdealMulStageStandard
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (i : ZCCompletedGroupAlgebraIndex C G) :
    Submodule (ZCCompletedGroupAlgebraStage C G i)
      (zcCompletedGroupAlgebraStageAugmentationIdeal C G i) :=
  Submodule.span (ZCCompletedGroupAlgebraStage C G i)
    (Set.range fun p :
      (zcCompletedGroupAlgebraOpenImageQuotientMap C hC hForm psi hpsi hfopen i).ker ×
        zcCompletedGroupAlgebraStageAugmentationIdeal C G i =>
        (MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus)
            (CompletedGroupAlgebraQuotientInClass G C i.2) p.1.1 - 1) • p.2)

/-- A finite-stage product generator belongs to the finite-stage product submodule. -/
theorem zcCompletedGAOpenImageKernelAugmentationIdealMulStageStandard_generator_mem
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (i : ZCCompletedGroupAlgebraIndex C G)
    (q : (zcCompletedGroupAlgebraOpenImageQuotientMap C hC hForm psi hpsi hfopen i).ker)
    (s : zcCompletedGroupAlgebraStageAugmentationIdeal C G i) :
    (MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus)
        (CompletedGroupAlgebraQuotientInClass G C i.2) q.1 - 1) • s ∈
      zcCompletedGroupAlgebraOpenImageKernelAugmentationIdealMulStageStandard
        C hC hForm psi hpsi hfopen i :=
  Submodule.subset_span (Set.mem_range_self (q, s))

/-- An actual kernel element determines a class in the finite-stage open-image kernel. -/
def zcCompletedGroupAlgebraOpenImageKernelClass
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (i : ZCCompletedGroupAlgebraIndex C G)
    (n : ProfiniteKernelSubgroup psi) :
    (zcCompletedGroupAlgebraOpenImageQuotientMap C hC hForm psi hpsi hfopen i).ker := by
  refine ⟨(QuotientGroup.mk'
      ((((OrderDual.ofDual i.2).1 : OpenNormalSubgroup G) : Subgroup G)) n.1 :
        CompletedGroupAlgebraQuotientInClass G C i.2), ?_⟩
  change
    zcCompletedGroupAlgebraOpenImageQuotientMap C hC hForm psi hpsi hfopen i
        (QuotientGroup.mk'
          ((((OrderDual.ofDual i.2).1 : OpenNormalSubgroup G) : Subgroup G)) n.1 :
            CompletedGroupAlgebraQuotientInClass G C i.2) = 1
  rw [zcCompletedGroupAlgebraOpenImageQuotientMap_mk]
  change QuotientGroup.mk'
      ((((OrderDual.ofDual
        (zcCompletedGroupAlgebraOpenImageIndexInClass C hForm psi hpsi hfopen i)).1 :
          OpenNormalSubgroup H) : Subgroup H)) (psi n.1) = 1
  rw [show psi n.1 = 1 from n.2]
  simp only [QuotientGroup.mk'_apply, QuotientGroup.mk_one]

/--
The open-image kernel class has the expected underlying subgroup, characterized by finite-stage
Fox coordinate formulas.
-/
@[simp]
theorem zcCompletedGroupAlgebraOpenImageKernelClass_val
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (i : ZCCompletedGroupAlgebraIndex C G)
    (n : ProfiniteKernelSubgroup psi) :
    (zcCompletedGroupAlgebraOpenImageKernelClass C hC hForm psi hpsi hfopen i n).1 =
      QuotientGroup.mk'
        ((((OrderDual.ofDual i.2).1 : OpenNormalSubgroup G) : Subgroup G)) n.1 :=
  rfl

/-- The finite-stage augmentation-ideal projection is compatible with scalar multiplication. -/
@[simp 900]
theorem zcCompletedGroupAlgebraStandardAugmentationIdealProjection_kernel_generator_smul
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (i : ZCCompletedGroupAlgebraIndex C G)
    (n : ProfiniteKernelSubgroup psi)
    (s : zcCompletedGroupAlgebraStandardAugmentationIdeal C G) :
    zcCompletedGroupAlgebraStandardAugmentationIdealProjection C i
        ((zcGroupLike C G n.1 - 1) • s) =
      (MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus)
          (CompletedGroupAlgebraQuotientInClass G C i.2)
          (zcCompletedGroupAlgebraOpenImageKernelClass
            C hC hForm psi hpsi hfopen i n).1 - 1) •
        zcCompletedGroupAlgebraStandardAugmentationIdealProjection C i s := by
  apply Subtype.ext
  change zcCompletedGroupAlgebraProjection C G i
      ((zcGroupLike C G n.1 - 1) * (s : ZCCompletedGroupAlgebra C G)) =
    (MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus)
        (CompletedGroupAlgebraQuotientInClass G C i.2)
        (QuotientGroup.mk'
          ((((OrderDual.ofDual i.2).1 : OpenNormalSubgroup G) : Subgroup G)) n.1) - 1) *
      zcCompletedGroupAlgebraProjection C G i (s : ZCCompletedGroupAlgebra C G)
  rw [zcCompletedGroupAlgebraProjection_mul]
  simp only [zcCompletedGroupAlgebraProjection_sub, zcCompletedGroupAlgebraProjection_groupLike,
    zcCompletedGroupAlgebraProjection_one, QuotientGroup.mk'_apply]

/--
Projecting an element of \(I(\ker\psi)I(G)\) to an open-image finite stage lands in the
corresponding finite-stage kernel-augmentation product.
-/
theorem zcCompletedGAKernelAugmentationIdealMulStandard_proj_mem_openImageStage
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (i : ZCCompletedGroupAlgebraIndex C G)
    {x : zcCompletedGroupAlgebraStandardAugmentationIdeal C G}
    (hx : x ∈ zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi) :
    zcCompletedGroupAlgebraStandardAugmentationIdealProjection C i x ∈
      zcCompletedGroupAlgebraOpenImageKernelAugmentationIdealMulStageStandard
        C hC hForm psi hpsi hfopen i := by
  let T :=
    zcCompletedGroupAlgebraOpenImageKernelAugmentationIdealMulStageStandard
      C hC hForm psi hpsi hfopen i
  refine Submodule.span_induction
    (p := fun x _ => zcCompletedGroupAlgebraStandardAugmentationIdealProjection C i x ∈ T)
    ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨p, rfl⟩
    rcases p with ⟨n, s⟩
    rw [zcCompletedGroupAlgebraStandardAugmentationIdealProjection_kernel_generator_smul
      C hC hForm psi hpsi hfopen i n s]
    exact
      zcCompletedGAOpenImageKernelAugmentationIdealMulStageStandard_generator_mem
        C hC hForm psi hpsi hfopen i
        (zcCompletedGroupAlgebraOpenImageKernelClass C hC hForm psi hpsi hfopen i n)
        (zcCompletedGroupAlgebraStandardAugmentationIdealProjection C i s)
  · simp only [zcCompletedGroupAlgebraStandardAugmentationIdealProjection_zero, zero_mem, T]
  · intro x y _ _ hx hy
    simpa [T] using T.add_mem hx hy
  · intro a x _ hx
    rw [zcCompletedGroupAlgebraStandardAugmentationIdealProjection_smul]
    exact T.smul_mem (zcCompletedGroupAlgebraProjection C G i a) hx

/--
Every element of the finite-stage open-image kernel-augmentation product is the projection of an
element of the algebraic product \(I(\ker\psi)I(G)\).
-/
theorem zcCompletedGAOpenImageKernelAugmentationIdealMulStageStandard_mem_proj
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (i : ZCCompletedGroupAlgebraIndex C G)
    (x : zcCompletedGroupAlgebraStageAugmentationIdeal C G i)
    (hx :
      x ∈ zcCompletedGroupAlgebraOpenImageKernelAugmentationIdealMulStageStandard
        C hC hForm psi hpsi hfopen i) :
    ∃ y ∈ zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi,
      zcCompletedGroupAlgebraStandardAugmentationIdealProjection C i y = x := by
  let T :=
    zcCompletedGroupAlgebraOpenImageKernelAugmentationIdealMulStageStandard
      C hC hForm psi hpsi hfopen i
  let P : zcCompletedGroupAlgebraStageAugmentationIdeal C G i → Prop := fun x =>
    ∃ y ∈ zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi,
      zcCompletedGroupAlgebraStandardAugmentationIdealProjection C i y = x
  refine Submodule.span_induction (p := fun x _ => P x) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨p, rfl⟩
    rcases p with ⟨q, s⟩
    rcases
      zcCompletedGroupAlgebraOpenImageQuotientMap_kernel_lift
        C hC hForm psi hpsi hfopen i q with
      ⟨n, hn⟩
    rcases
      zcCompletedGroupAlgebraStageAugmentationIdeal_mem_projection_standard
        (C := C) (H := G) i s with
      ⟨s', hs', hs'proj⟩
    let sStd : zcCompletedGroupAlgebraStandardAugmentationIdeal C G := ⟨s', hs'⟩
    refine ⟨(zcGroupLike C G n.1 - 1) • sStd,
      zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard_generator_mem C psi n sStd, ?_⟩
    rw [zcCompletedGroupAlgebraStandardAugmentationIdealProjection_kernel_generator_smul
      C hC hForm psi hpsi hfopen i n sStd]
    apply Subtype.ext
    change
      (MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus)
          (CompletedGroupAlgebraQuotientInClass G C i.2)
          (QuotientGroup.mk'
            ((((OrderDual.ofDual i.2).1 : OpenNormalSubgroup G) : Subgroup G)) n.1) - 1) *
        zcCompletedGroupAlgebraProjection C G i s' =
      (MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus)
          (CompletedGroupAlgebraQuotientInClass G C i.2) q.1 - 1) * s.1
    rw [hn, hs'proj]
  · refine ⟨0, (zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi).zero_mem, ?_⟩
    simp only [zcCompletedGroupAlgebraStandardAugmentationIdealProjection_zero]
  · intro x y _ _ hx hy
    rcases hx with ⟨x', hx'mem, hx'proj⟩
    rcases hy with ⟨y', hy'mem, hy'proj⟩
    refine ⟨x' + y',
      (zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi).add_mem hx'mem hy'mem, ?_⟩
    simp only [zcCompletedGroupAlgebraStandardAugmentationIdealProjection_add, hx'proj, hy'proj]
  · intro a x _ hx
    rcases hx with ⟨x', hx'mem, hx'proj⟩
    rcases zcCompletedGroupAlgebraProjection_surjective C G i a with ⟨a', ha'⟩
    refine ⟨a' • x',
      (zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi).smul_mem a' hx'mem, ?_⟩
    rw [zcCompletedGroupAlgebraStandardAugmentationIdealProjection_smul, ha', hx'proj]

/--
The closed finite-stage hull of \(I(\ker \psi)I(G)\) inside the standard source augmentation
ideal: an element belongs exactly when every finite projection belongs to the finite-stage
open-image kernel product.
-/
def zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi) :
    Submodule (ZCCompletedGroupAlgebra C G)
      (zcCompletedGroupAlgebraStandardAugmentationIdeal C G) where
  carrier := {x | ∀ i : ZCCompletedGroupAlgebraIndex C G,
    zcCompletedGroupAlgebraStandardAugmentationIdealProjection C i x ∈
      zcCompletedGroupAlgebraOpenImageKernelAugmentationIdealMulStageStandard
        C hC hForm psi hpsi hfopen i}
  zero_mem' := by
    intro i
    simp only [zcCompletedGroupAlgebraStandardAugmentationIdealProjection_zero, zero_mem]
  add_mem' := by
    intro x y hx hy i
    simpa using
      (zcCompletedGroupAlgebraOpenImageKernelAugmentationIdealMulStageStandard
        C hC hForm psi hpsi hfopen i).add_mem (hx i) (hy i)
  smul_mem' := by
    intro a x hx i
    rw [zcCompletedGroupAlgebraStandardAugmentationIdealProjection_smul]
    exact
      (zcCompletedGroupAlgebraOpenImageKernelAugmentationIdealMulStageStandard
        C hC hForm psi hpsi hfopen i).smul_mem
        (zcCompletedGroupAlgebraProjection C G i a) (hx i)

/-- The algebraic product is contained in its finite-stage closed hull. -/
theorem zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard_le_closed
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi) :
    zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi ≤
      zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
        C hC hForm psi hpsi hfopen := by
  intro x hx i
  exact
    zcCompletedGAKernelAugmentationIdealMulStandard_proj_mem_openImageStage
      C hC hForm psi hpsi hfopen i hx

/-- The finite-stage hull is closed in the standard source augmentation ideal. -/
theorem isClosed_zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi) :
    IsClosed
      ((zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
        C hC hForm psi hpsi hfopen :
          Set (zcCompletedGroupAlgebraStandardAugmentationIdeal C G))) := by
  change IsClosed {x : zcCompletedGroupAlgebraStandardAugmentationIdeal C G |
    ∀ i : ZCCompletedGroupAlgebraIndex C G,
      zcCompletedGroupAlgebraStandardAugmentationIdealProjection C i x ∈
        zcCompletedGroupAlgebraOpenImageKernelAugmentationIdealMulStageStandard
          C hC hForm psi hpsi hfopen i}
  simp only [Set.ofPred_forall]
  refine isClosed_iInter ?_
  intro i
  have : DiscreteTopology (zcCompletedGroupAlgebraStageAugmentationIdeal C G i) := by
    infer_instance
  exact
    (isClosed_discrete
      ((zcCompletedGroupAlgebraOpenImageKernelAugmentationIdealMulStageStandard
        C hC hForm psi hpsi hfopen i :
          Set (zcCompletedGroupAlgebraStageAugmentationIdeal C G i)))).preimage
      (continuous_zcCompletedGroupAlgebraStandardAugmentationIdealProjection C i)

/-- The closure of the algebraic product is contained in the finite-stage closed hull. -/
theorem closure_zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard_le_closed
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi) :
    closure
        ((zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi :
          Set (zcCompletedGroupAlgebraStandardAugmentationIdeal C G))) ⊆
      (zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
        C hC hForm psi hpsi hfopen :
          Set (zcCompletedGroupAlgebraStandardAugmentationIdeal C G)) := by
  exact
    closure_minimal
      (by
        intro x hx
        exact
          zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard_le_closed
            C hC hForm psi hpsi hfopen hx)
      (isClosed_zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
        C hC hForm psi hpsi hfopen)

/-- The finite-stage closed hull is contained in the closure of the algebraic product. -/
theorem zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed_le_closure
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi) :
    (zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
        C hC hForm psi hpsi hfopen :
          Set (zcCompletedGroupAlgebraStandardAugmentationIdeal C G)) ⊆
      closure
        ((zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi :
          Set (zcCompletedGroupAlgebraStandardAugmentationIdeal C G))) := by
  intro x hx
  let R := ZCCompletedGroupAlgebra C G
  let Ssys := zcCompletedGroupAlgebraSystem C G
  let Ystd : Set (zcCompletedGroupAlgebraStandardAugmentationIdeal C G) :=
    zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi
  let Yamb : Set R := Subtype.val '' Ystd
  have hxAmb : (x : R) ∈ closure Yamb := by
    let : Nonempty (ZCCompletedGroupAlgebraIndex C G) :=
      ⟨(ProCGroups.Completion.ProCIntegerIndex.terminal (C := C) inferInstance,
        zcCompletedGroupAlgebraTopIndex C G)⟩
    let : ∀ i : ZCCompletedGroupAlgebraIndex C G, TopologicalSpace (Ssys.X i) :=
      Ssys.topologicalSpace
    let : ∀ i : ZCCompletedGroupAlgebraIndex C G, CompactSpace (Ssys.X i) := fun i => by
      dsimp [Ssys, zcCompletedGroupAlgebraSystem]
      change @CompactSpace (ZCCompletedGroupAlgebraStage C G i) ⊥
      let : Fact (0 < i.1.modulus) := ⟨i.1.positive⟩
      let : Finite (ZCCompletedGroupAlgebraStage C G i) :=
        finite_modNCompletedGroupAlgebraStageInClass
          (n := i.1.modulus) (G := G) C i.2
      exact Finite.compactSpace
    let : ∀ i : ZCCompletedGroupAlgebraIndex C G, T2Space (Ssys.X i) := fun i => by
      dsimp [Ssys, zcCompletedGroupAlgebraSystem]
      change @T2Space (ZCCompletedGroupAlgebraStage C G i) ⊥
      exact @DiscreteTopology.toT2Space _ ⊥ ⟨rfl⟩
    have hdir : Directed (· ≤ ·) (id : ZCCompletedGroupAlgebraIndex C G →
        ZCCompletedGroupAlgebraIndex C G) :=
      directed_zcCompletedGroupAlgebraIndex_of_formation (C := C) (H := G) hForm
    have hxLim :
        (show Ssys.inverseLimit from (x : R)) ∈
          closure (show Set Ssys.inverseLimit from Yamb) := by
      rw [Ssys.mem_isClosed_iff_forall_projection_mem hdir isClosed_closure]
      intro i
      rcases
        zcCompletedGAOpenImageKernelAugmentationIdealMulStageStandard_mem_proj
          C hC hForm psi hpsi hfopen i
          (zcCompletedGroupAlgebraStandardAugmentationIdealProjection C i x)
          (hx i) with
        ⟨y, hy, hyproj⟩
      refine ⟨(y : R), subset_closure ?_, ?_⟩
      · exact ⟨y, by simpa [Ystd] using hy, rfl⟩
      · change
          zcCompletedGroupAlgebraProjection C G i (y : R) =
            zcCompletedGroupAlgebraProjection C G i (x : R)
        exact congrArg Subtype.val hyproj
    convert hxLim using 1 <;> rfl
  have hclosure :
      closure Ystd =
        (Subtype.val : zcCompletedGroupAlgebraStandardAugmentationIdeal C G → R) ⁻¹'
          closure Yamb := by
    exact Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image Ystd
  change x ∈ closure Ystd
  rw [hclosure]
  exact hxAmb

/-- The closure of \(I(\ker \psi)I(G)\) is exactly the finite-stage kernel-product condition. -/
theorem closure_zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard_eq_closed
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi) :
    closure
        ((zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi :
          Set (zcCompletedGroupAlgebraStandardAugmentationIdeal C G))) =
      (zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
        C hC hForm psi hpsi hfopen :
          Set (zcCompletedGroupAlgebraStandardAugmentationIdeal C G)) := by
  exact Set.Subset.antisymm
    (closure_zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard_le_closed
      C hC hForm psi hpsi hfopen)
    (zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed_le_closure
      C hC hForm psi hpsi hfopen)

/--
The algebraic product is closed exactly when it already equals the finite-stage closed hull.
This is the precise non-circular closedness frontier.
-/
theorem isClosed_zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard_iff_eq_closed
    {C : ProCGroups.FiniteGroupClass.{u}}
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    {psi : ContinuousMonoidHom G H} (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi) :
    IsClosed
        ((zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi :
          Set (zcCompletedGroupAlgebraStandardAugmentationIdeal C G))) ↔
      (zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi :
          Set (zcCompletedGroupAlgebraStandardAugmentationIdeal C G)) =
        (zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
          C hC hForm psi hpsi hfopen :
            Set (zcCompletedGroupAlgebraStandardAugmentationIdeal C G)) := by
  constructor
  · intro hclosed
    apply Set.Subset.antisymm
    · exact zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard_le_closed
        C hC hForm psi hpsi hfopen
    · intro x hx
      have hxclosure :
          x ∈ closure
            ((zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi :
              Set (zcCompletedGroupAlgebraStandardAugmentationIdeal C G))) := by
        rw [closure_zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard_eq_closed
          C hC hForm psi hpsi hfopen]
        exact hx
      rwa [hclosed.closure_eq] at hxclosure
  · intro hEq
    rw [hEq]
    exact isClosed_zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
      C hC hForm psi hpsi hfopen


/--
The source-side augmentation quotient \(I\mathbb{Z}_C\llbracket G\rrbracket / I(\ker \psi)
I\mathbb{Z}_C\llbracket G\rrbracket\), before descending scalars to \(\mathbb{Z}_C\llbracket
H\rrbracket\).
-/
abbrev KernelAugmentationIdealQuotient
    (psi : ContinuousMonoidHom G H) : Type u :=
  zcCompletedGroupAlgebraStandardAugmentationIdeal C G ⧸
    zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi

/--
The closed source-side augmentation quotient, using the finite-stage closed hull of \(I(\ker
\psi)I(G)\) as denominator.
-/
abbrev KernelAugmentationIdealClosedQuotient
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi) : Type u :=
  zcCompletedGroupAlgebraStandardAugmentationIdeal C G ⧸
    zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
      C hC hForm psi hpsi hfopen

/-- The quotient map to the closed source augmentation quotient is a quotient map. -/
theorem isQuotientMap_kernelAugmentationIdealClosedQuotient_mkQ
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi) :
    Topology.IsQuotientMap
      (zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
        C hC hForm psi hpsi hfopen).mkQ := by
  rw [Topology.isQuotientMap_iff]
  constructor
  · exact ⟨rfl⟩
  · exact
      Submodule.Quotient.mk_surjective
        (p := zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
          C hC hForm psi hpsi hfopen)

/--
Continuity out of the closed source augmentation quotient can be tested after precomposing with
the quotient map from the standard augmentation ideal.
-/
theorem continuous_kernelAugmentationIdealClosedQuotient_iff_comp_mkQ
    {C : ProCGroups.FiniteGroupClass.{u}}
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    {hC : ProCGroups.FiniteGroupClass.Hereditary C}
    {hForm : ProCGroups.FiniteGroupClass.Formation C}
    {psi : ContinuousMonoidHom G H} {hpsi : Function.Surjective psi}
    {hfopen : IsOpenMap psi}
    {A : Type u} [TopologicalSpace A]
    {f : KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen → A} :
    Continuous f ↔
      Continuous (fun x : zcCompletedGroupAlgebraStandardAugmentationIdeal C G =>
        f ((zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
          C hC hForm psi hpsi hfopen).mkQ x)) := by
  simpa [Function.comp_def] using
    (isQuotientMap_kernelAugmentationIdealClosedQuotient_mkQ
      C hC hForm psi hpsi hfopen).continuous_iff (g := f)

/-- The closed source augmentation quotient is \(T_1\) for the quotient topology. -/
theorem t1Space_kernelAugmentationIdealClosedQuotient
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi) :
    T1Space (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) := by
  let : IsClosed
      ((zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
        C hC hForm psi hpsi hfopen :
          Submodule (ZCCompletedGroupAlgebra C G)
            (zcCompletedGroupAlgebraStandardAugmentationIdeal C G)) :
        Set (zcCompletedGroupAlgebraStandardAugmentationIdeal C G)) :=
    isClosed_zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
      C hC hForm psi hpsi hfopen
  infer_instance

/-- The zero class is closed in the closed source augmentation quotient. -/
theorem isClosed_zero_kernelAugmentationIdealClosedQuotient
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi) :
    IsClosed
      ({0} : Set
        (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen)) := by
  let : T1Space
      (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
    t1Space_kernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen
  exact isClosed_singleton

/-- The finite-stage quotient of the source augmentation ideal by the open-image kernel product. -/
abbrev KernelAugmentationIdealClosedStageQuotient
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (i : ZCCompletedGroupAlgebraIndex C G) : Type u :=
  zcCompletedGroupAlgebraStageAugmentationIdeal C G i ⧸
    zcCompletedGroupAlgebraOpenImageKernelAugmentationIdealMulStageStandard
      C hC hForm psi hpsi hfopen i

/-- The finite-stage coordinate of the closed source augmentation quotient. -/
def kernelAugmentationIdealClosedQuotientStageProjection
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (i : ZCCompletedGroupAlgebraIndex C G) :
    KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen →ₛₗ[
      zcCompletedGroupAlgebraProjectionRingHom C G i]
      KernelAugmentationIdealClosedStageQuotient C hC hForm psi hpsi hfopen i :=
  (zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
    C hC hForm psi hpsi hfopen).mapQ
    (zcCompletedGroupAlgebraOpenImageKernelAugmentationIdealMulStageStandard
      C hC hForm psi hpsi hfopen i)
    (zcCompletedGroupAlgebraStandardAugmentationIdealProjectionLinear C i)
    (by
      intro x hx
      exact hx i)

/--
The stage projection of a closed kernel-augmentation quotient class is represented by the
corresponding finite-stage projection.
-/
@[simp 900]
theorem kernelAugmentationIdealClosedQuotientStageProjection_mk
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (i : ZCCompletedGroupAlgebraIndex C G)
    (x : zcCompletedGroupAlgebraStandardAugmentationIdeal C G) :
    kernelAugmentationIdealClosedQuotientStageProjection
        C hC hForm psi hpsi hfopen i
        ((zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
          C hC hForm psi hpsi hfopen).mkQ x) =
      ((zcCompletedGroupAlgebraOpenImageKernelAugmentationIdealMulStageStandard
          C hC hForm psi hpsi hfopen i).mkQ
        (zcCompletedGroupAlgebraStandardAugmentationIdealProjection C i x) :
        KernelAugmentationIdealClosedStageQuotient C hC hForm psi hpsi hfopen i) := by
  exact
    Submodule.mapQ_apply
      (zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
        C hC hForm psi hpsi hfopen)
      (zcCompletedGroupAlgebraOpenImageKernelAugmentationIdealMulStageStandard
        C hC hForm psi hpsi hfopen i)
      (zcCompletedGroupAlgebraStandardAugmentationIdealProjectionLinear C i)
      x

/-- Each finite-stage coordinate of the closed source augmentation quotient is continuous. -/
theorem continuous_kernelAugmentationIdealClosedQuotientStageProjection
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (i : ZCCompletedGroupAlgebraIndex C G) :
    Continuous
      (kernelAugmentationIdealClosedQuotientStageProjection
        C hC hForm psi hpsi hfopen i) := by
  rw [continuous_kernelAugmentationIdealClosedQuotient_iff_comp_mkQ
    (C := C) (G := G) (H := H) (hC := hC) (hForm := hForm)
    (psi := psi) (hpsi := hpsi) (hfopen := hfopen)]
  have hproj :
      Continuous (zcCompletedGroupAlgebraStandardAugmentationIdealProjection C i) :=
    continuous_zcCompletedGroupAlgebraStandardAugmentationIdealProjection C i
  have hq :
      Continuous (fun y : zcCompletedGroupAlgebraStageAugmentationIdeal C G i =>
        ((zcCompletedGroupAlgebraOpenImageKernelAugmentationIdealMulStageStandard
          C hC hForm psi hpsi hfopen i).mkQ y :
          KernelAugmentationIdealClosedStageQuotient C hC hForm psi hpsi hfopen i)) :=
    continuous_quotient_mk'
  have hcomp := hq.comp hproj
  have hfun :
      ((fun y : zcCompletedGroupAlgebraStageAugmentationIdeal C G i =>
          ((zcCompletedGroupAlgebraOpenImageKernelAugmentationIdealMulStageStandard
            C hC hForm psi hpsi hfopen i).mkQ y :
            KernelAugmentationIdealClosedStageQuotient C hC hForm psi hpsi hfopen i)) ∘
        zcCompletedGroupAlgebraStandardAugmentationIdealProjection C i) =
      (fun x : zcCompletedGroupAlgebraStandardAugmentationIdeal C G =>
        kernelAugmentationIdealClosedQuotientStageProjection
          C hC hForm psi hpsi hfopen i
          ((zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
            C hC hForm psi hpsi hfopen).mkQ x)) := by
    funext x
    exact
      (kernelAugmentationIdealClosedQuotientStageProjection_mk
        C hC hForm psi hpsi hfopen i x).symm
  exact hfun ▸ hcomp

/-- The product of all finite-stage coordinates of the closed source augmentation quotient. -/
def kernelAugmentationIdealClosedQuotientStageProjectionProduct
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi) :
    KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen →
      ∀ i : ZCCompletedGroupAlgebraIndex C G,
        KernelAugmentationIdealClosedStageQuotient C hC hForm psi hpsi hfopen i :=
  fun x i => kernelAugmentationIdealClosedQuotientStageProjection
    C hC hForm psi hpsi hfopen i x

/--
Evaluating the product projection of the closed kernel-augmentation quotient at `i` returns its
stage projection at `i`.
-/
@[simp]
theorem kernelAugmentationIdealClosedQuotientStageProjectionProduct_apply
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (x : KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen)
    (i : ZCCompletedGroupAlgebraIndex C G) :
    kernelAugmentationIdealClosedQuotientStageProjectionProduct
        C hC hForm psi hpsi hfopen x i =
      kernelAugmentationIdealClosedQuotientStageProjection
        C hC hForm psi hpsi hfopen i x :=
  rfl

/-- The finite-stage coordinate product of the closed source augmentation quotient is continuous. -/
theorem continuous_kernelAugmentationIdealClosedQuotientStageProjectionProduct
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi) :
    Continuous
      (kernelAugmentationIdealClosedQuotientStageProjectionProduct
        C hC hForm psi hpsi hfopen) := by
  exact continuous_pi fun i =>
    continuous_kernelAugmentationIdealClosedQuotientStageProjection
      C hC hForm psi hpsi hfopen i

/-- Finite-stage coordinates separate points in the closed source augmentation quotient. -/
theorem kernelAugmentationIdealClosedQuotientStageProjectionProduct_injective
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi) :
    Function.Injective
      (kernelAugmentationIdealClosedQuotientStageProjectionProduct
        C hC hForm psi hpsi hfopen) := by
  let S :=
    zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
      C hC hForm psi hpsi hfopen
  intro qx qy hxy
  revert qy
  refine Submodule.Quotient.induction_on (p := S) qx ?_
  intro x qy hxy
  revert hxy
  refine Submodule.Quotient.induction_on (p := S) qy ?_
  intro y hxy
  apply (Submodule.Quotient.eq S).2
  change x - y ∈ S
  intro i
  let T :=
    zcCompletedGroupAlgebraOpenImageKernelAugmentationIdealMulStageStandard
      C hC hForm psi hpsi hfopen i
  have hi :
      kernelAugmentationIdealClosedQuotientStageProjection
          C hC hForm psi hpsi hfopen i (Submodule.Quotient.mk (p := S) x) =
        kernelAugmentationIdealClosedQuotientStageProjection
          C hC hForm psi hpsi hfopen i (Submodule.Quotient.mk (p := S) y) := by
    exact congrFun hxy i
  have hstage :
      zcCompletedGroupAlgebraStandardAugmentationIdealProjection C i x -
          zcCompletedGroupAlgebraStandardAugmentationIdealProjection C i y ∈ T := by
    apply (Submodule.Quotient.eq T).1
    change
      kernelAugmentationIdealClosedQuotientStageProjection
          C hC hForm psi hpsi hfopen i (S.mkQ x) =
        kernelAugmentationIdealClosedQuotientStageProjection
          C hC hForm psi hpsi hfopen i (S.mkQ y) at hi
    rw [kernelAugmentationIdealClosedQuotientStageProjection_mk,
      kernelAugmentationIdealClosedQuotientStageProjection_mk] at hi
    exact hi
  simpa [S, T] using hstage

/-- Extensionality for the closed source augmentation quotient by finite-stage coordinates. -/
theorem kernelAugmentationIdealClosedQuotientStageProjection_ext
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    {x y : KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen}
    (h : ∀ i : ZCCompletedGroupAlgebraIndex C G,
      kernelAugmentationIdealClosedQuotientStageProjection
        C hC hForm psi hpsi hfopen i x =
      kernelAugmentationIdealClosedQuotientStageProjection
        C hC hForm psi hpsi hfopen i y) :
    x = y := by
  exact
    kernelAugmentationIdealClosedQuotientStageProjectionProduct_injective
      C hC hForm psi hpsi hfopen
      (by
        funext i
        exact h i)

/--
The quotient topology on the closed source augmentation quotient is exactly the topology induced
by all finite closed-quotient coordinates.
-/
theorem kernelAugmentationIdealClosedQuotient_topology_eq_induced_stageProjProduct
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi) :
    (inferInstance :
      TopologicalSpace
        (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen)) =
      TopologicalSpace.induced
        (kernelAugmentationIdealClosedQuotientStageProjectionProduct
          C hC hForm psi hpsi hfopen) inferInstance := by
  let Sclosed :=
    zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
      C hC hForm psi hpsi hfopen
  let Q := KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen
  let stageProduct :=
    kernelAugmentationIdealClosedQuotientStageProjectionProduct
      C hC hForm psi hpsi hfopen
  ext U
  constructor
  · intro hU
    let Tind : TopologicalSpace Q :=
      TopologicalSpace.induced stageProduct inferInstance
    rw [@isOpen_iff_forall_mem_open Q Tind U]
    intro qx hqxU
    refine Submodule.Quotient.induction_on
      (p := Sclosed)
      (C := fun qx =>
        qx ∈ U → ∃ t, t ⊆ U ∧ @IsOpen Q Tind t ∧ qx ∈ t)
      qx ?_ hqxU
    intro x hxU
    let q : zcCompletedGroupAlgebraStandardAugmentationIdeal C G → Q :=
      Sclosed.mkQ
    have hUquot :
        @IsOpen Q (QuotientModule.Quotient.topologicalSpace Sclosed) U := hU
    have hpreOpen :
        @IsOpen
          (zcCompletedGroupAlgebraStandardAugmentationIdeal C G)
          inferInstance (q ⁻¹' U) := by
      change
        @IsOpen
          (zcCompletedGroupAlgebraStandardAugmentationIdeal C G)
          inferInstance (q ⁻¹' U) at hUquot
      exact hUquot
    rcases isOpen_induced_iff.mp hpreOpen with ⟨V, hVopen, hVeq⟩
    have hxV : (x : ZCCompletedGroupAlgebra C G) ∈ V := by
      have hxpre : x ∈ q ⁻¹' U := hxU
      rwa [← hVeq] at hxpre
    let Ssys := zcCompletedGroupAlgebraSystem C G
    let : Nonempty (ZCCompletedGroupAlgebraIndex C G) :=
      ⟨(ProCGroups.Completion.ProCIntegerIndex.terminal (C := C) inferInstance,
        zcCompletedGroupAlgebraTopIndex C G)⟩
    let : ∀ i : ZCCompletedGroupAlgebraIndex C G, TopologicalSpace (Ssys.X i) :=
      Ssys.topologicalSpace
    let : ∀ i : ZCCompletedGroupAlgebraIndex C G, CompactSpace (Ssys.X i) := fun i => by
      dsimp [Ssys, zcCompletedGroupAlgebraSystem]
      change @CompactSpace (ZCCompletedGroupAlgebraStage C G i) ⊥
      let : Fact (0 < i.1.modulus) := ⟨i.1.positive⟩
      let : Finite (ZCCompletedGroupAlgebraStage C G i) :=
        finite_modNCompletedGroupAlgebraStageInClass
          (n := i.1.modulus) (G := G) C i.2
      exact Finite.compactSpace
    let : ∀ i : ZCCompletedGroupAlgebraIndex C G, T2Space (Ssys.X i) := fun i => by
      dsimp [Ssys, zcCompletedGroupAlgebraSystem]
      change @T2Space (ZCCompletedGroupAlgebraStage C G i) ⊥
      exact @DiscreteTopology.toT2Space _ ⊥ ⟨rfl⟩
    have hdir : Directed (· ≤ ·) (id : ZCCompletedGroupAlgebraIndex C G →
        ZCCompletedGroupAlgebraIndex C G) :=
      directed_zcCompletedGroupAlgebraIndex_of_formation (C := C) (H := G) hForm
    rcases Ssys.exists_projection_preimage_subset hdir hVopen hxV with
      ⟨i, W, hWopen, hxW, hWV⟩
    let t : Set Q :=
      {z | kernelAugmentationIdealClosedQuotientStageProjection
        C hC hForm psi hpsi hfopen i z =
        kernelAugmentationIdealClosedQuotientStageProjection
          C hC hForm psi hpsi hfopen i (q x)}
    refine ⟨t, ?_, ?_, ?_⟩
    · intro z hz
      refine Submodule.Quotient.induction_on
        (p := Sclosed)
        (C := fun z => z ∈ t → z ∈ U)
        z ?_ hz
      intro y hy
      let T :=
        zcCompletedGroupAlgebraOpenImageKernelAugmentationIdealMulStageStandard
          C hC hForm psi hpsi hfopen i
      have hyStage :
          zcCompletedGroupAlgebraStandardAugmentationIdealProjection C i y -
              zcCompletedGroupAlgebraStandardAugmentationIdealProjection C i x ∈ T := by
        apply (Submodule.Quotient.eq T).1
        have hy' := hy
        change
          kernelAugmentationIdealClosedQuotientStageProjection
              C hC hForm psi hpsi hfopen i (Sclosed.mkQ y) =
            kernelAugmentationIdealClosedQuotientStageProjection
              C hC hForm psi hpsi hfopen i (Sclosed.mkQ x) at hy'
        rw [kernelAugmentationIdealClosedQuotientStageProjection_mk,
          kernelAugmentationIdealClosedQuotientStageProjection_mk] at hy'
        exact hy'
      rcases
          zcCompletedGAOpenImageKernelAugmentationIdealMulStageStandard_mem_proj
            C hC hForm psi hpsi hfopen i
            (zcCompletedGroupAlgebraStandardAugmentationIdealProjection C i y -
              zcCompletedGroupAlgebraStandardAugmentationIdealProjection C i x)
            hyStage with
        ⟨r, hr, hrproj⟩
      have hq : q (y - r) = q y := by
        apply (Submodule.Quotient.eq Sclosed).2
        change (y - r) - y ∈ Sclosed
        have hdiff : (y - r) - y = -r := by
          abel
        rw [hdiff]
        exact Sclosed.neg_mem
          (zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard_le_closed
            C hC hForm psi hpsi hfopen hr)
      have hproj_eq :
          zcCompletedGroupAlgebraStandardAugmentationIdealProjection C i (y - r) =
            zcCompletedGroupAlgebraStandardAugmentationIdealProjection C i x := by
        rw [zcCompletedGroupAlgebraStandardAugmentationIdealProjection_sub, hrproj]
        abel
      have hyW : Ssys.projection i ((y - r : zcCompletedGroupAlgebraStandardAugmentationIdeal C G) :
          ZCCompletedGroupAlgebra C G) ∈ W := by
        have hval := congrArg Subtype.val hproj_eq
        change
          zcCompletedGroupAlgebraProjection C G i
              ((y - r : zcCompletedGroupAlgebraStandardAugmentationIdeal C G) :
                ZCCompletedGroupAlgebra C G) =
            zcCompletedGroupAlgebraProjection C G i
              (x : ZCCompletedGroupAlgebra C G) at hval
        have hxW' :
            zcCompletedGroupAlgebraProjection C G i
              (x : ZCCompletedGroupAlgebra C G) ∈ W := by
          change
            zcCompletedGroupAlgebraProjection C G i
              (x : ZCCompletedGroupAlgebra C G) ∈ W at hxW
          exact hxW
        change
          zcCompletedGroupAlgebraProjection C G i
            (((y - r : zcCompletedGroupAlgebraStandardAugmentationIdeal C G) :
              ZCCompletedGroupAlgebra C G)) ∈ W
        rw [hval]
        exact hxW'
      have hyV :
          (((y - r : zcCompletedGroupAlgebraStandardAugmentationIdeal C G) :
            ZCCompletedGroupAlgebra C G)) ∈ V :=
        hWV hyW
      have hyU : q (y - r) ∈ U := by
        have hyPre :
            (y - r : zcCompletedGroupAlgebraStandardAugmentationIdeal C G) ∈
              (Subtype.val : zcCompletedGroupAlgebraStandardAugmentationIdeal C G →
                ZCCompletedGroupAlgebra C G) ⁻¹' V := hyV
        rwa [hVeq] at hyPre
      rwa [hq] at hyU
    · let : TopologicalSpace Q := Tind
      have hprod : Continuous stageProduct :=
        continuous_induced_dom
      have hcoord :
          Continuous (fun z : Q =>
            kernelAugmentationIdealClosedQuotientStageProjection
              C hC hForm psi hpsi hfopen i z) := by
        have hi := (continuous_apply i).comp hprod
        change Continuous
          (kernelAugmentationIdealClosedQuotientStageProjection
            C hC hForm psi hpsi hfopen i) at hi
        exact hi
      have hsingle_open :
          IsOpen
            (Set.singleton (kernelAugmentationIdealClosedQuotientStageProjection
              C hC hForm psi hpsi hfopen i (q x)) :
              Set (KernelAugmentationIdealClosedStageQuotient C hC hForm psi hpsi hfopen i)) := by
        let T :=
          zcCompletedGroupAlgebraOpenImageKernelAugmentationIdealMulStageStandard
            C hC hForm psi hpsi hfopen i
        have : DiscreteTopology (zcCompletedGroupAlgebraStageAugmentationIdeal C G i) := by
          infer_instance
        change
          @IsOpen
            (KernelAugmentationIdealClosedStageQuotient C hC hForm psi hpsi hfopen i)
            (TopologicalSpace.coinduced T.mkQ inferInstance)
            (Set.singleton (kernelAugmentationIdealClosedQuotientStageProjection
              C hC hForm psi hpsi hfopen i (q x)) :
              Set (KernelAugmentationIdealClosedStageQuotient C hC hForm psi hpsi hfopen i))
        rw [isOpen_coinduced]
        exact isOpen_discrete _
      exact
        hsingle_open.preimage hcoord
    · exact rfl
  · intro hU
    rcases isOpen_induced_iff.mp hU with ⟨V, hVopen, hVU⟩
    rw [← hVU]
    exact hVopen.preimage
      (continuous_kernelAugmentationIdealClosedQuotientStageProjectionProduct
        C hC hForm psi hpsi hfopen)

/--
The finite-stage source-to-open-image group-algebra map used to descend the source-stage action
on the closed finite augmentation quotient to the matching target stage.
-/
def zcCompletedGroupAlgebraOpenImageStageRingHom
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (i : ZCCompletedGroupAlgebraIndex C G) :
    ZCCompletedGroupAlgebraStage C G i →+*
      ZCCompletedGroupAlgebraStage C H
        (zcCompletedGroupAlgebraOpenImageTargetIndex C hForm psi hpsi hfopen i) :=
  MonoidAlgebra.mapDomainRingHom (ModNCompletedCoeff i.1.modulus)
    (zcCompletedGroupAlgebraOpenImageQuotientMap C hC hForm psi hpsi hfopen i)

/--
The open-image stage ring homomorphism sends generators according to the finite-stage Fox
coordinate formula.
-/
@[simp]
theorem zcCompletedGroupAlgebraOpenImageStageRingHom_of
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (i : ZCCompletedGroupAlgebraIndex C G)
    (q : CompletedGroupAlgebraQuotientInClass G C i.2) :
    zcCompletedGroupAlgebraOpenImageStageRingHom C hC hForm psi hpsi hfopen i
        (MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus)
          (CompletedGroupAlgebraQuotientInClass G C i.2) q) =
      MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus)
        (CompletedGroupAlgebraQuotientInClass H C
          (zcCompletedGroupAlgebraOpenImageTargetIndex C hForm psi hpsi hfopen i).2)
        (zcCompletedGroupAlgebraOpenImageQuotientMap
          C hC hForm psi hpsi hfopen i q) := by
  simp only [zcCompletedGroupAlgebraOpenImageStageRingHom, MonoidAlgebra.of_apply]
  exact MonoidAlgebra.mapDomain_single

/-- The finite-stage source-to-open-image group-algebra map is surjective. -/
theorem zcCompletedGroupAlgebraOpenImageStageRingHom_surjective
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (i : ZCCompletedGroupAlgebraIndex C G) :
    Function.Surjective
      (zcCompletedGroupAlgebraOpenImageStageRingHom
        C hC hForm psi hpsi hfopen i) := by
  intro y
  change
    MonoidAlgebra (ModNCompletedCoeff i.1.modulus)
      (CompletedGroupAlgebraQuotientInClass H C
        (zcCompletedGroupAlgebraOpenImageIndexInClass C hForm psi hpsi hfopen i)) at y
  rcases
      Finsupp.mapDomain_surjective (M := ModNCompletedCoeff i.1.modulus)
        (zcCompletedGroupAlgebraOpenImageQuotientMap_surjective
          C hC hForm psi hpsi hfopen i) y.coeff with
    ⟨x, hx⟩
  refine ⟨MonoidAlgebra.ofCoeff x, ?_⟩
  change MonoidAlgebra.mapDomain
    (zcCompletedGroupAlgebraOpenImageQuotientMap
      C hC hForm psi hpsi hfopen i) (MonoidAlgebra.ofCoeff x) = y
  apply MonoidAlgebra.coeff_injective
  simpa [MonoidAlgebra.mapDomain] using hx

/--
Source-stage elements in the kernel of the open-image stage map multiply the finite augmentation
stage into the finite kernel-product denominator.
-/
theorem zcCompletedGroupAlgebraOpenImageStageRingHom_ker_smul_mem
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (i : ZCCompletedGroupAlgebraIndex C G)
    (k : ZCCompletedGroupAlgebraStage C G i)
    (hk : k ∈ RingHom.ker
      (zcCompletedGroupAlgebraOpenImageStageRingHom
        C hC hForm psi hpsi hfopen i))
    (s : zcCompletedGroupAlgebraStageAugmentationIdeal C G i) :
    k • s ∈
      zcCompletedGroupAlgebraOpenImageKernelAugmentationIdealMulStageStandard
        C hC hForm psi hpsi hfopen i := by
  let f := zcCompletedGroupAlgebraOpenImageQuotientMap
    C hC hForm psi hpsi hfopen i
  let T :=
    zcCompletedGroupAlgebraOpenImageKernelAugmentationIdealMulStageStandard
      C hC hForm psi hpsi hfopen i
  have hkIdeal :
      k ∈ groupAlgebraMapDomainKernelAugmentationIdeal
        (R := ModNCompletedCoeff i.1.modulus) f := by
    have hk' :
        k ∈ RingHom.ker
          (MonoidAlgebra.mapDomainRingHom
            (ModNCompletedCoeff i.1.modulus) f) := by
      change MonoidAlgebra.mapDomain f k = 0 at hk
      exact hk
    rwa [groupAlgebraMapDomainRingHom_ker_eq_kernelAugmentationIdeal_of_surjective
      (R := ModNCompletedCoeff i.1.modulus) f
      (zcCompletedGroupAlgebraOpenImageQuotientMap_surjective
        C hC hForm psi hpsi hfopen i)] at hk'
  change k • s ∈ T
  rw [groupAlgebraMapDomainKernelAugmentationIdeal] at hkIdeal
  refine Submodule.span_induction
    (p := fun k _ => k • s ∈ T) ?hgen ?hzero ?hadd ?hsmul hkIdeal
  · rintro _ ⟨q, rfl⟩
    exact
      zcCompletedGAOpenImageKernelAugmentationIdealMulStageStandard_generator_mem
        C hC hForm psi hpsi hfopen i q s
  · simp only [zero_smul, zero_mem]
  · intro a b _ _ ha hb
    simpa [add_smul] using T.add_mem ha hb
  · intro a b _ hb
    simpa [mul_smul] using T.smul_mem a hb

/-- Source-stage kernels act trivially on the closed finite augmentation quotient. -/
theorem kernelAugmentationIdealClosedStageQuotient_openImageStageRingHom_ker_smul_eq_zero
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (i : ZCCompletedGroupAlgebraIndex C G)
    (k : ZCCompletedGroupAlgebraStage C G i)
    (hk : k ∈ RingHom.ker
      (zcCompletedGroupAlgebraOpenImageStageRingHom
        C hC hForm psi hpsi hfopen i))
    (x : KernelAugmentationIdealClosedStageQuotient C hC hForm psi hpsi hfopen i) :
    k • x = 0 := by
  let T :=
    zcCompletedGroupAlgebraOpenImageKernelAugmentationIdealMulStageStandard
      C hC hForm psi hpsi hfopen i
  refine Submodule.Quotient.induction_on (p := T) x ?_
  intro s
  apply (Submodule.Quotient.mk_eq_zero (p := T)).2
  exact
    zcCompletedGroupAlgebraOpenImageStageRingHom_ker_smul_mem
      C hC hForm psi hpsi hfopen i k hk s

/--
The finite closed augmentation quotient as a module over the matching open-image target
group-algebra stage.
-/
@[implicit_reducible]
def kernelAugmentationIdealClosedStageQuotientTargetStageModule
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (i : ZCCompletedGroupAlgebraIndex C G) :
    Module
      (ZCCompletedGroupAlgebraStage C H
        (zcCompletedGroupAlgebraOpenImageTargetIndex C hForm psi hpsi hfopen i))
      (KernelAugmentationIdealClosedStageQuotient C hC hForm psi hpsi hfopen i) := by
  let φ := zcCompletedGroupAlgebraOpenImageStageRingHom
    C hC hForm psi hpsi hfopen i
  let hφ := zcCompletedGroupAlgebraOpenImageStageRingHom_surjective
    C hC hForm psi hpsi hfopen i
  letI : SMul
      (ZCCompletedGroupAlgebraStage C H
        (zcCompletedGroupAlgebraOpenImageTargetIndex C hForm psi hpsi hfopen i))
      (KernelAugmentationIdealClosedStageQuotient C hC hForm psi hpsi hfopen i) :=
    ⟨fun a x => Function.surjInv hφ a • x⟩
  refine hφ.moduleLeft φ ?_
  intro a x
  change Function.surjInv hφ (φ a) • x = a • x
  have hdiff : Function.surjInv hφ (φ a) - a ∈ RingHom.ker φ := by
    rw [RingHom.mem_ker, map_sub, Function.surjInv_eq hφ, sub_self]
  have hzero :=
    kernelAugmentationIdealClosedStageQuotient_openImageStageRingHom_ker_smul_eq_zero
      C hC hForm psi hpsi hfopen i
      (Function.surjInv hφ (φ a) - a) hdiff x
  rw [sub_smul] at hzero
  exact sub_eq_zero.mp hzero

/-- The stage quotient target module map is compatible with scalar multiplication. -/
theorem kernelAugmentationIdealClosedStageQuotientTargetStageModule_map_smul
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (i : ZCCompletedGroupAlgebraIndex C G)
    (a : ZCCompletedGroupAlgebraStage C G i)
    (x : KernelAugmentationIdealClosedStageQuotient C hC hForm psi hpsi hfopen i) :
    letI : Module
        (ZCCompletedGroupAlgebraStage C H
          (zcCompletedGroupAlgebraOpenImageTargetIndex C hForm psi hpsi hfopen i))
        (KernelAugmentationIdealClosedStageQuotient C hC hForm psi hpsi hfopen i) :=
      kernelAugmentationIdealClosedStageQuotientTargetStageModule
        C hC hForm psi hpsi hfopen i
    zcCompletedGroupAlgebraOpenImageStageRingHom C hC hForm psi hpsi hfopen i a • x =
      a • x := by
  let φ := zcCompletedGroupAlgebraOpenImageStageRingHom
    C hC hForm psi hpsi hfopen i
  let hφ := zcCompletedGroupAlgebraOpenImageStageRingHom_surjective
    C hC hForm psi hpsi hfopen i
  let : Module
      (ZCCompletedGroupAlgebraStage C H
        (zcCompletedGroupAlgebraOpenImageTargetIndex C hForm psi hpsi hfopen i))
      (KernelAugmentationIdealClosedStageQuotient C hC hForm psi hpsi hfopen i) :=
    kernelAugmentationIdealClosedStageQuotientTargetStageModule
      C hC hForm psi hpsi hfopen i
  change Function.surjInv hφ (φ a) • x = a • x
  have hdiff : Function.surjInv hφ (φ a) - a ∈ RingHom.ker φ := by
    rw [RingHom.mem_ker, map_sub, Function.surjInv_eq hφ, sub_self]
  have hzero :=
    kernelAugmentationIdealClosedStageQuotient_openImageStageRingHom_ker_smul_eq_zero
      C hC hForm psi hpsi hfopen i
      (Function.surjInv hφ (φ a) - a) hdiff x
  rw [sub_smul] at hzero
  exact sub_eq_zero.mp hzero

/--
The finite source quotient paired with the open-image target stage for a source group-algebra
coordinate.
-/
@[implicit_reducible]
def zcCompletedDifferentialModuleOpenImageIndex
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (i : ZCCompletedGroupAlgebraIndex C G) :
    ZCCompletedDifferentialModuleIndex C psi.toMonoidHom where
  source := OrderDual.ofDual i.2
  target := zcCompletedGroupAlgebraOpenImageTargetIndex C hForm psi hpsi hfopen i
  compatible := by
    intro g hg
    change psi g ∈
      ((((OrderDual.ofDual
        (zcCompletedGroupAlgebraOpenImageTargetIndex C hForm psi hpsi hfopen i).2).1 :
          OpenNormalSubgroup H) : Subgroup H))
    exact ⟨g, hg, rfl⟩

/--
The open-image stage condition for the \(\mathbb{Z}_C\)-completed differential module is
equivalent to the finite-stage coordinate condition.
-/
@[simp 900]
theorem zcCompletedDifferentialModuleOpenImageIndex_stageScalar
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (i : ZCCompletedGroupAlgebraIndex C G)
    (q : zcCompletedDifferentialModuleStageSource C psi.toMonoidHom
      (zcCompletedDifferentialModuleOpenImageIndex C hForm psi hpsi hfopen i)) :
    zcCompletedDifferentialModuleStageScalar C psi.toMonoidHom
        (zcCompletedDifferentialModuleOpenImageIndex C hForm psi hpsi hfopen i) q =
      zcCompletedGroupAlgebraOpenImageStageRingHom C hC hForm psi hpsi hfopen i
        (MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus)
          (CompletedGroupAlgebraQuotientInClass G C i.2) q) := by
  refine QuotientGroup.induction_on q ?_
  intro g
  rw [zcCompletedDifferentialModuleStageScalar_coe]
  have hq :=
    zcCompletedGroupAlgebraOpenImageQuotientMap_mk
      C hC hForm psi hpsi hfopen i g
  change
    zcCompletedGroupAlgebraOpenImageQuotientMap C hC hForm psi hpsi hfopen i
        (QuotientGroup.mk g :
          CompletedGroupAlgebraQuotientInClass G C i.2) =
      (QuotientGroup.mk (psi g) :
        CompletedGroupAlgebraQuotientInClass H C
          (zcCompletedGroupAlgebraOpenImageTargetIndex
            C hForm psi hpsi hfopen i).2) at hq
  have hof :=
    zcCompletedGroupAlgebraOpenImageStageRingHom_of
      C hC hForm psi hpsi hfopen i
        (QuotientGroup.mk g : CompletedGroupAlgebraQuotientInClass G C i.2)
  change
    MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus)
        (CompletedGroupAlgebraQuotientInClass H C
          (zcCompletedGroupAlgebraOpenImageTargetIndex
            C hForm psi hpsi hfopen i).2)
        (QuotientGroup.mk (psi g)) =
      zcCompletedGroupAlgebraOpenImageStageRingHom C hC hForm psi hpsi hfopen i
        (MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus)
          (CompletedGroupAlgebraQuotientInClass G C i.2)
          (QuotientGroup.mk g))
  exact Eq.trans
    (congrArg
      (MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus)
        (CompletedGroupAlgebraQuotientInClass H C
          (zcCompletedGroupAlgebraOpenImageTargetIndex
            C hForm psi hpsi hfopen i).2))
      hq).symm
    hof.symm

/-- The finite source-boundary coordinate over the matching open-image target stage. -/
def kernelAugmentationIdealClosedStageQuotientBoundary
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (i : ZCCompletedGroupAlgebraIndex C G) :
    let j := zcCompletedDifferentialModuleOpenImageIndex C hForm psi hpsi hfopen i
    letI : Module (zcCompletedDifferentialModuleStageRing C psi.toMonoidHom j)
        (KernelAugmentationIdealClosedStageQuotient C hC hForm psi hpsi hfopen i) :=
      kernelAugmentationIdealClosedStageQuotientTargetStageModule
        C hC hForm psi hpsi hfopen i
    ScalarCrossedHom
      (zcCompletedDifferentialModuleStageScalar C psi.toMonoidHom j)
      (KernelAugmentationIdealClosedStageQuotient C hC hForm psi hpsi hfopen i) := by
  let j := zcCompletedDifferentialModuleOpenImageIndex C hForm psi hpsi hfopen i
  let T :=
    zcCompletedGroupAlgebraOpenImageKernelAugmentationIdealMulStageStandard
      C hC hForm psi hpsi hfopen i
  letI : Module (zcCompletedDifferentialModuleStageRing C psi.toMonoidHom j)
      (KernelAugmentationIdealClosedStageQuotient C hC hForm psi hpsi hfopen i) :=
    kernelAugmentationIdealClosedStageQuotientTargetStageModule
      C hC hForm psi hpsi hfopen i
  refine
    { toFun := fun q =>
        Submodule.Quotient.mk
          (p := zcCompletedGroupAlgebraOpenImageKernelAugmentationIdealMulStageStandard
            C hC hForm psi hpsi hfopen i)
          (zcCompletedGroupAlgebraStageAugmentationGeneratorSubtype C G i q)
      map_mul' := ?_ }
  intro q r
  rw [scalarCrossedAction_apply]
  rw [zcCompletedDifferentialModuleOpenImageIndex_stageScalar
    (C := C) (hC := hC) (hForm := hForm) (psi := psi)
    (hpsi := hpsi) (hfopen := hfopen) (i := i)]
  rw [kernelAugmentationIdealClosedStageQuotientTargetStageModule_map_smul
    (C := C) (hC := hC) (hForm := hForm) (psi := psi)
    (hpsi := hpsi) (hfopen := hfopen) (i := i)
    (a := MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus)
      (CompletedGroupAlgebraQuotientInClass G C i.2) q)
    (x := Submodule.Quotient.mk
      (p := zcCompletedGroupAlgebraOpenImageKernelAugmentationIdealMulStageStandard
        C hC hForm psi hpsi hfopen i)
      (zcCompletedGroupAlgebraStageAugmentationGeneratorSubtype C G i r))]
  change
    Submodule.Quotient.mk (p := T)
        (zcCompletedGroupAlgebraStageAugmentationGeneratorSubtype C G i (q * r)) =
      Submodule.Quotient.mk (p := T)
          (zcCompletedGroupAlgebraStageAugmentationGeneratorSubtype C G i q) +
        MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus)
            (CompletedGroupAlgebraQuotientInClass G C i.2) q •
          Submodule.Quotient.mk (p := T)
            (zcCompletedGroupAlgebraStageAugmentationGeneratorSubtype C G i r)
  rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_add]
  apply congrArg (fun s : zcCompletedGroupAlgebraStageAugmentationIdeal C G i =>
    Submodule.Quotient.mk (p := T) s)
  apply Subtype.ext
  change
    MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus)
        (CompletedGroupAlgebraQuotientInClass G C i.2) (q * r) - 1 =
      (MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus)
          (CompletedGroupAlgebraQuotientInClass G C i.2) q - 1) +
        MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus)
          (CompletedGroupAlgebraQuotientInClass G C i.2) q *
          (MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus)
            (CompletedGroupAlgebraQuotientInClass G C i.2) r - 1)
  change CompletedGroupAlgebraQuotientInClass G C i.2 at q r
  change
    MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus)
        (CompletedGroupAlgebraQuotientInClass G C i.2) (q * r) - 1 =
      (MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus)
          (CompletedGroupAlgebraQuotientInClass G C i.2) q - 1) +
        MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus)
          (CompletedGroupAlgebraQuotientInClass G C i.2) q *
          (MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus)
            (CompletedGroupAlgebraQuotientInClass G C i.2) r - 1)
  rw [map_mul, mul_sub, mul_one]
  abel

/-- The finite-stage lift induced by the finite closed source-boundary coordinate. -/
def kernelAugmentationIdealClosedStageQuotientBoundaryLift
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (i : ZCCompletedGroupAlgebraIndex C G) :
    let j := zcCompletedDifferentialModuleOpenImageIndex C hForm psi hpsi hfopen i
    letI : Module (zcCompletedDifferentialModuleStageRing C psi.toMonoidHom j)
        (KernelAugmentationIdealClosedStageQuotient C hC hForm psi hpsi hfopen i) :=
      kernelAugmentationIdealClosedStageQuotientTargetStageModule
        C hC hForm psi hpsi hfopen i
    CrossedDifferentialPreModule
        (zcCompletedDifferentialModuleStageRing C psi.toMonoidHom j)
        (zcCompletedDifferentialModuleStageSource C psi.toMonoidHom j) →ₗ[
      zcCompletedDifferentialModuleStageRing C psi.toMonoidHom j]
      KernelAugmentationIdealClosedStageQuotient C hC hForm psi hpsi hfopen i := by
  let j := zcCompletedDifferentialModuleOpenImageIndex C hForm psi hpsi hfopen i
  letI : Module (zcCompletedDifferentialModuleStageRing C psi.toMonoidHom j)
      (KernelAugmentationIdealClosedStageQuotient C hC hForm psi hpsi hfopen i) :=
    kernelAugmentationIdealClosedStageQuotientTargetStageModule
      C hC hForm psi hpsi hfopen i
  exact
    crossedDifferentialModuleLiftLinear
      (R := zcCompletedDifferentialModuleStageRing C psi.toMonoidHom j)
      (kernelAugmentationIdealClosedStageQuotientBoundary
        C hC hForm psi hpsi hfopen i)

/--
The boundary lift lands in the finite-stage closed augmentation quotient by the Fox-differential
kernel condition.
-/
@[simp 900]
theorem kernelAugmentationIdealClosedStageQuotientBoundaryLift_single
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (i : ZCCompletedGroupAlgebraIndex C G)
    (q : zcCompletedDifferentialModuleStageSource C psi.toMonoidHom
      (zcCompletedDifferentialModuleOpenImageIndex C hForm psi hpsi hfopen i))
    (a : zcCompletedDifferentialModuleStageRing C psi.toMonoidHom
      (zcCompletedDifferentialModuleOpenImageIndex C hForm psi hpsi hfopen i)) :
    let j := zcCompletedDifferentialModuleOpenImageIndex C hForm psi hpsi hfopen i
    letI : Module (zcCompletedDifferentialModuleStageRing C psi.toMonoidHom j)
        (KernelAugmentationIdealClosedStageQuotient C hC hForm psi hpsi hfopen i) :=
      kernelAugmentationIdealClosedStageQuotientTargetStageModule
        C hC hForm psi hpsi hfopen i
    kernelAugmentationIdealClosedStageQuotientBoundaryLift
        C hC hForm psi hpsi hfopen i (Finsupp.single q a) =
      a • kernelAugmentationIdealClosedStageQuotientBoundary
        C hC hForm psi hpsi hfopen i q := by
  let j := zcCompletedDifferentialModuleOpenImageIndex C hForm psi hpsi hfopen i
  let : Module (zcCompletedDifferentialModuleStageRing C psi.toMonoidHom j)
      (KernelAugmentationIdealClosedStageQuotient C hC hForm psi hpsi hfopen i) :=
    kernelAugmentationIdealClosedStageQuotientTargetStageModule
      C hC hForm psi hpsi hfopen i
  simp only [ContinuousMonoidHom.coe_toMonoidHom, Lean.Elab.WF.paramLet,
  kernelAugmentationIdealClosedStageQuotientBoundaryLift,
      crossedDifferentialModuleLiftLinear_single]

/--
The canonical quotient map from the algebraic kernel-product quotient to its closed finite-stage
quotient.
-/
def zcCompletedGroupAlgebraKernelAugmentationQuotientToClosedQuotient
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi) :
    KernelAugmentationIdealQuotient C psi →ₗ[ZCCompletedGroupAlgebra C G]
      KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen :=
  (zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi).mapQ
    (zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
      C hC hForm psi hpsi hfopen)
    LinearMap.id
    (by
      intro x hx
      simpa using
        zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard_le_closed
          C hC hForm psi hpsi hfopen hx)

/--
The map from the algebraic kernel-product quotient to the closed quotient sends a representative
to its closed quotient class.
-/
@[simp]
theorem zcCompletedGroupAlgebraKernelAugmentationQuotientToClosedQuotient_mk
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (x : zcCompletedGroupAlgebraStandardAugmentationIdeal C G) :
    zcCompletedGroupAlgebraKernelAugmentationQuotientToClosedQuotient
        C hC hForm psi hpsi hfopen (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk x := by
  rw [zcCompletedGroupAlgebraKernelAugmentationQuotientToClosedQuotient,
    Submodule.mapQ_apply]
  rfl

/--
The canonical map from the algebraic quotient \(I(G) / I(\ker \psi)I(G)\) to the closed
finite-stage quotient is injective exactly when the algebraic product already equals its
finite-stage closed hull.
-/
theorem zcCompletedGAKerAugQuotToClosedQuotient_inj_iff_eq_closed
    {C : ProCGroups.FiniteGroupClass.{u}}
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    {hC : ProCGroups.FiniteGroupClass.Hereditary C}
    {hForm : ProCGroups.FiniteGroupClass.Formation C}
    {psi : ContinuousMonoidHom G H} {hpsi : Function.Surjective psi}
    {hfopen : IsOpenMap psi} :
    Function.Injective
        (zcCompletedGroupAlgebraKernelAugmentationQuotientToClosedQuotient
          C hC hForm psi hpsi hfopen) ↔
      (zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi :
          Set (zcCompletedGroupAlgebraStandardAugmentationIdeal C G)) =
        (zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
          C hC hForm psi hpsi hfopen :
            Set (zcCompletedGroupAlgebraStandardAugmentationIdeal C G)) := by
  let S := zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi
  let T :=
    zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
      C hC hForm psi hpsi hfopen
  let Q :=
    zcCompletedGroupAlgebraKernelAugmentationQuotientToClosedQuotient
      C hC hForm psi hpsi hfopen
  constructor
  · intro hQ
    apply Set.Subset.antisymm
    · intro x hx
      exact zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard_le_closed
        C hC hForm psi hpsi hfopen hx
    · intro x hx
      have hmap :
          Q (Submodule.Quotient.mk (p := S) x) = 0 := by
        rw [zcCompletedGroupAlgebraKernelAugmentationQuotientToClosedQuotient_mk
          (C := C) (hC := hC) (hForm := hForm) (psi := psi)
          (hpsi := hpsi) (hfopen := hfopen) x]
        exact (Submodule.Quotient.mk_eq_zero (p := T) (x := x)).2 hx
      have hzero :
          (Submodule.Quotient.mk (p := S) x :
            KernelAugmentationIdealQuotient C psi) = 0 := by
        apply hQ
        rw [hmap, map_zero]
      exact (Submodule.Quotient.mk_eq_zero (p := S) (x := x)).1 hzero
  · intro hEq a b hxy
    revert b
    refine Submodule.Quotient.induction_on
      (p := S) a ?_
    intro x y hxy
    revert hxy
    refine Submodule.Quotient.induction_on
      (p := S) y ?_
    intro y hxy
    apply (Submodule.Quotient.eq S).2
    have hmemT : x - y ∈ T := by
      apply (Submodule.Quotient.eq T).1
      simpa [Q, zcCompletedGroupAlgebraKernelAugmentationQuotientToClosedQuotient_mk
        (C := C) (hC := hC) (hForm := hForm) (psi := psi)
        (hpsi := hpsi) (hfopen := hfopen)] using hxy
    have hEqST : (S : Set (zcCompletedGroupAlgebraStandardAugmentationIdeal C G)) = T := by
      simpa [S, T] using hEq
    have hmemTset :
        (x - y) ∈
          (T : Set (zcCompletedGroupAlgebraStandardAugmentationIdeal C G)) := hmemT
    have hmemSset :
        (x - y) ∈
          (S : Set (zcCompletedGroupAlgebraStandardAugmentationIdeal C G)) := by
      rw [hEqST]
      exact hmemTset
    exact hmemSset

/--
Closedness of \(I(\ker \psi)I(G)\) is equivalently the injectivity of the canonical map from the
algebraic source augmentation quotient to the closed finite-stage quotient.
-/
theorem isClosed_zcCompletedGAKernelAugmentationIdealMulStandard_iff_toClosedQuotient_inj
    {C : ProCGroups.FiniteGroupClass.{u}}
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    {psi : ContinuousMonoidHom G H} (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi) :
    IsClosed
        ((zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi :
          Set (zcCompletedGroupAlgebraStandardAugmentationIdeal C G))) ↔
      Function.Injective
        (zcCompletedGroupAlgebraKernelAugmentationQuotientToClosedQuotient
          C hC hForm psi hpsi hfopen) := by
  rw [isClosed_zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard_iff_eq_closed
    (C := C) (psi := psi) hC hForm hpsi hfopen]
  exact
    (zcCompletedGAKerAugQuotToClosedQuotient_inj_iff_eq_closed
      (C := C) (hC := hC) (hForm := hForm) (psi := psi)
      (hpsi := hpsi) (hfopen := hfopen)).symm

/-- The source Fox boundary, valued in the source augmentation quotient. -/
def zcCompletedGroupAlgebraSourceBoundaryToKernelAugmentationQuotient
    (psi : ContinuousMonoidHom G H) :
    ScalarCrossedHom
      (zcCompletedGroupAlgebraScalar C (MonoidHom.id G))
      (KernelAugmentationIdealQuotient C psi) :=
  (zcCompletedGroupAlgebraBoundaryToStandardAugmentationIdeal
      C G (MonoidHom.id G)).mapLinear
    (Submodule.mkQ
      (zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi))

/-- The source Fox boundary, valued in the closed source augmentation quotient. -/
def zcCompletedGroupAlgebraSourceBoundaryToKernelAugmentationClosedQuotient
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi) :
    ScalarCrossedHom
      (zcCompletedGroupAlgebraScalar C (MonoidHom.id G))
      (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
  (zcCompletedGroupAlgebraBoundaryToStandardAugmentationIdeal
      C G (MonoidHom.id G)).mapLinear
    (Submodule.mkQ
      (zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
        C hC hForm psi hpsi hfopen))

/--
The map from the algebraic source augmentation quotient to the closed quotient sends source
boundary classes to the corresponding closed source boundary classes.
-/
@[simp]
theorem zcCompletedGroupAlgebraKernelAugmentationQuotientToClosedQuotient_sourceBoundary
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi) (g : G) :
    zcCompletedGroupAlgebraKernelAugmentationQuotientToClosedQuotient
        C hC hForm psi hpsi hfopen
        (zcCompletedGroupAlgebraSourceBoundaryToKernelAugmentationQuotient C psi g) =
      zcCompletedGroupAlgebraSourceBoundaryToKernelAugmentationClosedQuotient
        C hC hForm psi hpsi hfopen g := by
  simp only [zcCompletedGroupAlgebraSourceBoundaryToKernelAugmentationQuotient,
    zcCompletedGroupAlgebraSourceBoundaryToKernelAugmentationClosedQuotient,
    ScalarCrossedHom.mapLinear_apply,
    Submodule.mkQ_apply]
  rw [
    zcCompletedGroupAlgebraKernelAugmentationQuotientToClosedQuotient_mk]

/-- The source Fox boundary into the closed source augmentation quotient is continuous. -/
theorem continuous_zcCompletedGASourceBoundaryToKerAugClosedQuot
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi) :
    Continuous
      (zcCompletedGroupAlgebraSourceBoundaryToKernelAugmentationClosedQuotient
        C hC hForm psi hpsi hfopen) := by
  have hstd :
      Continuous
        (zcCompletedGroupAlgebraBoundaryToStandardAugmentationIdeal
          C G (MonoidHom.id G)) := by
    have hval :
        Continuous (fun g : G =>
          (zcCompletedGroupAlgebraBoundaryToStandardAugmentationIdeal
            C G (MonoidHom.id G) g : ZCCompletedGroupAlgebra C G)) :=
      continuous_zcCompletedGroupAlgebraBoundary
        (C := C) (G := G) (MonoidHom.id G) continuous_id
    exact Continuous.subtype_mk hval
      (fun g =>
        (zcCompletedGroupAlgebraBoundaryToStandardAugmentationIdeal
          C G (MonoidHom.id G) g).2)
  have hq :
      Continuous (fun x : zcCompletedGroupAlgebraStandardAugmentationIdeal C G =>
        (Submodule.Quotient.mk x :
          KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen)) :=
    continuous_quotient_mk'
  exact hq.comp hstd

omit [IsTopologicalGroup H] in
/-- Products \((n-1)s\) vanish in the source augmentation quotient. -/
@[simp]
theorem zcCompletedGroupAlgebraKernelAugmentationIdealQuotient_mk_generator_smul
    (psi : ContinuousMonoidHom G H) (n : ProfiniteKernelSubgroup psi)
    (s : zcCompletedGroupAlgebraStandardAugmentationIdeal C G) :
    Submodule.Quotient.mk
        (p := zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi)
        ((zcGroupLike C G n.1 - 1) • s) = 0 := by
  apply (Submodule.Quotient.mk_eq_zero
    (p := zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi)).2
  exact zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard_generator_mem C psi n s

omit [IsTopologicalGroup H] in
/--
Source group-like actions with the same image under psi agree on the source augmentation
quotient. This is the algebraic descent statement needed before a completed target scalar action
can be installed.
-/
theorem zcCompletedGroupAlgebraKernelAugmentationQuotient_groupLike_smul_eq_of_map_eq
    (psi : ContinuousMonoidHom G H) {g₁ g₂ : G} (h : psi g₁ = psi g₂)
    (x : KernelAugmentationIdealQuotient C psi) :
    zcGroupLike C G g₁ • x = zcGroupLike C G g₂ • x := by
  refine Submodule.Quotient.induction_on
    (p := zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi) x ?_
  intro y
  apply (Submodule.Quotient.eq
    (zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi)).2
  let n : ProfiniteKernelSubgroup psi :=
    ⟨g₂⁻¹ * g₁, by
      change psi (g₂⁻¹ * g₁) = 1
      rw [map_mul, map_inv, h]
      simp only [inv_mul_cancel]⟩
  have hgen :
      (zcGroupLike C G n.1 - 1) • y ∈
        zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi :=
    zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard_generator_mem C psi n y
  have hmem :
      zcGroupLike C G g₂ • ((zcGroupLike C G n.1 - 1) • y) ∈
        zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi :=
    (zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi).smul_mem
      (zcGroupLike C G g₂) hgen
  convert hmem using 1
  apply Subtype.ext
  change zcGroupLike C G g₁ * (y : ZCCompletedGroupAlgebra C G) -
      zcGroupLike C G g₂ * (y : ZCCompletedGroupAlgebra C G) =
    zcGroupLike C G g₂ *
      ((zcGroupLike C G n.1 - 1) * (y : ZCCompletedGroupAlgebra C G))
  rw [sub_mul, one_mul, mul_sub, ← mul_assoc, ← map_mul]
  simp only [mul_inv_cancel_left, n]

omit [IsTopologicalGroup H] in
/--
The additive endomorphism of the source augmentation quotient induced by any chosen lift of a
target element.
-/
def zcCompletedGroupAlgebraKernelAugmentationQuotientTargetGroupLikeEndOfSurjective
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi) (h : H) :
    AddMonoid.End (KernelAugmentationIdealQuotient C psi) where
  toFun x := zcGroupLike C G (Function.surjInv hpsi h) • x
  map_zero' := smul_zero _
  map_add' := by
    intro x y
    rw [smul_add]

omit [IsTopologicalGroup H] in
/--
The chosen-lift target group-like endomorphism acts by scalar multiplication with the completed
group-like element of the selected source lift.
-/
@[simp]
theorem zcCompletedGAKerAugQuotTargetGroupLikeEndOfSurjective_apply
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi) (h : H)
    (x : KernelAugmentationIdealQuotient C psi) :
    zcCompletedGroupAlgebraKernelAugmentationQuotientTargetGroupLikeEndOfSurjective
        C psi hpsi h x =
      zcGroupLike C G (Function.surjInv hpsi h) • x :=
  rfl

omit [IsTopologicalGroup H] in
/--
The chosen-lift target action agrees with scalar multiplication by any source lift of the same
target element.
-/
theorem zcCompletedGAKerAugQuotTargetGroupLikeEndOfSurjective_eq_smul_of_map_eq
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi) {h : H} {g : G}
    (hg : psi g = h) (x : KernelAugmentationIdealQuotient C psi) :
    zcCompletedGroupAlgebraKernelAugmentationQuotientTargetGroupLikeEndOfSurjective
        C psi hpsi h x =
      zcGroupLike C G g • x := by
  have hlift : psi (Function.surjInv hpsi h) = psi g := by
    rw [Function.surjInv_eq hpsi h, hg]
  exact zcCompletedGroupAlgebraKernelAugmentationQuotient_groupLike_smul_eq_of_map_eq
    C psi hlift x

omit [IsTopologicalGroup H] in
/--
The chosen-lift target group-like endomorphism for the identity target element acts as the
identity.
-/
@[simp]
theorem zcCompletedGAKerAugQuotTargetGroupLikeEndOfSurjective_one_apply
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (x : KernelAugmentationIdealQuotient C psi) :
    zcCompletedGroupAlgebraKernelAugmentationQuotientTargetGroupLikeEndOfSurjective
        C psi hpsi (1 : H) x = x := by
  have hmap : psi (Function.surjInv hpsi (1 : H)) = psi (1 : G) := by
    rw [Function.surjInv_eq hpsi (1 : H), map_one]
  have hsmul :=
    zcCompletedGroupAlgebraKernelAugmentationQuotient_groupLike_smul_eq_of_map_eq
      C psi hmap x
  simpa using hsmul

omit [IsTopologicalGroup H] in
/-- The chosen-lift target group-like endomorphisms multiply pointwise on the quotient. -/
theorem zcCompletedGAKerAugQuotTargetGroupLikeEndOfSurjective_mul_apply
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi) (h₁ h₂ : H)
    (x : KernelAugmentationIdealQuotient C psi) :
    zcCompletedGroupAlgebraKernelAugmentationQuotientTargetGroupLikeEndOfSurjective
        C psi hpsi (h₁ * h₂) x =
      zcCompletedGroupAlgebraKernelAugmentationQuotientTargetGroupLikeEndOfSurjective
        C psi hpsi h₁
        (zcCompletedGroupAlgebraKernelAugmentationQuotientTargetGroupLikeEndOfSurjective
          C psi hpsi h₂ x) := by
  let s₁ : G := Function.surjInv hpsi h₁
  let s₂ : G := Function.surjInv hpsi h₂
  let s₁₂ : G := Function.surjInv hpsi (h₁ * h₂)
  have hs : psi s₁₂ = psi (s₁ * s₂) := by
    rw [map_mul]
    simp only [Function.surjInv_eq hpsi, s₁₂, s₁, s₂]
  have hsmul :=
    zcCompletedGroupAlgebraKernelAugmentationQuotient_groupLike_smul_eq_of_map_eq
      C psi hs x
  change zcGroupLike C G s₁₂ • x =
    zcGroupLike C G s₁ • (zcGroupLike C G s₂ • x)
  rw [← mul_smul]
  rw [← (zcGroupLike C G).map_mul s₁ s₂]
  exact hsmul

omit [IsTopologicalGroup H] in
/--
The descended group-like target action on the source augmentation quotient, for a surjective
\(\psi\).
-/
def zcCompletedGAKerAugQuotTargetGroupLikeActionOfSurjective
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi) :
    H →* AddMonoid.End (KernelAugmentationIdealQuotient C psi) where
  toFun h :=
    zcCompletedGroupAlgebraKernelAugmentationQuotientTargetGroupLikeEndOfSurjective
      C psi hpsi h
  map_one' := by
    refine AddMonoidHom.ext ?_
    intro x
    exact
      zcCompletedGAKerAugQuotTargetGroupLikeEndOfSurjective_one_apply
        C psi hpsi x
  map_mul' h₁ h₂ := by
    refine AddMonoidHom.ext ?_
    intro x
    change
      zcCompletedGroupAlgebraKernelAugmentationQuotientTargetGroupLikeEndOfSurjective
          C psi hpsi (h₁ * h₂) x =
        zcCompletedGroupAlgebraKernelAugmentationQuotientTargetGroupLikeEndOfSurjective
          C psi hpsi h₁
          (zcCompletedGroupAlgebraKernelAugmentationQuotientTargetGroupLikeEndOfSurjective
            C psi hpsi h₂ x)
    exact
      zcCompletedGAKerAugQuotTargetGroupLikeEndOfSurjective_mul_apply
        C psi hpsi h₁ h₂ x

omit [IsTopologicalGroup H] in
/--
The descended target group-like action for a surjective map acts through the selected source
lift.
-/
@[simp]
theorem zcCompletedGAKerAugQuotTargetGroupLikeActionOfSurjective_apply
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi) (h : H)
    (x : KernelAugmentationIdealQuotient C psi) :
    zcCompletedGAKerAugQuotTargetGroupLikeActionOfSurjective
        C psi hpsi h x =
      zcGroupLike C G (Function.surjInv hpsi h) • x :=
  rfl

omit [IsTopologicalGroup H] in
/--
Coefficients from \(\mathbb{Z}_C\) act on the source augmentation quotient through the source
completed group algebra.
-/
def zcCompletedGroupAlgebraKernelAugmentationQuotientTargetCoeffEnd
    (psi : ContinuousMonoidHom G H) (a : ZCCoeff C) :
    AddMonoid.End (KernelAugmentationIdealQuotient C psi) where
  toFun x := zcCompletedGroupAlgebraCoeffMap C G a • x
  map_zero' := smul_zero _
  map_add' := by
    intro x y
    rw [smul_add]

omit [IsTopologicalGroup H] in
/--
The target coefficient endomorphism acts on the kernel-augmentation quotient by multiplication with
the coefficient-map image of `a`.
-/
@[simp]
theorem zcCompletedGroupAlgebraKernelAugmentationQuotientTargetCoeffEnd_apply
    (psi : ContinuousMonoidHom G H) (a : ZCCoeff C)
    (x : KernelAugmentationIdealQuotient C psi) :
    zcCompletedGroupAlgebraKernelAugmentationQuotientTargetCoeffEnd C psi a x =
      zcCompletedGroupAlgebraCoeffMap C G a • x :=
  rfl

omit [IsTopologicalGroup H] in
/-- The coefficient action of \(\mathbb{Z}_C\) on the source augmentation quotient. -/
def zcCompletedGroupAlgebraKernelAugmentationQuotientTargetCoeffAction
    (psi : ContinuousMonoidHom G H) :
    ZCCoeff C →+* AddMonoid.End (KernelAugmentationIdealQuotient C psi) where
  toFun a := zcCompletedGroupAlgebraKernelAugmentationQuotientTargetCoeffEnd C psi a
  map_zero' := by
    refine AddMonoidHom.ext ?_
    intro x
    change zcCompletedGroupAlgebraCoeffMap C G (0 : ZCCoeff C) • x = 0
    rw [map_zero, zero_smul]
  map_one' := by
    refine AddMonoidHom.ext ?_
    intro x
    change zcCompletedGroupAlgebraCoeffMap C G (1 : ZCCoeff C) • x = x
    rw [map_one, one_smul]
  map_add' a b := by
    refine AddMonoidHom.ext ?_
    intro x
    change zcCompletedGroupAlgebraCoeffMap C G (a + b) • x =
      zcCompletedGroupAlgebraCoeffMap C G a • x +
        zcCompletedGroupAlgebraCoeffMap C G b • x
    rw [map_add, add_smul]
  map_mul' a b := by
    refine AddMonoidHom.ext ?_
    intro x
    change zcCompletedGroupAlgebraCoeffMap C G (a * b) • x =
      zcCompletedGroupAlgebraCoeffMap C G a •
        (zcCompletedGroupAlgebraCoeffMap C G b • x)
    rw [map_mul, mul_smul]

omit [IsTopologicalGroup H] in
/--
Coefficient elements are central with respect to group-like elements in \(\mathbb{Z}_C\llbracket
G\rrbracket\).
-/
theorem zcCompletedGroupAlgebraCoeffMap_mul_groupLike_eq_groupLike_mul_coeffMap
    (a : ZCCoeff C) (g : G) :
    zcCompletedGroupAlgebraCoeffMap C G a * zcGroupLike C G g =
      zcGroupLike C G g * zcCompletedGroupAlgebraCoeffMap C G a := by
  apply Subtype.ext
  funext i
  let : Fact (0 < i.1.modulus) := ⟨i.1.positive⟩
  change
    zcCompletedGroupAlgebraProjection C G i
        (zcCompletedGroupAlgebraCoeffMap C G a * zcGroupLike C G g) =
      zcCompletedGroupAlgebraProjection C G i
        (zcGroupLike C G g * zcCompletedGroupAlgebraCoeffMap C G a)
  rw [zcCompletedGroupAlgebraProjection_mul, zcCompletedGroupAlgebraProjection_coeffMap,
    zcCompletedGroupAlgebraProjection_groupLike]
  exact MonoidAlgebra.single_one_comm _ _

omit [IsTopologicalGroup H] in
/--
The algebraic target group algebra \(\mathbb{Z}_C[H]\) acts on the source augmentation quotient.
This is the dense algebraic part of the eventual completed \(\mathbb{Z}_C\llbracket
H\rrbracket\) scalar action.
-/
def kerAugQuotTargetGAActionOfSurj
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi) :
    MonoidAlgebra (ZCCoeff C) H →+*
      AddMonoid.End (KernelAugmentationIdealQuotient C psi) :=
  MonoidAlgebra.liftNCRingHom
    (zcCompletedGroupAlgebraKernelAugmentationQuotientTargetCoeffAction C psi)
    (zcCompletedGAKerAugQuotTargetGroupLikeActionOfSurjective
      C psi hpsi)
    (by
      intro a h
      rw [Commute]
      apply AddMonoidHom.ext
      intro x
      change
        zcCompletedGroupAlgebraCoeffMap C G a •
            (zcGroupLike C G (Function.surjInv hpsi h) • x) =
          zcGroupLike C G (Function.surjInv hpsi h) •
            (zcCompletedGroupAlgebraCoeffMap C G a • x)
      rw [← mul_smul, ← mul_smul,
        zcCompletedGroupAlgebraCoeffMap_mul_groupLike_eq_groupLike_mul_coeffMap])

omit [IsTopologicalGroup H] in
/--
The induced target group-algebra action evaluates on group-like elements by lifting through the
chosen surjection.
-/
@[simp]
theorem kerAugQuotTargetGAActionOfSurj_of
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi) (h : H) :
    kerAugQuotTargetGAActionOfSurj
        C psi hpsi (MonoidAlgebra.of (ZCCoeff C) H h) =
      zcCompletedGAKerAugQuotTargetGroupLikeActionOfSurjective
        C psi hpsi h := by
  apply AddMonoidHom.ext
  intro x
  simp only [kerAugQuotTargetGAActionOfSurj, MonoidAlgebra.of_apply,
      MonoidAlgebra.liftNCRingHom_single,
  map_one, one_mul]

omit [IsTopologicalGroup H] in
/-- The descended algebraic `Z_C[H]`-module structure on the source augmentation quotient. -/
noncomputable abbrev
    zcCompletedGroupAlgebraKernelAugmentationQuotientTargetGroupAlgebraModuleOfSurjective
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi) :
    Module (MonoidAlgebra (ZCCoeff C) H) (KernelAugmentationIdealQuotient C psi) :=
  Module.compHom (KernelAugmentationIdealQuotient C psi)
    (kerAugQuotTargetGAActionOfSurj
      C psi hpsi)

omit [IsTopologicalGroup H] in
/-- The target group-algebra module structure acts by the induced quotient action. -/
@[simp]
theorem kerAugQuotTargetGAModuleOfSurj_smul
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (a : MonoidAlgebra (ZCCoeff C) H) (x : KernelAugmentationIdealQuotient C psi) :
    letI : Module (MonoidAlgebra (ZCCoeff C) H) (KernelAugmentationIdealQuotient C psi) :=
      zcCompletedGroupAlgebraKernelAugmentationQuotientTargetGroupAlgebraModuleOfSurjective
        C psi hpsi
    a • x =
      kerAugQuotTargetGAActionOfSurj
        C psi hpsi a x := by
  rfl

omit [IsTopologicalGroup H] in
/-- A group-like basis element acts on the target quotient module by the induced quotient action. -/
@[simp]
theorem kerAugQuotTargetGAModuleOfSurj_of_smul
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi) (h : H)
    (x : KernelAugmentationIdealQuotient C psi) :
    letI : Module (MonoidAlgebra (ZCCoeff C) H) (KernelAugmentationIdealQuotient C psi) :=
      zcCompletedGroupAlgebraKernelAugmentationQuotientTargetGroupAlgebraModuleOfSurjective
        C psi hpsi
    MonoidAlgebra.of (ZCCoeff C) H h • x =
      zcGroupLike C G (Function.surjInv hpsi h) • x := by
  let : Module (MonoidAlgebra (ZCCoeff C) H) (KernelAugmentationIdealQuotient C psi) :=
    zcCompletedGroupAlgebraKernelAugmentationQuotientTargetGroupAlgebraModuleOfSurjective
      C psi hpsi
  change
    kerAugQuotTargetGAActionOfSurj
        C psi hpsi (MonoidAlgebra.of (ZCCoeff C) H h) x =
      zcGroupLike C G (Function.surjInv hpsi h) • x
  rw [kerAugQuotTargetGAActionOfSurj_of]
  rfl

omit [IsTopologicalGroup H] in
/--
The algebraic target group-algebra action by \([h]\) agrees with source multiplication by any
lift of \(h\).
-/
theorem kerAugQuotTargetGAModuleOfSurj_of_smul_eq_source_groupLike_smul
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi) {h : H} {g : G}
    (hg : psi g = h) (x : KernelAugmentationIdealQuotient C psi) :
    letI : Module (MonoidAlgebra (ZCCoeff C) H) (KernelAugmentationIdealQuotient C psi) :=
      zcCompletedGroupAlgebraKernelAugmentationQuotientTargetGroupAlgebraModuleOfSurjective
        C psi hpsi
    MonoidAlgebra.of (ZCCoeff C) H h • x = zcGroupLike C G g • x := by
  let : Module (MonoidAlgebra (ZCCoeff C) H) (KernelAugmentationIdealQuotient C psi) :=
    zcCompletedGroupAlgebraKernelAugmentationQuotientTargetGroupAlgebraModuleOfSurjective
      C psi hpsi
  rw [kerAugQuotTargetGAModuleOfSurj_of_smul]
  have hlift : psi (Function.surjInv hpsi h) = psi g := by
    rw [Function.surjInv_eq hpsi h, hg]
  exact zcCompletedGroupAlgebraKernelAugmentationQuotient_groupLike_smul_eq_of_map_eq
    C psi hlift x

omit [IsTopologicalGroup H] in
/--
The source boundary is a crossed differential for the descended algebraic target group-algebra
coefficients.
-/
def zcCompletedGASourceBoundaryToKerAugQuotTargetGACrossedHomOfSurjective
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi) :
    letI : Module (MonoidAlgebra (ZCCoeff C) H) (KernelAugmentationIdealQuotient C psi) :=
      zcCompletedGroupAlgebraKernelAugmentationQuotientTargetGroupAlgebraModuleOfSurjective
        C psi hpsi
    ScalarCrossedHom
      ((MonoidAlgebra.of (ZCCoeff C) H).comp psi.toMonoidHom)
      (KernelAugmentationIdealQuotient C psi) := by
  letI : Module (MonoidAlgebra (ZCCoeff C) H) (KernelAugmentationIdealQuotient C psi) :=
    zcCompletedGroupAlgebraKernelAugmentationQuotientTargetGroupAlgebraModuleOfSurjective
      C psi hpsi
  exact
    { toFun := zcCompletedGroupAlgebraSourceBoundaryToKernelAugmentationQuotient C psi
      map_mul' := by
        intro g h
        rw [(zcCompletedGroupAlgebraSourceBoundaryToKernelAugmentationQuotient
          C psi).map_mul]
        congr 1
        exact
          (kerAugQuotTargetGAModuleOfSurj_of_smul_eq_source_groupLike_smul
            C psi hpsi (h := psi g) (g := g) rfl
            (zcCompletedGroupAlgebraSourceBoundaryToKernelAugmentationQuotient
              C psi h)).symm }

omit [IsTopologicalGroup H] in
/--
The algebraic target-coefficient universal differential module maps to the source augmentation
quotient by \(dg \mapsto\) \([g]-1\).
-/
def zcAlgebraicDifferentialModuleToKernelAugmentationQuotientOfSurjective
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi) :
    letI : Module (MonoidAlgebra (ZCCoeff C) H) (KernelAugmentationIdealQuotient C psi) :=
      zcCompletedGroupAlgebraKernelAugmentationQuotientTargetGroupAlgebraModuleOfSurjective
        C psi hpsi
    CrossedDifferentialModule ((MonoidAlgebra.of (ZCCoeff C) H).comp psi.toMonoidHom) →ₗ[
      MonoidAlgebra (ZCCoeff C) H] KernelAugmentationIdealQuotient C psi := by
  letI : Module (MonoidAlgebra (ZCCoeff C) H) (KernelAugmentationIdealQuotient C psi) :=
    zcCompletedGroupAlgebraKernelAugmentationQuotientTargetGroupAlgebraModuleOfSurjective
      C psi hpsi
  exact
    crossedHomModuleLift
      (A := KernelAugmentationIdealQuotient C psi)
      ((MonoidAlgebra.of (ZCCoeff C) H).comp psi.toMonoidHom)
      (zcCompletedGASourceBoundaryToKerAugQuotTargetGACrossedHomOfSurjective
        C psi hpsi)

omit [IsTopologicalGroup H] in
/--
The algebraic differential module maps universally to the kernel-augmentation quotient in the
surjective case.
-/
@[simp]
theorem zcAlgebraicDifferentialModuleToKernelAugmentationQuotientOfSurjective_universal
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi) (g : G) :
    letI : Module (MonoidAlgebra (ZCCoeff C) H) (KernelAugmentationIdealQuotient C psi) :=
      zcCompletedGroupAlgebraKernelAugmentationQuotientTargetGroupAlgebraModuleOfSurjective
        C psi hpsi
    zcAlgebraicDifferentialModuleToKernelAugmentationQuotientOfSurjective C psi hpsi
        (universalCrossedDifferential
          ((MonoidAlgebra.of (ZCCoeff C) H).comp psi.toMonoidHom) g) =
      zcCompletedGroupAlgebraSourceBoundaryToKernelAugmentationQuotient C psi g := by
  let : Module (MonoidAlgebra (ZCCoeff C) H) (KernelAugmentationIdealQuotient C psi) :=
    zcCompletedGroupAlgebraKernelAugmentationQuotientTargetGroupAlgebraModuleOfSurjective
      C psi hpsi
  exact
    crossedHomModuleLift_universal
      (A := KernelAugmentationIdealQuotient C psi)
      ((MonoidAlgebra.of (ZCCoeff C) H).comp psi.toMonoidHom)
      (zcCompletedGASourceBoundaryToKerAugQuotTargetGACrossedHomOfSurjective
        C psi hpsi) g

omit [IsTopologicalGroup H] in
/--
Multiplying an algebraic kernel-augmentation element by a standard augmentation element lands in
the algebraic product \(I(\ker \psi)I(G)\). The remaining completed-target descent problem is
exactly replacing the first hypothesis by membership in the completed map kernel.
-/
theorem mulStandard_mul_mem_of_mem_kernelAugIdealMul
    (psi : ContinuousMonoidHom G H)
    {k : ZCCompletedGroupAlgebra C G}
    (hk : k ∈ zcCompletedGroupAlgebraKernelAugmentationIdealMul C psi)
    (y : zcCompletedGroupAlgebraStandardAugmentationIdeal C G) :
    (⟨k * (y : ZCCompletedGroupAlgebra C G),
      (zcCompletedGroupAlgebraStandardAugmentationIdeal C G).mul_mem_left k y.2⟩ :
        zcCompletedGroupAlgebraStandardAugmentationIdeal C G) ∈
      zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi := by
  let S := zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi
  refine Submodule.span_induction
    (p := fun k _ =>
      ∀ y : zcCompletedGroupAlgebraStandardAugmentationIdeal C G,
        (⟨k * (y : ZCCompletedGroupAlgebra C G),
          (zcCompletedGroupAlgebraStandardAugmentationIdeal C G).mul_mem_left k y.2⟩ :
            zcCompletedGroupAlgebraStandardAugmentationIdeal C G) ∈ S) ?_ ?_ ?_ ?_ hk y
  · rintro _ ⟨n, rfl⟩ y
    exact zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard_generator_mem C psi n y
  · intro y
    convert S.zero_mem using 1
    ext
    simp only [zero_mul, zcCompletedGroupAlgebraProjection_zero, ZeroMemClass.coe_zero]
  · intro a b _ _ ha hb y
    have hsum : (⟨a * (y : ZCCompletedGroupAlgebra C G),
          (zcCompletedGroupAlgebraStandardAugmentationIdeal C G).mul_mem_left a y.2⟩ :
            zcCompletedGroupAlgebraStandardAugmentationIdeal C G) +
        (⟨b * (y : ZCCompletedGroupAlgebra C G),
          (zcCompletedGroupAlgebraStandardAugmentationIdeal C G).mul_mem_left b y.2⟩ :
            zcCompletedGroupAlgebraStandardAugmentationIdeal C G) ∈ S :=
      S.add_mem (ha y) (hb y)
    convert hsum using 1
    ext
    simp only [add_mul, zcCompletedGroupAlgebraProjection_add,
        zcCompletedGroupAlgebraProjection_mul,
  MonoidAlgebra.coeff_add, AddMemClass.mk_add_mk]
  · intro a b _ hb y
    have hsmul : a •
        (⟨b * (y : ZCCompletedGroupAlgebra C G),
          (zcCompletedGroupAlgebraStandardAugmentationIdeal C G).mul_mem_left b y.2⟩ :
            zcCompletedGroupAlgebraStandardAugmentationIdeal C G) ∈ S :=
      S.smul_mem a (hb y)
    convert hsmul using 1
    ext
    simp only [smul_eq_mul, mul_assoc, zcCompletedGroupAlgebraProjection_mul, SetLike.mk_smul_mk]

/--
Under the finite-stage open-map kernel theorem, a completed-kernel scalar times a standard
augmentation element lies in the closure of the algebraic product; no closedness hypothesis is
assumed.
-/
theorem zcCompletedGAKernelAugmentationIdealMulStandard_mul_mem_closure_of_mem_ker_map
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    {k : ZCCompletedGroupAlgebra C G}
    (hk : k ∈ RingHom.ker (zcCompletedGroupAlgebraMap C hC psi))
    (y : zcCompletedGroupAlgebraStandardAugmentationIdeal C G) :
    (⟨k * (y : ZCCompletedGroupAlgebra C G),
      (zcCompletedGroupAlgebraStandardAugmentationIdeal C G).mul_mem_left k y.2⟩ :
        zcCompletedGroupAlgebraStandardAugmentationIdeal C G) ∈
      closure
        ((zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi :
          Set (zcCompletedGroupAlgebraStandardAugmentationIdeal C G))) := by
  let R := ZCCompletedGroupAlgebra C G
  let I := zcCompletedGroupAlgebraKernelAugmentationIdealMul C psi
  let S := zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi
  let f : R → zcCompletedGroupAlgebraStandardAugmentationIdeal C G := fun a =>
    ⟨a * (y : R), (zcCompletedGroupAlgebraStandardAugmentationIdeal C G).mul_mem_left a y.2⟩
  have hf : Continuous f := by
    have hmul : Continuous (fun a : R => a * (y : R)) :=
      continuous_id.mul continuous_const
    exact Continuous.subtype_mk hmul
      (fun a => (zcCompletedGroupAlgebraStandardAugmentationIdeal C G).mul_mem_left a y.2)
  have hkClosure : k ∈ closure ((I : Set R)) := by
    have hEq :=
      closure_zcCompletedGAKernelAugmentationIdealMul_eq_ker_map_of_openMap_surj
        C hC hForm psi hpsi hfopen
    rw [hEq]
    exact hk
  have hmemImage : f k ∈ f '' closure ((I : Set R)) := ⟨k, hkClosure, rfl⟩
  have hclosureImage : f k ∈ closure (f '' ((I : Set R))) :=
    image_closure_subset_closure_image hf hmemImage
  have himage_subset : f '' ((I : Set R)) ⊆ (S : Set _) := by
    rintro _ ⟨a, ha, rfl⟩
    exact
      mulStandard_mul_mem_of_mem_kernelAugIdealMul
        C psi ha y
  exact closure_mono himage_subset hclosureImage

/--
If \(k\) lies in the kernel of the completed group-algebra map, then \(k y\) lies in the
finite-stage closed hull of \(I(\ker\psi)I(G)\) for every standard augmentation element \(y\).
-/
theorem zcCompletedGAKernelAugmentationIdealMulStandard_mul_mem_closed_of_mem_ker_map
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    {k : ZCCompletedGroupAlgebra C G}
    (hk : k ∈ RingHom.ker (zcCompletedGroupAlgebraMap C hC psi))
    (y : zcCompletedGroupAlgebraStandardAugmentationIdeal C G) :
    (⟨k * (y : ZCCompletedGroupAlgebra C G),
      (zcCompletedGroupAlgebraStandardAugmentationIdeal C G).mul_mem_left k y.2⟩ :
        zcCompletedGroupAlgebraStandardAugmentationIdeal C G) ∈
      zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
        C hC hForm psi hpsi hfopen := by
  have hclosure :=
    zcCompletedGAKernelAugmentationIdealMulStandard_mul_mem_closure_of_mem_ker_map
      C hC hForm psi hpsi hfopen hk y
  rwa [closure_zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard_eq_closed
    C hC hForm psi hpsi hfopen] at hclosure

/--
Completed-kernel scalars send the standard source augmentation ideal into the finite-stage
closed hull of \(I(\ker \psi)I(G)\).
-/
theorem zcCompletedGAKernelAugmentationIdealMulStandard_kernelMulStandard_le_closed
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi) :
    ∀ k : ZCCompletedGroupAlgebra C G,
      k ∈ RingHom.ker (zcCompletedGroupAlgebraMap C hC psi) →
      ∀ y : zcCompletedGroupAlgebraStandardAugmentationIdeal C G,
        (⟨k * (y : ZCCompletedGroupAlgebra C G),
          (zcCompletedGroupAlgebraStandardAugmentationIdeal C G).mul_mem_left k y.2⟩ :
            zcCompletedGroupAlgebraStandardAugmentationIdeal C G) ∈
          zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
            C hC hForm psi hpsi hfopen := by
  intro k hk y
  exact
    zcCompletedGAKernelAugmentationIdealMulStandard_mul_mem_closed_of_mem_ker_map
      C hC hForm psi hpsi hfopen hk y

/--
If the algebraic product \(I(\ker \psi)I(G)\) is closed in the standard augmentation ideal, then
completed-kernel scalars send standard augmentation elements into that product.
-/
theorem zcCompletedGAKernelAugmentationIdealMulStandard_kernelMulStandard_le_of_isClosed
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (hclosed :
      IsClosed
        ((zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi :
          Set (zcCompletedGroupAlgebraStandardAugmentationIdeal C G)))) :
    ∀ k : ZCCompletedGroupAlgebra C G,
      k ∈ RingHom.ker (zcCompletedGroupAlgebraMap C hC psi) →
      ∀ y : zcCompletedGroupAlgebraStandardAugmentationIdeal C G,
        (⟨k * (y : ZCCompletedGroupAlgebra C G),
          (zcCompletedGroupAlgebraStandardAugmentationIdeal C G).mul_mem_left k y.2⟩ :
            zcCompletedGroupAlgebraStandardAugmentationIdeal C G) ∈
          zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi := by
  intro k hk y
  have hclosure :=
    zcCompletedGAKernelAugmentationIdealMulStandard_mul_mem_closure_of_mem_ker_map
      C hC hForm psi hpsi hfopen hk y
  rwa [hclosed.closure_eq] at hclosure

/--
If the canonical map from the algebraic source augmentation quotient to the closed finite-stage
quotient is injective, then completed-kernel scalars multiply standard augmentation elements
into the algebraic product \(I(\ker \psi)I(G)\). This descent step uses finite-stage closed
membership and converts it back to algebraic membership through injectivity of the quotient
comparison map.
-/
theorem kernelMulStandard_le_of_toClosedQuotient_inj
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (hinj :
      Function.Injective
        (zcCompletedGroupAlgebraKernelAugmentationQuotientToClosedQuotient
          C hC hForm psi hpsi hfopen)) :
    ∀ k : ZCCompletedGroupAlgebra C G,
      k ∈ RingHom.ker (zcCompletedGroupAlgebraMap C hC psi) →
      ∀ y : zcCompletedGroupAlgebraStandardAugmentationIdeal C G,
        (⟨k * (y : ZCCompletedGroupAlgebra C G),
          (zcCompletedGroupAlgebraStandardAugmentationIdeal C G).mul_mem_left k y.2⟩ :
            zcCompletedGroupAlgebraStandardAugmentationIdeal C G) ∈
          zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi := by
  intro k hk y
  let S := zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi
  let T :=
    zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
      C hC hForm psi hpsi hfopen
  let x : zcCompletedGroupAlgebraStandardAugmentationIdeal C G :=
    ⟨k * (y : ZCCompletedGroupAlgebra C G),
      (zcCompletedGroupAlgebraStandardAugmentationIdeal C G).mul_mem_left k y.2⟩
  have hxT : x ∈ T :=
    zcCompletedGAKernelAugmentationIdealMulStandard_mul_mem_closed_of_mem_ker_map
      C hC hForm psi hpsi hfopen hk y
  have hxmap :
      zcCompletedGroupAlgebraKernelAugmentationQuotientToClosedQuotient
          C hC hForm psi hpsi hfopen
          (Submodule.Quotient.mk (p := S) x) = 0 := by
    rw [zcCompletedGroupAlgebraKernelAugmentationQuotientToClosedQuotient_mk
      (C := C) (hC := hC) (hForm := hForm) (psi := psi)
      (hpsi := hpsi) (hfopen := hfopen) x]
    exact (Submodule.Quotient.mk_eq_zero (p := T) (x := x)).2 hxT
  have hxzero :
      (Submodule.Quotient.mk (p := S) x :
        KernelAugmentationIdealQuotient C psi) = 0 := by
    apply hinj
    rw [hxmap, map_zero]
  exact (Submodule.Quotient.mk_eq_zero (p := S) (x := x)).1 hxzero

/--
If every completed-kernel scalar sends the standard source augmentation ideal into \(I(\ker
\psi)I(G)\), then the completed kernel acts trivially on the quotient.
-/
theorem zcCompletedGAKerAugQuot_ker_map_smul_eq_zero_of_kernelMulStandard_le
    (hC : ProCGroups.FiniteGroupClass.Hereditary C) (psi : ContinuousMonoidHom G H)
    (hker_mul :
      ∀ k : ZCCompletedGroupAlgebra C G,
        k ∈ RingHom.ker (zcCompletedGroupAlgebraMap C hC psi) →
        ∀ y : zcCompletedGroupAlgebraStandardAugmentationIdeal C G,
          (⟨k * (y : ZCCompletedGroupAlgebra C G),
            (zcCompletedGroupAlgebraStandardAugmentationIdeal C G).mul_mem_left k y.2⟩ :
              zcCompletedGroupAlgebraStandardAugmentationIdeal C G) ∈
            zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi)
    (k : ZCCompletedGroupAlgebra C G)
    (hk : k ∈ RingHom.ker (zcCompletedGroupAlgebraMap C hC psi))
    (x : KernelAugmentationIdealQuotient C psi) :
    k • x = 0 := by
  refine Submodule.Quotient.induction_on
    (p := zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi) x ?_
  intro y
  apply (Submodule.Quotient.mk_eq_zero
    (p := zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi)).2
  change
    (⟨k * (y : ZCCompletedGroupAlgebra C G),
      (zcCompletedGroupAlgebraStandardAugmentationIdeal C G).mul_mem_left k y.2⟩ :
        zcCompletedGroupAlgebraStandardAugmentationIdeal C G) ∈
      zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi
  exact hker_mul k hk y

/--
Conditional descent of the source action to a completed target \(\mathbb{Z}_C\llbracket
H\rrbracket\)-module. The extra hypothesis is exactly the missing kernel-product statement; it
is kept explicit so that closure membership is not used as algebraic equality.
-/
def zcCompletedGroupAlgebraTargetLiftOfSurjective
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi) :
    ZCCompletedGroupAlgebra C H → ZCCompletedGroupAlgebra C G :=
  Function.surjInv
    (zcCompletedGroupAlgebraMap_surjective_of_surjective
      (C := C) (hC := hC) hForm psi hpsi)

/--
For a surjective presentation, the completed group-algebra map sends the chosen target lift of `a`
back to `a`.
-/
@[simp 900]
theorem zcCompletedGroupAlgebraMap_targetLiftOfSurjective
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (a : ZCCompletedGroupAlgebra C H) :
    zcCompletedGroupAlgebraMap C hC psi
        (zcCompletedGroupAlgebraTargetLiftOfSurjective C hC hForm psi hpsi a) = a :=
  Function.surjInv_eq
    (zcCompletedGroupAlgebraMap_surjective_of_surjective
      (C := C) (hC := hC) hForm psi hpsi) a

/--
The kernel-multiple containment hypothesis makes the source augmentation quotient a module over
the target completed group algebra, using chosen lifts along the surjective presentation.
-/
@[implicit_reducible]
def zcCompletedGAKerAugQuotTargetCompletedModuleOfSurjective_of_kernelMulStandard_le
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hker_mul :
      ∀ k : ZCCompletedGroupAlgebra C G,
        k ∈ RingHom.ker (zcCompletedGroupAlgebraMap C hC psi) →
        ∀ y : zcCompletedGroupAlgebraStandardAugmentationIdeal C G,
          (⟨k * (y : ZCCompletedGroupAlgebra C G),
            (zcCompletedGroupAlgebraStandardAugmentationIdeal C G).mul_mem_left k y.2⟩ :
              zcCompletedGroupAlgebraStandardAugmentationIdeal C G) ∈
            zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi) :
    Module (ZCCompletedGroupAlgebra C H) (KernelAugmentationIdealQuotient C psi) := by
  letI : SMul (ZCCompletedGroupAlgebra C H)
      (KernelAugmentationIdealQuotient C psi) :=
    ⟨fun a x => zcCompletedGroupAlgebraTargetLiftOfSurjective
      C hC hForm psi hpsi a • x⟩
  refine (zcCompletedGroupAlgebraMap_surjective_of_surjective
    (C := C) (hC := hC) hForm psi hpsi).moduleLeft
      (zcCompletedGroupAlgebraMap C hC psi) ?_
  intro a x
  change zcCompletedGroupAlgebraTargetLiftOfSurjective C hC hForm psi hpsi
      (zcCompletedGroupAlgebraMap C hC psi a) • x =
    a • x
  have hdiff :
      zcCompletedGroupAlgebraTargetLiftOfSurjective C hC hForm psi hpsi
          (zcCompletedGroupAlgebraMap C hC psi a) - a ∈
        RingHom.ker (zcCompletedGroupAlgebraMap C hC psi) := by
    change zcCompletedGroupAlgebraMap C hC psi
        (zcCompletedGroupAlgebraTargetLiftOfSurjective C hC hForm psi hpsi
          (zcCompletedGroupAlgebraMap C hC psi a) - a) = 0
    rw [map_sub, zcCompletedGroupAlgebraMap_targetLiftOfSurjective, sub_self]
  have hzero :=
    zcCompletedGAKerAugQuot_ker_map_smul_eq_zero_of_kernelMulStandard_le
      C hC psi hker_mul
      (zcCompletedGroupAlgebraTargetLiftOfSurjective C hC hForm psi hpsi
        (zcCompletedGroupAlgebraMap C hC psi a) - a) hdiff x
  rw [sub_smul] at hzero
  exact sub_eq_zero.mp hzero

/--
Closedness of the kernel-multiple submodule supplies the containment needed to descend the target
completed-group-algebra module structure to the source augmentation quotient.
-/
@[implicit_reducible]
def zcCompletedGAKerAugQuotTargetCompletedModuleOfSurjective_of_closed_kernelMulStandard
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (hclosed :
      IsClosed
        ((zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi :
          Set (zcCompletedGroupAlgebraStandardAugmentationIdeal C G)))) :
    Module (ZCCompletedGroupAlgebra C H) (KernelAugmentationIdealQuotient C psi) :=
  zcCompletedGAKerAugQuotTargetCompletedModuleOfSurjective_of_kernelMulStandard_le
    C hC hForm psi hpsi
    (zcCompletedGAKernelAugmentationIdealMulStandard_kernelMulStandard_le_of_isClosed
      C hC hForm psi hpsi hfopen hclosed)

/-- The completed kernel acts trivially on the closed source augmentation quotient. -/
theorem zcCompletedGroupAlgebraKernelAugmentationClosedQuotient_ker_map_smul_eq_zero
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (k : ZCCompletedGroupAlgebra C G)
    (hk : k ∈ RingHom.ker (zcCompletedGroupAlgebraMap C hC psi))
    (x : KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :
    k • x = 0 := by
  refine Submodule.Quotient.induction_on
    (p := zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
      C hC hForm psi hpsi hfopen) x ?_
  intro y
  apply (Submodule.Quotient.mk_eq_zero
    (p := zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
      C hC hForm psi hpsi hfopen)).2
  change
    (⟨k * (y : ZCCompletedGroupAlgebra C G),
      (zcCompletedGroupAlgebraStandardAugmentationIdeal C G).mul_mem_left k y.2⟩ :
        zcCompletedGroupAlgebraStandardAugmentationIdeal C G) ∈
      zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
        C hC hForm psi hpsi hfopen
  exact
    zcCompletedGAKernelAugmentationIdealMulStandard_kernelMulStandard_le_closed
      C hC hForm psi hpsi hfopen k hk y

/--
Unconditional descent of the source action to a completed target \(\mathbb{Z}_C\llbracket
H\rrbracket\)-module on the closed source augmentation quotient.
-/
@[implicit_reducible]
def kerAugClosedQuotTargetCompletedModuleOfSurj
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi) :
    Module (ZCCompletedGroupAlgebra C H)
      (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) := by
  letI : SMul (ZCCompletedGroupAlgebra C H)
      (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
    ⟨fun a x => zcCompletedGroupAlgebraTargetLiftOfSurjective
      C hC hForm psi hpsi a • x⟩
  refine (zcCompletedGroupAlgebraMap_surjective_of_surjective
    (C := C) (hC := hC) hForm psi hpsi).moduleLeft
      (zcCompletedGroupAlgebraMap C hC psi) ?_
  intro a x
  change zcCompletedGroupAlgebraTargetLiftOfSurjective C hC hForm psi hpsi
      (zcCompletedGroupAlgebraMap C hC psi a) • x =
    a • x
  have hdiff :
      zcCompletedGroupAlgebraTargetLiftOfSurjective C hC hForm psi hpsi
          (zcCompletedGroupAlgebraMap C hC psi a) - a ∈
        RingHom.ker (zcCompletedGroupAlgebraMap C hC psi) := by
    change zcCompletedGroupAlgebraMap C hC psi
        (zcCompletedGroupAlgebraTargetLiftOfSurjective C hC hForm psi hpsi
          (zcCompletedGroupAlgebraMap C hC psi a) - a) = 0
    rw [map_sub, zcCompletedGroupAlgebraMap_targetLiftOfSurjective, sub_self]
  have hzero :=
    zcCompletedGroupAlgebraKernelAugmentationClosedQuotient_ker_map_smul_eq_zero
      C hC hForm psi hpsi hfopen
      (zcCompletedGroupAlgebraTargetLiftOfSurjective C hC hForm psi hpsi
        (zcCompletedGroupAlgebraMap C hC psi a) - a) hdiff x
  rw [sub_smul] at hzero
  exact sub_eq_zero.mp hzero

/-- The closed quotient target module action is compatible with mapped scalars. -/
theorem kerAugClosedQuotTargetCompletedModuleOfSurj_map_smul
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (a : ZCCompletedGroupAlgebra C G)
    (x : KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :
    letI : Module (ZCCompletedGroupAlgebra C H)
        (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
      kerAugClosedQuotTargetCompletedModuleOfSurj
        C hC hForm psi hpsi hfopen
    zcCompletedGroupAlgebraMap C hC psi a • x = a • x := by
  let : Module (ZCCompletedGroupAlgebra C H)
      (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
    kerAugClosedQuotTargetCompletedModuleOfSurj
      C hC hForm psi hpsi hfopen
  change zcCompletedGroupAlgebraTargetLiftOfSurjective C hC hForm psi hpsi
      (zcCompletedGroupAlgebraMap C hC psi a) • x =
    a • x
  have hdiff :
      zcCompletedGroupAlgebraTargetLiftOfSurjective C hC hForm psi hpsi
          (zcCompletedGroupAlgebraMap C hC psi a) - a ∈
        RingHom.ker (zcCompletedGroupAlgebraMap C hC psi) := by
    change zcCompletedGroupAlgebraMap C hC psi
        (zcCompletedGroupAlgebraTargetLiftOfSurjective C hC hForm psi hpsi
          (zcCompletedGroupAlgebraMap C hC psi a) - a) = 0
    rw [map_sub, zcCompletedGroupAlgebraMap_targetLiftOfSurjective, sub_self]
  have hzero :=
    zcCompletedGroupAlgebraKernelAugmentationClosedQuotient_ker_map_smul_eq_zero
      C hC hForm psi hpsi hfopen
      (zcCompletedGroupAlgebraTargetLiftOfSurjective C hC hForm psi hpsi
        (zcCompletedGroupAlgebraMap C hC psi a) - a) hdiff x
  rw [sub_smul] at hzero
  exact sub_eq_zero.mp hzero

/--
Source scalar multiplication on the closed source augmentation quotient is continuous in the
source scalar, for a fixed quotient element.
-/
theorem continuous_zcCompletedGAKerAugClosedQuot_source_smul_const
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (x : KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :
    Continuous (fun a : ZCCompletedGroupAlgebra C G => a • x) := by
  refine Submodule.Quotient.induction_on
    (p := zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
      C hC hForm psi hpsi hfopen) x ?_
  intro y
  have hpre :
      Continuous (fun a : ZCCompletedGroupAlgebra C G =>
        (⟨a * (y : ZCCompletedGroupAlgebra C G),
          (zcCompletedGroupAlgebraStandardAugmentationIdeal C G).mul_mem_left a y.2⟩ :
          zcCompletedGroupAlgebraStandardAugmentationIdeal C G)) := by
    have hmul : Continuous (fun a : ZCCompletedGroupAlgebra C G =>
        a * (y : ZCCompletedGroupAlgebra C G)) :=
      continuous_id.mul continuous_const
    exact Continuous.subtype_mk hmul
      (fun a => (zcCompletedGroupAlgebraStandardAugmentationIdeal C G).mul_mem_left a y.2)
  have hq :
      Continuous (fun z : zcCompletedGroupAlgebraStandardAugmentationIdeal C G =>
        (Submodule.Quotient.mk
          (p := zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
            C hC hForm psi hpsi hfopen) z :
          KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen)) :=
    continuous_quotient_mk'
  change Continuous (fun a : ZCCompletedGroupAlgebra C G =>
    (Submodule.Quotient.mk
      (p := zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
        C hC hForm psi hpsi hfopen)
      ⟨a * (y : ZCCompletedGroupAlgebra C G),
        (zcCompletedGroupAlgebraStandardAugmentationIdeal C G).mul_mem_left a y.2⟩ :
      KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen))
  exact hq.comp hpre

/--
Descended target scalar multiplication on the closed source augmentation quotient is continuous
in the target scalar, for a fixed quotient element.
-/
theorem continuous_kerAugClosedQuotTargetCompletedModuleOfSurj_smul_const
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (x : KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :
    letI : Module (ZCCompletedGroupAlgebra C H)
        (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
      kerAugClosedQuotTargetCompletedModuleOfSurj
        C hC hForm psi hpsi hfopen
    Continuous (fun a : ZCCompletedGroupAlgebra C H => a • x) := by
  let : Module (ZCCompletedGroupAlgebra C H)
      (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
    kerAugClosedQuotTargetCompletedModuleOfSurj
      C hC hForm psi hpsi hfopen
  let q := zcCompletedGroupAlgebraMap C hC psi
  have hq : Topology.IsQuotientMap q :=
    isQuotientMap_zcCompletedGroupAlgebraMap_of_surjective C hC hForm psi hpsi
  rw [hq.continuous_iff]
  change Continuous (fun a : ZCCompletedGroupAlgebra C G => q a • x)
  have hsource :=
    continuous_zcCompletedGAKerAugClosedQuot_source_smul_const
      C hC hForm psi hpsi hfopen x
  have hEq :
      (fun a : ZCCompletedGroupAlgebra C G => q a • x) =
        (fun a : ZCCompletedGroupAlgebra C G => a • x) := by
    funext a
    exact
      kerAugClosedQuotTargetCompletedModuleOfSurj_map_smul
        C hC hForm psi hpsi hfopen a x
  simpa [hEq] using hsource

/--
Source scalar multiplication on the closed source augmentation quotient is jointly continuous.
-/
theorem continuous_zcCompletedGroupAlgebraKernelAugmentationClosedQuotient_source_smul
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi) :
    Continuous (fun p : ZCCompletedGroupAlgebra C G ×
        KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen =>
      p.1 • p.2) := by
  let S :=
    zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
      C hC hForm psi hpsi hfopen
  have hquot :
      IsOpenQuotientMap
        (Prod.map (id : ZCCompletedGroupAlgebra C G → ZCCompletedGroupAlgebra C G)
          (fun z : zcCompletedGroupAlgebraStandardAugmentationIdeal C G =>
            (Submodule.Quotient.mk (p := S) z :
              KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen))) :=
    IsOpenQuotientMap.id.prodMap S.isOpenQuotientMap_mkQ
  rw [← hquot.continuous_comp_iff]
  have hpre :
      Continuous (fun p : ZCCompletedGroupAlgebra C G ×
          zcCompletedGroupAlgebraStandardAugmentationIdeal C G =>
        (⟨p.1 * (p.2 : ZCCompletedGroupAlgebra C G),
          (zcCompletedGroupAlgebraStandardAugmentationIdeal C G).mul_mem_left p.1 p.2.2⟩ :
          zcCompletedGroupAlgebraStandardAugmentationIdeal C G)) := by
    have hmul : Continuous (fun p : ZCCompletedGroupAlgebra C G ×
        zcCompletedGroupAlgebraStandardAugmentationIdeal C G =>
        p.1 * (p.2 : ZCCompletedGroupAlgebra C G)) :=
      continuous_fst.mul (continuous_subtype_val.comp continuous_snd)
    exact Continuous.subtype_mk hmul
      (fun p => (zcCompletedGroupAlgebraStandardAugmentationIdeal C G).mul_mem_left p.1 p.2.2)
  have hmk :
      Continuous (fun z : zcCompletedGroupAlgebraStandardAugmentationIdeal C G =>
        (Submodule.Quotient.mk (p := S) z :
          KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen)) :=
    continuous_quotient_mk'
  change Continuous (fun p : ZCCompletedGroupAlgebra C G ×
      zcCompletedGroupAlgebraStandardAugmentationIdeal C G =>
    (Submodule.Quotient.mk (p := S)
      ⟨p.1 * (p.2 : ZCCompletedGroupAlgebra C G),
        (zcCompletedGroupAlgebraStandardAugmentationIdeal C G).mul_mem_left p.1 p.2.2⟩ :
      KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen))
  exact hmk.comp hpre

/--
Descended target scalar multiplication on the closed source augmentation quotient is jointly
continuous.
-/
theorem continuous_kerAugClosedQuotTargetCompletedModuleOfSurj_smul
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi) :
    letI : Module (ZCCompletedGroupAlgebra C H)
        (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
      kerAugClosedQuotTargetCompletedModuleOfSurj
        C hC hForm psi hpsi hfopen
    Continuous (fun p : ZCCompletedGroupAlgebra C H ×
        KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen =>
      p.1 • p.2) := by
  let : Module (ZCCompletedGroupAlgebra C H)
      (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
    kerAugClosedQuotTargetCompletedModuleOfSurj
      C hC hForm psi hpsi hfopen
  let q := zcCompletedGroupAlgebraMap C hC psi
  have hq : IsOpenQuotientMap q :=
    isOpenQuotientMap_zcCompletedGroupAlgebraMap_of_surjective C hC hForm psi hpsi
  have hquot :
      IsOpenQuotientMap
        (Prod.map q
          (id :
            KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen →
            KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen)) :=
    hq.prodMap IsOpenQuotientMap.id
  rw [← hquot.continuous_comp_iff]
  have hsource :=
    continuous_zcCompletedGroupAlgebraKernelAugmentationClosedQuotient_source_smul
      C hC hForm psi hpsi hfopen
  have hEq :
      (fun p : ZCCompletedGroupAlgebra C G ×
          KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen =>
        q p.1 • p.2) =
        (fun p : ZCCompletedGroupAlgebra C G ×
            KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen =>
          p.1 • p.2) := by
    funext p
    exact
      kerAugClosedQuotTargetCompletedModuleOfSurj_map_smul
        C hC hForm psi hpsi hfopen p.1 p.2
  simpa [Function.comp_def, Prod.map, hEq] using hsource

/--
The closed source augmentation quotient is a topological module for the source completed group
algebra.
-/
theorem continuousSMul_zcCompletedGroupAlgebraKernelAugmentationClosedQuotient_source
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi) :
    ContinuousSMul (ZCCompletedGroupAlgebra C G)
      (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) where
  continuous_smul :=
    continuous_zcCompletedGroupAlgebraKernelAugmentationClosedQuotient_source_smul
      C hC hForm psi hpsi hfopen

/--
The descended target module structure on the closed source augmentation quotient is topological.
-/
theorem continuousSMul_kerAugClosedQuotTargetCompletedModuleOfSurj
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi) :
    letI : Module (ZCCompletedGroupAlgebra C H)
        (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
      kerAugClosedQuotTargetCompletedModuleOfSurj
        C hC hForm psi hpsi hfopen
    ContinuousSMul (ZCCompletedGroupAlgebra C H)
      (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) := by
  let : Module (ZCCompletedGroupAlgebra C H)
      (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
    kerAugClosedQuotTargetCompletedModuleOfSurj
      C hC hForm psi hpsi hfopen
  exact
    ⟨continuous_kerAugClosedQuotTargetCompletedModuleOfSurj_smul
      C hC hForm psi hpsi hfopen⟩

/-- Group-like elements act on the closed quotient target module by the induced target action. -/
theorem kerAugClosedQuotTargetCompletedModuleOfSurj_groupLike_smul
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (g : G) (x : KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :
    letI : Module (ZCCompletedGroupAlgebra C H)
        (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
      kerAugClosedQuotTargetCompletedModuleOfSurj
        C hC hForm psi hpsi hfopen
    zcGroupLike C H (psi g) • x = zcGroupLike C G g • x := by
  let : Module (ZCCompletedGroupAlgebra C H)
      (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
    kerAugClosedQuotTargetCompletedModuleOfSurj
      C hC hForm psi hpsi hfopen
  rw [← zcCompletedGroupAlgebraMap_groupLike (C := C) (hC := hC) psi g]
  exact
    kerAugClosedQuotTargetCompletedModuleOfSurj_map_smul
      C hC hForm psi hpsi hfopen (zcGroupLike C G g) x

/--
The source boundary to the closed source augmentation quotient is a crossed differential for the
descended completed target scalars.
-/
def zcCompletedGASourceBoundaryToKerAugClosedQuotTargetCompletedCrossedHomOfSurjective
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi) :
    letI : Module (ZCCompletedGroupAlgebra C H)
        (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
      kerAugClosedQuotTargetCompletedModuleOfSurj
        C hC hForm psi hpsi hfopen
    ScalarCrossedHom
      (zcCompletedGroupAlgebraScalar C psi.toMonoidHom)
      (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) := by
  letI : Module (ZCCompletedGroupAlgebra C H)
      (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
    kerAugClosedQuotTargetCompletedModuleOfSurj
      C hC hForm psi hpsi hfopen
  exact
    { toFun :=
        zcCompletedGroupAlgebraSourceBoundaryToKernelAugmentationClosedQuotient
          C hC hForm psi hpsi hfopen
      map_mul' := by
        intro g h
        rw [(zcCompletedGroupAlgebraSourceBoundaryToKernelAugmentationClosedQuotient
          C hC hForm psi hpsi hfopen).map_mul]
        congr 1
        change zcGroupLike C G g •
            zcCompletedGroupAlgebraSourceBoundaryToKernelAugmentationClosedQuotient
              C hC hForm psi hpsi hfopen h =
          zcGroupLike C H (psi g) •
            zcCompletedGroupAlgebraSourceBoundaryToKernelAugmentationClosedQuotient
              C hC hForm psi hpsi hfopen h
        exact
          (kerAugClosedQuotTargetCompletedModuleOfSurj_groupLike_smul
            C hC hForm psi hpsi hfopen g
            (zcCompletedGroupAlgebraSourceBoundaryToKernelAugmentationClosedQuotient
              C hC hForm psi hpsi hfopen h)).symm }

/--
Projecting a chosen completed source lift of a target coefficient to a source stage and then
passing to the open-image stage recovers the corresponding target finite-stage projection.
-/
theorem zcCompletedGroupAlgebraOpenImageStageRingHom_projection_targetLift
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (i : ZCCompletedGroupAlgebraIndex C G)
    (a : ZCCompletedGroupAlgebra C H) :
    zcCompletedGroupAlgebraOpenImageStageRingHom C hC hForm psi hpsi hfopen i
        (zcCompletedGroupAlgebraProjection C G i
          (zcCompletedGroupAlgebraTargetLiftOfSurjective C hC hForm psi hpsi a)) =
      zcCompletedGroupAlgebraProjection C H
        (zcCompletedGroupAlgebraOpenImageTargetIndex C hForm psi hpsi hfopen i) a := by
  let b := zcCompletedGroupAlgebraTargetLiftOfSurjective C hC hForm psi hpsi a
  have hsource :
      (i.1,
        completedGroupAlgebraComapIndexInClass (G := G) (H := H) C hC psi
          (zcCompletedGroupAlgebraOpenImageIndexInClass C hForm psi hpsi hfopen i)) ≤ i :=
    ⟨le_rfl, zcCompletedGroupAlgebraOpenImage_comapIndex_le C hC hForm psi hpsi hfopen i⟩
  have hstage :
      zcCompletedGroupAlgebraOpenImageStageRingHom C hC hForm psi hpsi hfopen i
          (zcCompletedGroupAlgebraProjection C G i b) =
        zcCompletedGroupAlgebraMapStage C hC psi
          (zcCompletedGroupAlgebraOpenImageTargetIndex C hForm psi hpsi hfopen i)
            (zcCompletedGroupAlgebraTransition C G hsource
              (zcCompletedGroupAlgebraProjection C G i b)) := by
    exact congrFun
      (congrArg DFunLike.coe
        (zcCompletedGroupAlgebraOpenImageQuotientMap_stage_eq
          C hC hForm psi hpsi hfopen i))
      (zcCompletedGroupAlgebraProjection C G i b)
  rw [hstage, zcCompletedGroupAlgebraTransition_projection]
  change
    zcCompletedGroupAlgebraMapStage C hC psi
        (zcCompletedGroupAlgebraOpenImageTargetIndex C hForm psi hpsi hfopen i)
        (zcCompletedGroupAlgebraProjection C G
          ((zcCompletedGroupAlgebraOpenImageTargetIndex C hForm psi hpsi hfopen i).1,
            completedGroupAlgebraComapIndexInClass (G := G) (H := H) C hC psi
              (zcCompletedGroupAlgebraOpenImageTargetIndex C hForm psi hpsi hfopen i).2) b) =
      zcCompletedGroupAlgebraProjection C H
        (zcCompletedGroupAlgebraOpenImageTargetIndex C hForm psi hpsi hfopen i) a
  have hprojmap :=
    zcCompletedGroupAlgebraProjection_map
      (C := C) (hC := hC) (H := G) (K := H) (φ := psi)
      (i := zcCompletedGroupAlgebraOpenImageTargetIndex C hForm psi hpsi hfopen i)
      (x := b)
  have hmap : zcCompletedGroupAlgebraMap C hC psi b = a := by
    dsimp [b]
    exact zcCompletedGroupAlgebraMap_targetLiftOfSurjective C hC hForm psi hpsi a
  have hmain :
      zcCompletedGroupAlgebraProjection C H
          (zcCompletedGroupAlgebraOpenImageTargetIndex C hForm psi hpsi hfopen i)
          (zcCompletedGroupAlgebraMap C hC psi b) =
        zcCompletedGroupAlgebraProjection C H
          (zcCompletedGroupAlgebraOpenImageTargetIndex C hForm psi hpsi hfopen i) a :=
    congrArg
      (zcCompletedGroupAlgebraProjection C H
        (zcCompletedGroupAlgebraOpenImageTargetIndex C hForm psi hpsi hfopen i))
      hmap
  exact hprojmap.symm.trans hmain

/--
The i-th closed augmentation quotient coordinate of the completed source-boundary lift factors
through the corresponding open-image finite pre-stage.
-/
theorem kerAugIdealClosedQuotStageProj_liftLinear_eq_boundaryLift_preStageMap
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (i : ZCCompletedGroupAlgebraIndex C G)
    (x : CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G) :
    letI : Module (ZCCompletedGroupAlgebra C H)
        (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
      kerAugClosedQuotTargetCompletedModuleOfSurj
        C hC hForm psi hpsi hfopen
    let j := zcCompletedDifferentialModuleOpenImageIndex C hForm psi hpsi hfopen i
    letI : Module (zcCompletedDifferentialModuleStageRing C psi.toMonoidHom j)
        (KernelAugmentationIdealClosedStageQuotient C hC hForm psi hpsi hfopen i) :=
      kernelAugmentationIdealClosedStageQuotientTargetStageModule
        C hC hForm psi hpsi hfopen i
    kernelAugmentationIdealClosedQuotientStageProjection
        C hC hForm psi hpsi hfopen i
        (crossedDifferentialModuleLiftLinear
          (R := ZCCompletedGroupAlgebra C H)
          (zcCompletedGroupAlgebraSourceBoundaryToKernelAugmentationClosedQuotient
            C hC hForm psi hpsi hfopen) x) =
      kernelAugmentationIdealClosedStageQuotientBoundaryLift
        C hC hForm psi hpsi hfopen i
        (zcCompletedDifferentialModulePreStageMap C psi.toMonoidHom
          j x) := by
  let : Module (ZCCompletedGroupAlgebra C H)
      (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
    kerAugClosedQuotTargetCompletedModuleOfSurj
      C hC hForm psi hpsi hfopen
  let j := zcCompletedDifferentialModuleOpenImageIndex C hForm psi hpsi hfopen i
  let : Module (zcCompletedDifferentialModuleStageRing C psi.toMonoidHom j)
      (KernelAugmentationIdealClosedStageQuotient C hC hForm psi hpsi hfopen i) :=
    kernelAugmentationIdealClosedStageQuotientTargetStageModule
      C hC hForm psi hpsi hfopen i
  let : Module
      (ZCCompletedGroupAlgebraStage C H
        (zcCompletedGroupAlgebraOpenImageTargetIndex C hForm psi hpsi hfopen i))
      (KernelAugmentationIdealClosedStageQuotient C hC hForm psi hpsi hfopen i) :=
    kernelAugmentationIdealClosedStageQuotientTargetStageModule
      C hC hForm psi hpsi hfopen i
  refine Finsupp.induction_linear x ?zero ?add ?single
  · simp only [crossedDifferentialModuleLiftLinear, map_zero, ContinuousMonoidHom.coe_toMonoidHom,
  Lean.Elab.WF.paramLet, kernelAugmentationIdealClosedStageQuotientBoundaryLift,
  zcCompletedDifferentialModulePreStageMap]
  · intro x y hx hy
    simp only [map_add, hx, ContinuousMonoidHom.coe_toMonoidHom, Lean.Elab.WF.paramLet, hy]
  · intro g a
    dsimp only
    rw [crossedDifferentialModuleLiftLinear_single,
      zcCompletedDifferentialModulePreStageMap_single,
      kernelAugmentationIdealClosedStageQuotientBoundaryLift_single]
    let b := zcCompletedGroupAlgebraTargetLiftOfSurjective C hC hForm psi hpsi a
    have htarget :
        a • zcCompletedGroupAlgebraSourceBoundaryToKernelAugmentationClosedQuotient
            C hC hForm psi hpsi hfopen g =
          b • zcCompletedGroupAlgebraSourceBoundaryToKernelAugmentationClosedQuotient
            C hC hForm psi hpsi hfopen g := by
      rfl
    rw [htarget]
    change
      kernelAugmentationIdealClosedQuotientStageProjection
          C hC hForm psi hpsi hfopen i
          (b • zcCompletedGroupAlgebraSourceBoundaryToKernelAugmentationClosedQuotient
            C hC hForm psi hpsi hfopen g) =
        zcCompletedGroupAlgebraProjection C H
            (zcCompletedGroupAlgebraOpenImageTargetIndex C hForm psi hpsi hfopen i) a •
          kernelAugmentationIdealClosedStageQuotientBoundary
            C hC hForm psi hpsi hfopen i
            (zcCompletedDifferentialModuleStageSourceProj C psi.toMonoidHom j g)
    rw [map_smulₛₗ]
    rw [← zcCompletedGroupAlgebraOpenImageStageRingHom_projection_targetLift
      C hC hForm psi hpsi hfopen i a]
    rw [kernelAugmentationIdealClosedStageQuotientTargetStageModule_map_smul
      (C := C) (hC := hC) (hForm := hForm) (psi := psi)
      (hpsi := hpsi) (hfopen := hfopen) (i := i)
      (a := zcCompletedGroupAlgebraProjection C G i b)
      (x := kernelAugmentationIdealClosedStageQuotientBoundary
        C hC hForm psi hpsi hfopen i
        (zcCompletedDifferentialModuleStageSourceProj C psi.toMonoidHom j g))]
    have hstage_boundary :
        kernelAugmentationIdealClosedQuotientStageProjection
            C hC hForm psi hpsi hfopen i
            (zcCompletedGroupAlgebraSourceBoundaryToKernelAugmentationClosedQuotient
              C hC hForm psi hpsi hfopen g) =
          kernelAugmentationIdealClosedStageQuotientBoundary
            C hC hForm psi hpsi hfopen i
            (zcCompletedDifferentialModuleStageSourceProj C psi.toMonoidHom j g) := by
      rw [zcCompletedGroupAlgebraSourceBoundaryToKernelAugmentationClosedQuotient]
      let s : zcCompletedGroupAlgebraStandardAugmentationIdeal C G :=
        ⟨zcCompletedGroupAlgebraBoundary C (MonoidHom.id G) g,
          zcCompletedGroupAlgebraBoundary_mem_standardAugmentationIdeal
            C G (MonoidHom.id G) g⟩
      change
        kernelAugmentationIdealClosedQuotientStageProjection
            C hC hForm psi hpsi hfopen i
            (Submodule.Quotient.mk
              (p := zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
                C hC hForm psi hpsi hfopen) s) =
          kernelAugmentationIdealClosedStageQuotientBoundary
            C hC hForm psi hpsi hfopen i
            (zcCompletedDifferentialModuleStageSourceProj C psi.toMonoidHom j g)
      let T :=
        zcCompletedGroupAlgebraOpenImageKernelAugmentationIdealMulStageStandard
          C hC hForm psi hpsi hfopen i
      calc
        kernelAugmentationIdealClosedQuotientStageProjection
            C hC hForm psi hpsi hfopen i
            (Submodule.Quotient.mk
              (p := zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
                C hC hForm psi hpsi hfopen) s) =
          (Submodule.Quotient.mk
            (p := T)
            (zcCompletedGroupAlgebraStandardAugmentationIdealProjection C i s) :
            KernelAugmentationIdealClosedStageQuotient C hC hForm psi hpsi hfopen i) := by
            exact
              kernelAugmentationIdealClosedQuotientStageProjection_mk
                C hC hForm psi hpsi hfopen i s
        _ =
          kernelAugmentationIdealClosedStageQuotientBoundary
            C hC hForm psi hpsi hfopen i
            (zcCompletedDifferentialModuleStageSourceProj C psi.toMonoidHom j g) := by
            simp only [kernelAugmentationIdealClosedStageQuotientBoundary]
            change
              Submodule.Quotient.mk (p := T)
                  (zcCompletedGroupAlgebraStandardAugmentationIdealProjection C i s) =
                Submodule.Quotient.mk (p := T)
                  (zcCompletedGroupAlgebraStageAugmentationGeneratorSubtype C G i
                    (zcCompletedDifferentialModuleStageSourceProj
                      C psi.toMonoidHom j g))
            apply congrArg (fun y : zcCompletedGroupAlgebraStageAugmentationIdeal C G i =>
              (Submodule.Quotient.mk (p := T) y :
                KernelAugmentationIdealClosedStageQuotient C hC hForm psi hpsi hfopen i))
            apply Subtype.ext
            change
              zcCompletedGroupAlgebraProjection C G i
                  (zcGroupLike C G g - 1) =
                MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus)
                    (CompletedGroupAlgebraQuotientInClass G C i.2)
                    (QuotientGroup.mk g) - 1
            rw [zcCompletedGroupAlgebraProjection_sub,
              zcCompletedGroupAlgebraProjection_groupLike,
              zcCompletedGroupAlgebraProjection_one]
    rw [hstage_boundary]
    rfl

/--
Each finite closed-augmentation coordinate of the pre-quotient source-boundary lift is
continuous for the finite-stage pre-module topology.
-/
theorem continuous_kernelAugmentationIdealClosedQuotientStageProjection_liftLinear
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (i : ZCCompletedGroupAlgebraIndex C G) :
    letI : Module (ZCCompletedGroupAlgebra C H)
        (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
      kerAugClosedQuotTargetCompletedModuleOfSurj
        C hC hForm psi hpsi hfopen
    @Continuous
      (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)
      (KernelAugmentationIdealClosedStageQuotient C hC hForm psi hpsi hfopen i)
      (zcCompletedDifferentialPreModuleNaturalTopology C psi.toMonoidHom)
      inferInstance
      (fun x =>
        kernelAugmentationIdealClosedQuotientStageProjection
          C hC hForm psi hpsi hfopen i
          (crossedDifferentialModuleLiftLinear
            (R := ZCCompletedGroupAlgebra C H)
            (zcCompletedGroupAlgebraSourceBoundaryToKernelAugmentationClosedQuotient
              C hC hForm psi hpsi hfopen) x)) := by
  let : Module (ZCCompletedGroupAlgebra C H)
      (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
    kerAugClosedQuotTargetCompletedModuleOfSurj
      C hC hForm psi hpsi hfopen
  let j := zcCompletedDifferentialModuleOpenImageIndex C hForm psi hpsi hfopen i
  let : Module (zcCompletedDifferentialModuleStageRing C psi.toMonoidHom j)
      (KernelAugmentationIdealClosedStageQuotient C hC hForm psi hpsi hfopen i) :=
    kernelAugmentationIdealClosedStageQuotientTargetStageModule
      C hC hForm psi hpsi hfopen i
  let : TopologicalSpace
      (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G) :=
    zcCompletedDifferentialPreModuleNaturalTopology C psi.toMonoidHom
  let : TopologicalSpace
      (CrossedDifferentialPreModule
        (zcCompletedDifferentialModuleStageRing C psi.toMonoidHom j)
        (zcCompletedDifferentialModuleStageSource C psi.toMonoidHom j)) :=
    ⊥
  let : DiscreteTopology
      (CrossedDifferentialPreModule
        (zcCompletedDifferentialModuleStageRing C psi.toMonoidHom j)
        (zcCompletedDifferentialModuleStageSource C psi.toMonoidHom j)) :=
    ⟨rfl⟩
  have hpre :
      @Continuous
        (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)
        (CrossedDifferentialPreModule
          (zcCompletedDifferentialModuleStageRing C psi.toMonoidHom j)
          (zcCompletedDifferentialModuleStageSource C psi.toMonoidHom j))
        (zcCompletedDifferentialPreModuleNaturalTopology C psi.toMonoidHom)
        inferInstance
        (zcCompletedDifferentialModulePreStageMap C psi.toMonoidHom j) :=
    continuous_zcCompletedDifferentialModulePreStageMap_naturalTopology
      C psi.toMonoidHom j
  have hfinite :
      Continuous
        (kernelAugmentationIdealClosedStageQuotientBoundaryLift
          C hC hForm psi hpsi hfopen i) :=
    continuous_of_discreteTopology
  have hfactor :
      (fun x : CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G =>
        kernelAugmentationIdealClosedQuotientStageProjection
          C hC hForm psi hpsi hfopen i
          (crossedDifferentialModuleLiftLinear
            (R := ZCCompletedGroupAlgebra C H)
            (zcCompletedGroupAlgebraSourceBoundaryToKernelAugmentationClosedQuotient
              C hC hForm psi hpsi hfopen) x)) =
        fun x =>
          kernelAugmentationIdealClosedStageQuotientBoundaryLift
            C hC hForm psi hpsi hfopen i
            (zcCompletedDifferentialModulePreStageMap C psi.toMonoidHom j x) := by
    funext x
    exact
      kerAugIdealClosedQuotStageProj_liftLinear_eq_boundaryLift_preStageMap
        C hC hForm psi hpsi hfopen i x
  rw [hfactor]
  exact hfinite.comp hpre

/--
The pre-quotient source-boundary lift to the closed source augmentation quotient is continuous
for the finite-stage pre-module topology.
-/
theorem continuous_crossedDiffModuleLiftLinear_sourceBoundaryToKerAugClosedQuot
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi) :
    letI : Module (ZCCompletedGroupAlgebra C H)
        (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
      kerAugClosedQuotTargetCompletedModuleOfSurj
        C hC hForm psi hpsi hfopen
    @Continuous
      (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)
      (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen)
      (zcCompletedDifferentialPreModuleNaturalTopology C psi.toMonoidHom)
      inferInstance
      (crossedDifferentialModuleLiftLinear
        (R := ZCCompletedGroupAlgebra C H)
        (zcCompletedGroupAlgebraSourceBoundaryToKernelAugmentationClosedQuotient
          C hC hForm psi hpsi hfopen)) := by
  let : Module (ZCCompletedGroupAlgebra C H)
      (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
    kerAugClosedQuotTargetCompletedModuleOfSurj
      C hC hForm psi hpsi hfopen
  let : TopologicalSpace
      (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G) :=
    zcCompletedDifferentialPreModuleNaturalTopology C psi.toMonoidHom
  rw [kernelAugmentationIdealClosedQuotient_topology_eq_induced_stageProjProduct
    C hC hForm psi hpsi hfopen]
  rw [continuous_induced_rng]
  exact continuous_pi fun i =>
    continuous_kernelAugmentationIdealClosedQuotientStageProjection_liftLinear
      C hC hForm psi hpsi hfopen i

/--
The separated universal differential is also a crossed differential for source completed
group-algebra scalars after restricting scalars along \(\mathbb{Z}_C\llbracket G\rrbracket \to
\mathbb{Z}_C\llbracket H\rrbracket\).
-/
def zcSeparatedUniversalDifferentialSourceCompletedCrossedHom
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (psi : ContinuousMonoidHom G H) :
    letI : Module (ZCCompletedGroupAlgebra C G)
        (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom) :=
      Module.compHom _ (zcCompletedGroupAlgebraMap C hC psi)
    ScalarCrossedHom
      (zcCompletedGroupAlgebraScalar C (MonoidHom.id G))
      (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom) := by
  letI : Module (ZCCompletedGroupAlgebra C G)
      (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom) :=
    Module.compHom _ (zcCompletedGroupAlgebraMap C hC psi)
  exact
    { toFun := zcSeparatedUniversalDifferential C psi.toMonoidHom
      map_mul' := by
        intro g h
        rw [(zcSeparatedUniversalDifferential C psi.toMonoidHom).map_mul]
        congr 1
        change zcGroupLike C H (psi g) •
            zcSeparatedUniversalDifferential C psi.toMonoidHom h =
          zcCompletedGroupAlgebraMap C hC psi (zcGroupLike C G g) •
            zcSeparatedUniversalDifferential C psi.toMonoidHom h
        rw [zcCompletedGroupAlgebraMap_groupLike] }

/--
The source-identity completed differential module maps to the separated module for \(\psi\) by
\(dg \mapsto\) \(d_{\mathrm{sep}}\) g, with source scalars restricted through
\(\mathbb{Z}_C\llbracket G\rrbracket\) \(\to\) \(\mathbb{Z}_C\llbracket H\rrbracket\).
-/
def zcCompletedDifferentialModuleIdToZCSeparatedCompletedDifferentialModule
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (psi : ContinuousMonoidHom G H) :
    letI : Module (ZCCompletedGroupAlgebra C G)
        (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom) :=
      Module.compHom _ (zcCompletedGroupAlgebraMap C hC psi)
    ZCCompletedDifferentialModule C (MonoidHom.id G) →ₗ[ZCCompletedGroupAlgebra C G]
      ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom := by
  letI : Module (ZCCompletedGroupAlgebra C G)
      (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom) :=
    Module.compHom _ (zcCompletedGroupAlgebraMap C hC psi)
  exact
    crossedHomModuleLift
      (A := ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom)
      (zcCompletedGroupAlgebraScalar C (MonoidHom.id G))
      (zcSeparatedUniversalDifferentialSourceCompletedCrossedHom C hC psi)

/--
The comparison map from the identity differential module to the separated completed module sends
the universal differential to the separated universal differential.
-/
@[simp]
theorem zcDiffModuleIdToZCSepDiffModule_universal
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (psi : ContinuousMonoidHom G H) (g : G) :
    zcCompletedDifferentialModuleIdToZCSeparatedCompletedDifferentialModule C hC psi
        (zcUniversalDifferential C (MonoidHom.id G) g) =
      zcSeparatedUniversalDifferential C psi.toMonoidHom g := by
  let : Module (ZCCompletedGroupAlgebra C G)
      (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom) :=
    Module.compHom _ (zcCompletedGroupAlgebraMap C hC psi)
  exact
    crossedHomModuleLift_universal
      (A := ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom)
      (zcCompletedGroupAlgebraScalar C (MonoidHom.id G))
      (zcSeparatedUniversalDifferentialSourceCompletedCrossedHom C hC psi) g

attribute [local implicit_reducible] zcCompletedDifferentialModuleIdentitySourceIndex

/--
The finite source-identity coefficient map agrees with first projecting a completed source
coefficient down to the source-identity stage and then applying the finite target map.
-/
theorem zcCompletedDifferentialModuleIdentitySourceStageRingHom_transition_mapStage
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (psi : ContinuousMonoidHom G H)
    (i : ZCCompletedDifferentialModuleIndex C psi.toMonoidHom) :
    let sourceIndex : ZCCompletedGroupAlgebraIndex C G :=
      (i.target.1, completedGroupAlgebraComapIndexInClass
        (G := G) (H := H) C hC psi i.target.2)
    let idIndex := zcCompletedDifferentialModuleIdentitySourceIndex C psi.toMonoidHom i
    let hle : sourceIndex ≤ idIndex.target := by
      constructor
      · exact le_rfl
      · exact i.compatible
    ∀ x : ZCCompletedGroupAlgebraStage C G idIndex.target,
      zcCompletedGroupAlgebraMapStage C hC psi i.target
          (zcCompletedGroupAlgebraTransition C G hle x) =
        zcCompletedDifferentialModuleIdentitySourceStageRingHom C psi.toMonoidHom i x := by
  intro sourceIndex idIndex hle x
  refine MonoidAlgebra.induction_on
    (motive := fun x : ZCCompletedGroupAlgebraStage C G idIndex.target =>
      zcCompletedGroupAlgebraMapStage C hC psi i.target
          (zcCompletedGroupAlgebraTransition C G hle x) =
        zcCompletedDifferentialModuleIdentitySourceStageRingHom C psi.toMonoidHom i x)
    x ?single ?add ?smul
  · intro q
    refine QuotientGroup.induction_on q ?_
    intro g
    dsimp only [sourceIndex, idIndex, hle,
      zcCompletedDifferentialModuleIdentitySourceIndex] at ⊢
    erw [zcCompletedGroupAlgebraTransition_of]
    simp only [MonoidAlgebra.of_apply]
    simp only [zcCompletedGroupAlgebraMapStage,
      zcCompletedDifferentialModuleIdentitySourceStageRingHom]
    change MonoidAlgebra.mapDomain _ _ = MonoidAlgebra.mapDomain _ _
    let targetSubgroup : Subgroup G :=
      ((OrderDual.ofDual (completedGroupAlgebraComapIndexInClass
        (G := G) (H := H) C hC psi i.target.2)).1 : OpenNormalSubgroup G)
    have hsource_le : (i.source.1 : Subgroup G) ≤ targetSubgroup := by
      change
        (i.source.1 : Subgroup G) ≤
          (((OrderDual.ofDual i.target.2).1 : OpenNormalSubgroup H) : Subgroup H).comap
            psi.toMonoidHom
      exact i.compatible
    have hsource_le_id :
        (i.source.1 : Subgroup G) ≤
          Subgroup.comap (MonoidHom.id G) targetSubgroup := by
      intro a ha
      exact hsource_le ha
    let qSource : CompletedGroupAlgebraQuotientInClass G C (OrderDual.toDual i.source) :=
      QuotientGroup.mk' (i.source.1 : Subgroup G) g
    have hmap :
        (QuotientGroup.map (i.source.1 : Subgroup G)
          targetSubgroup
          (MonoidHom.id G) hsource_le_id) qSource =
            (QuotientGroup.mk'
              targetSubgroup g :
              CompletedGroupAlgebraQuotientInClass G C
                (completedGroupAlgebraComapIndexInClass
                  (G := G) (H := H) C hC psi i.target.2)) := by
      exact QuotientGroup.map_mk'
        (i.source.1 : Subgroup G) targetSubgroup
        (MonoidHom.id G) hsource_le_id g
    change
      MonoidAlgebra.mapDomain _
          (MonoidAlgebra.single
            ((QuotientGroup.map (i.source.1 : Subgroup G)
              targetSubgroup
              (MonoidHom.id G) hsource_le_id) qSource) 1) =
        MonoidAlgebra.mapDomain _
          (MonoidAlgebra.of (ModNCompletedCoeff i.target.1.modulus)
            (CompletedGroupAlgebraQuotientInClass G C (OrderDual.toDual i.source)) qSource)
    rw [hmap]
    dsimp only [CompletedGroupAlgebraQuotientInClass,
      openNormalSubgroupInClassSystem] at ⊢
    rw [MonoidAlgebra.mapDomain_single]
    erw [MonoidAlgebra.of_apply, MonoidAlgebra.mapDomain_single]
    change MonoidAlgebra.single
        ((completedGroupAlgebraComapQuotientMapInClass (G := G) (H := H) C hC psi i.target.2)
          (QuotientGroup.mk'
            ((((OrderDual.ofDual (completedGroupAlgebraComapIndexInClass
              (G := G) (H := H) C hC psi i.target.2)).1 :
                OpenNormalSubgroup G) : Subgroup G)) g)) 1 =
      MonoidAlgebra.single
        ((zcCompletedDifferentialModuleStagePsi C psi.toMonoidHom i)
          (QuotientGroup.mk' (i.source.1 : Subgroup G) g)) 1
    rw [completedGroupAlgebraComapQuotientMapInClass_mk]
    change MonoidAlgebra.single (QuotientGroup.mk'
        ((((OrderDual.ofDual i.target.2).1 : OpenNormalSubgroup H) : Subgroup H))
        (psi g)) 1 =
      MonoidAlgebra.single
        ((QuotientGroup.map (i.source.1 : Subgroup G)
          ((((OrderDual.ofDual i.target.2).1 : OpenNormalSubgroup H) : Subgroup H))
          psi.toMonoidHom i.compatible)
          (QuotientGroup.mk' (i.source.1 : Subgroup G) g)) 1
    rw [QuotientGroup.map_mk']
    rfl
  · intro x y hx hy
    calc
      zcCompletedGroupAlgebraMapStage C hC psi i.target
          (zcCompletedGroupAlgebraTransition C G hle (x + y)) =
        zcCompletedGroupAlgebraMapStage C hC psi i.target
          (zcCompletedGroupAlgebraTransition C G hle x +
            zcCompletedGroupAlgebraTransition C G hle y) := by
              rw [map_add]
      _ =
        zcCompletedGroupAlgebraMapStage C hC psi i.target
            (zcCompletedGroupAlgebraTransition C G hle x) +
          zcCompletedGroupAlgebraMapStage C hC psi i.target
            (zcCompletedGroupAlgebraTransition C G hle y) := by
              rw [map_add]
      _ =
        zcCompletedDifferentialModuleIdentitySourceStageRingHom
            C psi.toMonoidHom i x +
          zcCompletedDifferentialModuleIdentitySourceStageRingHom
            C psi.toMonoidHom i y := by
              rw [hx, hy]
      _ =
        zcCompletedDifferentialModuleIdentitySourceStageRingHom
          C psi.toMonoidHom i (x + y) := by
            exact
              (map_add
                (zcCompletedDifferentialModuleIdentitySourceStageRingHom
                  C psi.toMonoidHom i) x y).symm
  · intro r x hx
    rcases ZMod.intCast_surjective r with ⟨t, rfl⟩
    rw [Algebra.smul_def, RingHom.map_mul, RingHom.map_mul, hx]
    simp only [zcCompletedGroupAlgebraMapStage,
      zcCompletedGroupAlgebraTransition, modNCompletedGroupAlgebraStageCoeffMapInClass,
      modNCompletedGroupRingCoeffMap, AlgHom.toRingHom_eq_coe, map_intCast]
    symm
    calc
      zcCompletedDifferentialModuleIdentitySourceStageRingHom
          C psi.toMonoidHom i (↑t * x) =
        zcCompletedDifferentialModuleIdentitySourceStageRingHom
            C psi.toMonoidHom i (↑t) *
          zcCompletedDifferentialModuleIdentitySourceStageRingHom
            C psi.toMonoidHom i x := by
              exact map_mul _ _ _
      _ = ↑t *
          zcCompletedDifferentialModuleIdentitySourceStageRingHom
            C psi.toMonoidHom i x := by
              rw [map_intCast]

/--
Completed source coefficients viewed at the identity-source stage agree with target finite
projections after applying the completed group-algebra map.
-/
theorem zcCompletedDifferentialModuleIdentitySourceStageRingHom_projection_map
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (psi : ContinuousMonoidHom G H)
    (i : ZCCompletedDifferentialModuleIndex C psi.toMonoidHom)
    (a : ZCCompletedGroupAlgebra C G) :
    zcCompletedDifferentialModuleIdentitySourceStageRingHom C psi.toMonoidHom i
      (zcCompletedGroupAlgebraProjection C G
        (zcCompletedDifferentialModuleIdentitySourceIndex C psi.toMonoidHom i).target a) =
    zcCompletedGroupAlgebraProjection C H i.target
      (zcCompletedGroupAlgebraMap C hC psi a) := by
  let sourceIndex : ZCCompletedGroupAlgebraIndex C G :=
    (i.target.1, completedGroupAlgebraComapIndexInClass
      (G := G) (H := H) C hC psi i.target.2)
  let idIndex := zcCompletedDifferentialModuleIdentitySourceIndex C psi.toMonoidHom i
  have hle : sourceIndex ≤ idIndex.target := by
    constructor
    · exact le_rfl
    · exact i.compatible
  rw [zcCompletedGroupAlgebraProjection_map]
  rw [← zcCompletedDifferentialModuleIdentitySourceStageRingHom_transition_mapStage
    C hC psi i (zcCompletedGroupAlgebraProjection C G idIndex.target a)]
  rw [zcCompletedGroupAlgebraTransition_projection]

/--
Finite-stage projections of the identity-source lift to the separated \(\psi\)-module are
computed by first projecting to the matching source-identity finite stage.
-/
theorem zcDiffModuleIdToZCSepDiffModule_stageProj
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (psi : ContinuousMonoidHom G H)
    (i : ZCCompletedDifferentialModuleIndex C psi.toMonoidHom)
    (x : ZCCompletedDifferentialModule C (MonoidHom.id G)) :
    zcSeparatedCompletedDifferentialModuleStageProjectionAdd C psi.toMonoidHom i
        (zcCompletedDifferentialModuleIdToZCSeparatedCompletedDifferentialModule C hC psi x) =
      zcCompletedDifferentialModuleIdentitySourceStageToStage C psi.toMonoidHom i
        (zcCompletedDifferentialModuleStageProjection C (MonoidHom.id G)
          (zcCompletedDifferentialModuleIdentitySourceIndex C psi.toMonoidHom i) x) := by
  let : Module (ZCCompletedGroupAlgebra C G)
      (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom) :=
    Module.compHom _ (zcCompletedGroupAlgebraMap C hC psi)
  let : Module (ZCCompletedGroupAlgebra C G)
      (ZCCompletedDifferentialModuleStage C psi.toMonoidHom i) :=
    Module.compHom _ (zcCompletedGroupAlgebraMap C hC psi)
  let idIndex := zcCompletedDifferentialModuleIdentitySourceIndex C psi.toMonoidHom i
  let : Module
      (zcCompletedDifferentialModuleStageRing C (MonoidHom.id G) idIndex)
      (ZCCompletedDifferentialModuleStage C psi.toMonoidHom i) :=
    Module.compHom _ (zcCompletedDifferentialModuleIdentitySourceStageRingHom C psi.toMonoidHom i)
  let L :
      ZCCompletedDifferentialModule C (MonoidHom.id G) →ₗ[ZCCompletedGroupAlgebra C G]
        ZCCompletedDifferentialModuleStage C psi.toMonoidHom i :=
    { toFun := fun x =>
        zcSeparatedCompletedDifferentialModuleStageProjectionAdd C psi.toMonoidHom i
          (zcCompletedDifferentialModuleIdToZCSeparatedCompletedDifferentialModule C hC psi x)
      map_add' := by
        intro x y
        rw [map_add, map_add]
      map_smul' := by
        intro a x
        rw [map_smul]
        change
          zcSeparatedCompletedDifferentialModuleStageProjectionAdd C psi.toMonoidHom i
              (zcCompletedGroupAlgebraMap C hC psi a •
                zcCompletedDifferentialModuleIdToZCSeparatedCompletedDifferentialModule
                  C hC psi x) =
            zcCompletedGroupAlgebraMap C hC psi a •
              zcSeparatedCompletedDifferentialModuleStageProjectionAdd C psi.toMonoidHom i
                (zcCompletedDifferentialModuleIdToZCSeparatedCompletedDifferentialModule
                  C hC psi x)
        rw [map_smul] }
  let R :
      ZCCompletedDifferentialModule C (MonoidHom.id G) →ₗ[ZCCompletedGroupAlgebra C G]
        ZCCompletedDifferentialModuleStage C psi.toMonoidHom i :=
    { toFun := fun x =>
        zcCompletedDifferentialModuleIdentitySourceStageToStage C psi.toMonoidHom i
          (zcCompletedDifferentialModuleStageProjection C (MonoidHom.id G)
            (zcCompletedDifferentialModuleIdentitySourceIndex C psi.toMonoidHom i) x)
      map_add' := by
        intro x y
        rw [map_add, map_add]
      map_smul' := by
        intro a x
        rw [map_smul]
        change
          zcCompletedDifferentialModuleIdentitySourceStageToStage C psi.toMonoidHom i
              (zcCompletedGroupAlgebraProjection C G
                idIndex.target a •
                zcCompletedDifferentialModuleStageProjection C (MonoidHom.id G)
                  idIndex x) =
            zcCompletedGroupAlgebraProjection C H i.target
                (zcCompletedGroupAlgebraMap C hC psi a) •
              zcCompletedDifferentialModuleIdentitySourceStageToStage C psi.toMonoidHom i
                (zcCompletedDifferentialModuleStageProjection C (MonoidHom.id G)
                  idIndex x)
        rw [map_smul]
        change
          zcCompletedDifferentialModuleIdentitySourceStageRingHom C psi.toMonoidHom i
              (zcCompletedGroupAlgebraProjection C G idIndex.target a) •
            zcCompletedDifferentialModuleIdentitySourceStageToStage C psi.toMonoidHom i
              (zcCompletedDifferentialModuleStageProjection C (MonoidHom.id G)
                idIndex x) =
            zcCompletedGroupAlgebraProjection C H i.target
                (zcCompletedGroupAlgebraMap C hC psi a) •
              zcCompletedDifferentialModuleIdentitySourceStageToStage C psi.toMonoidHom i
                (zcCompletedDifferentialModuleStageProjection C (MonoidHom.id G)
                  idIndex x)
        rw [zcCompletedDifferentialModuleIdentitySourceStageRingHom_projection_map C hC psi i a] }
  have hLR : L = R := by
    apply crossedDifferentialModuleHom_ext
      (zcCompletedGroupAlgebraScalar C (MonoidHom.id G))
    intro g
    change
      zcSeparatedCompletedDifferentialModuleStageProjectionAdd C psi.toMonoidHom i
          (zcCompletedDifferentialModuleIdToZCSeparatedCompletedDifferentialModule C hC psi
            (zcUniversalDifferential C (MonoidHom.id G) g)) =
        zcCompletedDifferentialModuleIdentitySourceStageToStage C psi.toMonoidHom i
          (zcCompletedDifferentialModuleStageProjection C (MonoidHom.id G)
            idIndex (zcUniversalDifferential C (MonoidHom.id G) g))
    rw [zcDiffModuleIdToZCSepDiffModule_universal,
      zcSeparatedCompletedDifferentialModuleStageProjectionAdd_universal]
    calc
      zcCompletedDifferentialModuleStageDifferential C psi.toMonoidHom i g =
          zcCompletedDifferentialModuleStageProjection C psi.toMonoidHom i
            (zcUniversalDifferential C psi.toMonoidHom g) := by
          rw [zcCompletedDifferentialModuleStageProjection_universal]
      _ =
          zcCompletedDifferentialModuleIdentitySourceStageToStage C psi.toMonoidHom i
            (zcCompletedDifferentialModuleStageProjection C (MonoidHom.id G)
              idIndex (zcUniversalDifferential C (MonoidHom.id G) g)) := by
          exact
            (zcDiffModuleIdentitySourceStageToStage_stageProj_universal
              C psi.toMonoidHom i g).symm
  exact LinearMap.congr_fun hLR x

/--
The finite comparison from the source-identity stage to the \(\psi\)-stage commutes with the
finite Fox boundary.
-/
theorem zcCompletedDifferentialModuleStageBoundary_identitySourceStageToStage
    (ψ : G →* H)
    (i : ZCCompletedDifferentialModuleIndex C ψ)
    (x : ZCCompletedDifferentialModuleStage C (MonoidHom.id G)
        (zcCompletedDifferentialModuleIdentitySourceIndex C ψ i)) :
    zcCompletedDifferentialModuleStageBoundary C ψ i
        (zcCompletedDifferentialModuleIdentitySourceStageToStage C ψ i x) =
      zcCompletedDifferentialModuleIdentitySourceStageRingHom C ψ i
        (zcCompletedDifferentialModuleStageBoundary C (MonoidHom.id G)
          (zcCompletedDifferentialModuleIdentitySourceIndex C ψ i) x) := by
  let j := zcCompletedDifferentialModuleIdentitySourceIndex C ψ i
  let : Module (zcCompletedDifferentialModuleStageRing C (MonoidHom.id G) j)
      (zcCompletedDifferentialModuleStageRing C ψ i) :=
    Module.compHom _ (zcCompletedDifferentialModuleIdentitySourceStageRingHom C ψ i)
  let : Module (zcCompletedDifferentialModuleStageRing C (MonoidHom.id G) j)
      (ZCCompletedDifferentialModuleStage C ψ i) :=
    Module.compHom _ (zcCompletedDifferentialModuleIdentitySourceStageRingHom C ψ i)
  let ringMapLinear :
      zcCompletedDifferentialModuleStageRing C (MonoidHom.id G) j →ₗ[
        zcCompletedDifferentialModuleStageRing C (MonoidHom.id G) j]
        zcCompletedDifferentialModuleStageRing C ψ i := {
    toFun := zcCompletedDifferentialModuleIdentitySourceStageRingHom C ψ i
    map_add' := by
      intro a b
      exact map_add (zcCompletedDifferentialModuleIdentitySourceStageRingHom C ψ i) a b
    map_smul' := by
      intro a b
      change
        zcCompletedDifferentialModuleIdentitySourceStageRingHom C ψ i (a * b) =
          zcCompletedDifferentialModuleIdentitySourceStageRingHom C ψ i a *
            zcCompletedDifferentialModuleIdentitySourceStageRingHom C ψ i b
      exact map_mul (zcCompletedDifferentialModuleIdentitySourceStageRingHom C ψ i) a b }
  let L :
      ZCCompletedDifferentialModuleStage C (MonoidHom.id G) j →ₗ[
        zcCompletedDifferentialModuleStageRing C (MonoidHom.id G) j]
        zcCompletedDifferentialModuleStageRing C ψ i := {
    toFun := fun x =>
      zcCompletedDifferentialModuleStageBoundary C ψ i
        (zcCompletedDifferentialModuleIdentitySourceStageToStage C ψ i x)
    map_add' := by
      intro x y
      rw [map_add, map_add]
    map_smul' := by
      intro a x
      rw [map_smul]
      change
        zcCompletedDifferentialModuleStageBoundary C ψ i
            (zcCompletedDifferentialModuleIdentitySourceStageRingHom C ψ i a •
              zcCompletedDifferentialModuleIdentitySourceStageToStage C ψ i x) =
          zcCompletedDifferentialModuleIdentitySourceStageRingHom C ψ i a •
            zcCompletedDifferentialModuleStageBoundary C ψ i
              (zcCompletedDifferentialModuleIdentitySourceStageToStage C ψ i x)
      rw [map_smul] }
  let R :
      ZCCompletedDifferentialModuleStage C (MonoidHom.id G) j →ₗ[
        zcCompletedDifferentialModuleStageRing C (MonoidHom.id G) j]
        zcCompletedDifferentialModuleStageRing C ψ i :=
    ringMapLinear.comp
      (zcCompletedDifferentialModuleStageBoundary C (MonoidHom.id G) j)
  have hLR : L = R := by
    apply crossedDifferentialModuleHom_ext
      (coeff := zcCompletedDifferentialModuleStageScalar C (MonoidHom.id G) j)
    intro q
    change
      zcCompletedDifferentialModuleStageBoundary C ψ i
          (zcCompletedDifferentialModuleIdentitySourceStageToStage C ψ i
            (universalCrossedDifferential
              (zcCompletedDifferentialModuleStageScalar C (MonoidHom.id G) j) q)) =
        zcCompletedDifferentialModuleIdentitySourceStageRingHom C ψ i
          (zcCompletedDifferentialModuleStageBoundary C (MonoidHom.id G) j
            (universalCrossedDifferential
              (zcCompletedDifferentialModuleStageScalar C (MonoidHom.id G) j) q))
    rw [zcCompletedDifferentialModuleIdentitySourceStageToStage_universal]
    have hboundaryTarget :
        zcCompletedDifferentialModuleStageBoundary C ψ i
            (universalCrossedDifferential
              (zcCompletedDifferentialModuleStageScalar C ψ i) q) =
          zcCompletedDifferentialModuleStageScalar C ψ i q - 1 := by
      rw [zcCompletedDifferentialModuleStageBoundary,
        crossedHomModuleLift_universal, coefficientFoxBoundaryCrossedHom_apply]
    have hboundarySource :
        zcCompletedDifferentialModuleStageBoundary C (MonoidHom.id G) j
            (universalCrossedDifferential
              (zcCompletedDifferentialModuleStageScalar C (MonoidHom.id G) j) q) =
          zcCompletedDifferentialModuleStageScalar C (MonoidHom.id G) j q - 1 := by
      rw [zcCompletedDifferentialModuleStageBoundary,
        crossedHomModuleLift_universal, coefficientFoxBoundaryCrossedHom_apply]
    rw [hboundaryTarget, hboundarySource]
    rw [map_sub, map_one,
      zcCompletedDifferentialModuleIdentitySourceStageRingHom_stageScalar]
  exact LinearMap.congr_fun hLR x

omit [IsTopologicalGroup H] in
/--
Applying the finite identity boundary after the source-identity finite projection recovers the
finite projection of the standard augmentation-valued completed Fox tail.
-/
theorem zcCompletedDifferentialModuleIdentitySourceStageBoundary_stageProj
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (psi : ContinuousMonoidHom G H)
    (i : ZCCompletedDifferentialModuleIndex C psi.toMonoidHom)
    (x : ZCCompletedDifferentialModule C (MonoidHom.id G)) :
    let j := zcCompletedDifferentialModuleIdentitySourceIndex C psi.toMonoidHom i
    zcCompletedDifferentialModuleStageBoundary C (MonoidHom.id G) j
        (zcCompletedDifferentialModuleStageProjection C (MonoidHom.id G) j x) =
      ((zcCompletedGroupAlgebraStandardAugmentationIdealProjection C j.target
        (zcToStdAugIdeal C G (MonoidHom.id G) x) :
          zcCompletedGroupAlgebraStageAugmentationIdeal C G j.target) :
        ZCCompletedGroupAlgebraStage C G j.target) := by
  intro j
  have hcomp := congrArg (fun f => f x)
    (zcDiffModuleStageBoundaryCompletedLinearMap_comp_stageProj
      C (MonoidHom.id G) j)
  simpa [LinearMap.comp_apply,
    zcToStdAugIdeal_val] using hcomp

/--
The identity-source lift to the separated \(\psi\)-module kills the kernel of the standard
augmentation-valued completed Fox tail.
-/
theorem zcDiffModuleIdToZCSepDiffModule_eq_zero_of_zcToStandard_eq_zero
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (psi : ContinuousMonoidHom G H)
    (x : ZCCompletedDifferentialModule C (MonoidHom.id G))
    (hx :
      zcToStdAugIdeal C G (MonoidHom.id G) x = 0) :
    zcCompletedDifferentialModuleIdToZCSeparatedCompletedDifferentialModule C hC psi x = 0 := by
  have hxFox : zcToCompletedGroupAlgebra C (MonoidHom.id G) x = 0 := by
    have hxval :=
      congrArg
        (fun y : zcCompletedGroupAlgebraStandardAugmentationIdeal C G =>
          (y : ZCCompletedGroupAlgebra C G)) hx
    simpa [zcToStdAugIdeal_val] using hxval
  apply zcSeparatedCompletedDifferentialModuleStageProjectionsSeparate C psi.toMonoidHom
  intro i
  rw [zcDiffModuleIdToZCSepDiffModule_stageProj]
  have hsource :
      zcCompletedDifferentialModuleStageProjection C (MonoidHom.id G)
          (zcCompletedDifferentialModuleIdentitySourceIndex C psi.toMonoidHom i) x = 0 :=
    zcDiffModuleIdentitySourceStageProj_eq_zero_of_zcTo_eq_zero
      C psi.toMonoidHom i x hxFox
  rw [hsource, map_zero]

omit [IsTopologicalGroup G] in
/--
The standard-augmentation-valued completed Fox tail is continuous for the finite-stage natural
topology on the completed differential module.
-/
theorem continuous_zcToStdAugIdeal_naturalTopology
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (psi : ContinuousMonoidHom G H) :
    @Continuous
      (ZCCompletedDifferentialModule C psi.toMonoidHom)
      (zcCompletedGroupAlgebraStandardAugmentationIdeal C H)
      (zcCompletedDifferentialModuleNaturalTopology C psi.toMonoidHom)
      inferInstance
      (zcToStdAugIdeal C H psi.toMonoidHom) := by
  let : TopologicalSpace (ZCCompletedDifferentialModule C psi.toMonoidHom) :=
    zcCompletedDifferentialModuleNaturalTopology C psi.toMonoidHom
  have hval :
      @Continuous
        (ZCCompletedDifferentialModule C psi.toMonoidHom)
        (ZCCompletedGroupAlgebra C H)
        (zcCompletedDifferentialModuleNaturalTopology C psi.toMonoidHom)
        inferInstance
        (fun x =>
          (zcToStdAugIdeal
            C H psi.toMonoidHom x : ZCCompletedGroupAlgebra C H)) := by
    have hfun :
        (fun x : ZCCompletedDifferentialModule C psi.toMonoidHom =>
          (zcToStdAugIdeal C H psi.toMonoidHom x : ZCCompletedGroupAlgebra C H)) =
          zcToCompletedGroupAlgebra C psi.toMonoidHom := by
      funext x
      exact zcToStdAugIdeal_val C H psi.toMonoidHom x
    rw [hfun]
    exact continuous_zcToCompletedGroupAlgebra_naturalTopology C hC psi
  exact Continuous.subtype_mk hval
    (fun x => (zcToStdAugIdeal
      C H psi.toMonoidHom x).2)

/--
Kernel group-like source scalars act trivially on the separated module after scalar restriction
along \(\mathbb{Z}_C\llbracket G\rrbracket \to \mathbb{Z}_C\llbracket H\rrbracket\).
-/
theorem zcSeparatedCompletedDifferentialModule_source_kernel_groupLike_smul
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (psi : ContinuousMonoidHom G H) (n : ProfiniteKernelSubgroup psi)
    (x : ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom) :
    letI : Module (ZCCompletedGroupAlgebra C G)
        (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom) :=
      Module.compHom _ (zcCompletedGroupAlgebraMap C hC psi)
    zcGroupLike C G n.1 • x = x := by
  let : Module (ZCCompletedGroupAlgebra C G)
      (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom) :=
    Module.compHom _ (zcCompletedGroupAlgebraMap C hC psi)
  change zcCompletedGroupAlgebraMap C hC psi (zcGroupLike C G n.1) • x = x
  rw [zcCompletedGroupAlgebraMap_groupLike]
  have hn : psi n.1 = 1 := by
    exact MonoidHom.mem_ker.mp
      (show n.1 ∈ psi.toMonoidHom.ker from n.2)
  rw [hn]
  rw [map_one]
  exact one_smul _ x

/--
Source scalar restriction on the separated module is exactly target scalar multiplication after
applying the completed group-algebra map.
-/
theorem zcSeparatedCompletedDifferentialModule_source_map_smul
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (psi : ContinuousMonoidHom G H)
    (a : ZCCompletedGroupAlgebra C G)
    (x : ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom) :
    letI : Module (ZCCompletedGroupAlgebra C G)
        (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom) :=
      Module.compHom _ (zcCompletedGroupAlgebraMap C hC psi)
    zcCompletedGroupAlgebraMap C hC psi a • x = a • x := by
  let : Module (ZCCompletedGroupAlgebra C G)
      (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom) :=
    Module.compHom _ (zcCompletedGroupAlgebraMap C hC psi)
  rfl

/--
Elements of the source kernel augmentation ideal act trivially on the separated module after
restricting scalars along the source map.
-/
theorem zcSeparatedCompletedDifferentialModule_source_kernel_sub_one_smul
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (psi : ContinuousMonoidHom G H) (n : ProfiniteKernelSubgroup psi)
    (x : ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom) :
    letI : Module (ZCCompletedGroupAlgebra C G)
        (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom) :=
      Module.compHom _ (zcCompletedGroupAlgebraMap C hC psi)
    (zcGroupLike C G n.1 - 1) • x = 0 := by
  let : Module (ZCCompletedGroupAlgebra C G)
      (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom) :=
    Module.compHom _ (zcCompletedGroupAlgebraMap C hC psi)
  calc
    (zcGroupLike C G n.1 - 1) • x =
        zcGroupLike C G n.1 • x - x := by
      rw [sub_smul, one_smul]
    _ = 0 := by
      rw [zcSeparatedCompletedDifferentialModule_source_kernel_groupLike_smul C hC psi n x]
      exact sub_self x

/--
The identity-source lift to the separated module kills source kernel augmentation generators
after scalar multiplication.
-/
theorem zcDiffModuleIdToZCSepDiffModule_kernel_sub_one_smul
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (psi : ContinuousMonoidHom G H) (n : ProfiniteKernelSubgroup psi)
    (x : ZCCompletedDifferentialModule C (MonoidHom.id G)) :
    zcCompletedDifferentialModuleIdToZCSeparatedCompletedDifferentialModule C hC psi
        ((zcGroupLike C G n.1 - 1) • x) = 0 := by
  let : Module (ZCCompletedGroupAlgebra C G)
      (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom) :=
    Module.compHom _ (zcCompletedGroupAlgebraMap C hC psi)
  rw [map_smul]
  exact
    zcSeparatedCompletedDifferentialModule_source_kernel_sub_one_smul
      C hC psi n
      (zcCompletedDifferentialModuleIdToZCSeparatedCompletedDifferentialModule
        C hC psi x)

/-- A conditional source-standard-augmentation map to the separated module.  The only remaining
well-definedness input is that the identity Fox tail kernel is killed by the source-identity
lift to the separated module. -/
noncomputable def
    stdAugIdealToZCSepDiffOfBoundaryKernel
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (psi : ContinuousMonoidHom G H)
    (hker :
      ∀ x : ZCCompletedDifferentialModule C (MonoidHom.id G),
        zcToStdAugIdeal C G (MonoidHom.id G) x = 0 →
          zcCompletedDifferentialModuleIdToZCSeparatedCompletedDifferentialModule
            C hC psi x = 0) :
    let : Module (ZCCompletedGroupAlgebra C G)
        (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom) :=
      Module.compHom _ (zcCompletedGroupAlgebraMap C hC psi)
    zcCompletedGroupAlgebraStandardAugmentationIdeal C G →ₗ[ZCCompletedGroupAlgebra C G]
      ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom := by
  let : Module (ZCCompletedGroupAlgebra C G)
      (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom) :=
    Module.compHom _ (zcCompletedGroupAlgebraMap C hC psi)
  let f :=
    zcToStdAugIdeal C G (MonoidHom.id G)
  let L :=
    zcCompletedDifferentialModuleIdToZCSeparatedCompletedDifferentialModule C hC psi
  have hf : Function.Surjective f := by
    exact
      zcToStdAugIdeal_surjective_of_surjective
        C G (MonoidHom.id G) (fun g => ⟨g, rfl⟩)
  have hker_le : LinearMap.ker f ≤ LinearMap.ker L := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    exact hker x hx
  exact
    ((LinearMap.ker f).liftQ L hker_le).comp
      (f.quotKerEquivOfSurjective hf).symm.toLinearMap

/-- The source-standard-augmentation map to the separated module. -/
noncomputable def
    stdAugIdealToZCSepDiff
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (psi : ContinuousMonoidHom G H) :
    let : Module (ZCCompletedGroupAlgebra C G)
        (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom) :=
      Module.compHom _ (zcCompletedGroupAlgebraMap C hC psi)
    zcCompletedGroupAlgebraStandardAugmentationIdeal C G →ₗ[ZCCompletedGroupAlgebra C G]
      ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom :=
  stdAugIdealToZCSepDiffOfBoundaryKernel
    C hC psi
    (zcDiffModuleIdToZCSepDiffModule_eq_zero_of_zcToStandard_eq_zero
      C hC psi)

/-- The conditional map out of the standard augmentation ideal recovers the canonical map from
the completed differential module after composing with its quotient map. -/
@[simp 900]
theorem
    stdAugIdealToZCSepDiffOfBoundaryKernel_comp_zcToStdAugIdeal
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (psi : ContinuousMonoidHom G H)
    (hker :
      ∀ x : ZCCompletedDifferentialModule C (MonoidHom.id G),
        zcToStdAugIdeal C G (MonoidHom.id G) x = 0 →
          zcCompletedDifferentialModuleIdToZCSeparatedCompletedDifferentialModule
            C hC psi x = 0) :
    let : Module (ZCCompletedGroupAlgebra C G)
        (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom) :=
      Module.compHom _ (zcCompletedGroupAlgebraMap C hC psi)
    (stdAugIdealToZCSepDiffOfBoundaryKernel
        C hC psi hker).comp
      (zcToStdAugIdeal C G (MonoidHom.id G)) =
    zcCompletedDifferentialModuleIdToZCSeparatedCompletedDifferentialModule C hC psi := by
  let : Module (ZCCompletedGroupAlgebra C G)
      (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom) :=
    Module.compHom _ (zcCompletedGroupAlgebraMap C hC psi)
  let f :=
    zcToStdAugIdeal C G (MonoidHom.id G)
  let L :=
    zcCompletedDifferentialModuleIdToZCSeparatedCompletedDifferentialModule C hC psi
  have hf : Function.Surjective f := by
    exact
      zcToStdAugIdeal_surjective_of_surjective
        C G (MonoidHom.id G) (fun g => ⟨g, rfl⟩)
  have hker_le : LinearMap.ker f ≤ LinearMap.ker L := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    exact hker x hx
  apply LinearMap.ext
  intro x
  change
    (((LinearMap.ker f).liftQ L hker_le).comp
      (f.quotKerEquivOfSurjective hf).symm.toLinearMap).comp f x = L x
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  have hsymm :
      (f.quotKerEquivOfSurjective hf).symm.toLinearMap (f x) =
        Submodule.Quotient.mk x := by
    exact LinearMap.quotKerEquivOfSurjective_symm_apply (f := f) hf x
  rw [hsymm, Submodule.liftQ_apply]

/-- The standard augmentation-ideal map recovers the canonical separated differential-module
map after precomposition with the quotient map. -/
@[simp]
theorem
    stdAugIdealToZCSepDiff_comp_zcToStdAugIdeal
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (psi : ContinuousMonoidHom G H) :
    let : Module (ZCCompletedGroupAlgebra C G)
        (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom) :=
      Module.compHom _ (zcCompletedGroupAlgebraMap C hC psi)
    (stdAugIdealToZCSepDiff
        C hC psi).comp
      (zcToStdAugIdeal C G (MonoidHom.id G)) =
    zcCompletedDifferentialModuleIdToZCSeparatedCompletedDifferentialModule C hC psi := by
  exact
    stdAugIdealToZCSepDiffOfBoundaryKernel_comp_zcToStdAugIdeal
      C hC psi
      (zcDiffModuleIdToZCSepDiffModule_eq_zero_of_zcToStandard_eq_zero
        C hC psi)

/-- Finite-stage boundary formula for the source-standard map into the separated module. -/
theorem
    stdAugIdealToZCSepDiff_stageBoundary_stageProj
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (psi : ContinuousMonoidHom G H)
    (i : ZCCompletedDifferentialModuleIndex C psi.toMonoidHom)
    (s : zcCompletedGroupAlgebraStandardAugmentationIdeal C G) :
    zcCompletedDifferentialModuleStageBoundary C psi.toMonoidHom i
        (zcSeparatedCompletedDifferentialModuleStageProjectionAdd C psi.toMonoidHom i
          (stdAugIdealToZCSepDiff
            C hC psi s)) =
      zcCompletedGroupAlgebraProjection C H i.target
        (zcCompletedGroupAlgebraMap C hC psi
          (s : ZCCompletedGroupAlgebra C G)) := by
  let : Module (ZCCompletedGroupAlgebra C G)
      (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom) :=
    Module.compHom _ (zcCompletedGroupAlgebraMap C hC psi)
  let f :=
    zcToStdAugIdeal C G (MonoidHom.id G)
  let M :=
    stdAugIdealToZCSepDiff
      C hC psi
  let L :=
    zcCompletedDifferentialModuleIdToZCSeparatedCompletedDifferentialModule C hC psi
  have hf : Function.Surjective f := by
    exact
      zcToStdAugIdeal_surjective_of_surjective
        C G (MonoidHom.id G) (fun g => ⟨g, rfl⟩)
  rcases hf s with ⟨x, hx⟩
  rw [← hx]
  have hcomp :=
    congrArg (fun F => F x)
      (stdAugIdealToZCSepDiff_comp_zcToStdAugIdeal
        C hC psi)
  change M (f x) = L x at hcomp
  rw [hcomp]
  rw [zcDiffModuleIdToZCSepDiffModule_stageProj]
  rw [zcCompletedDifferentialModuleStageBoundary_identitySourceStageToStage]
  rw [zcCompletedDifferentialModuleIdentitySourceStageBoundary_stageProj]
  let idIndex := zcCompletedDifferentialModuleIdentitySourceIndex C psi.toMonoidHom i
  have hmap :=
    zcCompletedDifferentialModuleIdentitySourceStageRingHom_projection_map
      C hC psi i (f x : ZCCompletedGroupAlgebra C G)
  simpa [f, idIndex] using hmap

/-- The finite-stage projection of the source-standard map depends only on the matching
source-identity finite projection of the standard augmentation ideal. -/
theorem
    stdAugIdealToZCSepDiff_stageProj_eq_of_standardProj_eq
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (psi : ContinuousMonoidHom G H)
    (i : ZCCompletedDifferentialModuleIndex C psi.toMonoidHom)
    {s t : zcCompletedGroupAlgebraStandardAugmentationIdeal C G}
    (hst :
      zcCompletedGroupAlgebraStandardAugmentationIdealProjection C
          (zcCompletedDifferentialModuleIdentitySourceIndex C psi.toMonoidHom i).target s =
        zcCompletedGroupAlgebraStandardAugmentationIdealProjection C
          (zcCompletedDifferentialModuleIdentitySourceIndex C psi.toMonoidHom i).target t) :
    zcSeparatedCompletedDifferentialModuleStageProjectionAdd C psi.toMonoidHom i
        (stdAugIdealToZCSepDiff
          C hC psi s) =
      zcSeparatedCompletedDifferentialModuleStageProjectionAdd C psi.toMonoidHom i
        (stdAugIdealToZCSepDiff
          C hC psi t) := by
  let : Module (ZCCompletedGroupAlgebra C G)
      (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom) :=
    Module.compHom _ (zcCompletedGroupAlgebraMap C hC psi)
  let f :=
    zcToStdAugIdeal C G (MonoidHom.id G)
  let M :=
    stdAugIdealToZCSepDiff
      C hC psi
  let L :=
    zcCompletedDifferentialModuleIdToZCSeparatedCompletedDifferentialModule C hC psi
  let idIndex := zcCompletedDifferentialModuleIdentitySourceIndex C psi.toMonoidHom i
  have hf : Function.Surjective f := by
    exact
      zcToStdAugIdeal_surjective_of_surjective
        C G (MonoidHom.id G) (fun g => ⟨g, rfl⟩)
  rcases hf s with ⟨x, hx⟩
  rcases hf t with ⟨y, hy⟩
  have hxyProjection :
      zcCompletedGroupAlgebraStandardAugmentationIdealProjection C idIndex.target (f x) =
        zcCompletedGroupAlgebraStandardAugmentationIdealProjection C idIndex.target (f y) := by
    simpa [idIndex, hx, hy] using hst
  have hcomp_x :=
    congrArg (fun F => F x)
      (stdAugIdealToZCSepDiff_comp_zcToStdAugIdeal
        C hC psi)
  have hcomp_y :=
    congrArg (fun F => F y)
      (stdAugIdealToZCSepDiff_comp_zcToStdAugIdeal
        C hC psi)
  change M (f x) = L x at hcomp_x
  change M (f y) = L y at hcomp_y
  rw [← hx, ← hy, hcomp_x, hcomp_y]
  rw [zcDiffModuleIdToZCSepDiffModule_stageProj,
    zcDiffModuleIdToZCSepDiffModule_stageProj]
  have hsource :
      zcCompletedDifferentialModuleStageProjection C (MonoidHom.id G) idIndex x =
        zcCompletedDifferentialModuleStageProjection C (MonoidHom.id G) idIndex y := by
    apply sub_eq_zero.mp
    have hzero :
        zcCompletedDifferentialModuleStageProjection C (MonoidHom.id G) idIndex (x - y) = 0 :=
      zcDiffModuleIdentitySourceStageProj_eq_zero_of_boundary_eq_zero
        C psi.toMonoidHom i (x - y) (by
          rw [map_sub]
          rw [map_sub]
          rw [zcCompletedDifferentialModuleIdentitySourceStageBoundary_stageProj,
            zcCompletedDifferentialModuleIdentitySourceStageBoundary_stageProj]
          rw [hxyProjection, sub_self])
    simpa [map_sub] using hzero
  rw [hsource]

/-- Each finite-stage coordinate of the source-standard map into the separated module is
continuous.  The coordinate factors through the matching finite standard augmentation
projection. -/
theorem
    continuous_stdAugIdealToZCSepDiff_stageProj
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (psi : ContinuousMonoidHom G H)
    (i : ZCCompletedDifferentialModuleIndex C psi.toMonoidHom) :
    Continuous
      (fun s : zcCompletedGroupAlgebraStandardAugmentationIdeal C G =>
        zcSeparatedCompletedDifferentialModuleStageProjectionAdd C psi.toMonoidHom i
          (stdAugIdealToZCSepDiff
            C hC psi s)) := by
  let idIndex := zcCompletedDifferentialModuleIdentitySourceIndex C psi.toMonoidHom i
  let p :=
    zcCompletedGroupAlgebraStandardAugmentationIdealProjection C idIndex.target
  have hsurj : Function.Surjective p :=
    zcCompletedGroupAlgebraStandardAugmentationIdealProjection_surjective C idIndex.target
  let F : zcCompletedGroupAlgebraStageAugmentationIdeal C G idIndex.target →
      ZCCompletedDifferentialModuleStage C psi.toMonoidHom i := fun y =>
    zcSeparatedCompletedDifferentialModuleStageProjectionAdd C psi.toMonoidHom i
      (stdAugIdealToZCSepDiff
        C hC psi (Classical.choose (hsurj y)))
  have hfactor :
      (fun s : zcCompletedGroupAlgebraStandardAugmentationIdeal C G =>
        zcSeparatedCompletedDifferentialModuleStageProjectionAdd C psi.toMonoidHom i
          (stdAugIdealToZCSepDiff
            C hC psi s)) =
        fun s => F (p s) := by
    funext s
    exact
      stdAugIdealToZCSepDiff_stageProj_eq_of_standardProj_eq
        C hC psi i
        (by
          dsimp [p, F]
          exact (Classical.choose_spec (hsurj (p s))).symm)
  rw [hfactor]
  have : DiscreteTopology (zcCompletedGroupAlgebraStageAugmentationIdeal C G idIndex.target) := by
    infer_instance
  have hF : Continuous F :=
    continuous_of_discreteTopology
  exact hF.comp (continuous_zcCompletedGroupAlgebraStandardAugmentationIdealProjection C
      idIndex.target)

/-- The product of all finite-stage coordinates of the source-standard map into the separated
module is continuous. -/
theorem
    continuous_stdAugIdealToZCSepDiff_stageProjProduct
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (psi : ContinuousMonoidHom G H) :
    Continuous
      (fun s : zcCompletedGroupAlgebraStandardAugmentationIdeal C G =>
        zcSeparatedCompletedDifferentialModuleStageProjectionProduct C psi.toMonoidHom
          (stdAugIdealToZCSepDiff
            C hC psi s)) := by
  exact continuous_pi fun i =>
    continuous_stdAugIdealToZCSepDiff_stageProj
      C hC psi i

/-- The source-standard map to the separated completed differential module is continuous for
the finite-stage quotient topology. -/
theorem
    continuous_stdAugIdealToZCSepDiff
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) :
    let : TopologicalSpace (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom) :=
      zcSeparatedCompletedDifferentialModuleNaturalTopology C psi.toMonoidHom
    @Continuous
      (zcCompletedGroupAlgebraStandardAugmentationIdeal C G)
      (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom)
      inferInstance
      (zcSeparatedCompletedDifferentialModuleNaturalTopology C psi.toMonoidHom)
      (stdAugIdealToZCSepDiff
        C hC psi) := by
  let : Nonempty (ZCCompletedDifferentialModuleIndex C psi.toMonoidHom) :=
    nonempty_zcCompletedDifferentialModuleIndex C hC psi
  rw [zcSepDiffModuleNaturalTopology_eq_induced_stageProjProduct
    C psi.toMonoidHom (directed_zcCompletedDifferentialModuleIndex C hForm hC psi)]
  rw [continuous_induced_rng]
  exact
    continuous_stdAugIdealToZCSepDiff_stageProjProduct
      C hC psi

/-- The conditional augmentation-ideal map sends a group boundary to the separated universal
differential of that group element. -/
@[simp 900]
theorem
    stdAugIdealToZCSepDiffOfBoundaryKernel_boundary
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (psi : ContinuousMonoidHom G H)
    (hker :
      ∀ x : ZCCompletedDifferentialModule C (MonoidHom.id G),
        zcToStdAugIdeal C G (MonoidHom.id G) x = 0 →
          zcCompletedDifferentialModuleIdToZCSeparatedCompletedDifferentialModule
            C hC psi x = 0)
    (g : G) :
    stdAugIdealToZCSepDiffOfBoundaryKernel
        C hC psi hker
        ⟨zcCompletedGroupAlgebraBoundary C (MonoidHom.id G) g,
          zcCompletedGroupAlgebraBoundary_mem_standardAugmentationIdeal
            C G (MonoidHom.id G) g⟩ =
      zcSeparatedUniversalDifferential C psi.toMonoidHom g := by
  let : Module (ZCCompletedGroupAlgebra C G)
      (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom) :=
    Module.compHom _ (zcCompletedGroupAlgebraMap C hC psi)
  have hcomp :=
    congrArg
      (fun f =>
        f (zcUniversalDifferential C (MonoidHom.id G) g))
      (stdAugIdealToZCSepDiffOfBoundaryKernel_comp_zcToStdAugIdeal
        C hC psi hker)
  change
    stdAugIdealToZCSepDiffOfBoundaryKernel C hC psi hker
        (zcToStdAugIdeal C G (MonoidHom.id G)
          (zcUniversalDifferential C (MonoidHom.id G) g)) =
      zcCompletedDifferentialModuleIdToZCSeparatedCompletedDifferentialModule
        C hC psi (zcUniversalDifferential C (MonoidHom.id G) g) at hcomp
  have hboundary :
      zcToStdAugIdeal C G (MonoidHom.id G)
          (zcUniversalDifferential C (MonoidHom.id G) g) =
        ⟨zcCompletedGroupAlgebraBoundary C (MonoidHom.id G) g,
          zcCompletedGroupAlgebraBoundary_mem_standardAugmentationIdeal
            C G (MonoidHom.id G) g⟩ := by
    exact
      crossedHomModuleLift_universal
        (A := zcCompletedGroupAlgebraStandardAugmentationIdeal C G)
        (zcCompletedGroupAlgebraScalar C (MonoidHom.id G))
        (zcCompletedGroupAlgebraBoundaryToStandardAugmentationIdeal
          C G (MonoidHom.id G))
        g
  calc
    stdAugIdealToZCSepDiffOfBoundaryKernel
        C hC psi hker
        ⟨zcCompletedGroupAlgebraBoundary C (MonoidHom.id G) g,
          zcCompletedGroupAlgebraBoundary_mem_standardAugmentationIdeal
            C G (MonoidHom.id G) g⟩ =
      zcCompletedDifferentialModuleIdToZCSeparatedCompletedDifferentialModule
        C hC psi (zcUniversalDifferential C (MonoidHom.id G) g) := by
        rw [← hboundary]
        exact hcomp
    _ = zcSeparatedUniversalDifferential C psi.toMonoidHom g := by
        exact
          zcDiffModuleIdToZCSepDiffModule_universal
            C hC psi g

/-- The augmentation-ideal map sends a group boundary to the separated universal
differential. -/
@[simp]
theorem
    stdAugIdealToZCSepDiff_boundary
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (psi : ContinuousMonoidHom G H)
    (g : G) :
    stdAugIdealToZCSepDiff
        C hC psi
        ⟨zcCompletedGroupAlgebraBoundary C (MonoidHom.id G) g,
          zcCompletedGroupAlgebraBoundary_mem_standardAugmentationIdeal
            C G (MonoidHom.id G) g⟩ =
      zcSeparatedUniversalDifferential C psi.toMonoidHom g := by
  exact
    stdAugIdealToZCSepDiffOfBoundaryKernel_boundary
      C hC psi
      (zcDiffModuleIdToZCSepDiffModule_eq_zero_of_zcToStandard_eq_zero
        C hC psi) g

/-- The conditional source-standard map kills each algebraic kernel-product generator. -/
theorem
    stdAugIdealToZCSepDiffOfBoundaryKernel_kernel_generator_smul
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (psi : ContinuousMonoidHom G H)
    (hker :
      ∀ x : ZCCompletedDifferentialModule C (MonoidHom.id G),
        zcToStdAugIdeal C G (MonoidHom.id G) x = 0 →
          zcCompletedDifferentialModuleIdToZCSeparatedCompletedDifferentialModule
            C hC psi x = 0)
    (n : ProfiniteKernelSubgroup psi)
    (s : zcCompletedGroupAlgebraStandardAugmentationIdeal C G) :
    stdAugIdealToZCSepDiffOfBoundaryKernel
        C hC psi hker ((zcGroupLike C G n.1 - 1) • s) = 0 := by
  let : Module (ZCCompletedGroupAlgebra C G)
      (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom) :=
    Module.compHom _ (zcCompletedGroupAlgebraMap C hC psi)
  let f :=
    zcToStdAugIdeal C G (MonoidHom.id G)
  let M :=
    stdAugIdealToZCSepDiffOfBoundaryKernel
      C hC psi hker
  let L :=
    zcCompletedDifferentialModuleIdToZCSeparatedCompletedDifferentialModule C hC psi
  have hf : Function.Surjective f := by
    exact
      zcToStdAugIdeal_surjective_of_surjective
        C G (MonoidHom.id G) (fun g => ⟨g, rfl⟩)
  rcases hf s with ⟨y, hy⟩
  have hcomp :=
    congrArg
      (fun F =>
        F ((zcGroupLike C G n.1 - 1) • y))
      (stdAugIdealToZCSepDiffOfBoundaryKernel_comp_zcToStdAugIdeal
        C hC psi hker)
  change
    M (f ((zcGroupLike C G n.1 - 1) • y)) =
      L ((zcGroupLike C G n.1 - 1) • y) at hcomp
  have harg :
      (zcGroupLike C G n.1 - 1) • s =
        f ((zcGroupLike C G n.1 - 1) • y) := by
    rw [map_smul, hy]
  calc
    M ((zcGroupLike C G n.1 - 1) • s) =
        M (f ((zcGroupLike C G n.1 - 1) • y)) := by
          rw [harg]
    _ = L ((zcGroupLike C G n.1 - 1) • y) := by
          exact hcomp
    _ = 0 := by
          exact
            zcDiffModuleIdToZCSepDiffModule_kernel_sub_one_smul
              C hC psi n y

/-- The conditional source-standard map kills the algebraic product `I(ker psi) I(G)`. -/
theorem
    stdAugIdealToZCSepDiffOfBoundaryKernel_kills_kernelMulStandard
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (psi : ContinuousMonoidHom G H)
    (hker :
      ∀ x : ZCCompletedDifferentialModule C (MonoidHom.id G),
        zcToStdAugIdeal C G (MonoidHom.id G) x = 0 →
          zcCompletedDifferentialModuleIdToZCSeparatedCompletedDifferentialModule
            C hC psi x = 0)
    {x : zcCompletedGroupAlgebraStandardAugmentationIdeal C G}
    (hx : x ∈ zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi) :
    stdAugIdealToZCSepDiffOfBoundaryKernel
        C hC psi hker x = 0 := by
  let : Module (ZCCompletedGroupAlgebra C G)
      (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom) :=
    Module.compHom _ (zcCompletedGroupAlgebraMap C hC psi)
  let M :=
    stdAugIdealToZCSepDiffOfBoundaryKernel
      C hC psi hker
  rw [zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard] at hx
  refine Submodule.span_induction
    (p := fun y _ => M y = 0) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨p, rfl⟩
    exact
      stdAugIdealToZCSepDiffOfBoundaryKernel_kernel_generator_smul
        C hC psi hker p.1 p.2
  · exact map_zero M
  · intro y z _ _ hy hz
    rw [map_add, hy, hz, add_zero]
  · intro a y _ hy
    rw [map_smul, hy, smul_zero]

/-- The source-standard map kills the algebraic product `I(ker psi) I(G)`. -/
theorem
    stdAugIdealToZCSepDiff_kills_kernelMulStandard
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (psi : ContinuousMonoidHom G H)
    {x : zcCompletedGroupAlgebraStandardAugmentationIdeal C G}
    (hx : x ∈ zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi) :
    stdAugIdealToZCSepDiff
        C hC psi x = 0 :=
  stdAugIdealToZCSepDiffOfBoundaryKernel_kills_kernelMulStandard
    C hC psi
    (zcDiffModuleIdToZCSepDiffModule_eq_zero_of_zcToStandard_eq_zero
      C hC psi) hx

/-- If the conditional source-standard map is continuous for the separated quotient topology,
then killing the algebraic denominator implies that it kills the finite-stage closed denominator.
-/
theorem
    stdAugIdealToZCSepDiffOfBoundaryKernel_kills_kernelMulStandardClosed_of_continuous
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (hker :
      ∀ x : ZCCompletedDifferentialModule C (MonoidHom.id G),
        zcToStdAugIdeal C G (MonoidHom.id G) x = 0 →
          zcCompletedDifferentialModuleIdToZCSeparatedCompletedDifferentialModule
            C hC psi x = 0)
    (hcont :
      let : TopologicalSpace (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom) :=
        zcSeparatedCompletedDifferentialModuleNaturalTopology C psi.toMonoidHom
      @Continuous
        (zcCompletedGroupAlgebraStandardAugmentationIdeal C G)
        (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom)
        inferInstance
        (zcSeparatedCompletedDifferentialModuleNaturalTopology C psi.toMonoidHom)
        (stdAugIdealToZCSepDiffOfBoundaryKernel
          C hC psi hker))
    {x : zcCompletedGroupAlgebraStandardAugmentationIdeal C G}
    (hx : x ∈ zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
        C hC hForm psi hpsi hfopen) :
    stdAugIdealToZCSepDiffOfBoundaryKernel
        C hC psi hker x = 0 := by
  let : TopologicalSpace (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom) :=
    zcSeparatedCompletedDifferentialModuleNaturalTopology C psi.toMonoidHom
  let M :=
    stdAugIdealToZCSepDiffOfBoundaryKernel
      C hC psi hker
  have hxcl :
      x ∈ closure
        ((zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi :
          Set (zcCompletedGroupAlgebraStandardAugmentationIdeal C G))) := by
    rw [closure_zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard_eq_closed
      C hC hForm psi hpsi hfopen]
    exact hx
  have hclosed_preimage :
      IsClosed
        (M ⁻¹'
          ({0} : Set (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom))) := by
    exact
      (isClosed_zero_zcSeparatedCompletedDifferentialModuleNaturalTopology
        C psi.toMonoidHom).preimage hcont
  have hsubset :
      ((zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi :
        Set (zcCompletedGroupAlgebraStandardAugmentationIdeal C G))) ⊆
        M ⁻¹' ({0} : Set (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom)) := by
    intro y hy
    exact
      stdAugIdealToZCSepDiffOfBoundaryKernel_kills_kernelMulStandard
        C hC psi hker hy
  exact closure_minimal hsubset hclosed_preimage hxcl

/-- If the source-standard map is continuous for the separated quotient topology, then it kills
the closed finite-stage denominator. -/
theorem
    stdAugIdealToZCSepDiff_kills_kernelMulStandardClosed_of_continuous
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (hcont :
      let : TopologicalSpace (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom) :=
        zcSeparatedCompletedDifferentialModuleNaturalTopology C psi.toMonoidHom
      @Continuous
        (zcCompletedGroupAlgebraStandardAugmentationIdeal C G)
        (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom)
        inferInstance
        (zcSeparatedCompletedDifferentialModuleNaturalTopology C psi.toMonoidHom)
        (stdAugIdealToZCSepDiff
          C hC psi))
    {x : zcCompletedGroupAlgebraStandardAugmentationIdeal C G}
    (hx : x ∈ zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
        C hC hForm psi hpsi hfopen) :
    stdAugIdealToZCSepDiff
        C hC psi x = 0 := by
  have hcont' :
      let : TopologicalSpace (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom) :=
        zcSeparatedCompletedDifferentialModuleNaturalTopology C psi.toMonoidHom
      @Continuous
        (zcCompletedGroupAlgebraStandardAugmentationIdeal C G)
        (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom)
        inferInstance
        (zcSeparatedCompletedDifferentialModuleNaturalTopology C psi.toMonoidHom)
        (stdAugIdealToZCSepDiffOfBoundaryKernel
          C hC psi
          (zcDiffModuleIdToZCSepDiffModule_eq_zero_of_zcToStandard_eq_zero
            C hC psi)) := by
    simpa [stdAugIdealToZCSepDiff] using hcont
  exact
    stdAugIdealToZCSepDiffOfBoundaryKernel_kills_kernelMulStandardClosed_of_continuous
      C hC hForm psi hpsi hfopen
      (zcDiffModuleIdToZCSepDiffModule_eq_zero_of_zcToStandard_eq_zero
        C hC psi) hcont' hx

/-- The source-standard map kills the closed finite-stage denominator. -/
theorem
    stdAugIdealToZCSepDiff_kills_kernelMulStandardClosed
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    {x : zcCompletedGroupAlgebraStandardAugmentationIdeal C G}
    (hx : x ∈ zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
        C hC hForm psi hpsi hfopen) :
    stdAugIdealToZCSepDiff
        C hC psi x = 0 :=
  stdAugIdealToZCSepDiff_kills_kernelMulStandardClosed_of_continuous
    C hC hForm psi hpsi hfopen
    (continuous_stdAugIdealToZCSepDiff
      C hC hForm psi) hx

/-- A conditional reverse map from the closed source augmentation quotient to the separated
module.  The remaining closed-denominator input is isolated as `hclosed_kill`. -/
noncomputable def
    kerAugIdealQuotToZCSepDiffOfBoundaryKernelOfClosedKill
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (hker :
      ∀ x : ZCCompletedDifferentialModule C (MonoidHom.id G),
        zcToStdAugIdeal C G (MonoidHom.id G) x = 0 →
          zcCompletedDifferentialModuleIdToZCSeparatedCompletedDifferentialModule
            C hC psi x = 0)
    (hclosed_kill :
      ∀ x : zcCompletedGroupAlgebraStandardAugmentationIdeal C G,
        x ∈ zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
            C hC hForm psi hpsi hfopen →
          stdAugIdealToZCSepDiffOfBoundaryKernel
            C hC psi hker x = 0) :
    let : Module (ZCCompletedGroupAlgebra C G)
        (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom) :=
      Module.compHom _ (zcCompletedGroupAlgebraMap C hC psi)
    KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen
      →ₗ[ZCCompletedGroupAlgebra C G]
    ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom := by
  let : Module (ZCCompletedGroupAlgebra C G)
      (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom) :=
    Module.compHom _ (zcCompletedGroupAlgebraMap C hC psi)
  let M :=
    stdAugIdealToZCSepDiffOfBoundaryKernel
      C hC psi hker
  exact
    (zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
      C hC hForm psi hpsi hfopen).liftQ M
      (by
        intro x hx
        rw [LinearMap.mem_ker]
        exact hclosed_kill x hx)

/-- The conditional map from the closed augmentation quotient sends the class of a boundary to
the separated universal differential. -/
@[simp 900]
theorem
    kerAugIdealQuotToZCSepDiffOfBoundaryKernelOfClosedKill_boundary
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (hker :
      ∀ x : ZCCompletedDifferentialModule C (MonoidHom.id G),
        zcToStdAugIdeal C G (MonoidHom.id G) x = 0 →
          zcCompletedDifferentialModuleIdToZCSeparatedCompletedDifferentialModule
            C hC psi x = 0)
    (hclosed_kill :
      ∀ x : zcCompletedGroupAlgebraStandardAugmentationIdeal C G,
        x ∈ zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
            C hC hForm psi hpsi hfopen →
          stdAugIdealToZCSepDiffOfBoundaryKernel
            C hC psi hker x = 0)
    (g : G) :
    kerAugIdealQuotToZCSepDiffOfBoundaryKernelOfClosedKill
        C hC hForm psi hpsi hfopen hker hclosed_kill
        (Submodule.Quotient.mk
          (p := zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
            C hC hForm psi hpsi hfopen)
          ⟨zcCompletedGroupAlgebraBoundary C (MonoidHom.id G) g,
            zcCompletedGroupAlgebraBoundary_mem_standardAugmentationIdeal
              C G (MonoidHom.id G) g⟩) =
      zcSeparatedUniversalDifferential C psi.toMonoidHom g := by
  let : Module (ZCCompletedGroupAlgebra C G)
      (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom) :=
    Module.compHom _ (zcCompletedGroupAlgebraMap C hC psi)
  rw [kerAugIdealQuotToZCSepDiffOfBoundaryKernelOfClosedKill,
    Submodule.liftQ_apply]
  exact
    stdAugIdealToZCSepDiffOfBoundaryKernel_boundary
      C hC psi hker g

/-- Target-linear version of the conditional reverse map from the closed source augmentation
quotient to the separated module. -/
noncomputable def
    kerAugIdealQuotToZCSepDiffLinearOfBoundaryKernelOfClosedKill
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (hker :
      ∀ x : ZCCompletedDifferentialModule C (MonoidHom.id G),
        zcToStdAugIdeal C G (MonoidHom.id G) x = 0 →
          zcCompletedDifferentialModuleIdToZCSeparatedCompletedDifferentialModule
            C hC psi x = 0)
    (hclosed_kill :
      ∀ x : zcCompletedGroupAlgebraStandardAugmentationIdeal C G,
        x ∈ zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
            C hC hForm psi hpsi hfopen →
          stdAugIdealToZCSepDiffOfBoundaryKernel
            C hC psi hker x = 0) :
    let : Module (ZCCompletedGroupAlgebra C H)
        (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
      kerAugClosedQuotTargetCompletedModuleOfSurj
        C hC hForm psi hpsi hfopen
    KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen
      →ₗ[ZCCompletedGroupAlgebra C H]
    ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom := by
  let : Module (ZCCompletedGroupAlgebra C H)
      (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
    kerAugClosedQuotTargetCompletedModuleOfSurj
      C hC hForm psi hpsi hfopen
  let : Module (ZCCompletedGroupAlgebra C G)
      (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom) :=
    Module.compHom _ (zcCompletedGroupAlgebraMap C hC psi)
  let Q :=
    kerAugIdealQuotToZCSepDiffOfBoundaryKernelOfClosedKill
      C hC hForm psi hpsi hfopen hker hclosed_kill
  refine
    { toFun := Q
      map_add' := by
        intro x y
        exact map_add Q x y
      map_smul' := by
        intro a x
        change Q
            (zcCompletedGroupAlgebraTargetLiftOfSurjective C hC hForm psi hpsi a • x) =
          a • Q x
        rw [map_smul]
        symm
        calc
          a • Q x =
              zcCompletedGroupAlgebraMap C hC psi
                  (zcCompletedGroupAlgebraTargetLiftOfSurjective C hC hForm psi hpsi a) •
                Q x := by
                rw [zcCompletedGroupAlgebraMap_targetLiftOfSurjective]
          _ =
              zcCompletedGroupAlgebraTargetLiftOfSurjective C hC hForm psi hpsi a •
                Q x := by
                exact
                  zcSeparatedCompletedDifferentialModule_source_map_smul
                    C hC psi
                    (zcCompletedGroupAlgebraTargetLiftOfSurjective C hC hForm psi hpsi a)
                    (Q x) }

/-- The target-linear conditional quotient map sends each boundary class to the separated
universal differential. -/
@[simp 900]
theorem
    kerAugIdealQuotToZCSepDiffLinearOfBoundaryKernelOfClosedKill_boundary
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (hker :
      ∀ x : ZCCompletedDifferentialModule C (MonoidHom.id G),
        zcToStdAugIdeal C G (MonoidHom.id G) x = 0 →
          zcCompletedDifferentialModuleIdToZCSeparatedCompletedDifferentialModule
            C hC psi x = 0)
    (hclosed_kill :
      ∀ x : zcCompletedGroupAlgebraStandardAugmentationIdeal C G,
        x ∈ zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
            C hC hForm psi hpsi hfopen →
          stdAugIdealToZCSepDiffOfBoundaryKernel
            C hC psi hker x = 0)
    (g : G) :
    kerAugIdealQuotToZCSepDiffLinearOfBoundaryKernelOfClosedKill
        C hC hForm psi hpsi hfopen hker hclosed_kill
        (Submodule.Quotient.mk
          (p := zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
            C hC hForm psi hpsi hfopen)
          ⟨zcCompletedGroupAlgebraBoundary C (MonoidHom.id G) g,
            zcCompletedGroupAlgebraBoundary_mem_standardAugmentationIdeal
              C G (MonoidHom.id G) g⟩) =
      zcSeparatedUniversalDifferential C psi.toMonoidHom g := by
  exact
    kerAugIdealQuotToZCSepDiffOfBoundaryKernelOfClosedKill_boundary
      C hC hForm psi hpsi hfopen hker hclosed_kill g

/-- Target-linear reverse map from the closed source augmentation quotient to the separated
module, reducing the closed-denominator condition to continuity of the source-standard map. -/
noncomputable def
    kerAugIdealQuotToZCSepDiffLinearOfBoundaryKernelOfContStdMap
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (hker :
      ∀ x : ZCCompletedDifferentialModule C (MonoidHom.id G),
        zcToStdAugIdeal C G (MonoidHom.id G) x = 0 →
          zcCompletedDifferentialModuleIdToZCSeparatedCompletedDifferentialModule
            C hC psi x = 0)
    (hcont :
      let : TopologicalSpace (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom) :=
        zcSeparatedCompletedDifferentialModuleNaturalTopology C psi.toMonoidHom
      @Continuous
        (zcCompletedGroupAlgebraStandardAugmentationIdeal C G)
        (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom)
        inferInstance
        (zcSeparatedCompletedDifferentialModuleNaturalTopology C psi.toMonoidHom)
        (stdAugIdealToZCSepDiffOfBoundaryKernel
          C hC psi hker)) :
    let : Module (ZCCompletedGroupAlgebra C H)
        (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
      kerAugClosedQuotTargetCompletedModuleOfSurj
        C hC hForm psi hpsi hfopen
    KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen
      →ₗ[ZCCompletedGroupAlgebra C H]
    ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom :=
  kerAugIdealQuotToZCSepDiffLinearOfBoundaryKernelOfClosedKill
    C hC hForm psi hpsi hfopen hker
    (fun _ hx =>
      stdAugIdealToZCSepDiffOfBoundaryKernel_kills_kernelMulStandardClosed_of_continuous
        C hC hForm psi hpsi hfopen hker hcont hx)

/-- Under continuity of the conditional standard map, the target-linear quotient map sends a
boundary class to the separated universal differential. -/
@[simp 900]
theorem
    kerAugIdealQuotToZCSepDiffLinearOfBoundaryKernelOfContStdMap_boundary
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (hker :
      ∀ x : ZCCompletedDifferentialModule C (MonoidHom.id G),
        zcToStdAugIdeal C G (MonoidHom.id G) x = 0 →
          zcCompletedDifferentialModuleIdToZCSeparatedCompletedDifferentialModule
            C hC psi x = 0)
    (hcont :
      let : TopologicalSpace (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom) :=
        zcSeparatedCompletedDifferentialModuleNaturalTopology C psi.toMonoidHom
      @Continuous
        (zcCompletedGroupAlgebraStandardAugmentationIdeal C G)
        (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom)
        inferInstance
        (zcSeparatedCompletedDifferentialModuleNaturalTopology C psi.toMonoidHom)
        (stdAugIdealToZCSepDiffOfBoundaryKernel
          C hC psi hker))
    (g : G) :
    kerAugIdealQuotToZCSepDiffLinearOfBoundaryKernelOfContStdMap
        C hC hForm psi hpsi hfopen hker hcont
        (Submodule.Quotient.mk
          (p := zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
            C hC hForm psi hpsi hfopen)
          ⟨zcCompletedGroupAlgebraBoundary C (MonoidHom.id G) g,
            zcCompletedGroupAlgebraBoundary_mem_standardAugmentationIdeal
              C G (MonoidHom.id G) g⟩) =
      zcSeparatedUniversalDifferential C psi.toMonoidHom g := by
  exact
    kerAugIdealQuotToZCSepDiffLinearOfBoundaryKernelOfClosedKill_boundary
      C hC hForm psi hpsi hfopen hker
      (fun x hx =>
        stdAugIdealToZCSepDiffOfBoundaryKernel_kills_kernelMulStandardClosed_of_continuous
          C hC hForm psi hpsi hfopen hker hcont hx)
      g

/-- Reverse map from the closed source augmentation quotient to the separated module, assuming
only that the closed denominator is killed by the unconditional source-standard map. -/
noncomputable def
    kerAugIdealQuotToZCSepDiffOfClosedKill
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (hclosed_kill :
      ∀ x : zcCompletedGroupAlgebraStandardAugmentationIdeal C G,
        x ∈ zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
            C hC hForm psi hpsi hfopen →
          stdAugIdealToZCSepDiff
            C hC psi x = 0) :
    let : Module (ZCCompletedGroupAlgebra C G)
        (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom) :=
      Module.compHom _ (zcCompletedGroupAlgebraMap C hC psi)
    KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen
      →ₗ[ZCCompletedGroupAlgebra C G]
    ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom :=
  kerAugIdealQuotToZCSepDiffOfBoundaryKernelOfClosedKill
    C hC hForm psi hpsi hfopen
    (zcDiffModuleIdToZCSepDiffModule_eq_zero_of_zcToStandard_eq_zero
      C hC psi)
    (fun x hx => by
      simpa [stdAugIdealToZCSepDiff]
        using hclosed_kill x hx)

/-- If the closed denominator is killed, the resulting quotient map sends a boundary class to
the separated universal differential. -/
@[simp 900]
theorem
    kerAugIdealQuotToZCSepDiffOfClosedKill_boundary
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (hclosed_kill :
      ∀ x : zcCompletedGroupAlgebraStandardAugmentationIdeal C G,
        x ∈ zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
            C hC hForm psi hpsi hfopen →
          stdAugIdealToZCSepDiff
            C hC psi x = 0)
    (g : G) :
    kerAugIdealQuotToZCSepDiffOfClosedKill
        C hC hForm psi hpsi hfopen hclosed_kill
        (Submodule.Quotient.mk
          (p := zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
            C hC hForm psi hpsi hfopen)
          ⟨zcCompletedGroupAlgebraBoundary C (MonoidHom.id G) g,
            zcCompletedGroupAlgebraBoundary_mem_standardAugmentationIdeal
              C G (MonoidHom.id G) g⟩) =
      zcSeparatedUniversalDifferential C psi.toMonoidHom g := by
  exact
    kerAugIdealQuotToZCSepDiffOfBoundaryKernelOfClosedKill_boundary
      C hC hForm psi hpsi hfopen
      (zcDiffModuleIdToZCSepDiffModule_eq_zero_of_zcToStandard_eq_zero
        C hC psi)
      (fun x hx => by
        simpa [stdAugIdealToZCSepDiff]
          using hclosed_kill x hx) g

/-- The reverse map from the closed source augmentation quotient to the separated module is
continuous once the source-standard map is continuous. -/
theorem
    continuous_kerAugIdealQuotToZCSepDiffOfClosedKill
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (hclosed_kill :
      ∀ x : zcCompletedGroupAlgebraStandardAugmentationIdeal C G,
        x ∈ zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
            C hC hForm psi hpsi hfopen →
          stdAugIdealToZCSepDiff
            C hC psi x = 0)
    (hcont :
      let : TopologicalSpace (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom) :=
        zcSeparatedCompletedDifferentialModuleNaturalTopology C psi.toMonoidHom
      @Continuous
        (zcCompletedGroupAlgebraStandardAugmentationIdeal C G)
        (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom)
        inferInstance
        (zcSeparatedCompletedDifferentialModuleNaturalTopology C psi.toMonoidHom)
        (stdAugIdealToZCSepDiff
          C hC psi)) :
    let : TopologicalSpace (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom) :=
      zcSeparatedCompletedDifferentialModuleNaturalTopology C psi.toMonoidHom
    Continuous
      (kerAugIdealQuotToZCSepDiffOfClosedKill
        C hC hForm psi hpsi hfopen hclosed_kill) := by
  let : TopologicalSpace (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom) :=
    zcSeparatedCompletedDifferentialModuleNaturalTopology C psi.toMonoidHom
  rw [continuous_kernelAugmentationIdealClosedQuotient_iff_comp_mkQ
    (C := C) (hC := hC) (hForm := hForm) (psi := psi)
    (hpsi := hpsi) (hfopen := hfopen)]
  have hcomp :
      (fun x : zcCompletedGroupAlgebraStandardAugmentationIdeal C G =>
        kerAugIdealQuotToZCSepDiffOfClosedKill
          C hC hForm psi hpsi hfopen hclosed_kill
          ((zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
            C hC hForm psi hpsi hfopen).mkQ x)) =
      stdAugIdealToZCSepDiff
        C hC psi := by
    funext x
    rfl
  rw [hcomp]
  exact hcont

/-- Target-linear reverse map from the closed source augmentation quotient to the separated
module, assuming only that the closed denominator is killed by the unconditional source-standard
map. -/
noncomputable def
    kerAugIdealQuotToZCSepDiffLinearOfClosedKill
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (hclosed_kill :
      ∀ x : zcCompletedGroupAlgebraStandardAugmentationIdeal C G,
        x ∈ zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
            C hC hForm psi hpsi hfopen →
          stdAugIdealToZCSepDiff
            C hC psi x = 0) :
    let : Module (ZCCompletedGroupAlgebra C H)
        (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
      kerAugClosedQuotTargetCompletedModuleOfSurj
        C hC hForm psi hpsi hfopen
    KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen
      →ₗ[ZCCompletedGroupAlgebra C H]
    ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom :=
  kerAugIdealQuotToZCSepDiffLinearOfBoundaryKernelOfClosedKill
    C hC hForm psi hpsi hfopen
    (zcDiffModuleIdToZCSepDiffModule_eq_zero_of_zcToStandard_eq_zero
      C hC psi)
    (fun x hx => by
      simpa [stdAugIdealToZCSepDiff]
        using hclosed_kill x hx)

/-- The target-linear map induced by annihilating the closed denominator has the expected value
on boundary classes. -/
@[simp 900]
theorem
    kerAugIdealQuotToZCSepDiffLinearOfClosedKill_boundary
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (hclosed_kill :
      ∀ x : zcCompletedGroupAlgebraStandardAugmentationIdeal C G,
        x ∈ zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
            C hC hForm psi hpsi hfopen →
          stdAugIdealToZCSepDiff
            C hC psi x = 0)
    (g : G) :
    kerAugIdealQuotToZCSepDiffLinearOfClosedKill
        C hC hForm psi hpsi hfopen hclosed_kill
        (Submodule.Quotient.mk
          (p := zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
            C hC hForm psi hpsi hfopen)
          ⟨zcCompletedGroupAlgebraBoundary C (MonoidHom.id G) g,
            zcCompletedGroupAlgebraBoundary_mem_standardAugmentationIdeal
              C G (MonoidHom.id G) g⟩) =
      zcSeparatedUniversalDifferential C psi.toMonoidHom g :=
  kerAugIdealQuotToZCSepDiffOfClosedKill_boundary
    C hC hForm psi hpsi hfopen hclosed_kill g

/-- Target-linear reverse map from the closed source augmentation quotient to the separated
module, reducing the closed-denominator condition to continuity of the unconditional
source-standard map. -/
noncomputable def
    kerAugIdealQuotToZCSepDiffLinearOfContStdMap
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (hcont :
      let : TopologicalSpace (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom) :=
        zcSeparatedCompletedDifferentialModuleNaturalTopology C psi.toMonoidHom
      @Continuous
        (zcCompletedGroupAlgebraStandardAugmentationIdeal C G)
        (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom)
        inferInstance
        (zcSeparatedCompletedDifferentialModuleNaturalTopology C psi.toMonoidHom)
        (stdAugIdealToZCSepDiff
          C hC psi)) :
    let : Module (ZCCompletedGroupAlgebra C H)
        (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
      kerAugClosedQuotTargetCompletedModuleOfSurj
        C hC hForm psi hpsi hfopen
    KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen
      →ₗ[ZCCompletedGroupAlgebra C H]
    ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom :=
  kerAugIdealQuotToZCSepDiffLinearOfClosedKill
    C hC hForm psi hpsi hfopen
    (fun _ hx =>
      stdAugIdealToZCSepDiff_kills_kernelMulStandardClosed_of_continuous
        C hC hForm psi hpsi hfopen hcont hx)

/-- Continuity of the standard map gives a target-linear quotient map with the expected value
on boundary classes. -/
@[simp 900]
theorem
    kerAugIdealQuotToZCSepDiffLinearOfContStdMap_boundary
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (hcont :
      let : TopologicalSpace (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom) :=
        zcSeparatedCompletedDifferentialModuleNaturalTopology C psi.toMonoidHom
      @Continuous
        (zcCompletedGroupAlgebraStandardAugmentationIdeal C G)
        (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom)
        inferInstance
        (zcSeparatedCompletedDifferentialModuleNaturalTopology C psi.toMonoidHom)
        (stdAugIdealToZCSepDiff
          C hC psi))
    (g : G) :
    kerAugIdealQuotToZCSepDiffLinearOfContStdMap
        C hC hForm psi hpsi hfopen hcont
        (Submodule.Quotient.mk
          (p := zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
            C hC hForm psi hpsi hfopen)
          ⟨zcCompletedGroupAlgebraBoundary C (MonoidHom.id G) g,
            zcCompletedGroupAlgebraBoundary_mem_standardAugmentationIdeal
              C G (MonoidHom.id G) g⟩) =
      zcSeparatedUniversalDifferential C psi.toMonoidHom g :=
  kerAugIdealQuotToZCSepDiffLinearOfClosedKill_boundary
    C hC hForm psi hpsi hfopen
    (fun _ hx =>
      stdAugIdealToZCSepDiff_kills_kernelMulStandardClosed_of_continuous
        C hC hForm psi hpsi hfopen hcont hx) g

/-- The target-linear reverse map obtained from a continuous source-standard map is continuous. -/
theorem
    continuous_kerAugIdealQuotToZCSepDiffLinearOfContStdMap
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (hcont :
      let : TopologicalSpace (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom) :=
        zcSeparatedCompletedDifferentialModuleNaturalTopology C psi.toMonoidHom
      @Continuous
        (zcCompletedGroupAlgebraStandardAugmentationIdeal C G)
        (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom)
        inferInstance
        (zcSeparatedCompletedDifferentialModuleNaturalTopology C psi.toMonoidHom)
        (stdAugIdealToZCSepDiff
          C hC psi)) :
    let : TopologicalSpace (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom) :=
      zcSeparatedCompletedDifferentialModuleNaturalTopology C psi.toMonoidHom
    Continuous
      (kerAugIdealQuotToZCSepDiffLinearOfContStdMap
        C hC hForm psi hpsi hfopen hcont) := by
  let : TopologicalSpace (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom) :=
    zcSeparatedCompletedDifferentialModuleNaturalTopology C psi.toMonoidHom
  change Continuous
    (kerAugIdealQuotToZCSepDiffOfClosedKill
      C hC hForm psi hpsi hfopen
      (fun _ hx =>
        stdAugIdealToZCSepDiff_kills_kernelMulStandardClosed_of_continuous
          C hC hForm psi hpsi hfopen hcont hx))
  exact
    continuous_kerAugIdealQuotToZCSepDiffOfClosedKill
      C hC hForm psi hpsi hfopen
      (fun _ hx =>
        stdAugIdealToZCSepDiff_kills_kernelMulStandardClosed_of_continuous
          C hC hForm psi hpsi hfopen hcont hx)
      hcont

/-- Target-linear reverse map from the closed source augmentation quotient to the separated
module. -/
noncomputable def
    kerAugIdealQuotToZCSepDiffLinear
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi) :
    let : Module (ZCCompletedGroupAlgebra C H)
        (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
      kerAugClosedQuotTargetCompletedModuleOfSurj
        C hC hForm psi hpsi hfopen
    KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen
      →ₗ[ZCCompletedGroupAlgebra C H]
    ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom :=
  kerAugIdealQuotToZCSepDiffLinearOfContStdMap
    C hC hForm psi hpsi hfopen
    (continuous_stdAugIdealToZCSepDiff
      C hC hForm psi)

/-- The canonical target-linear reverse map sends each boundary class to the separated
universal differential. -/
@[simp 900]
theorem
    kerAugIdealQuotToZCSepDiffLinear_boundary
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (g : G) :
    kerAugIdealQuotToZCSepDiffLinear
        C hC hForm psi hpsi hfopen
        (Submodule.Quotient.mk
          (p := zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
            C hC hForm psi hpsi hfopen)
          ⟨zcCompletedGroupAlgebraBoundary C (MonoidHom.id G) g,
            zcCompletedGroupAlgebraBoundary_mem_standardAugmentationIdeal
              C G (MonoidHom.id G) g⟩) =
      zcSeparatedUniversalDifferential C psi.toMonoidHom g :=
  kerAugIdealQuotToZCSepDiffLinearOfContStdMap_boundary
    C hC hForm psi hpsi hfopen
    (continuous_stdAugIdealToZCSepDiff
      C hC hForm psi) g

/-- The target-linear reverse map from the closed source augmentation quotient to the separated
module is continuous. -/
theorem
    continuous_kerAugIdealQuotToZCSepDiffLinear
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi) :
    let : TopologicalSpace (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom) :=
      zcSeparatedCompletedDifferentialModuleNaturalTopology C psi.toMonoidHom
    Continuous
      (kerAugIdealQuotToZCSepDiffLinear
        C hC hForm psi hpsi hfopen) :=
  continuous_kerAugIdealQuotToZCSepDiffLinearOfContStdMap
    C hC hForm psi hpsi hfopen
    (continuous_stdAugIdealToZCSepDiff
      C hC hForm psi)

/--
The completed universal differential module maps to the closed source augmentation quotient by
\(dg \mapsto\) \([g]-1\).
-/
def zcCompletedDifferentialModuleToKernelAugmentationClosedQuotientOfSurjective
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi) :
    letI : Module (ZCCompletedGroupAlgebra C H)
        (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
      kerAugClosedQuotTargetCompletedModuleOfSurj
        C hC hForm psi hpsi hfopen
    ZCCompletedDifferentialModule C psi.toMonoidHom →ₗ[ZCCompletedGroupAlgebra C H]
      KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen := by
  letI : Module (ZCCompletedGroupAlgebra C H)
      (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
    kerAugClosedQuotTargetCompletedModuleOfSurj
      C hC hForm psi hpsi hfopen
  exact
    crossedHomModuleLift
      (A := KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen)
      (zcCompletedGroupAlgebraScalar C psi.toMonoidHom)
      (zcCompletedGASourceBoundaryToKerAugClosedQuotTargetCompletedCrossedHomOfSurjective
        C hC hForm psi hpsi hfopen)

/--
The closed augmentation-quotient map sends the universal differential to the class of the
corresponding augmentation generator.
-/
@[simp 900]
theorem zcDiffToKerAugClosedQuotOfSurj_universal
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi) (g : G) :
    zcCompletedDifferentialModuleToKernelAugmentationClosedQuotientOfSurjective
        C hC hForm psi hpsi hfopen
        (zcUniversalDifferential C psi.toMonoidHom g) =
      zcCompletedGroupAlgebraSourceBoundaryToKernelAugmentationClosedQuotient
        C hC hForm psi hpsi hfopen g := by
  let : Module (ZCCompletedGroupAlgebra C H)
      (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
    kerAugClosedQuotTargetCompletedModuleOfSurj
      C hC hForm psi hpsi hfopen
  exact
    crossedHomModuleLift_universal
      (A := KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen)
      (zcCompletedGroupAlgebraScalar C psi.toMonoidHom)
      (zcCompletedGASourceBoundaryToKerAugClosedQuotTargetCompletedCrossedHomOfSurjective
        C hC hForm psi hpsi hfopen) g

/--
If the pre-quotient source-boundary lift to the closed augmentation quotient is continuous for
the finite-stage pre-module topology, then it kills the finite-stage closed relation
denominator. This is the descent criterion needed to factor the algebraic map through the
separated completed differential module.
-/
theorem zcDiffToKerAugClosedQuotOfSurj_kills_finiteClosedSubmodule_of_continuous_lift
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    [Nonempty (ZCCompletedDifferentialModuleIndex C psi.toMonoidHom)]
    (hdir : Directed (· ≤ ·)
      (id : ZCCompletedDifferentialModuleIndex C psi.toMonoidHom →
        ZCCompletedDifferentialModuleIndex C psi.toMonoidHom))
    (hcont :
      letI : Module (ZCCompletedGroupAlgebra C H)
          (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
        kerAugClosedQuotTargetCompletedModuleOfSurj
          C hC hForm psi hpsi hfopen
      @Continuous
        (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)
        (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen)
        (zcCompletedDifferentialPreModuleNaturalTopology C psi.toMonoidHom)
        inferInstance
        (crossedDifferentialModuleLiftLinear
          (R := ZCCompletedGroupAlgebra C H)
          (zcCompletedGroupAlgebraSourceBoundaryToKernelAugmentationClosedQuotient
            C hC hForm psi hpsi hfopen)))
    {x : CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G}
    (hx : x ∈ zcCompletedDifferentialRelationFiniteClosedSubmodule C psi.toMonoidHom) :
    letI : Module (ZCCompletedGroupAlgebra C H)
        (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
      kerAugClosedQuotTargetCompletedModuleOfSurj
        C hC hForm psi hpsi hfopen
    crossedDifferentialModuleLiftLinear
      (R := ZCCompletedGroupAlgebra C H)
      (zcCompletedGroupAlgebraSourceBoundaryToKernelAugmentationClosedQuotient
        C hC hForm psi hpsi hfopen) x = 0 := by
  let : Module (ZCCompletedGroupAlgebra C H)
      (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
    kerAugClosedQuotTargetCompletedModuleOfSurj
      C hC hForm psi hpsi hfopen
  let : T1Space
      (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
    t1Space_kernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen
  exact
    crossedDifferentialModuleLiftLinear_kills_finiteClosedSubmodule_of_continuous
      C psi.toMonoidHom hdir
      (zcCompletedGASourceBoundaryToKerAugClosedQuotTargetCompletedCrossedHomOfSurjective
        C hC hForm psi hpsi hfopen)
      hcont hx

/--
Version of zcDiffToKerAugClosedQuotOfSurj_kills_finiteClosedSubmodule_of_continuous_lift with
nonemptiness and directedness of finite stages supplied by the continuous source map.
-/
theorem zcDiffToKerAugClosedQuotOfSurj_kills_finiteClosedSubmodule_of_continuous_lift_of_surj
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (hcont :
      letI : Module (ZCCompletedGroupAlgebra C H)
          (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
        kerAugClosedQuotTargetCompletedModuleOfSurj
          C hC hForm psi hpsi hfopen
      @Continuous
        (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)
        (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen)
        (zcCompletedDifferentialPreModuleNaturalTopology C psi.toMonoidHom)
        inferInstance
        (crossedDifferentialModuleLiftLinear
          (R := ZCCompletedGroupAlgebra C H)
          (zcCompletedGroupAlgebraSourceBoundaryToKernelAugmentationClosedQuotient
            C hC hForm psi hpsi hfopen)))
    {x : CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G}
    (hx : x ∈ zcCompletedDifferentialRelationFiniteClosedSubmodule C psi.toMonoidHom) :
    letI : Module (ZCCompletedGroupAlgebra C H)
        (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
      kerAugClosedQuotTargetCompletedModuleOfSurj
        C hC hForm psi hpsi hfopen
    crossedDifferentialModuleLiftLinear
      (R := ZCCompletedGroupAlgebra C H)
      (zcCompletedGroupAlgebraSourceBoundaryToKernelAugmentationClosedQuotient
        C hC hForm psi hpsi hfopen) x = 0 := by
  let : Nonempty (ZCCompletedDifferentialModuleIndex C psi.toMonoidHom) :=
    nonempty_zcCompletedDifferentialModuleIndex C hC psi
  exact
    zcDiffToKerAugClosedQuotOfSurj_kills_finiteClosedSubmodule_of_continuous_lift
      C hC hForm psi hpsi hfopen
      (directed_zcCompletedDifferentialModuleIndex C hForm hC psi)
      hcont hx

/--
Under the explicit continuity hypothesis for the pre-quotient source-boundary lift, the closed
source augmentation quotient receives the separated completed universal differential module.
-/
def zcSepDiffToKerAugClosedQuotOfSurjective
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    [Nonempty (ZCCompletedDifferentialModuleIndex C psi.toMonoidHom)]
    (hdir : Directed (· ≤ ·)
      (id : ZCCompletedDifferentialModuleIndex C psi.toMonoidHom →
        ZCCompletedDifferentialModuleIndex C psi.toMonoidHom))
    (hcont :
      letI : Module (ZCCompletedGroupAlgebra C H)
          (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
        kerAugClosedQuotTargetCompletedModuleOfSurj
          C hC hForm psi hpsi hfopen
      @Continuous
        (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)
        (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen)
        (zcCompletedDifferentialPreModuleNaturalTopology C psi.toMonoidHom)
        inferInstance
        (crossedDifferentialModuleLiftLinear
          (R := ZCCompletedGroupAlgebra C H)
          (zcCompletedGroupAlgebraSourceBoundaryToKernelAugmentationClosedQuotient
            C hC hForm psi hpsi hfopen))) :
    letI : Module (ZCCompletedGroupAlgebra C H)
        (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
      kerAugClosedQuotTargetCompletedModuleOfSurj
        C hC hForm psi hpsi hfopen
    ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom →ₗ[ZCCompletedGroupAlgebra C H]
      KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen := by
  letI : Module (ZCCompletedGroupAlgebra C H)
      (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
    kerAugClosedQuotTargetCompletedModuleOfSurj
      C hC hForm psi hpsi hfopen
  letI : T1Space
      (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
    t1Space_kernelAugmentationIdealClosedQuotient
      C hC hForm psi hpsi hfopen
  exact
    zcSeparatedCompletedDifferentialModuleLiftOfContinuousPrelift
      C psi.toMonoidHom hdir
      (zcCompletedGASourceBoundaryToKerAugClosedQuotTargetCompletedCrossedHomOfSurjective
        C hC hForm psi hpsi hfopen)
      hcont

/--
Public version of the closed-augmentation descent map with finite-stage nonemptiness and
directedness supplied by the continuous source map.
-/
def zcSepDiffToKerAugClosedQuotOfSurjectiveOfContinuousLift
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (hcont :
      letI : Module (ZCCompletedGroupAlgebra C H)
          (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
        kerAugClosedQuotTargetCompletedModuleOfSurj
          C hC hForm psi hpsi hfopen
      @Continuous
        (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)
        (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen)
        (zcCompletedDifferentialPreModuleNaturalTopology C psi.toMonoidHom)
        inferInstance
        (crossedDifferentialModuleLiftLinear
          (R := ZCCompletedGroupAlgebra C H)
          (zcCompletedGroupAlgebraSourceBoundaryToKernelAugmentationClosedQuotient
            C hC hForm psi hpsi hfopen))) :
    letI : Module (ZCCompletedGroupAlgebra C H)
        (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
      kerAugClosedQuotTargetCompletedModuleOfSurj
        C hC hForm psi hpsi hfopen
    ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom →ₗ[ZCCompletedGroupAlgebra C H]
      KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen := by
  letI : Nonempty (ZCCompletedDifferentialModuleIndex C psi.toMonoidHom) :=
    nonempty_zcCompletedDifferentialModuleIndex C hC psi
  exact
    zcSepDiffToKerAugClosedQuotOfSurjective
      C hC hForm psi hpsi hfopen
      (directed_zcCompletedDifferentialModuleIndex C hForm hC psi)
      hcont

/--
The separated differential module maps universally to the closed kernel-augmentation quotient in
the surjective case.
-/
@[simp 900]
theorem zcSepDiffToKerAugClosedQuotOfSurjective_universal
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    [Nonempty (ZCCompletedDifferentialModuleIndex C psi.toMonoidHom)]
    (hdir : Directed (· ≤ ·)
      (id : ZCCompletedDifferentialModuleIndex C psi.toMonoidHom →
        ZCCompletedDifferentialModuleIndex C psi.toMonoidHom))
    (hcont :
      letI : Module (ZCCompletedGroupAlgebra C H)
          (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
        kerAugClosedQuotTargetCompletedModuleOfSurj
          C hC hForm psi hpsi hfopen
      @Continuous
        (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)
        (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen)
        (zcCompletedDifferentialPreModuleNaturalTopology C psi.toMonoidHom)
        inferInstance
        (crossedDifferentialModuleLiftLinear
          (R := ZCCompletedGroupAlgebra C H)
          (zcCompletedGroupAlgebraSourceBoundaryToKernelAugmentationClosedQuotient
            C hC hForm psi hpsi hfopen)))
    (g : G) :
    zcSepDiffToKerAugClosedQuotOfSurjective
        C hC hForm psi hpsi hfopen hdir hcont
        (zcSeparatedUniversalDifferential C psi.toMonoidHom g) =
      zcCompletedGroupAlgebraSourceBoundaryToKernelAugmentationClosedQuotient
        C hC hForm psi hpsi hfopen g := by
  let : Module (ZCCompletedGroupAlgebra C H)
      (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
    kerAugClosedQuotTargetCompletedModuleOfSurj
      C hC hForm psi hpsi hfopen
  let : T1Space
      (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
    t1Space_kernelAugmentationIdealClosedQuotient
      C hC hForm psi hpsi hfopen
  exact
    zcSeparatedCompletedDifferentialModuleLiftOfContinuousPrelift_universal
      C psi.toMonoidHom hdir
      (zcCompletedGASourceBoundaryToKerAugClosedQuotTargetCompletedCrossedHomOfSurjective
        C hC hForm psi hpsi hfopen)
      hcont g

/--
The lifted map from the separated completed differential module to the closed
augmentation-kernel quotient sends each separated universal differential to the corresponding
boundary quotient.
-/
@[simp 900]
theorem zcSepDiffToKerAugClosedQuotOfSurjectiveOfContinuousLift_universal
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (hcont :
      letI : Module (ZCCompletedGroupAlgebra C H)
          (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
        kerAugClosedQuotTargetCompletedModuleOfSurj
          C hC hForm psi hpsi hfopen
      @Continuous
        (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)
        (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen)
        (zcCompletedDifferentialPreModuleNaturalTopology C psi.toMonoidHom)
        inferInstance
        (crossedDifferentialModuleLiftLinear
          (R := ZCCompletedGroupAlgebra C H)
          (zcCompletedGroupAlgebraSourceBoundaryToKernelAugmentationClosedQuotient
            C hC hForm psi hpsi hfopen)))
    (g : G) :
    zcSepDiffToKerAugClosedQuotOfSurjectiveOfContinuousLift
        C hC hForm psi hpsi hfopen hcont
        (zcSeparatedUniversalDifferential C psi.toMonoidHom g) =
      zcCompletedGroupAlgebraSourceBoundaryToKernelAugmentationClosedQuotient
        C hC hForm psi hpsi hfopen g := by
  let : Nonempty (ZCCompletedDifferentialModuleIndex C psi.toMonoidHom) :=
    nonempty_zcCompletedDifferentialModuleIndex C hC psi
  exact
    zcSepDiffToKerAugClosedQuotOfSurjective_universal
      C hC hForm psi hpsi hfopen
      (directed_zcCompletedDifferentialModuleIndex C hForm hC psi)
      hcont g

/--
The separated closed-augmentation map is the factorization of the algebraic closed-augmentation
map through \(A_{\psi}(C) \to A_{\psi}(C)_{\mathrm{sep}}\).
-/
theorem zcSepDiffToKerAugClosedQuotOfSurjective_comp_toSep
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    [Nonempty (ZCCompletedDifferentialModuleIndex C psi.toMonoidHom)]
    (hdir : Directed (· ≤ ·)
      (id : ZCCompletedDifferentialModuleIndex C psi.toMonoidHom →
        ZCCompletedDifferentialModuleIndex C psi.toMonoidHom))
    (hcont :
      letI : Module (ZCCompletedGroupAlgebra C H)
          (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
        kerAugClosedQuotTargetCompletedModuleOfSurj
          C hC hForm psi hpsi hfopen
      @Continuous
        (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)
        (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen)
        (zcCompletedDifferentialPreModuleNaturalTopology C psi.toMonoidHom)
        inferInstance
        (crossedDifferentialModuleLiftLinear
          (R := ZCCompletedGroupAlgebra C H)
          (zcCompletedGroupAlgebraSourceBoundaryToKernelAugmentationClosedQuotient
            C hC hForm psi hpsi hfopen))) :
    letI : Module (ZCCompletedGroupAlgebra C H)
        (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
      kerAugClosedQuotTargetCompletedModuleOfSurj
        C hC hForm psi hpsi hfopen
    (zcSepDiffToKerAugClosedQuotOfSurjective
        C hC hForm psi hpsi hfopen hdir hcont).comp
      (zcCompletedDifferentialModuleToSeparated C psi.toMonoidHom) =
    zcCompletedDifferentialModuleToKernelAugmentationClosedQuotientOfSurjective
      C hC hForm psi hpsi hfopen := by
  let : Module (ZCCompletedGroupAlgebra C H)
      (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
    kerAugClosedQuotTargetCompletedModuleOfSurj
      C hC hForm psi hpsi hfopen
  apply crossedDifferentialModuleHom_ext
    (zcCompletedGroupAlgebraScalar C psi.toMonoidHom)
  intro g
  change
    zcSepDiffToKerAugClosedQuotOfSurjective
        C hC hForm psi hpsi hfopen hdir hcont
        (zcCompletedDifferentialModuleToSeparated C psi.toMonoidHom
          (zcUniversalDifferential C psi.toMonoidHom g)) =
      zcCompletedDifferentialModuleToKernelAugmentationClosedQuotientOfSurjective
        C hC hForm psi hpsi hfopen
        (zcUniversalDifferential C psi.toMonoidHom g)
  rw [zcCompletedDifferentialModuleToSeparated_universal,
    zcSepDiffToKerAugClosedQuotOfSurjective_universal,
    zcDiffToKerAugClosedQuotOfSurj_universal]

/--
The continuous-lift map to the closed kernel-augmentation quotient composes with separation as
expected.
-/
theorem zcSepDiffToKerAugClosedQuotOfSurjectiveOfContinuousLift_comp_toSep
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (hcont :
      letI : Module (ZCCompletedGroupAlgebra C H)
          (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
        kerAugClosedQuotTargetCompletedModuleOfSurj
          C hC hForm psi hpsi hfopen
      @Continuous
        (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)
        (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen)
        (zcCompletedDifferentialPreModuleNaturalTopology C psi.toMonoidHom)
        inferInstance
        (crossedDifferentialModuleLiftLinear
          (R := ZCCompletedGroupAlgebra C H)
          (zcCompletedGroupAlgebraSourceBoundaryToKernelAugmentationClosedQuotient
            C hC hForm psi hpsi hfopen))) :
    letI : Module (ZCCompletedGroupAlgebra C H)
        (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
      kerAugClosedQuotTargetCompletedModuleOfSurj
        C hC hForm psi hpsi hfopen
    (zcSepDiffToKerAugClosedQuotOfSurjectiveOfContinuousLift
        C hC hForm psi hpsi hfopen hcont).comp
      (zcCompletedDifferentialModuleToSeparated C psi.toMonoidHom) =
    zcCompletedDifferentialModuleToKernelAugmentationClosedQuotientOfSurjective
      C hC hForm psi hpsi hfopen := by
  let : Nonempty (ZCCompletedDifferentialModuleIndex C psi.toMonoidHom) :=
    nonempty_zcCompletedDifferentialModuleIndex C hC psi
  exact
    zcSepDiffToKerAugClosedQuotOfSurjective_comp_toSep
      C hC hForm psi hpsi hfopen
      (directed_zcCompletedDifferentialModuleIndex C hForm hC psi)
      hcont

/--
The descended forward map to the closed augmentation quotient is continuous once the
pre-quotient source-boundary lift is continuous.
-/
theorem continuous_zcSepDiffToKerAugClosedQuotOfSurjective
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    [Nonempty (ZCCompletedDifferentialModuleIndex C psi.toMonoidHom)]
    (hdir : Directed (· ≤ ·)
      (id : ZCCompletedDifferentialModuleIndex C psi.toMonoidHom →
        ZCCompletedDifferentialModuleIndex C psi.toMonoidHom))
    (hcont :
      letI : Module (ZCCompletedGroupAlgebra C H)
          (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
        kerAugClosedQuotTargetCompletedModuleOfSurj
          C hC hForm psi hpsi hfopen
      @Continuous
        (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)
        (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen)
        (zcCompletedDifferentialPreModuleNaturalTopology C psi.toMonoidHom)
        inferInstance
        (crossedDifferentialModuleLiftLinear
          (R := ZCCompletedGroupAlgebra C H)
          (zcCompletedGroupAlgebraSourceBoundaryToKernelAugmentationClosedQuotient
            C hC hForm psi hpsi hfopen))) :
    letI : TopologicalSpace (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom) :=
      zcSeparatedCompletedDifferentialModuleNaturalTopology C psi.toMonoidHom
    letI : Module (ZCCompletedGroupAlgebra C H)
        (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
      kerAugClosedQuotTargetCompletedModuleOfSurj
        C hC hForm psi hpsi hfopen
    @Continuous
      (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom)
      (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen)
      (zcSeparatedCompletedDifferentialModuleNaturalTopology C psi.toMonoidHom)
      inferInstance
      (zcSepDiffToKerAugClosedQuotOfSurjective
        C hC hForm psi hpsi hfopen hdir hcont) := by
  let : TopologicalSpace (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom) :=
    zcSeparatedCompletedDifferentialModuleNaturalTopology C psi.toMonoidHom
  let : Module (ZCCompletedGroupAlgebra C H)
      (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
    kerAugClosedQuotTargetCompletedModuleOfSurj
      C hC hForm psi hpsi hfopen
  rw [continuous_zcSeparatedCompletedDifferentialModule_iff_comp_mkQ
    (C := C) (G := G) (H := H) (ψ := psi.toMonoidHom)]
  have hcomp :
      (fun x : CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G =>
        zcSepDiffToKerAugClosedQuotOfSurjective
          C hC hForm psi hpsi hfopen hdir hcont
          ((zcCompletedDifferentialRelationFiniteClosedSubmodule C psi.toMonoidHom).mkQ x)) =
        crossedDifferentialModuleLiftLinear
          (R := ZCCompletedGroupAlgebra C H)
          (zcCompletedGroupAlgebraSourceBoundaryToKernelAugmentationClosedQuotient
            C hC hForm psi hpsi hfopen) := by
    funext x
    change
      (zcCompletedDifferentialRelationFiniteClosedSubmodule C psi.toMonoidHom).liftQ
          (crossedDifferentialModuleLiftLinear
            (R := ZCCompletedGroupAlgebra C H)
            (zcCompletedGroupAlgebraSourceBoundaryToKernelAugmentationClosedQuotient
              C hC hForm psi hpsi hfopen))
          _ ((zcCompletedDifferentialRelationFiniteClosedSubmodule C psi.toMonoidHom).mkQ x) =
        crossedDifferentialModuleLiftLinear
          (R := ZCCompletedGroupAlgebra C H)
          (zcCompletedGroupAlgebraSourceBoundaryToKernelAugmentationClosedQuotient
            C hC hForm psi hpsi hfopen) x
    rfl
  rw [hcomp]
  exact hcont

/--
Continuity of the forward map when the finite-stage index data are supplied by the continuous
source map.
-/
theorem continuous_zcSepDiffToKerAugClosedQuotOfSurjectiveOfContinuousLift
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (hcont :
      letI : Module (ZCCompletedGroupAlgebra C H)
          (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
        kerAugClosedQuotTargetCompletedModuleOfSurj
          C hC hForm psi hpsi hfopen
      @Continuous
        (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)
        (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen)
        (zcCompletedDifferentialPreModuleNaturalTopology C psi.toMonoidHom)
        inferInstance
        (crossedDifferentialModuleLiftLinear
          (R := ZCCompletedGroupAlgebra C H)
          (zcCompletedGroupAlgebraSourceBoundaryToKernelAugmentationClosedQuotient
            C hC hForm psi hpsi hfopen))) :
    letI : TopologicalSpace (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom) :=
      zcSeparatedCompletedDifferentialModuleNaturalTopology C psi.toMonoidHom
    letI : Module (ZCCompletedGroupAlgebra C H)
        (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
      kerAugClosedQuotTargetCompletedModuleOfSurj
        C hC hForm psi hpsi hfopen
    @Continuous
      (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom)
      (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen)
      (zcSeparatedCompletedDifferentialModuleNaturalTopology C psi.toMonoidHom)
      inferInstance
      (zcSepDiffToKerAugClosedQuotOfSurjectiveOfContinuousLift
        C hC hForm psi hpsi hfopen hcont) := by
  let : Nonempty (ZCCompletedDifferentialModuleIndex C psi.toMonoidHom) :=
    nonempty_zcCompletedDifferentialModuleIndex C hC psi
  exact
    continuous_zcSepDiffToKerAugClosedQuotOfSurjective
      C hC hForm psi hpsi hfopen
      (directed_zcCompletedDifferentialModuleIndex C hForm hC psi)
      hcont

/--
The map from the completed differential module to the closed augmentation quotient is surjective
when finite-stage representatives can be lifted.
-/
theorem zcDiffToKerAugClosedQuotOfSurj_surj
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi) :
    Function.Surjective
      (zcCompletedDifferentialModuleToKernelAugmentationClosedQuotientOfSurjective
        C hC hForm psi hpsi hfopen) := by
  let : Module (ZCCompletedGroupAlgebra C H)
      (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
    kerAugClosedQuotTargetCompletedModuleOfSurj
      C hC hForm psi hpsi hfopen
  intro x
  refine Submodule.Quotient.induction_on
    (p := zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
      C hC hForm psi hpsi hfopen) x ?_
  intro y
  let L :=
    zcCompletedDifferentialModuleToKernelAugmentationClosedQuotientOfSurjective
      C hC hForm psi hpsi hfopen
  let P : zcCompletedGroupAlgebraStandardAugmentationIdeal C G → Prop := fun y =>
    ∃ m : ZCCompletedDifferentialModule C psi.toMonoidHom,
      L m = Submodule.Quotient.mk
        (p := zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
          C hC hForm psi hpsi hfopen) y
  have hy : P y := by
    have hyspan : (y : ZCCompletedGroupAlgebra C G) ∈
        Submodule.span (ZCCompletedGroupAlgebra C G)
          (Set.range fun h : G => zcGroupLike C G h - 1) := by
      change (y : ZCCompletedGroupAlgebra C G) ∈
        zcCompletedGroupAlgebraStandardAugmentationIdeal C G
      exact y.2
    refine Submodule.span_induction
      (p := fun z hz =>
        P
          ⟨z, by
            simpa [zcCompletedGroupAlgebraStandardAugmentationIdeal_eq_span] using hz⟩)
      ?hgen ?hzero ?hadd ?hsmul hyspan
    · rintro _ ⟨g, rfl⟩
      refine ⟨zcUniversalDifferential C psi.toMonoidHom g, ?_⟩
      rw [zcDiffToKerAugClosedQuotOfSurj_universal]
      rfl
    · refine ⟨0, ?_⟩
      change (0 : KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) =
        Submodule.Quotient.mk
          (p := zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
            C hC hForm psi hpsi hfopen)
          (0 : zcCompletedGroupAlgebraStandardAugmentationIdeal C G)
      rw [Submodule.Quotient.mk_zero]
    · intro a b ha hb hpa hpb
      rcases hpa with ⟨ma, hma⟩
      rcases hpb with ⟨mb, hmb⟩
      refine ⟨ma + mb, ?_⟩
      rw [map_add, hma, hmb, ← Submodule.Quotient.mk_add]
      apply congrArg (fun t : zcCompletedGroupAlgebraStandardAugmentationIdeal C G =>
        Submodule.Quotient.mk
          (p := zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
            C hC hForm psi hpsi hfopen) t)
      exact Subtype.ext rfl
    · intro a b hb hpb
      rcases hpb with ⟨m, hm⟩
      refine ⟨zcCompletedGroupAlgebraMap C hC psi a • m, ?_⟩
      rw [map_smul, hm]
      calc
        zcCompletedGroupAlgebraMap C hC psi a •
            Submodule.Quotient.mk
              (p := zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
                C hC hForm psi hpsi hfopen)
              ⟨b, by
                simpa [zcCompletedGroupAlgebraStandardAugmentationIdeal_eq_span] using hb⟩ =
          a •
            Submodule.Quotient.mk
              (p := zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
                C hC hForm psi hpsi hfopen)
              ⟨b, by
                simpa [zcCompletedGroupAlgebraStandardAugmentationIdeal_eq_span] using hb⟩ := by
            exact
              kerAugClosedQuotTargetCompletedModuleOfSurj_map_smul
                C hC hForm psi hpsi hfopen a
                (Submodule.Quotient.mk
                  (p := zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
                    C hC hForm psi hpsi hfopen)
                  ⟨b, by
                    simpa [zcCompletedGroupAlgebraStandardAugmentationIdeal_eq_span] using hb⟩)
        _ = Submodule.Quotient.mk
              (p := zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
                C hC hForm psi hpsi hfopen)
              ⟨a • b, by
                rw [zcCompletedGroupAlgebraStandardAugmentationIdeal_eq_span]
                exact Submodule.smul_mem
                  (Submodule.span (ZCCompletedGroupAlgebra C G)
                    (Set.range fun h : G => zcGroupLike C G h - 1)) a hb⟩ := by
            rw [← Submodule.Quotient.mk_smul]
            apply congrArg (fun t : zcCompletedGroupAlgebraStandardAugmentationIdeal C G =>
              Submodule.Quotient.mk
                (p := zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
                  C hC hForm psi hpsi hfopen) t)
            exact Subtype.ext rfl
  exact hy

/--
The separated closed-augmentation map is surjective under the same pre-quotient continuity
hypothesis needed for the descent.
-/
theorem zcSepDiffToKerAugClosedQuotOfSurjective_surj
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    [Nonempty (ZCCompletedDifferentialModuleIndex C psi.toMonoidHom)]
    (hdir : Directed (· ≤ ·)
      (id : ZCCompletedDifferentialModuleIndex C psi.toMonoidHom →
        ZCCompletedDifferentialModuleIndex C psi.toMonoidHom))
    (hcont :
      letI : Module (ZCCompletedGroupAlgebra C H)
          (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
        kerAugClosedQuotTargetCompletedModuleOfSurj
          C hC hForm psi hpsi hfopen
      @Continuous
        (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)
        (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen)
        (zcCompletedDifferentialPreModuleNaturalTopology C psi.toMonoidHom)
        inferInstance
        (crossedDifferentialModuleLiftLinear
          (R := ZCCompletedGroupAlgebra C H)
          (zcCompletedGroupAlgebraSourceBoundaryToKernelAugmentationClosedQuotient
            C hC hForm psi hpsi hfopen))) :
    Function.Surjective
      (zcSepDiffToKerAugClosedQuotOfSurjective
        C hC hForm psi hpsi hfopen hdir hcont) := by
  let : Module (ZCCompletedGroupAlgebra C H)
      (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
    kerAugClosedQuotTargetCompletedModuleOfSurj
      C hC hForm psi hpsi hfopen
  intro y
  rcases
      zcDiffToKerAugClosedQuotOfSurj_surj
        C hC hForm psi hpsi hfopen y with
    ⟨m, hm⟩
  refine ⟨zcCompletedDifferentialModuleToSeparated C psi.toMonoidHom m, ?_⟩
  have hfactor :=
    congrArg (fun L : ZCCompletedDifferentialModule C psi.toMonoidHom →ₗ[ZCCompletedGroupAlgebra
        C H]
        KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen => L m)
      (zcSepDiffToKerAugClosedQuotOfSurjective_comp_toSep
        C hC hForm psi hpsi hfopen hdir hcont)
  change
    zcSepDiffToKerAugClosedQuotOfSurjective
        C hC hForm psi hpsi hfopen hdir hcont
        (zcCompletedDifferentialModuleToSeparated C psi.toMonoidHom m) =
      zcCompletedDifferentialModuleToKernelAugmentationClosedQuotientOfSurjective
        C hC hForm psi hpsi hfopen m at hfactor
  exact hfactor.trans hm

/-- The continuous-lift map to the closed kernel-augmentation quotient is surjective. -/
theorem zcSepDiffToKerAugClosedQuotOfSurjectiveOfContinuousLift_surj
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (hcont :
      letI : Module (ZCCompletedGroupAlgebra C H)
          (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
        kerAugClosedQuotTargetCompletedModuleOfSurj
          C hC hForm psi hpsi hfopen
      @Continuous
        (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)
        (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen)
        (zcCompletedDifferentialPreModuleNaturalTopology C psi.toMonoidHom)
        inferInstance
        (crossedDifferentialModuleLiftLinear
          (R := ZCCompletedGroupAlgebra C H)
          (zcCompletedGroupAlgebraSourceBoundaryToKernelAugmentationClosedQuotient
            C hC hForm psi hpsi hfopen))) :
    Function.Surjective
      (zcSepDiffToKerAugClosedQuotOfSurjectiveOfContinuousLift
        C hC hForm psi hpsi hfopen hcont) := by
  let : Nonempty (ZCCompletedDifferentialModuleIndex C psi.toMonoidHom) :=
    nonempty_zcCompletedDifferentialModuleIndex C hC psi
  exact
    zcSepDiffToKerAugClosedQuotOfSurjective_surj
      C hC hForm psi hpsi hfopen
      (directed_zcCompletedDifferentialModuleIndex C hForm hC psi)
      hcont

/--
The separated completed universal differential module maps to the closed source augmentation
quotient by \(dg \mapsto\) \([g]-1\). The pre-quotient lift continuity is supplied by the
finite-stage factorization theorem.
-/
def zcSeparatedCompletedDifferentialModuleToKernelAugmentationClosedQuotient
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi) :
    letI : Module (ZCCompletedGroupAlgebra C H)
        (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
      kerAugClosedQuotTargetCompletedModuleOfSurj
        C hC hForm psi hpsi hfopen
    ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom →ₗ[ZCCompletedGroupAlgebra C H]
      KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen := by
  let hcont :=
    continuous_crossedDiffModuleLiftLinear_sourceBoundaryToKerAugClosedQuot
      C hC hForm psi hpsi hfopen
  exact
    zcSepDiffToKerAugClosedQuotOfSurjectiveOfContinuousLift
      C hC hForm psi hpsi hfopen hcont

/--
The separated closed augmentation-quotient map sends the separated universal differential to the
closed augmentation quotient class.
-/
@[simp]
theorem zcSepDiffToKerAugClosedQuot_universal
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi) (g : G) :
    zcSeparatedCompletedDifferentialModuleToKernelAugmentationClosedQuotient
        C hC hForm psi hpsi hfopen
        (zcSeparatedUniversalDifferential C psi.toMonoidHom g) =
      zcCompletedGroupAlgebraSourceBoundaryToKernelAugmentationClosedQuotient
        C hC hForm psi hpsi hfopen g := by
  let hcont :=
    continuous_crossedDiffModuleLiftLinear_sourceBoundaryToKerAugClosedQuot
      C hC hForm psi hpsi hfopen
  simpa [zcSeparatedCompletedDifferentialModuleToKernelAugmentationClosedQuotient, hcont] using
    zcSepDiffToKerAugClosedQuotOfSurjectiveOfContinuousLift_universal
      C hC hForm psi hpsi hfopen hcont g

/--
The unconditional separated closed-augmentation map factors the algebraic map through
\(A_{\psi}(C) \to A_{\psi}(C)_{\mathrm{sep}}\).
-/
theorem zcSepDiffToKerAugClosedQuot_comp_toSep
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi) :
    letI : Module (ZCCompletedGroupAlgebra C H)
        (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
      kerAugClosedQuotTargetCompletedModuleOfSurj
        C hC hForm psi hpsi hfopen
    (zcSeparatedCompletedDifferentialModuleToKernelAugmentationClosedQuotient
        C hC hForm psi hpsi hfopen).comp
      (zcCompletedDifferentialModuleToSeparated C psi.toMonoidHom) =
    zcCompletedDifferentialModuleToKernelAugmentationClosedQuotientOfSurjective
      C hC hForm psi hpsi hfopen := by
  let hcont :=
    continuous_crossedDiffModuleLiftLinear_sourceBoundaryToKerAugClosedQuot
      C hC hForm psi hpsi hfopen
  simpa [zcSeparatedCompletedDifferentialModuleToKernelAugmentationClosedQuotient, hcont] using
    zcSepDiffToKerAugClosedQuotOfSurjectiveOfContinuousLift_comp_toSep
      C hC hForm psi hpsi hfopen hcont

/--
The separated closed-augmentation map is continuous, with the pre-quotient lift continuity
provided by the finite-stage factorization theorem.
-/
theorem continuous_zcSepDiffToKerAugClosedQuot
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi) :
    letI : TopologicalSpace (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom) :=
      zcSeparatedCompletedDifferentialModuleNaturalTopology C psi.toMonoidHom
    letI : Module (ZCCompletedGroupAlgebra C H)
        (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
      kerAugClosedQuotTargetCompletedModuleOfSurj
        C hC hForm psi hpsi hfopen
    @Continuous
      (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom)
      (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen)
      (zcSeparatedCompletedDifferentialModuleNaturalTopology C psi.toMonoidHom)
      inferInstance
      (zcSeparatedCompletedDifferentialModuleToKernelAugmentationClosedQuotient
        C hC hForm psi hpsi hfopen) := by
  let hcont :=
    continuous_crossedDiffModuleLiftLinear_sourceBoundaryToKerAugClosedQuot
      C hC hForm psi hpsi hfopen
  simpa [zcSeparatedCompletedDifferentialModuleToKernelAugmentationClosedQuotient, hcont] using
    continuous_zcSepDiffToKerAugClosedQuotOfSurjectiveOfContinuousLift
      C hC hForm psi hpsi hfopen hcont

/-- The separated map to the closed kernel-augmentation quotient is surjective. -/
theorem zcSepDiffToKerAugClosedQuot_surj
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi) :
    Function.Surjective
      (zcSeparatedCompletedDifferentialModuleToKernelAugmentationClosedQuotient
        C hC hForm psi hpsi hfopen) := by
  let hcont :=
    continuous_crossedDiffModuleLiftLinear_sourceBoundaryToKerAugClosedQuot
      C hC hForm psi hpsi hfopen
  simpa [zcSeparatedCompletedDifferentialModuleToKernelAugmentationClosedQuotient, hcont] using
    zcSepDiffToKerAugClosedQuotOfSurjectiveOfContinuousLift_surj
      C hC hForm psi hpsi hfopen hcont

/--
The reverse map from the closed augmentation quotient to the separated differential module is
evaluated on quotient classes by the constructed linear representative.
-/
@[simp]
theorem kerAugIdealQuotToZCSepDiffLinear_mk
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (x : zcCompletedGroupAlgebraStandardAugmentationIdeal C G) :
    kerAugIdealQuotToZCSepDiffLinear
        C hC hForm psi hpsi hfopen
        (Submodule.Quotient.mk
          (p := zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
            C hC hForm psi hpsi hfopen) x) =
      stdAugIdealToZCSepDiff
        C hC psi x := by
  rfl

/--
Composing the reverse closed-augmentation map with the forward separated map gives the identity.
-/
theorem kerAugIdealQuotToZCSepDiffLinear_comp_zcSepDiffToKerAugClosedQuot
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi) :
    letI : Module (ZCCompletedGroupAlgebra C H)
        (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
      kerAugClosedQuotTargetCompletedModuleOfSurj
        C hC hForm psi hpsi hfopen
    (kerAugIdealQuotToZCSepDiffLinear
        C hC hForm psi hpsi hfopen).comp
      (zcSeparatedCompletedDifferentialModuleToKernelAugmentationClosedQuotient
        C hC hForm psi hpsi hfopen) =
    LinearMap.id := by
  let : Module (ZCCompletedGroupAlgebra C H)
      (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
    kerAugClosedQuotTargetCompletedModuleOfSurj
      C hC hForm psi hpsi hfopen
  apply zcSeparatedCompletedDifferentialModuleHom_ext C psi.toMonoidHom
  intro g
  rw [LinearMap.comp_apply,
    zcSepDiffToKerAugClosedQuot_universal]
  rw [LinearMap.id_apply]
  change
    kerAugIdealQuotToZCSepDiffLinear C hC hForm psi hpsi hfopen
        (Submodule.Quotient.mk
          (p := zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
            C hC hForm psi hpsi hfopen)
          ⟨zcCompletedGroupAlgebraBoundary C (MonoidHom.id G) g,
            zcCompletedGroupAlgebraBoundary_mem_standardAugmentationIdeal
              C G (MonoidHom.id G) g⟩) =
      zcSeparatedUniversalDifferential C psi.toMonoidHom g
  exact
    kerAugIdealQuotToZCSepDiffLinear_boundary
      C hC hForm psi hpsi hfopen g

/--
Composing the forward separated map with the reverse closed-augmentation map gives the identity.
-/
theorem zcSepDiffToKerAugClosedQuot_comp_kerAugIdealQuotToZCSepDiffLinear
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi) :
    letI : Module (ZCCompletedGroupAlgebra C H)
        (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
      kerAugClosedQuotTargetCompletedModuleOfSurj
        C hC hForm psi hpsi hfopen
    (zcSeparatedCompletedDifferentialModuleToKernelAugmentationClosedQuotient
        C hC hForm psi hpsi hfopen).comp
      (kerAugIdealQuotToZCSepDiffLinear
        C hC hForm psi hpsi hfopen) =
    LinearMap.id := by
  let : Module (ZCCompletedGroupAlgebra C H)
      (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
    kerAugClosedQuotTargetCompletedModuleOfSurj
      C hC hForm psi hpsi hfopen
  let : Module (ZCCompletedGroupAlgebra C G)
      (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom) :=
    Module.compHom _ (zcCompletedGroupAlgebraMap C hC psi)
  apply LinearMap.ext
  intro x
  refine Submodule.Quotient.induction_on
    (p := zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
      C hC hForm psi hpsi hfopen) x ?_
  intro y
  let F :=
    zcSeparatedCompletedDifferentialModuleToKernelAugmentationClosedQuotient
      C hC hForm psi hpsi hfopen
  let S :=
    stdAugIdealToZCSepDiff
      C hC psi
  let Q : zcCompletedGroupAlgebraStandardAugmentationIdeal C G →
      KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen :=
    fun y => Submodule.Quotient.mk
      (p := zcCompletedGroupAlgebraKernelAugmentationIdealMulStandardClosed
        C hC hForm psi hpsi hfopen) y
  have hmk :
      kerAugIdealQuotToZCSepDiffLinear
          C hC hForm psi hpsi hfopen (Q y) =
        S y := by
    exact
      kerAugIdealQuotToZCSepDiffLinear_mk
        C hC hForm psi hpsi hfopen y
  change F
      (kerAugIdealQuotToZCSepDiffLinear
        C hC hForm psi hpsi hfopen (Q y)) = Q y
  rw [hmk]
  let P : zcCompletedGroupAlgebraStandardAugmentationIdeal C G → Prop := fun y =>
    F (S y) = Q y
  have hyspan : (y : ZCCompletedGroupAlgebra C G) ∈
      Submodule.span (ZCCompletedGroupAlgebra C G)
        (Set.range fun h : G => zcGroupLike C G h - 1) := by
    change (y : ZCCompletedGroupAlgebra C G) ∈
      zcCompletedGroupAlgebraStandardAugmentationIdeal C G
    exact y.2
  exact
    (Submodule.span_induction
      (p := fun z hz =>
        ∀ y' : zcCompletedGroupAlgebraStandardAugmentationIdeal C G,
          (y' : ZCCompletedGroupAlgebra C G) = z → P y')
      (by
        rintro _ ⟨g, rfl⟩ y' hy'
        have hy'' :
            y' =
              ⟨zcCompletedGroupAlgebraBoundary C (MonoidHom.id G) g,
                zcCompletedGroupAlgebraBoundary_mem_standardAugmentationIdeal
                  C G (MonoidHom.id G) g⟩ := by
          apply Subtype.ext
          change
            (y' : ZCCompletedGroupAlgebra C G) =
              zcGroupLike C G g - 1
          exact hy'
        rw [hy'']
        let yg : zcCompletedGroupAlgebraStandardAugmentationIdeal C G :=
          ⟨zcCompletedGroupAlgebraBoundary C (MonoidHom.id G) g,
            zcCompletedGroupAlgebraBoundary_mem_standardAugmentationIdeal
              C G (MonoidHom.id G) g⟩
        change P yg
        have hSg :
            S yg = zcSeparatedUniversalDifferential C psi.toMonoidHom g := by
          exact
            stdAugIdealToZCSepDiff_boundary
              C hC psi g
        dsimp [P, Q]
        calc
          F (S yg) = F (zcSeparatedUniversalDifferential C psi.toMonoidHom g) := by
            exact congrArg F hSg
          _ =
              zcCompletedGroupAlgebraSourceBoundaryToKernelAugmentationClosedQuotient
                C hC hForm psi hpsi hfopen g := by
              rw [zcSepDiffToKerAugClosedQuot_universal]
          _ = Submodule.Quotient.mk yg := rfl)
      (by
        intro y' hy'
        have hy'' : y' = 0 := by
          apply Subtype.ext
          simpa using hy'
        rw [hy'']
        change P (0 : zcCompletedGroupAlgebraStandardAugmentationIdeal C G)
        change F (S 0) = 0
        rw [map_zero, map_zero])
      (by
        intro a b ha hb hpa hpb y' hy'
        let ya : zcCompletedGroupAlgebraStandardAugmentationIdeal C G :=
          ⟨a, by
            simpa [zcCompletedGroupAlgebraStandardAugmentationIdeal_eq_span] using ha⟩
        let yb : zcCompletedGroupAlgebraStandardAugmentationIdeal C G :=
          ⟨b, by
            simpa [zcCompletedGroupAlgebraStandardAugmentationIdeal_eq_span] using hb⟩
        have hpa' : P ya := hpa ya rfl
        have hpb' : P yb := hpb yb rfl
        change F (S ya) = Q ya at hpa'
        change F (S yb) = Q yb at hpb'
        have hy'' : y' = ya + yb := by
          apply Subtype.ext
          simpa [ya, yb] using hy'
        rw [hy'']
        change P (ya + yb)
        change F (S (ya + yb)) = Q (ya + yb)
        rw [map_add, map_add, hpa', hpb']
        simp only [Submodule.Quotient.mk_add, Q])
      (by
        intro a b hb hpb y' hy'
        let yb : zcCompletedGroupAlgebraStandardAugmentationIdeal C G :=
          ⟨b, by
            simpa [zcCompletedGroupAlgebraStandardAugmentationIdeal_eq_span] using hb⟩
        have hpb' : P yb := hpb yb rfl
        change F (S yb) = Q yb at hpb'
        have hy'' : y' = a • yb := by
          apply Subtype.ext
          simpa [yb] using hy'
        rw [hy'']
        change P (a • yb)
        change F (S (a • yb)) = Q (a • yb)
        have hsource :
            a • S yb =
              zcCompletedGroupAlgebraMap C hC psi a • S yb := by
          exact
            (zcSeparatedCompletedDifferentialModule_source_map_smul
              C hC psi a (S yb)).symm
        calc
          F (S (a • yb)) = F (a • S yb) := by
            rw [map_smul]
          _ = F (zcCompletedGroupAlgebraMap C hC psi a • S yb) := by
            rw [hsource]
          _ = zcCompletedGroupAlgebraMap C hC psi a • F (S yb) := by
            rw [map_smul]
          _ = zcCompletedGroupAlgebraMap C hC psi a • Q yb := by
            rw [hpb']
          _ = a • Q yb := by
            exact
              kerAugClosedQuotTargetCompletedModuleOfSurj_map_smul
                C hC hForm psi hpsi hfopen a (Q yb)
          _ = Q (a • yb) := by
            dsimp [Q])
      hyspan) y rfl

/--
The separated completed differential module is the closed source augmentation quotient for a
surjective open continuous homomorphism.
-/
def zcSepDiffEquivKerAugClosedQuot_of_surj
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi) :
    letI : Module (ZCCompletedGroupAlgebra C H)
        (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
      kerAugClosedQuotTargetCompletedModuleOfSurj
        C hC hForm psi hpsi hfopen
    ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom
      ≃ₗ[ZCCompletedGroupAlgebra C H]
    KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen := by
  letI : Module (ZCCompletedGroupAlgebra C H)
      (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
    kerAugClosedQuotTargetCompletedModuleOfSurj
      C hC hForm psi hpsi hfopen
  exact
    LinearEquiv.ofLinearMap
      (zcSeparatedCompletedDifferentialModuleToKernelAugmentationClosedQuotient
        C hC hForm psi hpsi hfopen)
      (kerAugIdealQuotToZCSepDiffLinear
        C hC hForm psi hpsi hfopen)
      (zcSepDiffToKerAugClosedQuot_comp_kerAugIdealQuotToZCSepDiffLinear
        C hC hForm psi hpsi hfopen)
      (kerAugIdealQuotToZCSepDiffLinear_comp_zcSepDiffToKerAugClosedQuot
        C hC hForm psi hpsi hfopen)

/--
The Fox-coordinate equivalence is evaluated by the finite-stage coordinate formula in the
completed differential complex.
-/
@[simp]
theorem zcSepDiffEquivKerAugClosedQuot_of_surj_apply
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (x : ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom) :
    zcSepDiffEquivKerAugClosedQuot_of_surj
        C hC hForm psi hpsi hfopen x =
      zcSeparatedCompletedDifferentialModuleToKernelAugmentationClosedQuotient
        C hC hForm psi hpsi hfopen x := rfl

/--
The inverse Fox-coordinate equivalence is evaluated by reconstructing the class from its
completed coordinate data.
-/
@[simp]
theorem zcSepDiffEquivKerAugClosedQuot_of_surj_symm_apply
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (x : KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :
    (zcSepDiffEquivKerAugClosedQuot_of_surj
        C hC hForm psi hpsi hfopen).symm x =
      kerAugIdealQuotToZCSepDiffLinear
        C hC hForm psi hpsi hfopen x := rfl

/--
The closed source augmentation quotient equivalence identifies \(A_{\psi}(C)\) over
\(\mathbb{Z}_C\) with the separated completed differential module, rather than with the raw
algebraic quotient.
-/
def zcApsiEquivKerAugClosedQuot_of_surj
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi) :
    letI : Module (ZCCompletedGroupAlgebra C H)
        (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
      kerAugClosedQuotTargetCompletedModuleOfSurj
        C hC hForm psi hpsi hfopen
    ZCApsi C psi.toMonoidHom ≃ₗ[ZCCompletedGroupAlgebra C H]
      KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen :=
  zcSepDiffEquivKerAugClosedQuot_of_surj
    C hC hForm psi hpsi hfopen

/--
The Fox-coordinate equivalence is evaluated by the finite-stage coordinate formula in the
completed differential complex.
-/
@[simp]
theorem zcApsiEquivKerAugClosedQuot_of_surj_apply
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (x : ZCApsi C psi.toMonoidHom) :
    zcApsiEquivKerAugClosedQuot_of_surj
        C hC hForm psi hpsi hfopen x =
      zcSeparatedCompletedDifferentialModuleToKernelAugmentationClosedQuotient
        C hC hForm psi hpsi hfopen x := rfl

/--
The inverse Fox-coordinate equivalence is evaluated by reconstructing the class from its
completed coordinate data.
-/
@[simp]
theorem zcApsiEquivKerAugClosedQuot_of_surj_symm_apply
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (x : KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :
    (zcApsiEquivKerAugClosedQuot_of_surj
        C hC hForm psi hpsi hfopen).symm x =
      kerAugIdealQuotToZCSepDiffLinear
        C hC hForm psi hpsi hfopen x := rfl

/--
For a surjective target map, the completed target scalar action on the kernel-augmentation
quotient is compatible with applying the induced algebra map.
-/
theorem zcCompletedGAKerAugQuotTargetCompletedModuleOfSurjective_map_smul
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hker_mul :
      ∀ k : ZCCompletedGroupAlgebra C G,
        k ∈ RingHom.ker (zcCompletedGroupAlgebraMap C hC psi) →
        ∀ y : zcCompletedGroupAlgebraStandardAugmentationIdeal C G,
          (⟨k * (y : ZCCompletedGroupAlgebra C G),
            (zcCompletedGroupAlgebraStandardAugmentationIdeal C G).mul_mem_left k y.2⟩ :
              zcCompletedGroupAlgebraStandardAugmentationIdeal C G) ∈
            zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi)
    (a : ZCCompletedGroupAlgebra C G) (x : KernelAugmentationIdealQuotient C psi) :
    letI : Module (ZCCompletedGroupAlgebra C H) (KernelAugmentationIdealQuotient C psi) :=
      zcCompletedGAKerAugQuotTargetCompletedModuleOfSurjective_of_kernelMulStandard_le
        C hC hForm psi hpsi hker_mul
    zcCompletedGroupAlgebraMap C hC psi a • x = a • x := by
  let : Module (ZCCompletedGroupAlgebra C H) (KernelAugmentationIdealQuotient C psi) :=
    zcCompletedGAKerAugQuotTargetCompletedModuleOfSurjective_of_kernelMulStandard_le
      C hC hForm psi hpsi hker_mul
  change zcCompletedGroupAlgebraTargetLiftOfSurjective C hC hForm psi hpsi
      (zcCompletedGroupAlgebraMap C hC psi a) • x =
    a • x
  have hdiff :
      zcCompletedGroupAlgebraTargetLiftOfSurjective C hC hForm psi hpsi
          (zcCompletedGroupAlgebraMap C hC psi a) - a ∈
        RingHom.ker (zcCompletedGroupAlgebraMap C hC psi) := by
    change zcCompletedGroupAlgebraMap C hC psi
        (zcCompletedGroupAlgebraTargetLiftOfSurjective C hC hForm psi hpsi
          (zcCompletedGroupAlgebraMap C hC psi a) - a) = 0
    rw [map_sub, zcCompletedGroupAlgebraMap_targetLiftOfSurjective, sub_self]
  have hzero :=
    zcCompletedGAKerAugQuot_ker_map_smul_eq_zero_of_kernelMulStandard_le
      C hC psi hker_mul
      (zcCompletedGroupAlgebraTargetLiftOfSurjective C hC hForm psi hpsi
        (zcCompletedGroupAlgebraMap C hC psi a) - a) hdiff x
  rw [sub_smul] at hzero
  exact sub_eq_zero.mp hzero

/--
In the descended target module structure, the group-like element of \(\psi(g)\) acts in the same
way as the source group-like element of \(g\).
-/
theorem zcCompletedGAKerAugQuotTargetCompletedModuleOfSurjective_groupLike_smul
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hker_mul :
      ∀ k : ZCCompletedGroupAlgebra C G,
        k ∈ RingHom.ker (zcCompletedGroupAlgebraMap C hC psi) →
        ∀ y : zcCompletedGroupAlgebraStandardAugmentationIdeal C G,
          (⟨k * (y : ZCCompletedGroupAlgebra C G),
            (zcCompletedGroupAlgebraStandardAugmentationIdeal C G).mul_mem_left k y.2⟩ :
              zcCompletedGroupAlgebraStandardAugmentationIdeal C G) ∈
            zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi)
    (g : G) (x : KernelAugmentationIdealQuotient C psi) :
    letI : Module (ZCCompletedGroupAlgebra C H) (KernelAugmentationIdealQuotient C psi) :=
      zcCompletedGAKerAugQuotTargetCompletedModuleOfSurjective_of_kernelMulStandard_le
        C hC hForm psi hpsi hker_mul
    zcGroupLike C H (psi g) • x = zcGroupLike C G g • x := by
  let : Module (ZCCompletedGroupAlgebra C H) (KernelAugmentationIdealQuotient C psi) :=
    zcCompletedGAKerAugQuotTargetCompletedModuleOfSurjective_of_kernelMulStandard_le
      C hC hForm psi hpsi hker_mul
  rw [← zcCompletedGroupAlgebraMap_groupLike (C := C) (hC := hC) psi g]
  exact
    zcCompletedGAKerAugQuotTargetCompletedModuleOfSurjective_map_smul
      C hC hForm psi hpsi hker_mul (zcGroupLike C G g) x

/--
Under the explicit kernel-product hypothesis, the source boundary is a crossed differential for
the descended completed target scalars.
-/
def sourceBoundaryToKerAugTargetCrossedHomOfSurjectiveOfKernelMulStandardLe
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hker_mul :
      ∀ k : ZCCompletedGroupAlgebra C G,
        k ∈ RingHom.ker (zcCompletedGroupAlgebraMap C hC psi) →
        ∀ y : zcCompletedGroupAlgebraStandardAugmentationIdeal C G,
          (⟨k * (y : ZCCompletedGroupAlgebra C G),
            (zcCompletedGroupAlgebraStandardAugmentationIdeal C G).mul_mem_left k y.2⟩ :
              zcCompletedGroupAlgebraStandardAugmentationIdeal C G) ∈
            zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi) :
    letI : Module (ZCCompletedGroupAlgebra C H) (KernelAugmentationIdealQuotient C psi) :=
      zcCompletedGAKerAugQuotTargetCompletedModuleOfSurjective_of_kernelMulStandard_le
        C hC hForm psi hpsi hker_mul
    ScalarCrossedHom
      (zcCompletedGroupAlgebraScalar C psi.toMonoidHom)
      (KernelAugmentationIdealQuotient C psi) := by
  letI : Module (ZCCompletedGroupAlgebra C H) (KernelAugmentationIdealQuotient C psi) :=
    zcCompletedGAKerAugQuotTargetCompletedModuleOfSurjective_of_kernelMulStandard_le
      C hC hForm psi hpsi hker_mul
  exact
    { toFun := zcCompletedGroupAlgebraSourceBoundaryToKernelAugmentationQuotient C psi
      map_mul' := by
        intro g h
        rw [(zcCompletedGroupAlgebraSourceBoundaryToKernelAugmentationQuotient
          C psi).map_mul]
        congr 1
        change zcGroupLike C G g •
            zcCompletedGroupAlgebraSourceBoundaryToKernelAugmentationQuotient C psi h =
          zcGroupLike C H (psi g) •
            zcCompletedGroupAlgebraSourceBoundaryToKernelAugmentationQuotient C psi h
        exact
          (zcCompletedGAKerAugQuotTargetCompletedModuleOfSurjective_groupLike_smul
            C hC hForm psi hpsi hker_mul g
            (zcCompletedGroupAlgebraSourceBoundaryToKernelAugmentationQuotient
              C psi h)).symm }

/--
Under the explicit kernel-product hypothesis, the completed universal differential module maps
to the algebraic source augmentation quotient by \(dg \mapsto [g]-1\). The hypothesis is the
condition needed for the algebraic quotient \(I(G) / I(\ker \psi)I(G)\) to carry the completed
target \(\mathbb{Z}_C\llbracket H\rrbracket\)-module structure.
-/
def zcDiffToKerAugQuotOfSurj_of_kernelMulStandard_le
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hker_mul :
      ∀ k : ZCCompletedGroupAlgebra C G,
        k ∈ RingHom.ker (zcCompletedGroupAlgebraMap C hC psi) →
        ∀ y : zcCompletedGroupAlgebraStandardAugmentationIdeal C G,
          (⟨k * (y : ZCCompletedGroupAlgebra C G),
            (zcCompletedGroupAlgebraStandardAugmentationIdeal C G).mul_mem_left k y.2⟩ :
              zcCompletedGroupAlgebraStandardAugmentationIdeal C G) ∈
            zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi) :
    letI : Module (ZCCompletedGroupAlgebra C H) (KernelAugmentationIdealQuotient C psi) :=
      zcCompletedGAKerAugQuotTargetCompletedModuleOfSurjective_of_kernelMulStandard_le
        C hC hForm psi hpsi hker_mul
    ZCCompletedDifferentialModule C psi.toMonoidHom →ₗ[ZCCompletedGroupAlgebra C H]
      KernelAugmentationIdealQuotient C psi := by
  letI : Module (ZCCompletedGroupAlgebra C H) (KernelAugmentationIdealQuotient C psi) :=
    zcCompletedGAKerAugQuotTargetCompletedModuleOfSurjective_of_kernelMulStandard_le
      C hC hForm psi hpsi hker_mul
  exact
    crossedHomModuleLift
      (A := KernelAugmentationIdealQuotient C psi)
      (zcCompletedGroupAlgebraScalar C psi.toMonoidHom)
      (sourceBoundaryToKerAugTargetCrossedHomOfSurjectiveOfKernelMulStandardLe
        C hC hForm psi hpsi hker_mul)

/--
Under the kernel-product hypothesis, the algebraic source augmentation quotient map sends the
universal differential to the class of \([g]-1\).
-/
@[simp 900]
theorem zcDiffToKerAugQuotOfSurj_of_kernelMulStandard_le_universal
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hker_mul :
      ∀ k : ZCCompletedGroupAlgebra C G,
        k ∈ RingHom.ker (zcCompletedGroupAlgebraMap C hC psi) →
        ∀ y : zcCompletedGroupAlgebraStandardAugmentationIdeal C G,
          (⟨k * (y : ZCCompletedGroupAlgebra C G),
            (zcCompletedGroupAlgebraStandardAugmentationIdeal C G).mul_mem_left k y.2⟩ :
              zcCompletedGroupAlgebraStandardAugmentationIdeal C G) ∈
            zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi)
    (g : G) :
    zcDiffToKerAugQuotOfSurj_of_kernelMulStandard_le
        C hC hForm psi hpsi hker_mul
        (zcUniversalDifferential C psi.toMonoidHom g) =
      zcCompletedGroupAlgebraSourceBoundaryToKernelAugmentationQuotient C psi g := by
  let : Module (ZCCompletedGroupAlgebra C H) (KernelAugmentationIdealQuotient C psi) :=
    zcCompletedGAKerAugQuotTargetCompletedModuleOfSurjective_of_kernelMulStandard_le
      C hC hForm psi hpsi hker_mul
  exact
    crossedHomModuleLift_universal
      (A := KernelAugmentationIdealQuotient C psi)
      (zcCompletedGroupAlgebraScalar C psi.toMonoidHom)
      (sourceBoundaryToKerAugTargetCrossedHomOfSurjectiveOfKernelMulStandardLe
        C hC hForm psi hpsi hker_mul) g

/--
The algebraic map \(A_{\psi}(C) \to I(G) / I(\ker \psi)I(G)\) is onto once the algebraic
quotient has the completed target scalar action supplied by the explicit kernel-product
hypothesis.
-/
theorem zcDiffToKerAugQuotOfSurj_of_kernelMulStandard_le_surj
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hker_mul :
      ∀ k : ZCCompletedGroupAlgebra C G,
        k ∈ RingHom.ker (zcCompletedGroupAlgebraMap C hC psi) →
        ∀ y : zcCompletedGroupAlgebraStandardAugmentationIdeal C G,
          (⟨k * (y : ZCCompletedGroupAlgebra C G),
            (zcCompletedGroupAlgebraStandardAugmentationIdeal C G).mul_mem_left k y.2⟩ :
              zcCompletedGroupAlgebraStandardAugmentationIdeal C G) ∈
            zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi) :
    Function.Surjective
      (zcDiffToKerAugQuotOfSurj_of_kernelMulStandard_le
        C hC hForm psi hpsi hker_mul) := by
  let : Module (ZCCompletedGroupAlgebra C H) (KernelAugmentationIdealQuotient C psi) :=
    zcCompletedGAKerAugQuotTargetCompletedModuleOfSurjective_of_kernelMulStandard_le
      C hC hForm psi hpsi hker_mul
  intro x
  refine Submodule.Quotient.induction_on
    (p := zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi) x ?_
  intro y
  let L :=
    zcDiffToKerAugQuotOfSurj_of_kernelMulStandard_le
      C hC hForm psi hpsi hker_mul
  let P : zcCompletedGroupAlgebraStandardAugmentationIdeal C G → Prop := fun y =>
    ∃ m : ZCCompletedDifferentialModule C psi.toMonoidHom,
      L m = Submodule.Quotient.mk
        (p := zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi) y
  have hy : P y := by
    have hyspan : (y : ZCCompletedGroupAlgebra C G) ∈
        Submodule.span (ZCCompletedGroupAlgebra C G)
          (Set.range fun h : G => zcGroupLike C G h - 1) := by
      change (y : ZCCompletedGroupAlgebra C G) ∈
        zcCompletedGroupAlgebraStandardAugmentationIdeal C G
      exact y.2
    refine Submodule.span_induction
      (p := fun z hz =>
        P
          ⟨z, by
            simpa [zcCompletedGroupAlgebraStandardAugmentationIdeal_eq_span] using hz⟩)
      ?hgen ?hzero ?hadd ?hsmul hyspan
    · rintro _ ⟨g, rfl⟩
      refine ⟨zcUniversalDifferential C psi.toMonoidHom g, ?_⟩
      rw [zcDiffToKerAugQuotOfSurj_of_kernelMulStandard_le_universal]
      rfl
    · refine ⟨0, ?_⟩
      change (0 : KernelAugmentationIdealQuotient C psi) =
        Submodule.Quotient.mk
          (p := zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi)
          (0 : zcCompletedGroupAlgebraStandardAugmentationIdeal C G)
      rw [Submodule.Quotient.mk_zero]
    · intro a b ha hb hpa hpb
      rcases hpa with ⟨ma, hma⟩
      rcases hpb with ⟨mb, hmb⟩
      refine ⟨ma + mb, ?_⟩
      rw [map_add, hma, hmb, ← Submodule.Quotient.mk_add]
      apply congrArg (fun t : zcCompletedGroupAlgebraStandardAugmentationIdeal C G =>
        Submodule.Quotient.mk
          (p := zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi) t)
      exact Subtype.ext rfl
    · intro a b hb hpb
      rcases hpb with ⟨m, hm⟩
      refine ⟨zcCompletedGroupAlgebraMap C hC psi a • m, ?_⟩
      rw [map_smul, hm]
      calc
        zcCompletedGroupAlgebraMap C hC psi a •
            Submodule.Quotient.mk
              (p := zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi)
              ⟨b, by
                simpa [zcCompletedGroupAlgebraStandardAugmentationIdeal_eq_span] using hb⟩ =
          a •
            Submodule.Quotient.mk
              (p := zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi)
              ⟨b, by
                simpa [zcCompletedGroupAlgebraStandardAugmentationIdeal_eq_span] using hb⟩ := by
            exact
              zcCompletedGAKerAugQuotTargetCompletedModuleOfSurjective_map_smul
                C hC hForm psi hpsi hker_mul a
                (Submodule.Quotient.mk
                  (p := zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi)
                  ⟨b, by
                    simpa [zcCompletedGroupAlgebraStandardAugmentationIdeal_eq_span] using hb⟩)
        _ = Submodule.Quotient.mk
              (p := zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi)
              ⟨a • b, by
                rw [zcCompletedGroupAlgebraStandardAugmentationIdeal_eq_span]
                exact Submodule.smul_mem
                  (Submodule.span (ZCCompletedGroupAlgebra C G)
                    (Set.range fun h : G => zcGroupLike C G h - 1)) a hb⟩ := by
            rw [← Submodule.Quotient.mk_smul]
            apply congrArg (fun t : zcCompletedGroupAlgebraStandardAugmentationIdeal C G =>
              Submodule.Quotient.mk
                (p := zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi) t)
            exact Subtype.ext rfl
  exact hy

/--
Under the explicit kernel-product hypothesis, the natural map from the algebraic source
augmentation quotient to the closed quotient is \(\mathbb{Z}_C\llbracket H\rrbracket\)-linear.
-/
def zcCompletedGAKerAugQuotToClosedQuotientTargetLinear_of_kernelMulStandard_le
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (hker_mul :
      ∀ k : ZCCompletedGroupAlgebra C G,
        k ∈ RingHom.ker (zcCompletedGroupAlgebraMap C hC psi) →
        ∀ y : zcCompletedGroupAlgebraStandardAugmentationIdeal C G,
          (⟨k * (y : ZCCompletedGroupAlgebra C G),
            (zcCompletedGroupAlgebraStandardAugmentationIdeal C G).mul_mem_left k y.2⟩ :
              zcCompletedGroupAlgebraStandardAugmentationIdeal C G) ∈
            zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi) :
    letI : Module (ZCCompletedGroupAlgebra C H) (KernelAugmentationIdealQuotient C psi) :=
      zcCompletedGAKerAugQuotTargetCompletedModuleOfSurjective_of_kernelMulStandard_le
        C hC hForm psi hpsi hker_mul
    letI : Module (ZCCompletedGroupAlgebra C H)
        (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
      kerAugClosedQuotTargetCompletedModuleOfSurj
        C hC hForm psi hpsi hfopen
    KernelAugmentationIdealQuotient C psi →ₗ[ZCCompletedGroupAlgebra C H]
      KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen := by
  letI : Module (ZCCompletedGroupAlgebra C H) (KernelAugmentationIdealQuotient C psi) :=
    zcCompletedGAKerAugQuotTargetCompletedModuleOfSurjective_of_kernelMulStandard_le
      C hC hForm psi hpsi hker_mul
  letI : Module (ZCCompletedGroupAlgebra C H)
      (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
    kerAugClosedQuotTargetCompletedModuleOfSurj
      C hC hForm psi hpsi hfopen
  let Q :=
    zcCompletedGroupAlgebraKernelAugmentationQuotientToClosedQuotient
      C hC hForm psi hpsi hfopen
  refine
    { toFun := Q
      map_add' := by
        intro x y
        exact map_add Q x y
      map_smul' := by
        intro a x
        change Q
            (zcCompletedGroupAlgebraTargetLiftOfSurjective C hC hForm psi hpsi a • x) =
          a • Q x
        rw [map_smul]
        symm
        calc
          a • Q x =
              zcCompletedGroupAlgebraMap C hC psi
                  (zcCompletedGroupAlgebraTargetLiftOfSurjective C hC hForm psi hpsi a) •
                Q x := by
                rw [zcCompletedGroupAlgebraMap_targetLiftOfSurjective]
          _ =
              zcCompletedGroupAlgebraTargetLiftOfSurjective C hC hForm psi hpsi a • Q x := by
                exact
                  kerAugClosedQuotTargetCompletedModuleOfSurj_map_smul
                    C hC hForm psi hpsi hfopen
                    (zcCompletedGroupAlgebraTargetLiftOfSurjective C hC hForm psi hpsi a)
                    (Q x) }

/--
The natural map from the algebraic source augmentation quotient to the closed quotient sends
each algebraic quotient class to its closed quotient class.
-/
@[simp 900]
theorem zcCompletedGAKerAugQuotToClosedQuotientTargetLinear_of_kernelMulStandard_le_mk
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (hker_mul :
      ∀ k : ZCCompletedGroupAlgebra C G,
        k ∈ RingHom.ker (zcCompletedGroupAlgebraMap C hC psi) →
        ∀ y : zcCompletedGroupAlgebraStandardAugmentationIdeal C G,
          (⟨k * (y : ZCCompletedGroupAlgebra C G),
            (zcCompletedGroupAlgebraStandardAugmentationIdeal C G).mul_mem_left k y.2⟩ :
              zcCompletedGroupAlgebraStandardAugmentationIdeal C G) ∈
            zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi)
    (x : zcCompletedGroupAlgebraStandardAugmentationIdeal C G) :
    zcCompletedGAKerAugQuotToClosedQuotientTargetLinear_of_kernelMulStandard_le
        C hC hForm psi hpsi hfopen hker_mul (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk x :
        KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) := by
  let : Module (ZCCompletedGroupAlgebra C H) (KernelAugmentationIdealQuotient C psi) :=
    zcCompletedGAKerAugQuotTargetCompletedModuleOfSurjective_of_kernelMulStandard_le
      C hC hForm psi hpsi hker_mul
  let : Module (ZCCompletedGroupAlgebra C H)
      (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
    kerAugClosedQuotTargetCompletedModuleOfSurj
      C hC hForm psi hpsi hfopen
  rw [zcCompletedGAKerAugQuotToClosedQuotientTargetLinear_of_kernelMulStandard_le]
  exact
    zcCompletedGroupAlgebraKernelAugmentationQuotientToClosedQuotient_mk
      C hC hForm psi hpsi hfopen x

/--
The algebraic quotient map followed by the natural closed-quotient map is the closed quotient
map already constructed directly from \(A_{\psi}(C)\).
-/
theorem zcDiffToKerAugClosedQuotOfSurj_eq_toClosed_comp_quotient_of_kernelMulStandard_le
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H) (hpsi : Function.Surjective psi)
    (hfopen : IsOpenMap psi)
    (hker_mul :
      ∀ k : ZCCompletedGroupAlgebra C G,
        k ∈ RingHom.ker (zcCompletedGroupAlgebraMap C hC psi) →
        ∀ y : zcCompletedGroupAlgebraStandardAugmentationIdeal C G,
          (⟨k * (y : ZCCompletedGroupAlgebra C G),
            (zcCompletedGroupAlgebraStandardAugmentationIdeal C G).mul_mem_left k y.2⟩ :
              zcCompletedGroupAlgebraStandardAugmentationIdeal C G) ∈
            zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi) :
    (zcCompletedGAKerAugQuotToClosedQuotientTargetLinear_of_kernelMulStandard_le
        C hC hForm psi hpsi hfopen hker_mul).comp
      (zcDiffToKerAugQuotOfSurj_of_kernelMulStandard_le
        C hC hForm psi hpsi hker_mul) =
    zcCompletedDifferentialModuleToKernelAugmentationClosedQuotientOfSurjective
      C hC hForm psi hpsi hfopen := by
  let : Module (ZCCompletedGroupAlgebra C H) (KernelAugmentationIdealQuotient C psi) :=
    zcCompletedGAKerAugQuotTargetCompletedModuleOfSurjective_of_kernelMulStandard_le
      C hC hForm psi hpsi hker_mul
  let : Module (ZCCompletedGroupAlgebra C H)
      (KernelAugmentationIdealClosedQuotient C hC hForm psi hpsi hfopen) :=
    kerAugClosedQuotTargetCompletedModuleOfSurj
      C hC hForm psi hpsi hfopen
  apply crossedDifferentialModuleHom_ext
    (zcCompletedGroupAlgebraScalar C psi.toMonoidHom)
  intro g
  calc
    ((zcCompletedGAKerAugQuotToClosedQuotientTargetLinear_of_kernelMulStandard_le
          C hC hForm psi hpsi hfopen hker_mul).comp
        (zcDiffToKerAugQuotOfSurj_of_kernelMulStandard_le
          C hC hForm psi hpsi hker_mul))
        (zcUniversalDifferential C psi.toMonoidHom g)
        =
      zcCompletedGAKerAugQuotToClosedQuotientTargetLinear_of_kernelMulStandard_le
        C hC hForm psi hpsi hfopen hker_mul
        (zcCompletedGroupAlgebraSourceBoundaryToKernelAugmentationQuotient C psi g) := by
        rw [LinearMap.comp_apply,
          zcDiffToKerAugQuotOfSurj_of_kernelMulStandard_le_universal]
    _ =
      zcCompletedGroupAlgebraSourceBoundaryToKernelAugmentationClosedQuotient
        C hC hForm psi hpsi hfopen g := by
        rw [zcCompletedGroupAlgebraSourceBoundaryToKernelAugmentationQuotient]
        exact
          zcCompletedGAKerAugQuotToClosedQuotientTargetLinear_of_kernelMulStandard_le_mk
            C hC hForm psi hpsi hfopen hker_mul
            ⟨zcCompletedGroupAlgebraBoundary C (MonoidHom.id G) g,
              zcCompletedGroupAlgebraBoundary_mem_standardAugmentationIdeal
                C G (MonoidHom.id G) g⟩
    _ =
      zcCompletedDifferentialModuleToKernelAugmentationClosedQuotientOfSurjective
        C hC hForm psi hpsi hfopen
        (zcUniversalDifferential C psi.toMonoidHom g) := by
        rw [zcDiffToKerAugClosedQuotOfSurj_universal]

/--
Source kernel group-like differences act trivially on \(A_{\psi}(C)\) after restricting scalars
along \(\mathbb{Z}_C\llbracket G\rrbracket \to \mathbb{Z}_C\llbracket H\rrbracket\).
-/
theorem zcCompletedDifferentialModule_sourceKernelGroupLikeSubOne_smul_eq_zero
    (hC : ProCGroups.FiniteGroupClass.Hereditary C) (psi : ContinuousMonoidHom G H)
    (n : ProfiniteKernelSubgroup psi) (x : ZCCompletedDifferentialModule C psi.toMonoidHom) :
    letI : Module (ZCCompletedGroupAlgebra C G)
        (ZCCompletedDifferentialModule C psi.toMonoidHom) :=
      Module.compHom _ (zcCompletedGroupAlgebraMap C hC psi)
    (zcGroupLike C G n.1 - 1) • x = 0 := by
  let : Module (ZCCompletedGroupAlgebra C G)
      (ZCCompletedDifferentialModule C psi.toMonoidHom) :=
    Module.compHom _ (zcCompletedGroupAlgebraMap C hC psi)
  have hmap :
      zcCompletedGroupAlgebraMap C hC psi (zcGroupLike C G n.1 - 1) = 0 := by
    rw [map_sub, zcCompletedGroupAlgebraMap_groupLike, map_one]
    rw [show psi (n : G) = 1 from n.2]
    rw [map_one, sub_self]
  change zcCompletedGroupAlgebraMap C hC psi (zcGroupLike C G n.1 - 1) • x = 0
  rw [hmap, zero_smul]

/--
The algebraic product \(I(\ker \psi)I(G)\) acts trivially on \(A_{\psi}(C)\) after restricting
scalars along \(\mathbb{Z}_C\llbracket G\rrbracket \to \mathbb{Z}_C\llbracket H\rrbracket\).
-/
theorem zcCompletedDifferentialModule_kernelAugmentationIdealMulStandard_smul_eq_zero
    (hC : ProCGroups.FiniteGroupClass.Hereditary C) (psi : ContinuousMonoidHom G H)
    (y : zcCompletedGroupAlgebraStandardAugmentationIdeal C G)
    (hy : y ∈ zcCompletedGroupAlgebraKernelAugmentationIdealMulStandard C psi)
    (x : ZCCompletedDifferentialModule C psi.toMonoidHom) :
    letI : Module (ZCCompletedGroupAlgebra C G)
        (ZCCompletedDifferentialModule C psi.toMonoidHom) :=
      Module.compHom _ (zcCompletedGroupAlgebraMap C hC psi)
    (y : ZCCompletedGroupAlgebra C G) • x = 0 := by
  let : Module (ZCCompletedGroupAlgebra C G)
      (ZCCompletedDifferentialModule C psi.toMonoidHom) :=
    Module.compHom _ (zcCompletedGroupAlgebraMap C hC psi)
  change (y : ZCCompletedGroupAlgebra C G) • x = 0
  refine Submodule.span_induction
    (p := fun y : zcCompletedGroupAlgebraStandardAugmentationIdeal C G =>
      fun _ => (y : ZCCompletedGroupAlgebra C G) • x = 0) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨⟨n, s⟩, rfl⟩
    change ((zcGroupLike C G n.1 - 1) * (s : ZCCompletedGroupAlgebra C G)) • x = 0
    rw [mul_smul]
    exact zcCompletedDifferentialModule_sourceKernelGroupLikeSubOne_smul_eq_zero
      C hC psi n ((s : ZCCompletedGroupAlgebra C G) • x)
  · change (0 : ZCCompletedGroupAlgebra C G) • x = 0
    rw [zero_smul]
  · intro y z _ _ hy hz
    change ((y : ZCCompletedGroupAlgebra C G) +
        (z : ZCCompletedGroupAlgebra C G)) • x = 0
    rw [add_smul, hy, hz, zero_add]
  · intro a y _ hy
    change (a * (y : ZCCompletedGroupAlgebra C G)) • x = 0
    rw [mul_smul, hy, smul_zero]

end KernelAugmentationQuotient

end

end FoxDifferential
