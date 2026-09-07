import ProCGroups.FoxDifferential.Completed.ProCIntegerCoefficients.Augmentation
import ProCGroups.FoxDifferential.Completed.ProCIntegerCoefficients.Core
import ProCGroups.FoxDifferential.Completed.ProCIntegerCoefficients.FreeGroup.Fundamental

set_option autoImplicit false

/-!
# Fox differential: completed — \(\mathbb{Z}_C\) coefficients — naturality

The principal declarations in this module are:

- `zcCompletedGroupAlgebraMapStage`
  The finite-stage component of the target map on \(\mathbb{Z}_C\llbracket H\rrbracket\).
- `zcCompletedGroupAlgebraMapStageKernelIdeal`
  The kernel ideal of a finite-stage target map on completed group algebras.
- `zcCompletedGroupAlgebraMapStage_of`
  The finite stage of the \(\mathbb{Z}_C\)-completed group-algebra map sends a group-like basis
  element to the basis element supported at its image.
- `zcCompletedGroupAlgebraMapStage_single`
  The finite stage of the \(\mathbb{Z}_C\)-completed group-algebra map transports a singleton to the
  singleton at its quotient image.
-/

namespace FoxDifferential

noncomputable section

open scoped BigOperators
open ProCGroups.ProC

universe u v

section CompletedGroupAlgebraMap

variable (C : ProCGroups.FiniteGroupClass.{u})
variable (hC : ProCGroups.FiniteGroupClass.Hereditary C)
variable {H K : Type u}
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable [Group K] [TopologicalSpace K] [IsTopologicalGroup K]

/-- The finite-stage component of the target map on \(\mathbb{Z}_C\llbracket H\rrbracket\). -/
def zcCompletedGroupAlgebraMapStage
    (φ : H →ₜ* K) (i : ZCCompletedGroupAlgebraIndex C K) :
    ZCCompletedGroupAlgebraStage C H
        (i.1, completedGroupAlgebraComapIndexInClass
          (G := H) (H := K) C hC φ i.2) →+*
      ZCCompletedGroupAlgebraStage C K i :=
  MonoidAlgebra.mapDomainRingHom (ModNCompletedCoeff i.1.modulus)
    (completedGroupAlgebraComapQuotientMapInClass (G := H) (H := K) C hC φ i.2)

/--
The finite stage of the \(\mathbb{Z}_C\)-completed group-algebra map sends a group-like basis
element to the basis element supported at its image.
-/
@[simp]
theorem zcCompletedGroupAlgebraMapStage_of
    (φ : H →ₜ* K) (i : ZCCompletedGroupAlgebraIndex C K)
    (q : CompletedGroupAlgebraQuotientInClass H C
      (completedGroupAlgebraComapIndexInClass (G := H) (H := K) C hC φ i.2)) :
    zcCompletedGroupAlgebraMapStage C hC φ i
        (MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus) _ q) =
      MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus) _
        (completedGroupAlgebraComapQuotientMapInClass (G := H) (H := K) C hC φ i.2 q) := by
  simp only [zcCompletedGroupAlgebraMapStage, MonoidAlgebra.of_apply,
    MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single]

/--
The finite stage of the \(\mathbb{Z}_C\)-completed group-algebra map transports a singleton to the
singleton at its quotient image.
-/
theorem zcCompletedGroupAlgebraMapStage_single
    (φ : H →ₜ* K) (i : ZCCompletedGroupAlgebraIndex C K)
    (q : CompletedGroupAlgebraQuotientInClass H C
      (completedGroupAlgebraComapIndexInClass (G := H) (H := K) C hC φ i.2))
    (a : ModNCompletedCoeff i.1.modulus) :
    zcCompletedGroupAlgebraMapStage C hC φ i (MonoidAlgebra.single q a) =
      MonoidAlgebra.single
        (completedGroupAlgebraComapQuotientMapInClass (G := H) (H := K) C hC φ i.2 q) a := by
  simp only [zcCompletedGroupAlgebraMapStage, MonoidAlgebra.mapDomainRingHom_apply,
    MonoidAlgebra.mapDomain_single]

/--
A surjective target homomorphism induces a surjective map on every finite
\(\mathbb{Z}_C\)-coefficient, \(C\)-quotient stage of the completed group algebra.
-/
theorem zcCompletedGroupAlgebraMapStage_surjective_of_surjective
    (φ : H →ₜ* K) (hφ : Function.Surjective φ)
    (i : ZCCompletedGroupAlgebraIndex C K) :
    Function.Surjective (zcCompletedGroupAlgebraMapStage C hC φ i) := by
  intro y
  obtain ⟨x, hx⟩ :=
    Finsupp.mapDomain_surjective (M := ModNCompletedCoeff i.1.modulus)
      (completedGroupAlgebraComapQuotientMapInClass_surjective_of_surjective
        (G := H) (H := K) C hC φ hφ i.2) y.coeff
  refine ⟨MonoidAlgebra.ofCoeff x, ?_⟩
  apply MonoidAlgebra.coeff_injective
  exact hx

/-- A finite-stage target map is linear over the common residue coefficient ring. -/
theorem zcCompletedGroupAlgebraMapStage_smul
    (φ : H →ₜ* K) (i : ZCCompletedGroupAlgebraIndex C K)
    (a : ModNCompletedCoeff i.1.modulus)
    (x :
      ZCCompletedGroupAlgebraStage C H
        (i.1, completedGroupAlgebraComapIndexInClass
          (G := H) (H := K) C hC φ i.2)) :
    zcCompletedGroupAlgebraMapStage C hC φ i (a • x) =
      a • zcCompletedGroupAlgebraMapStage C hC φ i x := by
  rcases ZMod.intCast_surjective a with ⟨t, rfl⟩
  rw [Algebra.smul_def, Algebra.smul_def, RingHom.map_mul]
  simp only [zcCompletedGroupAlgebraMapStage, map_intCast, MonoidAlgebra.mapDomainRingHom_apply]

/-- The kernel ideal of a finite-stage target map on completed group algebras. -/
def zcCompletedGroupAlgebraMapStageKernelIdeal
    (φ : H →ₜ* K) (i : ZCCompletedGroupAlgebraIndex C K) :
    Ideal
      (ZCCompletedGroupAlgebraStage C H
        (i.1, completedGroupAlgebraComapIndexInClass
          (G := H) (H := K) C hC φ i.2)) :=
  RingHom.ker (zcCompletedGroupAlgebraMapStage C hC φ i)

/--
Membership in the completed group-algebra stage-map kernel ideal is equivalent to vanishing of
the corresponding finite-stage coordinate.
-/
@[simp]
theorem mem_zcCompletedGroupAlgebraMapStageKernelIdeal_iff
    {C : ProCGroups.FiniteGroupClass.{u}} {hC : C.Hereditary}
    {φ : H →ₜ* K} {i : ZCCompletedGroupAlgebraIndex C K}
    {x :
      ZCCompletedGroupAlgebraStage C H
        (i.1, completedGroupAlgebraComapIndexInClass
          (G := H) (H := K) C hC φ i.2)} :
    x ∈ zcCompletedGroupAlgebraMapStageKernelIdeal C hC φ i ↔
      zcCompletedGroupAlgebraMapStage C hC φ i x = 0 := by
  rw [zcCompletedGroupAlgebraMapStageKernelIdeal, RingHom.mem_ker]

/--
The finite-stage relation augmentation generator attached to an element of the quotient kernel.
-/
def zcCompletedGroupAlgebraMapStageRelationAugmentationGenerator
    (φ : H →ₜ* K) (i : ZCCompletedGroupAlgebraIndex C K)
    (q :
      (completedGroupAlgebraComapQuotientMapInClass
        (G := H) (H := K) C hC φ i.2).ker) :
    ZCCompletedGroupAlgebraStage C H
      (i.1, completedGroupAlgebraComapIndexInClass
        (G := H) (H := K) C hC φ i.2) :=
  MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus)
    (CompletedGroupAlgebraQuotientInClass H C
      (completedGroupAlgebraComapIndexInClass
        (G := H) (H := K) C hC φ i.2)) q.1 - 1

/-- The finite-stage relation augmentation ideal for a target map. -/
def zcCompletedGroupAlgebraMapStageRelationAugmentationIdeal
    (φ : H →ₜ* K) (i : ZCCompletedGroupAlgebraIndex C K) :
    Ideal
      (ZCCompletedGroupAlgebraStage C H
        (i.1, completedGroupAlgebraComapIndexInClass
          (G := H) (H := K) C hC φ i.2)) :=
  Ideal.span
    (Set.range
      (zcCompletedGroupAlgebraMapStageRelationAugmentationGenerator C hC φ i))

/-- A finite-stage relation augmentation generator lies in the kernel ideal. -/
theorem zcCompletedGroupAlgebraMapStageRelationAugmentationGenerator_mem_kernelIdeal
    (φ : H →ₜ* K) (i : ZCCompletedGroupAlgebraIndex C K)
    (q :
      (completedGroupAlgebraComapQuotientMapInClass
        (G := H) (H := K) C hC φ i.2).ker) :
    zcCompletedGroupAlgebraMapStageRelationAugmentationGenerator C hC φ i q ∈
      zcCompletedGroupAlgebraMapStageKernelIdeal C hC φ i := by
  rw [mem_zcCompletedGroupAlgebraMapStageKernelIdeal_iff]
  change zcCompletedGroupAlgebraMapStage C hC φ i
      (MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus)
          (CompletedGroupAlgebraQuotientInClass H C
            (completedGroupAlgebraComapIndexInClass
              (G := H) (H := K) C hC φ i.2)) q.1 - 1) = 0
  rw [map_sub, map_one, zcCompletedGroupAlgebraMapStage_of]
  have hq :
      completedGroupAlgebraComapQuotientMapInClass
          (G := H) (H := K) C hC φ i.2 q.1 = 1 := by
    exact MonoidHom.mem_ker.mp
      (show (q : CompletedGroupAlgebraQuotientInClass H C
        (completedGroupAlgebraComapIndexInClass
          (G := H) (H := K) C hC φ i.2)) ∈
          (completedGroupAlgebraComapQuotientMapInClass
            (G := H) (H := K) C hC φ i.2).ker from q.2)
  rw [hq]
  simp only [MonoidAlgebra.of_apply, MonoidAlgebra.one_def, sub_self]

/-- The finite-stage relation augmentation ideal is contained in the finite-stage kernel ideal. -/
theorem zcCompletedGroupAlgebraMapStageRelationAugmentationIdeal_le_kernelIdeal
    (φ : H →ₜ* K) (i : ZCCompletedGroupAlgebraIndex C K) :
    zcCompletedGroupAlgebraMapStageRelationAugmentationIdeal C hC φ i ≤
      zcCompletedGroupAlgebraMapStageKernelIdeal C hC φ i := by
  refine Ideal.span_le.2 ?_
  rintro x ⟨q, rfl⟩
  exact zcCompletedGroupAlgebraMapStageRelationAugmentationGenerator_mem_kernelIdeal
    C hC φ i q

/--
A linear section of a surjective finite-stage target map, obtained by choosing a source quotient
lift for each target quotient basis element.
-/
def zcCompletedGroupAlgebraMapStageTargetSection
    (φ : H →ₜ* K) (hφ : Function.Surjective φ)
    (i : ZCCompletedGroupAlgebraIndex C K) :
    ZCCompletedGroupAlgebraStage C K i →ₗ[ModNCompletedCoeff i.1.modulus]
      ZCCompletedGroupAlgebraStage C H
        (i.1, completedGroupAlgebraComapIndexInClass
          (G := H) (H := K) C hC φ i.2) :=
  (Finsupp.linearCombination (ModNCompletedCoeff i.1.modulus)
      (fun q : CompletedGroupAlgebraQuotientInClass K C i.2 =>
        MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus)
          (CompletedGroupAlgebraQuotientInClass H C
            (completedGroupAlgebraComapIndexInClass
              (G := H) (H := K) C hC φ i.2))
          (Function.surjInv
            (completedGroupAlgebraComapQuotientMapInClass_surjective_of_surjective
              (G := H) (H := K) C hC φ hφ i.2) q))).comp
    (MonoidAlgebra.coeffLinearEquiv
      (ModNCompletedCoeff i.1.modulus)).toLinearMap

/--
The chosen target section sends a group-like basis element to a group-like basis element over its
selected source representative.
-/
@[simp 900]
theorem zcCompletedGroupAlgebraMapStageTargetSection_of
    (φ : H →ₜ* K) (hφ : Function.Surjective φ)
    (i : ZCCompletedGroupAlgebraIndex C K)
    (q : CompletedGroupAlgebraQuotientInClass K C i.2) :
    zcCompletedGroupAlgebraMapStageTargetSection C hC φ hφ i
        (MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus)
          (CompletedGroupAlgebraQuotientInClass K C i.2) q) =
      MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus)
        (CompletedGroupAlgebraQuotientInClass H C
          (completedGroupAlgebraComapIndexInClass
            (G := H) (H := K) C hC φ i.2))
        (Function.surjInv
          (completedGroupAlgebraComapQuotientMapInClass_surjective_of_surjective
            (G := H) (H := K) C hC φ hφ i.2) q) := by
  change
    (Finsupp.linearCombination (ModNCompletedCoeff i.1.modulus)
      (fun q : CompletedGroupAlgebraQuotientInClass K C i.2 =>
        MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus)
          (CompletedGroupAlgebraQuotientInClass H C
            (completedGroupAlgebraComapIndexInClass
              (G := H) (H := K) C hC φ i.2))
          (Function.surjInv
            (completedGroupAlgebraComapQuotientMapInClass_surjective_of_surjective
              (G := H) (H := K) C hC φ hφ i.2) q)))
      (Finsupp.single q (1 : ModNCompletedCoeff i.1.modulus)) = _
  rw [Finsupp.linearCombination_single, one_smul]

/-- The chosen finite-stage section is a right inverse to the finite-stage target map. -/
theorem zcCompletedGroupAlgebraMapStage_targetSection
    (φ : H →ₜ* K) (hφ : Function.Surjective φ)
    (i : ZCCompletedGroupAlgebraIndex C K)
    (y : ZCCompletedGroupAlgebraStage C K i) :
    zcCompletedGroupAlgebraMapStage C hC φ i
        (zcCompletedGroupAlgebraMapStageTargetSection C hC φ hφ i y) = y := by
  classical
  refine MonoidAlgebra.induction_on
    (motive := fun y : ZCCompletedGroupAlgebraStage C K i =>
      zcCompletedGroupAlgebraMapStage C hC φ i
          (zcCompletedGroupAlgebraMapStageTargetSection C hC φ hφ i y) = y)
    y ?single ?add ?smul
  · intro q
    rw [zcCompletedGroupAlgebraMapStageTargetSection_of,
      zcCompletedGroupAlgebraMapStage_of]
    exact congrArg
      (MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus)
        (CompletedGroupAlgebraQuotientInClass K C i.2))
      (Function.surjInv_eq
        (completedGroupAlgebraComapQuotientMapInClass_surjective_of_surjective
          (G := H) (H := K) C hC φ hφ i.2) q)
  · intro x y hx hy
    rw [map_add, map_add, hx, hy]
  · intro a y hy
    rw [map_smul, zcCompletedGroupAlgebraMapStage_smul, hy]

/--
At a finite completed group-algebra stage, a source basis element minus the chosen lift of its
target image lies in the relation augmentation ideal.
-/
theorem zcCompletedGAMapStage_sourceBasis_sub_targetSection_mem_relationAugmentationIdeal
    (φ : H →ₜ* K) (hφ : Function.Surjective φ)
    (i : ZCCompletedGroupAlgebraIndex C K)
    (s :
      CompletedGroupAlgebraQuotientInClass H C
        (completedGroupAlgebraComapIndexInClass
          (G := H) (H := K) C hC φ i.2)) :
    MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus)
        (CompletedGroupAlgebraQuotientInClass H C
          (completedGroupAlgebraComapIndexInClass
            (G := H) (H := K) C hC φ i.2)) s -
      zcCompletedGroupAlgebraMapStageTargetSection C hC φ hφ i
        (zcCompletedGroupAlgebraMapStage C hC φ i
          (MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus)
            (CompletedGroupAlgebraQuotientInClass H C
              (completedGroupAlgebraComapIndexInClass
                (G := H) (H := K) C hC φ i.2)) s)) ∈
      zcCompletedGroupAlgebraMapStageRelationAugmentationIdeal C hC φ i := by
  let f :=
    completedGroupAlgebraComapQuotientMapInClass
      (G := H) (H := K) C hC φ i.2
  let hfsurj :
      Function.Surjective f :=
    completedGroupAlgebraComapQuotientMapInClass_surjective_of_surjective
      (G := H) (H := K) C hC φ hφ i.2
  let t : CompletedGroupAlgebraQuotientInClass K C i.2 := f s
  let lift :
      CompletedGroupAlgebraQuotientInClass H C
        (completedGroupAlgebraComapIndexInClass
          (G := H) (H := K) C hC φ i.2) :=
    Function.surjInv hfsurj t
  let q : f.ker :=
    ⟨lift⁻¹ * s, by
      change f (lift⁻¹ * s) = 1
      rw [map_mul, map_inv]
      have hlift : f lift = t := Function.surjInv_eq hfsurj t
      rw [hlift]
      simp only [inv_mul_cancel, t]⟩
  have hsection :
      zcCompletedGroupAlgebraMapStageTargetSection C hC φ hφ i
        (zcCompletedGroupAlgebraMapStage C hC φ i
          (MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus)
            (CompletedGroupAlgebraQuotientInClass H C
              (completedGroupAlgebraComapIndexInClass
                (G := H) (H := K) C hC φ i.2)) s)) =
        MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus)
          (CompletedGroupAlgebraQuotientInClass H C
            (completedGroupAlgebraComapIndexInClass
              (G := H) (H := K) C hC φ i.2)) lift := by
    rw [zcCompletedGroupAlgebraMapStage_of,
      zcCompletedGroupAlgebraMapStageTargetSection_of]
  rw [hsection]
  have hmul :
      MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus)
          (CompletedGroupAlgebraQuotientInClass H C
            (completedGroupAlgebraComapIndexInClass
              (G := H) (H := K) C hC φ i.2)) lift *
        zcCompletedGroupAlgebraMapStageRelationAugmentationGenerator C hC φ i q =
      MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus)
          (CompletedGroupAlgebraQuotientInClass H C
            (completedGroupAlgebraComapIndexInClass
              (G := H) (H := K) C hC φ i.2)) s -
        MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus)
          (CompletedGroupAlgebraQuotientInClass H C
            (completedGroupAlgebraComapIndexInClass
              (G := H) (H := K) C hC φ i.2)) lift := by
    simp only [zcCompletedGroupAlgebraMapStageRelationAugmentationGenerator, q,
      MonoidAlgebra.of_apply]
    rw [mul_sub, MonoidAlgebra.single_mul_single, mul_one]
    simp only [mul_inv_cancel_left, mul_one]
  rw [← hmul]
  exact
    (zcCompletedGroupAlgebraMapStageRelationAugmentationIdeal C hC φ i).mul_mem_left _
      (Ideal.subset_span ⟨q, rfl⟩)

/--
At a finite completed group-algebra stage, every source element minus the chosen lift of its
target image lies in the relation augmentation ideal.
-/
theorem zcCompletedGAMapStage_sub_targetSection_map_mem_relationAugmentationIdeal
    (φ : H →ₜ* K) (hφ : Function.Surjective φ)
    (i : ZCCompletedGroupAlgebraIndex C K)
    (x :
      ZCCompletedGroupAlgebraStage C H
        (i.1, completedGroupAlgebraComapIndexInClass
          (G := H) (H := K) C hC φ i.2)) :
    x - zcCompletedGroupAlgebraMapStageTargetSection C hC φ hφ i
        (zcCompletedGroupAlgebraMapStage C hC φ i x) ∈
      zcCompletedGroupAlgebraMapStageRelationAugmentationIdeal C hC φ i := by
  classical
  refine MonoidAlgebra.induction_on
    (motive := fun x :
      ZCCompletedGroupAlgebraStage C H
        (i.1, completedGroupAlgebraComapIndexInClass
          (G := H) (H := K) C hC φ i.2) =>
      x - zcCompletedGroupAlgebraMapStageTargetSection C hC φ hφ i
          (zcCompletedGroupAlgebraMapStage C hC φ i x) ∈
        zcCompletedGroupAlgebraMapStageRelationAugmentationIdeal C hC φ i)
    x ?single ?add ?smul
  · intro s
    exact
      zcCompletedGAMapStage_sourceBasis_sub_targetSection_mem_relationAugmentationIdeal
        C hC φ hφ i s
  · intro x y hx hy
    have hcalc :
        x + y - zcCompletedGroupAlgebraMapStageTargetSection C hC φ hφ i
            (zcCompletedGroupAlgebraMapStage C hC φ i (x + y)) =
          (x - zcCompletedGroupAlgebraMapStageTargetSection C hC φ hφ i
              (zcCompletedGroupAlgebraMapStage C hC φ i x)) +
            (y - zcCompletedGroupAlgebraMapStageTargetSection C hC φ hφ i
              (zcCompletedGroupAlgebraMapStage C hC φ i y)) := by
      rw [map_add, map_add]
      abel
    rw [hcalc]
    exact
      (zcCompletedGroupAlgebraMapStageRelationAugmentationIdeal C hC φ i).add_mem hx hy
  · intro a x hx
    have hmap_smul :
        zcCompletedGroupAlgebraMapStage C hC φ i (a • x) =
          a • zcCompletedGroupAlgebraMapStage C hC φ i x :=
      zcCompletedGroupAlgebraMapStage_smul C hC φ i a x
    have hcalc :
        a • x - zcCompletedGroupAlgebraMapStageTargetSection C hC φ hφ i
            (zcCompletedGroupAlgebraMapStage C hC φ i (a • x)) =
          a • (x - zcCompletedGroupAlgebraMapStageTargetSection C hC φ hφ i
            (zcCompletedGroupAlgebraMapStage C hC φ i x)) := by
      rw [hmap_smul, map_smul, smul_sub]
    rw [hcalc]
    rw [Algebra.smul_def]
    exact
      (zcCompletedGroupAlgebraMapStageRelationAugmentationIdeal C hC φ i).mul_mem_left _ hx

/--
In each finite stage, the kernel of a surjective target map is exactly the relation augmentation
ideal generated by the kernel of the finite quotient map.
-/
theorem zcCompletedGAMapStageKernelIdeal_eq_relationAugmentationIdeal_of_surj
    (φ : H →ₜ* K) (hφ : Function.Surjective φ)
    (i : ZCCompletedGroupAlgebraIndex C K) :
    zcCompletedGroupAlgebraMapStageKernelIdeal C hC φ i =
      zcCompletedGroupAlgebraMapStageRelationAugmentationIdeal C hC φ i := by
  apply le_antisymm
  · intro x hx
    have hxmap :
        zcCompletedGroupAlgebraMapStage C hC φ i x = 0 :=
      (mem_zcCompletedGroupAlgebraMapStageKernelIdeal_iff
        (C := C) (hC := hC) (φ := φ) (i := i)).1 hx
    have hdiff :=
      zcCompletedGAMapStage_sub_targetSection_map_mem_relationAugmentationIdeal
        C hC φ hφ i x
    rw [hxmap, map_zero, sub_zero] at hdiff
    exact hdiff
  · exact zcCompletedGroupAlgebraMapStageRelationAugmentationIdeal_le_kernelIdeal C hC φ i

/-- Target finite-stage maps commute with the pro-\(C\) transition maps. -/
theorem zcCompletedGroupAlgebraMapStage_compatible
    (φ : H →ₜ* K)
    {i j : ZCCompletedGroupAlgebraIndex C K} (hij : i ≤ j) :
    (zcCompletedGroupAlgebraTransition C K hij).comp
        (zcCompletedGroupAlgebraMapStage C hC φ j) =
      (zcCompletedGroupAlgebraMapStage C hC φ i).comp
        (zcCompletedGroupAlgebraTransition C H
          (show
            (i.1, completedGroupAlgebraComapIndexInClass
                (G := H) (H := K) C hC φ i.2) ≤
              (j.1, completedGroupAlgebraComapIndexInClass
                (G := H) (H := K) C hC φ j.2) from
            ⟨hij.1,
              completedGroupAlgebraComapIndexInClass_mono
                (G := H) (H := K) C hC φ hij.2⟩)) := by
  let : Fact (0 < i.1.modulus) := ⟨i.1.positive⟩
  let : Fact (0 < j.1.modulus) := ⟨j.1.positive⟩
  apply RingHom.ext
  intro x
  refine MonoidAlgebra.induction_on
    (motive := fun x =>
      ((zcCompletedGroupAlgebraTransition C K hij).comp
          (zcCompletedGroupAlgebraMapStage C hC φ j)) x =
        ((zcCompletedGroupAlgebraMapStage C hC φ i).comp
          (zcCompletedGroupAlgebraTransition C H
            (show
              (i.1, completedGroupAlgebraComapIndexInClass
                  (G := H) (H := K) C hC φ i.2) ≤
                (j.1, completedGroupAlgebraComapIndexInClass
                  (G := H) (H := K) C hC φ j.2) from
              ⟨hij.1,
                completedGroupAlgebraComapIndexInClass_mono
                  (G := H) (H := K) C hC φ hij.2⟩))) x)
    x ?_ ?_ ?_
  · intro q
    rw [RingHom.comp_apply, RingHom.comp_apply,
      zcCompletedGroupAlgebraMapStage_of, zcCompletedGroupAlgebraTransition_of,
      zcCompletedGroupAlgebraTransition_of]
    change
      MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus)
          (CompletedGroupAlgebraQuotientInClass K C i.2)
          ((OpenNormalSubgroupInClass.map
            (C := C) (G := K)
            (U := OrderDual.ofDual i.2) (V := OrderDual.ofDual j.2) hij.2)
            (completedGroupAlgebraComapQuotientMapInClass
              (G := H) (H := K) C hC φ j.2 q)) =
        zcCompletedGroupAlgebraMapStage C hC φ i
          (MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus)
            (CompletedGroupAlgebraQuotientInClass H C
              (completedGroupAlgebraComapIndexInClass (G := H) (H := K) C hC φ i.2))
            ((OpenNormalSubgroupInClass.map
              (C := C) (G := H)
              (U := OrderDual.ofDual
                (completedGroupAlgebraComapIndexInClass (G := H) (H := K) C hC φ i.2))
              (V := OrderDual.ofDual
                (completedGroupAlgebraComapIndexInClass (G := H) (H := K) C hC φ j.2))
              (completedGroupAlgebraComapIndexInClass_mono
                (G := H) (H := K) C hC φ hij.2)) q))
    erw [zcCompletedGroupAlgebraMapStage_of]
    exact congrArg (MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus)
      (CompletedGroupAlgebraQuotientInClass K C i.2))
      (congrFun
        (congrArg DFunLike.coe
          (completedGroupAlgebraComapQuotientMapInClass_compatible
            (G := H) (H := K) C hC φ hij.2)) q)
  · intro x y hx hy
    rw [map_add, map_add, hx, hy]
  · intro a x hx
    rcases ZMod.intCast_surjective a with ⟨t, rfl⟩
    rw [Algebra.smul_def, RingHom.map_mul, RingHom.map_mul, hx]
    simp only [zcCompletedGroupAlgebraTransition, modNCompletedGroupAlgebraStageCoeffMapInClass,
  modNCompletedGroupRingCoeffMap, AlgHom.toRingHom_eq_coe, zcCompletedGroupAlgebraMapStage,
      map_intCast,
  RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, MonoidAlgebra.mapDomainRingHom_apply]

/--
The completed group-algebra map \(\mathbb{Z}_C\llbracket H\rrbracket\) \(\to\)
\(\mathbb{Z}_C\llbracket K\rrbracket\) induced by a continuous homomorphism \(H \to K\).
-/
def zcCompletedGroupAlgebraMap (φ : H →ₜ* K) :
    ZCCompletedGroupAlgebra C H →+* ZCCompletedGroupAlgebra C K where
  toFun x := ⟨fun i =>
      zcCompletedGroupAlgebraMapStage C hC φ i
        (zcCompletedGroupAlgebraProjection C H
          (i.1, completedGroupAlgebraComapIndexInClass
            (G := H) (H := K) C hC φ i.2) x), by
    intro i j hij
    let hsource :
        (i.1, completedGroupAlgebraComapIndexInClass (G := H) (H := K) C hC φ i.2) ≤
          (j.1, completedGroupAlgebraComapIndexInClass (G := H) (H := K) C hC φ j.2) :=
      ⟨hij.1, completedGroupAlgebraComapIndexInClass_mono
        (G := H) (H := K) C hC φ hij.2⟩
    have hx := x.2
      (i.1, completedGroupAlgebraComapIndexInClass (G := H) (H := K) C hC φ i.2)
      (j.1, completedGroupAlgebraComapIndexInClass (G := H) (H := K) C hC φ j.2)
      hsource
    have hcompat := congrFun
      (congrArg DFunLike.coe
        (zcCompletedGroupAlgebraMapStage_compatible C hC φ hij))
      (zcCompletedGroupAlgebraProjection C H
        (j.1, completedGroupAlgebraComapIndexInClass (G := H) (H := K) C hC φ j.2) x)
    rw [RingHom.comp_apply, RingHom.comp_apply] at hcompat
    rw [hx] at hcompat
    simpa using hcompat⟩
  map_zero' := by
    apply Subtype.ext
    funext i
    simp only [zcCompletedGroupAlgebraMapStage, zcCompletedGroupAlgebraProjection_zero,
      MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_zero]
  map_add' := by
    intro x y
    apply Subtype.ext
    funext i
    simp only [zcCompletedGroupAlgebraProjection_add, map_add]
  map_one' := by
    apply Subtype.ext
    funext i
    simp only [zcCompletedGroupAlgebraMapStage, zcCompletedGroupAlgebraProjection_one,
  MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_one]
  map_mul' := by
    intro x y
    apply Subtype.ext
    funext i
    simp only [zcCompletedGroupAlgebraProjection_mul, map_mul]

/--
The \(\mathbb{Z}_C\)-completed group-algebra projection is computed by the corresponding
finite-stage coordinate map.
-/
@[simp]
theorem zcCompletedGroupAlgebraProjection_map
    (φ : H →ₜ* K) (i : ZCCompletedGroupAlgebraIndex C K)
    (x : ZCCompletedGroupAlgebra C H) :
    zcCompletedGroupAlgebraProjection C K i (zcCompletedGroupAlgebraMap C hC φ x) =
      zcCompletedGroupAlgebraMapStage C hC φ i
        (zcCompletedGroupAlgebraProjection C H
          (i.1, completedGroupAlgebraComapIndexInClass
            (G := H) (H := K) C hC φ i.2) x) :=
  rfl

/--
Membership in the kernel of the completed target map is exactly membership in the kernel of
every target-indexed finite stage.
-/
theorem mem_zcCompletedGroupAlgebraMap_ker_iff_stageKernelIdeal
    {C : ProCGroups.FiniteGroupClass.{u}} {hC : C.Hereditary}
    {φ : H →ₜ* K} {x : ZCCompletedGroupAlgebra C H} :
    x ∈ RingHom.ker (zcCompletedGroupAlgebraMap C hC φ) ↔
      ∀ i : ZCCompletedGroupAlgebraIndex C K,
        zcCompletedGroupAlgebraProjection C H
            (i.1, completedGroupAlgebraComapIndexInClass
              (G := H) (H := K) C hC φ i.2) x ∈
          zcCompletedGroupAlgebraMapStageKernelIdeal C hC φ i := by
  constructor
  · intro hx i
    rw [mem_zcCompletedGroupAlgebraMapStageKernelIdeal_iff]
    have hmap : zcCompletedGroupAlgebraMap C hC φ x = 0 :=
      (RingHom.mem_ker).1 hx
    have hi := congrArg (zcCompletedGroupAlgebraProjection C K i) hmap
    simpa [zcCompletedGroupAlgebraProjection_map] using hi
  · intro hstage
    rw [RingHom.mem_ker]
    apply Subtype.ext
    funext i
    change zcCompletedGroupAlgebraProjection C K i (zcCompletedGroupAlgebraMap C hC φ x) =
      zcCompletedGroupAlgebraProjection C K i (0 : ZCCompletedGroupAlgebra C K)
    rw [zcCompletedGroupAlgebraProjection_map]
    have hi :
        zcCompletedGroupAlgebraMapStage C hC φ i
          (zcCompletedGroupAlgebraProjection C H
            (i.1, completedGroupAlgebraComapIndexInClass
              (G := H) (H := K) C hC φ i.2) x) = 0 :=
      (mem_zcCompletedGroupAlgebraMapStageKernelIdeal_iff
        (C := C) (hC := hC) (φ := φ) (i := i)).1 (hstage i)
    simpa using hi

/--
For a surjective target map, membership in the completed kernel is equivalently membership in
the explicit relation-augmentation ideal at every target-indexed finite stage.
-/
theorem mem_zcCompletedGAMap_ker_iff_stageRelationAugmentationIdeal_of_surj
    {C : ProCGroups.FiniteGroupClass.{u}} {hC : C.Hereditary}
    {φ : H →ₜ* K} (hφ : Function.Surjective φ)
    {x : ZCCompletedGroupAlgebra C H} :
    x ∈ RingHom.ker (zcCompletedGroupAlgebraMap C hC φ) ↔
      ∀ i : ZCCompletedGroupAlgebraIndex C K,
        zcCompletedGroupAlgebraProjection C H
            (i.1, completedGroupAlgebraComapIndexInClass
              (G := H) (H := K) C hC φ i.2) x ∈
          zcCompletedGroupAlgebraMapStageRelationAugmentationIdeal C hC φ i := by
  constructor
  · intro hx i
    have hi := (mem_zcCompletedGroupAlgebraMap_ker_iff_stageKernelIdeal
      (C := C) (hC := hC) (φ := φ) (x := x)).1 hx i
    rwa [zcCompletedGAMapStageKernelIdeal_eq_relationAugmentationIdeal_of_surj
      C hC φ hφ i] at hi
  · intro hstage
    exact (mem_zcCompletedGroupAlgebraMap_ker_iff_stageKernelIdeal
      (C := C) (hC := hC) (φ := φ) (x := x)).2
      (fun i => by
        rw [zcCompletedGAMapStageKernelIdeal_eq_relationAugmentationIdeal_of_surj
          C hC φ hφ i]
        exact hstage i)

/--
The completed target map sends a group-like element to the group-like element represented by its
image under the target homomorphism.
-/
@[simp]
theorem zcCompletedGroupAlgebraMap_groupLike
    (φ : H →ₜ* K) (h : H) :
    zcCompletedGroupAlgebraMap C hC φ (zcGroupLike C H h) =
      zcGroupLike C K (φ h) := by
  apply Subtype.ext
  funext i
  change
    zcCompletedGroupAlgebraProjection C K i
        (zcCompletedGroupAlgebraMap C hC φ (zcGroupLike C H h)) =
      zcCompletedGroupAlgebraProjection C K i (zcGroupLike C K (φ h))
  rw [zcCompletedGroupAlgebraProjection_map,
    zcCompletedGroupAlgebraProjection_groupLike,
    zcCompletedGroupAlgebraProjection_groupLike]
  erw [zcCompletedGroupAlgebraMapStage_of]
  exact congrArg
    (MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus)
      (CompletedGroupAlgebraQuotientInClass K C i.2))
    (completedGroupAlgebraComapQuotientMapInClass_mk
      (G := H) (H := K) C hC φ i.2 h)

/-- The completed target map is linear over the induced map on coefficient group algebras. -/
@[simp]
theorem zcCompletedGroupAlgebraMap_scalar
    {G : Type v} [Group G] (φ : H →ₜ* K) (ψ : G →* H) (g : G) :
    zcCompletedGroupAlgebraMap C hC φ (zcCompletedGroupAlgebraScalar C ψ g) =
      zcCompletedGroupAlgebraScalar C (φ.toMonoidHom.comp ψ) g := by
  simp only [zcCompletedGroupAlgebraScalar, MonoidHom.coe_comp, Function.comp_apply,
  zcCompletedGroupAlgebraMap_groupLike, ContinuousMonoidHom.coe_toMonoidHom, MonoidHom.coe_coe]

/-- The completed target map is compatible with the corresponding boundary map. -/
@[simp]
theorem zcCompletedGroupAlgebraMap_boundary
    {G : Type v} [Group G] (φ : H →ₜ* K) (ψ : G →* H) (g : G) :
    zcCompletedGroupAlgebraMap C hC φ (zcCompletedGroupAlgebraBoundary C ψ g) =
      zcCompletedGroupAlgebraBoundary C (φ.toMonoidHom.comp ψ) g := by
  change zcCompletedGroupAlgebraMap C hC φ (zcGroupLike C H (ψ g) - 1) =
    zcGroupLike C K (φ (ψ g)) - 1
  simp only [map_sub, zcCompletedGroupAlgebraMap_groupLike, map_one]

/-- A finite-stage target map preserves the finite augmentation. -/
theorem zcCompletedGroupAlgebraMapStage_augmentation
    (φ : H →ₜ* K) (i : ZCCompletedGroupAlgebraIndex C K) :
    (modNCompletedGroupAlgebraStageAugmentationInClass i.1.modulus K C i.2).comp
        (zcCompletedGroupAlgebraMapStage C hC φ i) =
      modNCompletedGroupAlgebraStageAugmentationInClass i.1.modulus H C
        (completedGroupAlgebraComapIndexInClass (G := H) (H := K) C hC φ i.2) := by
  let : Fact (0 < i.1.modulus) := ⟨i.1.positive⟩
  apply MonoidAlgebra.ringHom_ext
  · intro a
    rw [RingHom.comp_apply, zcCompletedGroupAlgebraMapStage_single,
      modNCompletedGroupAlgebraStageAugmentationInClass_single,
      modNCompletedGroupAlgebraStageAugmentationInClass_single]
  · intro q
    rw [RingHom.comp_apply, zcCompletedGroupAlgebraMapStage_single,
      modNCompletedGroupAlgebraStageAugmentationInClass_single,
      modNCompletedGroupAlgebraStageAugmentationInClass_single]

/-- Completed augmentation is natural for target maps. -/
@[simp 900]
theorem zcCompletedGroupAlgebraAugmentation_map
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (φ : H →ₜ* K) (x : ZCCompletedGroupAlgebra C H) :
    zcCompletedGroupAlgebraAugmentation C K (zcCompletedGroupAlgebraMap C hC φ x) =
      zcCompletedGroupAlgebraAugmentation C H x := by
  ext i
  change zcCompletedGroupAlgebraAugmentationFamily C K
      (zcCompletedGroupAlgebraMap C hC φ x) i =
    zcCompletedGroupAlgebraAugmentationFamily C H x i
  let U : CompletedGroupAlgebraIndexInClass K C := zcCompletedGroupAlgebraTopIndex C K
  let V : CompletedGroupAlgebraIndexInClass H C := zcCompletedGroupAlgebraTopIndex C H
  have hV :
      completedGroupAlgebraComapIndexInClass (G := H) (H := K) C hC φ U = V := by
    simp only [zcCompletedGroupAlgebraTopIndex, completedGroupAlgebraComapIndexInClass_top, U, V]
  dsimp [zcCompletedGroupAlgebraAugmentationFamily]
  change
    (modNCompletedGroupAlgebraStageAugmentationInClass i.modulus K C U)
        (zcCompletedGroupAlgebraProjection C K (i, U)
          (zcCompletedGroupAlgebraMap C hC φ x)) =
      (modNCompletedGroupAlgebraStageAugmentationInClass i.modulus H C V)
        (zcCompletedGroupAlgebraProjection C H (i, V) x)
  rw [zcCompletedGroupAlgebraProjection_map]
  cases hV
  let y := zcCompletedGroupAlgebraProjection C H
    (i, completedGroupAlgebraComapIndexInClass (G := H) (H := K) C hC φ U) x
  change
    (modNCompletedGroupAlgebraStageAugmentationInClass i.modulus K C U)
        (zcCompletedGroupAlgebraMapStage C hC φ (i, U) y) =
      (modNCompletedGroupAlgebraStageAugmentationInClass i.modulus H C
        (completedGroupAlgebraComapIndexInClass (G := H) (H := K) C hC φ U)) y
  exact congrFun
    (congrArg DFunLike.coe
      (zcCompletedGroupAlgebraMapStage_augmentation C hC φ (i, U))) y

/--
The target map on completed \(\mathbb{Z}_C\) group algebras induced by the identity homomorphism
is the identity ring homomorphism.
-/
@[simp 900]
theorem zcCompletedGroupAlgebraMap_id :
    zcCompletedGroupAlgebraMap C hC (ContinuousMonoidHom.id H) =
      RingHom.id (ZCCompletedGroupAlgebra C H) := by
  apply RingHom.ext
  intro x
  apply Subtype.ext
  funext i
  change zcCompletedGroupAlgebraProjection C H i
      (zcCompletedGroupAlgebraMap C hC (ContinuousMonoidHom.id H) x) =
    zcCompletedGroupAlgebraProjection C H i x
  rw [zcCompletedGroupAlgebraProjection_map]
  have hfull :
      (i.1, completedGroupAlgebraComapIndexInClass (G := H) (H := H) C hC
          (ContinuousMonoidHom.id H) i.2) = i := by
    cases i
    simp only [completedGroupAlgebraComapIndexInClass_id]
  cases hfull
  change zcCompletedGroupAlgebraMapStage C hC (ContinuousMonoidHom.id H) i (x.1 i) =
    x.1 i
  refine MonoidAlgebra.induction_on
    (motive := fun y => zcCompletedGroupAlgebraMapStage C hC (ContinuousMonoidHom.id H) i y = y)
    (x.1 i) ?_ ?_ ?_
  · intro q
    rcases QuotientGroup.mk'_surjective
        ((((OrderDual.ofDual i.2).1 : OpenNormalSubgroup H) : Subgroup H)) q with
      ⟨g, rfl⟩
    erw [zcCompletedGroupAlgebraMapStage_of]
    rfl
  · intro a b ha hb
    rw [map_add, ha, hb]
    rfl
  · intro a y hy
    rcases ZMod.intCast_surjective a with ⟨t, rfl⟩
    rw [Algebra.smul_def, RingHom.map_mul, hy]
    simp only [zcCompletedGroupAlgebraMapStage, map_intCast]
    rfl

/-- Target maps on completed \(\mathbb{Z}_C\) group algebras compose functorially. -/
@[simp 900]
theorem zcCompletedGroupAlgebraMap_comp
    {L : Type u} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
    (φ : H →ₜ* K) (ψ : K →ₜ* L) :
    zcCompletedGroupAlgebraMap C hC (ψ.comp φ) =
      (zcCompletedGroupAlgebraMap C hC ψ).comp
        (zcCompletedGroupAlgebraMap C hC φ) := by
  apply RingHom.ext
  intro x
  apply Subtype.ext
  funext i
  change zcCompletedGroupAlgebraProjection C L i
      (zcCompletedGroupAlgebraMap C hC (ψ.comp φ) x) =
    zcCompletedGroupAlgebraProjection C L i
      (zcCompletedGroupAlgebraMap C hC ψ (zcCompletedGroupAlgebraMap C hC φ x))
  rw [zcCompletedGroupAlgebraProjection_map]
  rw [zcCompletedGroupAlgebraProjection_map]
  let j : ZCCompletedGroupAlgebraIndex C K :=
    (i.1, completedGroupAlgebraComapIndexInClass (G := K) (H := L) C hC ψ i.2)
  change zcCompletedGroupAlgebraMapStage C hC (ψ.comp φ) i
      (zcCompletedGroupAlgebraProjection C H
        (i.1, completedGroupAlgebraComapIndexInClass
          (G := H) (H := L) C hC (ψ.comp φ) i.2) x) =
    zcCompletedGroupAlgebraMapStage C hC ψ i
      (zcCompletedGroupAlgebraProjection C K j
        (zcCompletedGroupAlgebraMap C hC φ x))
  rw [zcCompletedGroupAlgebraProjection_map]
  have hidx :
      (i.1, completedGroupAlgebraComapIndexInClass
          (G := H) (H := L) C hC (ψ.comp φ) i.2) =
        (j.1, completedGroupAlgebraComapIndexInClass
          (G := H) (H := K) C hC φ j.2) := by
    subst j
    simp only [completedGroupAlgebraComapIndexInClass_comp]
  cases hidx
  have hstage :
      zcCompletedGroupAlgebraMapStage C hC (ψ.comp φ) i =
        (zcCompletedGroupAlgebraMapStage C hC ψ i).comp
          (zcCompletedGroupAlgebraMapStage C hC φ j) := by
    unfold zcCompletedGroupAlgebraMapStage
    rw [← MonoidAlgebra.mapDomainRingHom_comp]
    congr 1
    ext q
    refine QuotientGroup.induction_on q ?_
    intro g
    rfl
  exact congrFun (congrArg DFunLike.coe hstage)
    (zcCompletedGroupAlgebraProjection C H
      (j.1, completedGroupAlgebraComapIndexInClass
        (G := H) (H := K) C hC φ j.2) x)

end CompletedGroupAlgebraMap

section UniversalTarget

variable (C : ProCGroups.FiniteGroupClass.{v})
variable (hC : ProCGroups.FiniteGroupClass.Hereditary C)
variable {G : Type u} [Group G]
variable {H K : Type v}
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable [Group K] [TopologicalSpace K] [IsTopologicalGroup K]

/-- The target-pushed universal differential, bundled for the source
completed group-algebra scalar action. -/
def zcUniversalDifferentialTargetCrossedHom
    (ψ : G →* H) (φ : H →ₜ* K) :
    letI : Module (ZCCompletedGroupAlgebra C H)
        (ZCCompletedDifferentialModule C (φ.toMonoidHom.comp ψ)) :=
      Module.compHom _ (zcCompletedGroupAlgebraMap C hC φ)
    ScalarCrossedHom (zcCompletedGroupAlgebraScalar C ψ)
      (ZCCompletedDifferentialModule C (φ.toMonoidHom.comp ψ)) := by
  letI : Module (ZCCompletedGroupAlgebra C H)
      (ZCCompletedDifferentialModule C (φ.toMonoidHom.comp ψ)) :=
    Module.compHom _ (zcCompletedGroupAlgebraMap C hC φ)
  exact
    { toFun := fun g => zcUniversalDifferential C (φ.toMonoidHom.comp ψ) g
      map_mul' := by
        intro g h
        change zcUniversalDifferential C (φ.toMonoidHom.comp ψ) (g * h) =
          zcUniversalDifferential C (φ.toMonoidHom.comp ψ) g +
            zcCompletedGroupAlgebraScalar C ψ g •
              zcUniversalDifferential C (φ.toMonoidHom.comp ψ) h
        rw [ScalarCrossedHom.map_mul
          (zcUniversalDifferential C (φ.toMonoidHom.comp ψ)) g h]
        change zcUniversalDifferential C (φ.toMonoidHom.comp ψ) g +
            zcCompletedGroupAlgebraScalar C (φ.toMonoidHom.comp ψ) g •
              zcUniversalDifferential C (φ.toMonoidHom.comp ψ) h =
          zcUniversalDifferential C (φ.toMonoidHom.comp ψ) g +
            zcCompletedGroupAlgebraMap C hC φ
                (zcCompletedGroupAlgebraScalar C ψ g) •
              zcUniversalDifferential C (φ.toMonoidHom.comp ψ) h
        rw [zcCompletedGroupAlgebraMap_scalar] }

/--
Target functoriality for the completed universal differential module. The codomain is regarded
as a \(\mathbb{Z}_C\llbracket H\rrbracket\)-module by restriction of scalars along the completed
group-algebra map induced by \(\varphi : H \to K\), and the universal differential
\(d_{\psi}(g)\) is sent to \(d_{\varphi\circ\psi}(g)\).
-/
def zcCompletedDifferentialModuleTargetMap
    (ψ : G →* H) (φ : H →ₜ* K) :
    letI : Module (ZCCompletedGroupAlgebra C H)
        (ZCCompletedDifferentialModule C (φ.toMonoidHom.comp ψ)) :=
      Module.compHom _ (zcCompletedGroupAlgebraMap C hC φ)
    ZCCompletedDifferentialModule C ψ →ₗ[ZCCompletedGroupAlgebra C H]
      ZCCompletedDifferentialModule C (φ.toMonoidHom.comp ψ) := by
  letI : Module (ZCCompletedGroupAlgebra C H)
      (ZCCompletedDifferentialModule C (φ.toMonoidHom.comp ψ)) :=
    Module.compHom _ (zcCompletedGroupAlgebraMap C hC φ)
  exact
    crossedHomModuleLift
      (A := ZCCompletedDifferentialModule C (φ.toMonoidHom.comp ψ))
      (zcCompletedGroupAlgebraScalar C ψ)
      (zcUniversalDifferentialTargetCrossedHom C hC ψ φ)

/--
The universal target map on the completed differential module is determined by the target
homomorphism at finite stages.
-/
@[simp 900]
theorem zcCompletedDifferentialModuleTargetMap_universal
    (ψ : G →* H) (φ : H →ₜ* K) (g : G) :
    letI : Module (ZCCompletedGroupAlgebra C H)
        (ZCCompletedDifferentialModule C (φ.toMonoidHom.comp ψ)) :=
      Module.compHom _ (zcCompletedGroupAlgebraMap C hC φ)
    zcCompletedDifferentialModuleTargetMap C hC ψ φ
        (zcUniversalDifferential C ψ g) =
      zcUniversalDifferential C (φ.toMonoidHom.comp ψ) g := by
  let : Module (ZCCompletedGroupAlgebra C H)
      (ZCCompletedDifferentialModule C (φ.toMonoidHom.comp ψ)) :=
    Module.compHom _ (zcCompletedGroupAlgebraMap C hC φ)
  exact
    crossedHomModuleLift_universal
      (A := ZCCompletedDifferentialModule C (φ.toMonoidHom.comp ψ))
      (zcCompletedGroupAlgebraScalar C ψ)
      (zcUniversalDifferentialTargetCrossedHom C hC ψ φ) g

include hC

/-- Completed universal zero descends along a target homomorphism. -/
theorem zcUniversalDifferential_eq_zero_of_target
    (ψ : G →* H) (φ : H →ₜ* K) {g : G}
    (hg : zcUniversalDifferential C ψ g = 0) :
    zcUniversalDifferential C (φ.toMonoidHom.comp ψ) g = 0 := by
  let : Module (ZCCompletedGroupAlgebra C H)
      (ZCCompletedDifferentialModule C (φ.toMonoidHom.comp ψ)) :=
    Module.compHom _ (zcCompletedGroupAlgebraMap C hC φ)
  rw [← zcCompletedDifferentialModuleTargetMap_universal C hC ψ φ g, hg, map_zero]

variable {G' : Type u} [Group G']

/--
Vanishing of the completed universal differential descends along a commuting source-target
square: the relation \(\psi'\circ f = \varphi\circ\psi\) carries \(d_{\psi}(g)=0\) to
\(d_{\psi'}(f(g))=0\).
-/
theorem zcUniversalDifferential_eq_zero_of_source_target
    (ψ : G →* H) (ψ' : G' →* K) (f : G →* G') (φ : H →ₜ* K)
    (hcomm : ψ'.comp f = φ.toMonoidHom.comp ψ) {g : G}
    (hg : zcUniversalDifferential C ψ g = 0) :
    zcUniversalDifferential C ψ' (f g) = 0 := by
  have ht :
      zcUniversalDifferential C (φ.toMonoidHom.comp ψ) g = 0 :=
    zcUniversalDifferential_eq_zero_of_target C hC ψ φ hg
  have hs :
      zcUniversalDifferential C (ψ'.comp f) g = 0 := by
    rw [hcomm]
    exact ht
  exact zcUniversalDifferential_eq_zero_of_source C ψ' f hs

end UniversalTarget

section FreeGroup

variable (C : ProCGroups.FiniteGroupClass.{v})
variable (hC : ProCGroups.FiniteGroupClass.Hereditary C)
variable {X : Type u} [DecidableEq X]
variable {H K : Type v}
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable [Group K] [TopologicalSpace K] [IsTopologicalGroup K]

/-- A continuous homomorphism of target groups pushes completed Fox-coordinate vectors forward. -/
def zcFreeFoxCoordinatesMap (φ : H →ₜ* K) :
    ZCFreeFoxCoordinates C (X := X) (H := H) →
      ZCFreeFoxCoordinates C (X := X) (H := K) :=
  fun a x => zcCompletedGroupAlgebraMap C hC φ (a x)

omit [DecidableEq X] in
/--
The target push-forward map on completed free Fox-coordinate vectors is computed coordinatewise
by the completed group-algebra map.
-/
@[simp]
theorem zcFreeFoxCoordinatesMap_apply
    (φ : H →ₜ* K) (a : ZCFreeFoxCoordinates C (X := X) (H := H)) (x : X) :
    zcFreeFoxCoordinatesMap (X := X) C hC φ a x =
      zcCompletedGroupAlgebraMap C hC φ (a x) :=
  rfl

omit [DecidableEq X] in
/-- The coordinatewise target map induced by the identity homomorphism is the identity map. -/
@[simp]
theorem zcFreeFoxCoordinatesMap_id
    (a : ZCFreeFoxCoordinates C (X := X) (H := H)) :
    zcFreeFoxCoordinatesMap (X := X) C hC (ContinuousMonoidHom.id H) a = a := by
  funext x
  simp only [zcFreeFoxCoordinatesMap, zcCompletedGroupAlgebraMap_id, RingHom.id_apply]

omit [DecidableEq X] in
/-- Coordinatewise target maps on completed Fox-coordinate vectors compose functorially. -/
@[simp]
theorem zcFreeFoxCoordinatesMap_comp
    {L : Type v} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
    (φ : H →ₜ* K) (ψ : K →ₜ* L)
    (a : ZCFreeFoxCoordinates C (X := X) (H := H)) :
    zcFreeFoxCoordinatesMap (X := X) C hC (ψ.comp φ) a =
      zcFreeFoxCoordinatesMap (X := X) C hC ψ
        (zcFreeFoxCoordinatesMap (X := X) C hC φ a) := by
  funext x
  simp only [zcFreeFoxCoordinatesMap, zcCompletedGroupAlgebraMap_comp, RingHom.coe_comp,
      Function.comp_apply]

/-- Completed free-group Fox derivatives are natural under target pushforward. -/
theorem zcFreeGroupFoxDerivativeVector_mapTarget
    (ψ : FreeGroup X →* H) (φ : H →ₜ* K) (w : FreeGroup X) :
    zcFreeGroupFoxDerivativeVector C (φ.toMonoidHom.comp ψ) w =
      zcFreeFoxCoordinatesMap (X := X) C hC φ (zcFreeGroupFoxDerivativeVector C ψ w) := by
  let delta : ScalarCrossedHom
      (zcCompletedGroupAlgebraScalar C (φ.toMonoidHom.comp ψ))
      (ZCFreeFoxCoordinates C (X := X) (H := K)) :=
    { toFun := fun w =>
        zcFreeFoxCoordinatesMap (X := X) C hC φ
          (zcFreeGroupFoxDerivativeVector C ψ w)
      map_mul' := by
        intro u v
        funext x
        simp only [scalarCrossedAction_apply, zcFreeFoxCoordinatesMap_apply,
          ScalarCrossedHom.map_mul,
          zcCompletedGroupAlgebraScalar_apply, Pi.add_apply, Pi.smul_apply,
          smul_eq_mul, map_add, map_mul, zcCompletedGroupAlgebraMap_groupLike,
          ContinuousMonoidHom.coe_toMonoidHom, MonoidHom.coe_comp,
          MonoidHom.coe_coe, Function.comp_apply] }
  have hbasis :
      ∀ x : X, delta (FreeGroup.of x) = Pi.single x (1 : ZCCompletedGroupAlgebra C K) := by
    intro x
    change zcFreeFoxCoordinatesMap (X := X) C hC φ
        (zcFreeGroupFoxDerivativeVector C ψ (FreeGroup.of x)) =
      Pi.single x (1 : ZCCompletedGroupAlgebra C K)
    funext y
    by_cases hxy : x = y
    · subst y
      simp only [zcFreeFoxCoordinatesMap_apply, zcFreeGroupFoxDerivativeVector_of,
          Pi.single_eq_same, map_one,
  ]
    · simp only [zcFreeFoxCoordinatesMap_apply, zcFreeGroupFoxDerivativeVector_of, ne_eq, hxy,
        not_false_eq_true,
  Pi.single_eq_of_ne', map_zero]
  have hdelta_eq :
      delta = zcFreeGroupFoxDerivativeVector C (φ.toMonoidHom.comp ψ) :=
    zcFreeGroupFoxDerivativeVector_unique C (φ.toMonoidHom.comp ψ) delta hbasis
  exact congrArg
    (fun d : ScalarCrossedHom
      (zcCompletedGroupAlgebraScalar C (φ.toMonoidHom.comp ψ))
      (ZCFreeFoxCoordinates C (X := X) (H := K)) => d w)
    hdelta_eq.symm

/--
Changing the target group maps each completed Fox derivative through the completed group-algebra
map.
-/
theorem zcFreeGroupFoxDerivative_mapTarget
    (ψ : FreeGroup X →* H) (φ : H →ₜ* K) (w : FreeGroup X) (x : X) :
    zcFreeGroupFoxDerivative C (φ.toMonoidHom.comp ψ) x w =
      zcCompletedGroupAlgebraMap C hC φ (zcFreeGroupFoxDerivative C ψ x w) := by
  have h := congrFun (zcFreeGroupFoxDerivativeVector_mapTarget C hC ψ φ w) x
  change
    zcFreeGroupFoxDerivativeVector C (φ.toMonoidHom.comp ψ) w x =
      zcCompletedGroupAlgebraMap C hC φ
        (zcFreeGroupFoxDerivativeVector C ψ w x)
  exact h

section FiniteBasis

variable [Fintype X]

omit [DecidableEq X] in
/-- The completed Fox boundary is natural under target maps. -/
theorem zcFreeGroupFoxBoundary_mapTarget
    (ψ : FreeGroup X →* H) (φ : H →ₜ* K)
    (v : ZCFreeFoxCoordinates C (X := X) (H := H)) :
    zcCompletedGroupAlgebraMap C hC φ (zcFreeGroupFoxBoundary C ψ v) =
      zcFreeGroupFoxBoundary C (φ.toMonoidHom.comp ψ)
        (zcFreeFoxCoordinatesMap (X := X) C hC φ v) := by
  simp only [zcFreeGroupFoxBoundary_apply, map_sum, map_mul, map_sub,
      zcCompletedGroupAlgebraMap_groupLike,
  map_one, ContinuousMonoidHom.coe_toMonoidHom, zcFreeFoxCoordinatesMap, MonoidHom.coe_comp,
      MonoidHom.coe_coe,
  Function.comp_apply]

/--
Target naturality carries the boundary of the completed Fox derivative vector to the boundary of
the mapped derivative vector.
-/
theorem zcFreeGroupFoxBoundary_derivativeVector_mapTarget
    (ψ : FreeGroup X →* H) (φ : H →ₜ* K) (w : FreeGroup X) :
    zcCompletedGroupAlgebraMap C hC φ
        (zcFreeGroupFoxBoundary C ψ (zcFreeGroupFoxDerivativeVector C ψ w)) =
      zcFreeGroupFoxBoundary C (φ.toMonoidHom.comp ψ)
        (zcFreeGroupFoxDerivativeVector C (φ.toMonoidHom.comp ψ) w) := by
  rw [zcFreeGroupFoxBoundary_mapTarget, ← zcFreeGroupFoxDerivativeVector_mapTarget]

/--
The target-mapped completed Euler formula expresses the mapped boundary as the sum of mapped Fox
derivatives times generator boundaries.
-/
theorem zcFreeGroupFoxDerivative_euler_formula_mapTarget
    (ψ : FreeGroup X →* H) (φ : H →ₜ* K) (w : FreeGroup X) :
    zcCompletedGroupAlgebraMap C hC φ (zcGroupLike C H (ψ w) - 1) =
      ∑ i : X,
        zcFreeGroupFoxDerivative C (φ.toMonoidHom.comp ψ) i w *
          (zcGroupLike C K ((φ.toMonoidHom.comp ψ) (FreeGroup.of i)) - 1) := by
  change
    zcCompletedGroupAlgebraMap C hC φ
        (zcCompletedGroupAlgebraBoundary C ψ w) = _
  rw [zcCompletedGroupAlgebraMap_boundary]
  exact zcFreeGroupFoxDerivative_fundamental_formula C (φ.toMonoidHom.comp ψ) w

end FiniteBasis

end FreeGroup

end

end FoxDifferential
