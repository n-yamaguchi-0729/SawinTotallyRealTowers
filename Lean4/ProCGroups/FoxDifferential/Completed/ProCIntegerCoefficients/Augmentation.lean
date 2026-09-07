import ProCGroups.FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraModN.InClass.Augmentation
import ProCGroups.FoxDifferential.Completed.ProCIntegerCoefficients.AugmentationIdeal.Basic
import Mathlib.Algebra.Exact.Basic
import Mathlib.RingTheory.Ideal.Maps

set_option autoImplicit false

/-!
# Fox differential: completed — \(\mathbb{Z}_C\) coefficients — augmentation

The principal declarations in this module are:

- `zcCompletedGroupAlgebraTopIndex`
  The canonical trivial group quotient used to read the completed augmentation.
- `zcCompletedGroupAlgebraAugmentationFamily`
  The finite coefficient coordinate of the completed augmentation \(\mathbb{Z}_C\llbracket
  H\rrbracket \to \mathbb{Z}_C\).
- `zcCompletedGroupAlgebraTopIndex_le`
  The canonical trivial quotient is below every finite quotient index.
- `zcCompletedGroupAlgebraAugmentationFamily_compatible`
  The finite coefficient coordinates of the completed augmentation are compatible.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.Completion
open ProCGroups.ProC

universe u

section Augmentation

variable (C : ProCGroups.FiniteGroupClass.{u})
variable [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
variable (H : Type u) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- The canonical trivial group quotient used to read the completed augmentation. -/
abbrev zcCompletedGroupAlgebraTopIndex : CompletedGroupAlgebraIndexInClass H C :=
  OrderDual.toDual (OpenNormalSubgroupInClass.top (C := C) (G := H))

omit [IsTopologicalGroup H] in
/-- The canonical trivial quotient is below every finite quotient index. -/
theorem zcCompletedGroupAlgebraTopIndex_le
    (U : CompletedGroupAlgebraIndexInClass H C) :
    zcCompletedGroupAlgebraTopIndex C H ≤ U := by
  change ((OrderDual.ofDual U).1 : Subgroup H) ≤ (⊤ : Subgroup H)
  exact le_top

/--
The finite coefficient coordinate of the completed augmentation \(\mathbb{Z}_C\llbracket
H\rrbracket \to \mathbb{Z}_C\).
-/
def zcCompletedGroupAlgebraAugmentationFamily
    (x : ZCCompletedGroupAlgebra C H) (i : ProCIntegerIndex C) :
    ProCIntegerStage C i := by
  letI : Fact (0 < i.modulus) := ⟨i.positive⟩
  exact
    modNCompletedGroupAlgebraStageAugmentationInClass i.modulus H C
      (zcCompletedGroupAlgebraTopIndex C H)
      (zcCompletedGroupAlgebraProjection C H
        (i, zcCompletedGroupAlgebraTopIndex C H) x)

/-- The finite coefficient coordinates of the completed augmentation are compatible. -/
theorem zcCompletedGroupAlgebraAugmentationFamily_compatible
    (x : ZCCompletedGroupAlgebra C H) {i j : ProCIntegerIndex C} (hij : i ≤ j) :
    proCIntegerTransition (C := C) hij
        (zcCompletedGroupAlgebraAugmentationFamily C H x j) =
      zcCompletedGroupAlgebraAugmentationFamily C H x i := by
  let : Fact (0 < i.modulus) := ⟨i.positive⟩
  let : Fact (0 < j.modulus) := ⟨j.positive⟩
  let U := zcCompletedGroupAlgebraTopIndex C H
  have hx := x.2 (i, U) (j, U) ⟨hij, le_rfl⟩
  dsimp [zcCompletedGroupAlgebraAugmentationFamily]
  change
    modNCompletedCoeffMap (n := i.modulus) (m := j.modulus) hij
        ((modNCompletedGroupAlgebraStageAugmentationInClass j.modulus H C U)
          (x.1 (j, U))) =
      (modNCompletedGroupAlgebraStageAugmentationInClass i.modulus H C U)
        (x.1 (i, U))
  rw [← hx]
  simp only [zcCompletedGroupAlgebraTransition, RingHom.comp_apply,
    modNCompletedGroupAlgebraTransitionInClass_id, RingHom.id_apply]
  change
    modNCompletedCoeffMap (n := i.modulus) (m := j.modulus) hij
        ((modNCompletedGroupAlgebraStageAugmentationInClass j.modulus H C U)
          (x.1 (j, U))) =
      (modNCompletedGroupAlgebraStageAugmentationInClass i.modulus H C U)
        ((modNCompletedGroupAlgebraStageCoeffMapInClass
          (n := i.modulus) (m := j.modulus) (G := H) C U hij)
          (x.1 (j, U)))
  exact
    (congrFun
      (congrArg DFunLike.coe
        (modNCompletedGroupAlgebraStageAugmentationInClass_comp_stageCoeffMap
          (n := i.modulus) (G := H) C U (m := j.modulus) hij))
      (x.1 (j, U))).symm

/--
The completed augmentation \(\mathbb{Z}_C\llbracket H\rrbracket \to \mathbb{Z}_C\), obtained by
augmenting every finite stage \((\mathbb{Z}/n\mathbb{Z})[H/U]\) at the canonical trivial
quotient of \(H\).
-/
def zcCompletedGroupAlgebraAugmentation :
    ZCCompletedGroupAlgebra C H →+* ZCCoeff C where
  toFun x :=
    Subtype.mk
      (zcCompletedGroupAlgebraAugmentationFamily C H x)
      (by
        intro i j hij
        exact zcCompletedGroupAlgebraAugmentationFamily_compatible C H x hij)
  map_zero' := by
    ext i
    change zcCompletedGroupAlgebraAugmentationFamily C H
        (0 : ZCCompletedGroupAlgebra C H) i = 0
    simp only [zcCompletedGroupAlgebraAugmentationFamily,
        zcCompletedGroupAlgebraProjection_zero, map_zero]
  map_one' := by
    ext i
    change zcCompletedGroupAlgebraAugmentationFamily C H
        (1 : ZCCompletedGroupAlgebra C H) i = 1
    simp only [zcCompletedGroupAlgebraAugmentationFamily, zcCompletedGroupAlgebraProjection_one,
        map_one]
  map_add' x y := by
    ext i
    change zcCompletedGroupAlgebraAugmentationFamily C H (x + y) i =
      zcCompletedGroupAlgebraAugmentationFamily C H x i +
        zcCompletedGroupAlgebraAugmentationFamily C H y i
    simp only [zcCompletedGroupAlgebraAugmentationFamily, zcCompletedGroupAlgebraProjection_add,
        map_add]
  map_mul' x y := by
    ext i
    change zcCompletedGroupAlgebraAugmentationFamily C H (x * y) i =
      zcCompletedGroupAlgebraAugmentationFamily C H x i *
        zcCompletedGroupAlgebraAugmentationFamily C H y i
    simp only [zcCompletedGroupAlgebraAugmentationFamily, zcCompletedGroupAlgebraProjection_mul,
        map_mul]

/-- Projecting the completed augmentation gives the corresponding finite-stage augmentation. -/
@[simp]
theorem proCIntegerProj_zcCompletedGroupAlgebraAugmentation
    (i : ProCIntegerIndex C) (x : ZCCompletedGroupAlgebra C H) :
    proCIntegerProj (C := C) i (zcCompletedGroupAlgebraAugmentation C H x) =
      zcCompletedGroupAlgebraAugmentationFamily C H x i :=
  rfl

/--
The completed augmentation can be read after projecting to any finite group quotient stage, not
only the canonical trivial quotient used in its definition.
-/
theorem proCIntegerProj_zcCompletedGroupAlgebraAugmentation_eq_stage
    (i : ZCCompletedGroupAlgebraIndex C H) (x : ZCCompletedGroupAlgebra C H) :
    proCIntegerProj (C := C) i.1 (zcCompletedGroupAlgebraAugmentation C H x) =
      modNCompletedGroupAlgebraStageAugmentationInClass i.1.modulus H C i.2
        (zcCompletedGroupAlgebraProjection C H i x) := by
  let T := zcCompletedGroupAlgebraTopIndex C H
  let : Fact (0 < i.1.modulus) := ⟨i.1.positive⟩
  have hT : T ≤ i.2 := zcCompletedGroupAlgebraTopIndex_le C H i.2
  have hx := x.2 (i.1, T) i ⟨le_rfl, hT⟩
  dsimp [zcCompletedGroupAlgebraAugmentationFamily]
  change
    (modNCompletedGroupAlgebraStageAugmentationInClass i.1.modulus H C T) (x.1 (i.1, T)) =
      (modNCompletedGroupAlgebraStageAugmentationInClass i.1.modulus H C i.2) (x.1 i)
  rw [← hx]
  simp only [zcCompletedGroupAlgebraTransition, RingHom.comp_apply,
    modNCompletedGroupAlgebraStageCoeffMapInClass_rfl, RingHom.id_apply]
  exact congrFun
    (congrArg DFunLike.coe
      (modNCompletedGroupAlgebraStageAugmentationInClass_compatible
        (n := i.1.modulus) (G := H) C hT)) (x.1 i)

/-- The completed augmentation sends every group-like element to \(1\). -/
@[simp]
theorem zcCompletedGroupAlgebraAugmentation_groupLike (h : H) :
    zcCompletedGroupAlgebraAugmentation C H (zcGroupLike C H h) = 1 := by
  ext i
  simp only [proCIntegerProj_zcCompletedGroupAlgebraAugmentation,
      zcCompletedGroupAlgebraAugmentationFamily,
    zcCompletedGroupAlgebraProjection_groupLike, OrderDual.ofDual_toDual,
    proCIntegerProj_one]
  exact modNCompletedGroupAlgebraStageAugmentationInClass_of
    (n := i.modulus) (G := H) C (zcCompletedGroupAlgebraTopIndex C H)
      (QuotientGroup.mk h)

/-- The completed Fox boundary has augmentation zero. -/
@[simp]
theorem zcCompletedGroupAlgebraAugmentation_boundary
    {G : Type u} [Group G] (ψ : G →* H) (g : G) :
    zcCompletedGroupAlgebraAugmentation C H
        (zcCompletedGroupAlgebraBoundary C ψ g) = 0 := by
  change zcCompletedGroupAlgebraAugmentation C H
      (zcGroupLike C H (ψ g) - 1) = 0
  simp only [map_sub, zcCompletedGroupAlgebraAugmentation_groupLike, map_one, sub_self]

/--
The completed augmentation ideal, defined as the kernel of \(\mathbb{Z}_C\llbracket H\rrbracket
\to \mathbb{Z}_C\).
-/
def zcCompletedGroupAlgebraAugmentationIdeal :
    Ideal (ZCCompletedGroupAlgebra C H) :=
  RingHom.ker (zcCompletedGroupAlgebraAugmentation C H)

/-- The completed augmentation ideal is bundled as a subtype. -/
abbrev ZCCompletedGroupAlgebraAugmentationIdeal : Type u :=
  zcCompletedGroupAlgebraAugmentationIdeal C H

/--
A completed integer group-algebra element lies in the completed augmentation ideal iff the
completed augmentation sends it to zero.
-/
@[simp]
theorem mem_zcCompletedGroupAlgebraAugmentationIdeal_iff
    {C : ProCGroups.FiniteGroupClass.{u}}
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    {x : ZCCompletedGroupAlgebra C H} :
    x ∈ zcCompletedGroupAlgebraAugmentationIdeal C H ↔
      zcCompletedGroupAlgebraAugmentation C H x = 0 := by
  rw [zcCompletedGroupAlgebraAugmentationIdeal, RingHom.mem_ker]

/-- The algebraic standard-generator ideal is contained in the completed augmentation ideal. -/
theorem zcCompletedGroupAlgebraStandardAugmentationIdeal_le_augmentationIdeal :
    zcCompletedGroupAlgebraStandardAugmentationIdeal C H ≤
      zcCompletedGroupAlgebraAugmentationIdeal C H := by
  rw [zcCompletedGroupAlgebraStandardAugmentationIdeal]
  refine Ideal.span_le.2 ?_
  rintro x ⟨h, rfl⟩
  change zcGroupLike C H h - 1 ∈ zcCompletedGroupAlgebraAugmentationIdeal C H
  rw [mem_zcCompletedGroupAlgebraAugmentationIdeal_iff]
  simp only [map_sub, zcCompletedGroupAlgebraAugmentation_groupLike, map_one, sub_self]

/-- The completed Fox boundary lies in the completed augmentation ideal. -/
theorem zcCompletedGroupAlgebraBoundary_mem_augmentationIdeal
    {G : Type u} [Group G] (ψ : G →* H) (g : G) :
    zcCompletedGroupAlgebraBoundary C ψ g ∈
      zcCompletedGroupAlgebraAugmentationIdeal C H := by
  rw [mem_zcCompletedGroupAlgebraAugmentationIdeal_iff]
  simp only [zcCompletedGroupAlgebraAugmentation_boundary]

/--
If the completed augmentation kernel is the algebraic standard-generator ideal, then a
surjective completed Fox boundary gives exactness at \(\mathbb{Z}_C\llbracket H\rrbracket\).
-/
theorem exact_zcToCompletedGA_of_surj_of_standardAugmentationIdeal_eq_augmentationIdeal
    {G : Type u} [Group G] (ψ : G →* H) (hψ : Function.Surjective ψ)
    (hstandard :
      zcCompletedGroupAlgebraStandardAugmentationIdeal C H =
        zcCompletedGroupAlgebraAugmentationIdeal C H) :
    Function.Exact
      (zcToCompletedGroupAlgebra C ψ :
        ZCCompletedDifferentialModule C ψ → ZCCompletedGroupAlgebra C H)
      (zcCompletedGroupAlgebraAugmentation C H :
        ZCCompletedGroupAlgebra C H → ZCCoeff C) := by
  intro z
  constructor
  · intro hz
    have hzmem :
        z ∈ zcCompletedGroupAlgebraStandardAugmentationIdeal C H := by
      rw [hstandard]
      exact (mem_zcCompletedGroupAlgebraAugmentationIdeal_iff
        (C := C) (H := H) (x := z)).2 hz
    have hzrange :
        z ∈ LinearMap.range (zcToCompletedGroupAlgebra C ψ) := by
      rw [zcToCompletedGroupAlgebra_range_eq_standardAugmentationIdeal_of_surjective
        C H ψ hψ]
      exact hzmem
    exact hzrange
  · rintro ⟨m, rfl⟩
    have hmem :
        zcToCompletedGroupAlgebra C ψ m ∈
          zcCompletedGroupAlgebraAugmentationIdeal C H :=
      zcCompletedGroupAlgebraStandardAugmentationIdeal_le_augmentationIdeal C H
        (zcToCompletedGroupAlgebra_mem_standardAugmentationIdeal C H ψ m)
    exact (mem_zcCompletedGroupAlgebraAugmentationIdeal_iff
      (C := C) (H := H) (x := zcToCompletedGroupAlgebra C ψ m)).1 hmem

/--
For a surjective coefficient group map, exactness of the algebraic completed Fox tail is
equivalent to the algebraic standard-generator ideal already being the completed augmentation
ideal. This isolates the closed-range obstruction for infinite completed group algebras.
-/
theorem exact_zcToCompletedGA_iff_standardAugmentationIdeal_eq_augmentationIdeal_of_surj
    {C : ProCGroups.FiniteGroupClass.{u}}
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    {G : Type u} [Group G] (ψ : G →* H) (hψ : Function.Surjective ψ) :
    Function.Exact
        (zcToCompletedGroupAlgebra C ψ :
          ZCCompletedDifferentialModule C ψ → ZCCompletedGroupAlgebra C H)
        (zcCompletedGroupAlgebraAugmentation C H :
          ZCCompletedGroupAlgebra C H → ZCCoeff C) ↔
      zcCompletedGroupAlgebraStandardAugmentationIdeal C H =
        zcCompletedGroupAlgebraAugmentationIdeal C H := by
  constructor
  · intro hexact
    apply le_antisymm
    · exact zcCompletedGroupAlgebraStandardAugmentationIdeal_le_augmentationIdeal C H
    · intro z hz
      have hz0 :
          zcCompletedGroupAlgebraAugmentation C H z = 0 :=
        (mem_zcCompletedGroupAlgebraAugmentationIdeal_iff
          (C := C) (H := H) (x := z)).1 hz
      rcases (hexact z).1 hz0 with ⟨m, hm⟩
      have hzrange :
          z ∈ LinearMap.range (zcToCompletedGroupAlgebra C ψ) := ⟨m, hm⟩
      rwa [zcToCompletedGroupAlgebra_range_eq_standardAugmentationIdeal_of_surjective
        C H ψ hψ] at hzrange
  · intro hstandard
    exact
      exact_zcToCompletedGA_of_surj_of_standardAugmentationIdeal_eq_augmentationIdeal
        C H ψ hψ hstandard

/--
The completed augmentation \(\mathbb{Z}_C\llbracket H\rrbracket \to \mathbb{Z}_C\) is
surjective.
-/
theorem zcCompletedGroupAlgebraAugmentation_surjective :
    Function.Surjective (zcCompletedGroupAlgebraAugmentation C H) := by
  intro a
  refine ⟨⟨fun i => ?_, ?_⟩, ?_⟩
  · letI : Fact (0 < i.1.modulus) := ⟨i.1.positive⟩
    exact MonoidAlgebra.single
      (1 : CompletedGroupAlgebraQuotientInClass H C i.2)
      (proCIntegerProj (C := C) i.1 a)
  · intro i j hij
    let : Fact (0 < i.1.modulus) := ⟨i.1.positive⟩
    let : Fact (0 < j.1.modulus) := ⟨j.1.positive⟩
    have ha :
        modNCompletedCoeffMap (n := i.1.modulus) (m := j.1.modulus) hij.1
            (proCIntegerProj (C := C) j.1 a) =
          proCIntegerProj (C := C) i.1 a :=
      proCIntegerProj_transition (C := C) hij.1 a
    have hmap :
        modNCompletedGroupAlgebraTransitionInClass j.1.modulus H C hij.2
            (algebraMap (ModNCompletedCoeff j.1.modulus)
              (ZCCompletedGroupAlgebraStage C H j)
              (proCIntegerProj (C := C) j.1 a)) =
          algebraMap (ModNCompletedCoeff j.1.modulus)
            (ModNCompletedGroupAlgebraStageInClass j.1.modulus H C i.2)
            (proCIntegerProj (C := C) j.1 a) := by
      change MonoidAlgebra.mapDomain _
          (algebraMap (ModNCompletedCoeff j.1.modulus)
            (ZCCompletedGroupAlgebraStage C H j)
            (proCIntegerProj (C := C) j.1 a)) =
        algebraMap (ModNCompletedCoeff j.1.modulus)
          (ModNCompletedGroupAlgebraStageInClass j.1.modulus H C i.2)
          (proCIntegerProj (C := C) j.1 a)
      erw [MonoidAlgebra.mapDomain_algebraMap]
    change
      modNCompletedGroupAlgebraStageCoeffMapInClass
          (n := i.1.modulus) (m := j.1.modulus) (G := H) C i.2 hij.1
          (modNCompletedGroupAlgebraTransitionInClass j.1.modulus H C hij.2
            (algebraMap (ModNCompletedCoeff j.1.modulus)
              (ZCCompletedGroupAlgebraStage C H j)
              (proCIntegerProj (C := C) j.1 a))) =
        MonoidAlgebra.single
          (1 : CompletedGroupAlgebraQuotientInClass H C i.2)
          (proCIntegerProj (C := C) i.1 a)
    rw [hmap]
    change
      modNCompletedGroupAlgebraStageCoeffMapInClass
          (n := i.1.modulus) (m := j.1.modulus) (G := H) C i.2 hij.1
          (MonoidAlgebra.single
            (1 : CompletedGroupAlgebraQuotientInClass H C i.2)
            (proCIntegerProj (C := C) j.1 a)) =
        MonoidAlgebra.single
          (1 : CompletedGroupAlgebraQuotientInClass H C i.2)
          (proCIntegerProj (C := C) i.1 a)
    rw [modNCompletedGroupAlgebraStageCoeffMapInClass_single_apply, ha]
  · ext i
    let T := zcCompletedGroupAlgebraTopIndex C H
    let : Fact (0 < i.modulus) := ⟨i.positive⟩
    change
      (modNCompletedGroupAlgebraStageAugmentationInClass i.modulus H C T)
          (MonoidAlgebra.single
            (1 : CompletedGroupAlgebraQuotientInClass H C T)
            (proCIntegerProj (C := C) i a)) =
        proCIntegerProj (C := C) i a
    simp only [modNCompletedGroupAlgebraStageAugmentationInClass_single]

end Augmentation

end

end FoxDifferential
