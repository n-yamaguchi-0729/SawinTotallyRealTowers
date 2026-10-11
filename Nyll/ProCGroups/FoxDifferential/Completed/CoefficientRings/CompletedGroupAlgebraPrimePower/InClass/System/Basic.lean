/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraPrimePower.Basic.Augmentation
import Nyll.ProCGroups.FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraPrimePower.Basic.StageCoeffMap.Coeff

/-!
# Fox differential: prime-power completed group algebra — in class — system — basic

The principal declarations in this module are:

- `PrimePowerCompletedGroupAlgebraStageInClass`
  The class-restricted prime-power stage at index \((a,U)\), namely
  \((\mathrm{ZMod}\,\ell^a)[G/U]\).
- `primePowerCompletedGroupAlgebraTransitionInClass`
  The combined transition map for class-restricted prime-power stage calculus.
- `finite_primePowerCompletedGroupAlgebraStageInClass`
  Each class-indexed prime-power finite stage is finite.
- `primePowerCompletedGroupAlgebraTransitionInClass_of`
  The transition map sends a group-like basis element to the basis element supported at its image in
  the coarser quotient in the Fox differential construction.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u

variable (ℓ : ℕ) [Fact (0 < ℓ)]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [Fact (0 < ℓ)] in
/--
The class-restricted prime-power stage at index \((a,U)\), namely
\((\mathrm{ZMod}\,\ell^a)[G/U]\).
-/
abbrev PrimePowerCompletedGroupAlgebraStageInClass
    (C : ProCGroups.FiniteGroupClass.{u}) (i : PrimePowerCompletedGroupAlgebraIndexInClass G C) :
    Type _ :=
  ModNCompletedGroupAlgebraStageInClass (ℓ ^ i.1) G C i.2

/-- Each class-indexed prime-power finite stage is finite. -/
theorem finite_primePowerCompletedGroupAlgebraStageInClass
    (C : ProCGroups.FiniteGroupClass.{u})
    (i : PrimePowerCompletedGroupAlgebraIndexInClass G C) :
    Finite (PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i) := by
  let : Fact (0 < ℓ ^ i.1) := ⟨primePower_pos ℓ i.1⟩
  exact finite_modNCompletedGroupAlgebraStageInClass
    (n := ℓ ^ i.1) (G := G) C i.2

omit [Fact (0 < ℓ)] in
/-- The combined transition map for class-restricted prime-power stage calculus. -/
def primePowerCompletedGroupAlgebraTransitionInClass
    (C : ProCGroups.FiniteGroupClass.{u})
    {i j : PrimePowerCompletedGroupAlgebraIndexInClass G C} (hij : i ≤ j) :
    PrimePowerCompletedGroupAlgebraStageInClass ℓ G C j →+*
      PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i := by
  exact
    (modNCompletedGroupAlgebraStageCoeffMapInClass
        (n := ℓ ^ i.1) (m := ℓ ^ j.1) (G := G) C i.2
        (primePow_dvd_primePow (ℓ := ℓ) hij.1)).comp
      (modNCompletedGroupAlgebraTransitionInClass (n := ℓ ^ j.1) (G := G) C hij.2)

omit [Fact (0 < ℓ)] in
/--
The transition map sends a group-like basis element to the basis element supported at its image
in the coarser quotient in the Fox differential construction.
-/
@[simp]
theorem primePowerCompletedGroupAlgebraTransitionInClass_of
    (C : ProCGroups.FiniteGroupClass.{u})
    {i j : PrimePowerCompletedGroupAlgebraIndexInClass G C} (hij : i ≤ j)
    (q : CompletedGroupAlgebraQuotientInClass G C j.2) :
    primePowerCompletedGroupAlgebraTransitionInClass (ℓ := ℓ) (G := G) C hij
        (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ j.1)) _ q) =
      MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ i.1)) _
        ((OpenNormalSubgroupInClass.map
          (C := C) (G := G)
          (U := OrderDual.ofDual i.2) (V := OrderDual.ofDual j.2) hij.2) q) := by
  rw [primePowerCompletedGroupAlgebraTransitionInClass, RingHom.comp_apply,
    modNCompletedGroupAlgebraTransitionInClass_of]
  change
    (modNCompletedGroupAlgebraStageCoeffMapInClass
      (n := ℓ ^ i.1) (m := ℓ ^ j.1) (G := G) C i.2
      (primePow_dvd_primePow (ℓ := ℓ) hij.1))
        (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ j.1)) _
          ((OpenNormalSubgroupInClass.map
            (C := C) (G := G)
            (U := OrderDual.ofDual i.2) (V := OrderDual.ofDual j.2) hij.2) q)) =
      MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ i.1)) _
        ((OpenNormalSubgroupInClass.map
          (C := C) (G := G)
          (U := OrderDual.ofDual i.2) (V := OrderDual.ofDual j.2) hij.2) q)
  exact modNCompletedGroupAlgebraStageCoeffMapInClass_of
    (n := ℓ ^ i.1) (m := ℓ ^ j.1) (G := G) C i.2
    (primePow_dvd_primePow (ℓ := ℓ) hij.1)
    ((OpenNormalSubgroupInClass.map
      (C := C) (G := G)
      (U := OrderDual.ofDual i.2) (V := OrderDual.ofDual j.2) hij.2) q)

omit [Fact (0 < ℓ)] in
/--
The \(C\)-indexed transition map between finite stages sends a singleton supported at a class of
the finer quotient to the singleton supported at its image in the coarser quotient, preserving
the coefficient.
-/
@[simp]
theorem primePowerCompletedGroupAlgebraTransitionInClass_single
    (C : ProCGroups.FiniteGroupClass.{u})
    {i j : PrimePowerCompletedGroupAlgebraIndexInClass G C} (hij : i ≤ j)
    (q : CompletedGroupAlgebraQuotientInClass G C j.2)
    (a : ModNCompletedCoeff (ℓ ^ j.1)) :
    primePowerCompletedGroupAlgebraTransitionInClass (ℓ := ℓ) (G := G) C hij
        (MonoidAlgebra.single q a) =
      MonoidAlgebra.single
        ((OpenNormalSubgroupInClass.map
          (C := C) (G := G)
          (U := OrderDual.ofDual i.2) (V := OrderDual.ofDual j.2) hij.2) q)
        (modNCompletedCoeffMap
          (n := ℓ ^ i.1) (m := ℓ ^ j.1)
          (primePow_dvd_primePow (ℓ := ℓ) hij.1) a) := by
  change
    (modNCompletedGroupAlgebraStageCoeffMapInClass
      (n := ℓ ^ i.1) (m := ℓ ^ j.1) (G := G) C i.2
      (primePow_dvd_primePow (ℓ := ℓ) hij.1))
        (modNCompletedGroupAlgebraTransitionInClass
          (n := ℓ ^ j.1) (G := G) C hij.2 (MonoidAlgebra.single q a)) =
      MonoidAlgebra.single
        ((OpenNormalSubgroupInClass.map
          (C := C) (G := G)
          (U := OrderDual.ofDual i.2) (V := OrderDual.ofDual j.2) hij.2) q)
        (modNCompletedCoeffMap
          (n := ℓ ^ i.1) (m := ℓ ^ j.1)
          (primePow_dvd_primePow (ℓ := ℓ) hij.1) a)
  rw [modNCompletedGroupAlgebraTransitionInClass_single]
  exact modNCompletedGroupAlgebraStageCoeffMapInClass_single_apply
    (n := ℓ ^ i.1) (m := ℓ ^ j.1) (G := G) C i.2
    (primePow_dvd_primePow (ℓ := ℓ) hij.1)
    ((OpenNormalSubgroupInClass.map
      (C := C) (G := G)
      (U := OrderDual.ofDual i.2) (V := OrderDual.ofDual j.2) hij.2) q) a

omit [Fact (0 < ℓ)] in
/--
The transition map for the prime-power completed group algebra commutes with the finite-stage
coordinate maps.
-/
@[simp]
theorem primePowerCompletedGroupAlgebraTransitionInClass_eq
    (C : ProCGroups.FiniteGroupClass.{u})
    {i j : PrimePowerCompletedGroupAlgebraIndexInClass G C} (hij : i ≤ j) :
    primePowerCompletedGroupAlgebraTransitionInClass (ℓ := ℓ) (G := G) C hij =
      (modNCompletedGroupAlgebraStageCoeffMapInClass
          (n := ℓ ^ i.1) (m := ℓ ^ j.1) (G := G) C i.2
          (primePow_dvd_primePow (ℓ := ℓ) hij.1)).comp
        (modNCompletedGroupAlgebraTransitionInClass (ℓ ^ j.1) G C hij.2) := by
  rfl

omit [Fact (0 < ℓ)] in
/--
The class-indexed prime-power transition agrees with the explicit coefficient-and-quotient
transition formula.
-/
theorem primePowerCompletedGroupAlgebraTransitionInClass_eq'
    (C : ProCGroups.FiniteGroupClass.{u})
    {i j : PrimePowerCompletedGroupAlgebraIndexInClass G C} (hij : i ≤ j) :
    primePowerCompletedGroupAlgebraTransitionInClass (ℓ := ℓ) (G := G) C hij =
      (modNCompletedGroupAlgebraTransitionInClass (ℓ ^ i.1) G C hij.2).comp
        (modNCompletedGroupAlgebraStageCoeffMapInClass
          (n := ℓ ^ i.1) (m := ℓ ^ j.1) (G := G) C j.2
          (primePow_dvd_primePow (ℓ := ℓ) hij.1)) := by
  rw [primePowerCompletedGroupAlgebraTransitionInClass_eq]
  exact modNCompletedGroupAlgebraStageCoeffMapInClass_compatible
    (n := ℓ ^ i.1) (m := ℓ ^ j.1) (G := G) C
    (U := i.2) (V := j.2) hij.2
    (primePow_dvd_primePow (ℓ := ℓ) hij.1)

omit [Fact (0 < ℓ)] in
/--
The transition map attached to the identity refinement is the identity homomorphism in the Fox
differential construction.
-/
@[simp]
theorem primePowerCompletedGroupAlgebraTransitionInClass_id
    (C : ProCGroups.FiniteGroupClass.{u}) (i : PrimePowerCompletedGroupAlgebraIndexInClass G C) :
    primePowerCompletedGroupAlgebraTransitionInClass (ℓ := ℓ) (G := G) C
        (le_rfl : i ≤ i) =
      RingHom.id _ := by
  rw [primePowerCompletedGroupAlgebraTransitionInClass_eq]
  rw [modNCompletedGroupAlgebraTransitionInClass_id,
    modNCompletedGroupAlgebraStageCoeffMapInClass_rfl]
  simp only [RingHomCompTriple.comp_eq]

omit [Fact (0 < ℓ)] in
/--
Class-indexed prime-power completed group-algebra transitions compose along quotient refinements.
-/
@[simp 900]
theorem primePowerCompletedGroupAlgebraTransitionInClass_comp
    (C : ProCGroups.FiniteGroupClass.{u})
    {i j k : PrimePowerCompletedGroupAlgebraIndexInClass G C}
    (hij : i ≤ j) (hjk : j ≤ k) :
    (primePowerCompletedGroupAlgebraTransitionInClass (ℓ := ℓ) (G := G) C hij).comp
        (primePowerCompletedGroupAlgebraTransitionInClass (ℓ := ℓ) (G := G) C hjk) =
      primePowerCompletedGroupAlgebraTransitionInClass (ℓ := ℓ) (G := G) C
        (hij.trans hjk) := by
  calc
    (primePowerCompletedGroupAlgebraTransitionInClass (ℓ := ℓ) (G := G) C hij).comp
        (primePowerCompletedGroupAlgebraTransitionInClass (ℓ := ℓ) (G := G) C hjk)
      =
    ((modNCompletedGroupAlgebraStageCoeffMapInClass
          (n := ℓ ^ i.1) (m := ℓ ^ j.1) (G := G) C i.2
          (primePow_dvd_primePow (ℓ := ℓ) hij.1)).comp
        (modNCompletedGroupAlgebraTransitionInClass (ℓ ^ j.1) G C hij.2)).comp
      ((modNCompletedGroupAlgebraTransitionInClass (ℓ ^ j.1) G C hjk.2).comp
        (modNCompletedGroupAlgebraStageCoeffMapInClass
          (n := ℓ ^ j.1) (m := ℓ ^ k.1) (G := G) C k.2
          (primePow_dvd_primePow (ℓ := ℓ) hjk.1))) := by
          rw [primePowerCompletedGroupAlgebraTransitionInClass_eq,
            primePowerCompletedGroupAlgebraTransitionInClass_eq']
    _ =
    (modNCompletedGroupAlgebraStageCoeffMapInClass
        (n := ℓ ^ i.1) (m := ℓ ^ j.1) (G := G) C i.2
        (primePow_dvd_primePow (ℓ := ℓ) hij.1)).comp
      (((modNCompletedGroupAlgebraTransitionInClass (ℓ ^ j.1) G C hij.2).comp
          (modNCompletedGroupAlgebraTransitionInClass (ℓ ^ j.1) G C hjk.2)).comp
        (modNCompletedGroupAlgebraStageCoeffMapInClass
          (n := ℓ ^ j.1) (m := ℓ ^ k.1) (G := G) C k.2
          (primePow_dvd_primePow (ℓ := ℓ) hjk.1))) := by
          apply RingHom.ext
          intro x
          rfl
    _ =
    (modNCompletedGroupAlgebraStageCoeffMapInClass
        (n := ℓ ^ i.1) (m := ℓ ^ j.1) (G := G) C i.2
        (primePow_dvd_primePow (ℓ := ℓ) hij.1)).comp
      ((modNCompletedGroupAlgebraTransitionInClass (ℓ ^ j.1) G C
          (hij.2.trans hjk.2)).comp
        (modNCompletedGroupAlgebraStageCoeffMapInClass
          (n := ℓ ^ j.1) (m := ℓ ^ k.1) (G := G) C k.2
          (primePow_dvd_primePow (ℓ := ℓ) hjk.1))) := by
          rw [modNCompletedGroupAlgebraTransitionInClass_comp]
    _ =
    ((modNCompletedGroupAlgebraStageCoeffMapInClass
          (n := ℓ ^ i.1) (m := ℓ ^ j.1) (G := G) C i.2
          (primePow_dvd_primePow (ℓ := ℓ) hij.1)).comp
        (modNCompletedGroupAlgebraTransitionInClass (ℓ ^ j.1) G C
          (hij.2.trans hjk.2))).comp
      (modNCompletedGroupAlgebraStageCoeffMapInClass
        (n := ℓ ^ j.1) (m := ℓ ^ k.1) (G := G) C k.2
        (primePow_dvd_primePow (ℓ := ℓ) hjk.1)) := by
          rw [← RingHom.comp_assoc]
    _ =
    ((modNCompletedGroupAlgebraTransitionInClass (ℓ ^ i.1) G C
          (hij.2.trans hjk.2)).comp
        (modNCompletedGroupAlgebraStageCoeffMapInClass
          (n := ℓ ^ i.1) (m := ℓ ^ j.1) (G := G) C k.2
          (primePow_dvd_primePow (ℓ := ℓ) hij.1))).comp
      (modNCompletedGroupAlgebraStageCoeffMapInClass
        (n := ℓ ^ j.1) (m := ℓ ^ k.1) (G := G) C k.2
        (primePow_dvd_primePow (ℓ := ℓ) hjk.1)) := by
          rw [modNCompletedGroupAlgebraStageCoeffMapInClass_compatible
            (n := ℓ ^ i.1) (m := ℓ ^ j.1) (G := G) C
            (U := i.2) (V := k.2) (hUV := hij.2.trans hjk.2)
            (hnm := primePow_dvd_primePow (ℓ := ℓ) hij.1)]
    _ =
    (modNCompletedGroupAlgebraTransitionInClass (ℓ ^ i.1) G C
        (hij.2.trans hjk.2)).comp
      ((modNCompletedGroupAlgebraStageCoeffMapInClass
          (n := ℓ ^ i.1) (m := ℓ ^ j.1) (G := G) C k.2
          (primePow_dvd_primePow (ℓ := ℓ) hij.1)).comp
        (modNCompletedGroupAlgebraStageCoeffMapInClass
          (n := ℓ ^ j.1) (m := ℓ ^ k.1) (G := G) C k.2
          (primePow_dvd_primePow (ℓ := ℓ) hjk.1))) := by
          rw [RingHom.comp_assoc]
    _ =
    (modNCompletedGroupAlgebraTransitionInClass (ℓ ^ i.1) G C
        (hij.2.trans hjk.2)).comp
      (modNCompletedGroupAlgebraStageCoeffMapInClass
        (n := ℓ ^ i.1) (m := ℓ ^ k.1) (G := G) C k.2
        (primePow_dvd_primePow (ℓ := ℓ) (hij.trans hjk).1)) := by
          rw [modNCompletedGroupAlgebraStageCoeffMapInClass_comp
            (n := ℓ ^ i.1) (m := ℓ ^ j.1) (k := ℓ ^ k.1) (G := G) C
            (U := k.2)
            (hnm := primePow_dvd_primePow (ℓ := ℓ) hij.1)
            (hmk := primePow_dvd_primePow (ℓ := ℓ) hjk.1)]
    _ =
    primePowerCompletedGroupAlgebraTransitionInClass (ℓ := ℓ) (G := G) C
        (hij.trans hjk) := by
          rw [← primePowerCompletedGroupAlgebraTransitionInClass_eq'
            (ℓ := ℓ) (G := G) C (hij := hij.trans hjk)]

omit [Fact (0 < ℓ)] in
/--
Class-indexed finite-stage prime-power augmentation is compatible with transition maps and
coefficient reduction.
-/
@[simp]
theorem primePowerCompletedGroupAlgebraStageAugmentationInClass_comp_transition
    (C : ProCGroups.FiniteGroupClass.{u})
    {i j : PrimePowerCompletedGroupAlgebraIndexInClass G C} (hij : i ≤ j) :
    (modNCompletedGroupAlgebraStageAugmentationInClass (ℓ ^ i.1) G C i.2).comp
        (primePowerCompletedGroupAlgebraTransitionInClass (ℓ := ℓ) (G := G) C hij) =
      (modNCompletedCoeffMap
          (n := ℓ ^ i.1) (m := ℓ ^ j.1)
          (primePow_dvd_primePow (ℓ := ℓ) hij.1)).comp
        (modNCompletedGroupAlgebraStageAugmentationInClass (ℓ ^ j.1) G C j.2) := by
  rw [primePowerCompletedGroupAlgebraTransitionInClass]
  rw [← RingHom.comp_assoc]
  rw [modNCompletedGroupAlgebraStageAugmentationInClass_comp_coeffMap]
  rw [RingHom.comp_assoc]
  rw [modNCompletedGroupAlgebraStageAugmentationInClass_compatible]

omit [Fact (0 < ℓ)] in
/-- The class-restricted inverse system indexed by prime powers and \(C\)-quotients. -/
def primePowerCompletedGroupAlgebraSystemInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    InverseSystem (I := PrimePowerCompletedGroupAlgebraIndexInClass G C) where
  X := PrimePowerCompletedGroupAlgebraStageInClass ℓ G C
  topologicalSpace := fun _ => ⊥
  map := fun {i j} hij =>
    primePowerCompletedGroupAlgebraTransitionInClass (ℓ := ℓ) (G := G) C hij
  continuous_map := by
    intro i j hij
    let : TopologicalSpace (PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i) := ⊥
    let : TopologicalSpace (PrimePowerCompletedGroupAlgebraStageInClass ℓ G C j) := ⊥
    let : DiscreteTopology (PrimePowerCompletedGroupAlgebraStageInClass ℓ G C j) := ⟨rfl⟩
    exact continuous_of_discreteTopology
  map_id := by
    intro i
    funext x
    exact congrFun
      (congrArg DFunLike.coe
        (primePowerCompletedGroupAlgebraTransitionInClass_id
          (ℓ := ℓ) (G := G) C i)) x
  map_comp := by
    intro i j k hij hjk
    funext x
    exact congrFun
      (congrArg DFunLike.coe
        (primePowerCompletedGroupAlgebraTransitionInClass_comp
          (ℓ := ℓ) (G := G) C hij hjk)) x

omit [IsTopologicalGroup G] in
/--
The class-restricted prime-power group-algebra index family is directed under componentwise
order when \(C\) is a formation.
-/
theorem directed_primePowerCompletedGroupAlgebraIndexInClass
    (C : ProCGroups.FiniteGroupClass.{u}) (hForm : ProCGroups.FiniteGroupClass.Formation C) :
    Directed (· ≤ ·) (id : PrimePowerCompletedGroupAlgebraIndexInClass G C →
      PrimePowerCompletedGroupAlgebraIndexInClass G C) := by
  intro i j
  rcases directed_openNormalSubgroupInClass
      (C := C) (G := G) hForm i.2 j.2 with
    ⟨U, hiU, hjU⟩
  refine ⟨(max i.1 j.1, U), ?_, ?_⟩
  · exact ⟨le_max_left _ _, hiU⟩
  · exact ⟨le_max_right _ _, hjU⟩

omit [Fact (0 < ℓ)] in
/--
Every transition in the class-restricted prime-power completed group-algebra system is
surjective.
-/
theorem primePowerCompletedGroupAlgebraTransitionInClass_surjective
    (C : ProCGroups.FiniteGroupClass.{u})
    {i j : PrimePowerCompletedGroupAlgebraIndexInClass G C} (hij : i ≤ j) :
    Function.Surjective
      (primePowerCompletedGroupAlgebraTransitionInClass (ℓ := ℓ) (G := G) C hij) := by
  intro x
  rcases modNCompletedGroupAlgebraStageCoeffMapInClass_surjective
      (n := ℓ ^ i.1) (m := ℓ ^ j.1) (G := G) C i.2
      (primePow_dvd_primePow (ℓ := ℓ) hij.1) x with
    ⟨y, hy⟩
  rcases modNCompletedGroupAlgebraTransitionInClass_surjective
      (n := ℓ ^ j.1) (G := G) C hij.2 y with
    ⟨z, hz⟩
  refine ⟨z, ?_⟩
  rw [primePowerCompletedGroupAlgebraTransitionInClass_eq, RingHom.comp_apply, hz, hy]

omit [Fact (0 < ℓ)] in
/-- Compatibility for a class-restricted prime-power completed group algebra family. -/
def PrimePowerCompletedGroupAlgebraCompatibleInClass
    (C : ProCGroups.FiniteGroupClass.{u})
    (x : ∀ i : PrimePowerCompletedGroupAlgebraIndexInClass G C,
      PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i) : Prop :=
  (primePowerCompletedGroupAlgebraSystemInClass ℓ G C).Compatible x

omit [Fact (0 < ℓ)] in
/--
The class-restricted prime-power completed group algebra as an inverse-limit subtype. The
all-finite PrimePowerCompletedGroupAlgebra below remains the ringed concrete formulation; this
type is the class-indexed completed object that later Fox layers should target.
-/
abbrev PrimePowerCompletedGroupAlgebraInClass (C : ProCGroups.FiniteGroupClass.{u}) : Type _ :=
  {x : ∀ i : PrimePowerCompletedGroupAlgebraIndexInClass G C,
      PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i //
    PrimePowerCompletedGroupAlgebraCompatibleInClass (ℓ := ℓ) (G := G) C x}

omit [Fact (0 < ℓ)] in
/-- The projection from the class-restricted completed group algebra to a prime-power stage. -/
def primePowerCompletedGroupAlgebraProjectionInClass
    (C : ProCGroups.FiniteGroupClass.{u}) (i : PrimePowerCompletedGroupAlgebraIndexInClass G C) :
    PrimePowerCompletedGroupAlgebraInClass ℓ G C →
      PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i :=
  (primePowerCompletedGroupAlgebraSystemInClass ℓ G C).projection i

/--
Every finite-stage projection from the class-restricted prime-power completed group algebra is
surjective when \(C\) is a formation of finite quotient groups.
-/
theorem primePowerCompletedGroupAlgebraProjectionInClass_surjective
    (C : ProCGroups.FiniteGroupClass.{u})
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (i : PrimePowerCompletedGroupAlgebraIndexInClass G C) :
    Function.Surjective
      (primePowerCompletedGroupAlgebraProjectionInClass (ℓ := ℓ) (G := G) C i) := by
  let S := primePowerCompletedGroupAlgebraSystemInClass ℓ G C
  let : ∀ i : PrimePowerCompletedGroupAlgebraIndexInClass G C, TopologicalSpace (S.X i) :=
    fun i => S.topologicalSpace i
  let : ∀ i : PrimePowerCompletedGroupAlgebraIndexInClass G C, DiscreteTopology (S.X i) :=
    fun _ => ⟨rfl⟩
  let : ∀ i : PrimePowerCompletedGroupAlgebraIndexInClass G C, CompactSpace (S.X i) :=
    fun i => by
      let : Finite (S.X i) := by
        dsimp [S, primePowerCompletedGroupAlgebraSystemInClass]
        exact finite_primePowerCompletedGroupAlgebraStageInClass
          (ℓ := ℓ) (G := G) C i
      let : Fintype (S.X i) := Fintype.ofFinite _
      infer_instance
  let : ∀ i : PrimePowerCompletedGroupAlgebraIndexInClass G C, T2Space (S.X i) :=
    fun _ => inferInstance
  change Function.Surjective (S.projection i)
  exact
    S.surjective_π
      (directed_primePowerCompletedGroupAlgebraIndexInClass (G := G) C hForm)
      (fun {i j} hij =>
        primePowerCompletedGroupAlgebraTransitionInClass_surjective (ℓ := ℓ) (G := G) C hij)
      i

end

end FoxDifferential
