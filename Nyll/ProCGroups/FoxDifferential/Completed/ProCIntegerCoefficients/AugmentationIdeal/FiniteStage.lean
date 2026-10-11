/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.ProCIntegerCoefficients.Augmentation
import Nyll.ProCGroups.CompletedGroupAlgebra.ProfiniteModules.FiniteGroupAlgebra.Augmentation.Abstract

/-!
# Fox differential: completed — \(\mathbb{Z}_C\) coefficients — augmentation ideal — finite stage

The principal declarations in this module are:

- `zcCompletedGroupAlgebraStageAugmentationIdeal`
  The augmentation ideal in one finite stage of \(\mathbb{Z}_C\llbracket H\rrbracket\).
- `zcCompletedGroupAlgebraStageAugmentationGenerator`
  The standard generator \([q]-1\) in one finite stage of \(\mathbb{Z}_C\llbracket H\rrbracket\).
- `mem_zcCompletedGroupAlgebraStageAugmentationIdeal_iff`
  Membership in a finite-stage completed augmentation ideal is equivalent to vanishing under the
  corresponding stage augmentation map.
- `zcCompletedGroupAlgebraStageAugmentationGenerator_mem`
  A finite-stage standard generator lies in the finite-stage augmentation ideal.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.Completion
open ProCGroups.ProC

universe u

section FiniteStageAugmentationIdeal

variable (C : ProCGroups.FiniteGroupClass.{u})
variable (H : Type u) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- The augmentation ideal in one finite stage of \(\mathbb{Z}_C\llbracket H\rrbracket\). -/
def zcCompletedGroupAlgebraStageAugmentationIdeal
    (i : ZCCompletedGroupAlgebraIndex C H) :
    Ideal (ZCCompletedGroupAlgebraStage C H i) := by
  letI : Fact (0 < i.1.modulus) := ⟨i.1.positive⟩
  exact RingHom.ker
    (modNCompletedGroupAlgebraStageAugmentationInClass i.1.modulus H C i.2)

/--
Membership in a finite-stage completed augmentation ideal is equivalent to vanishing under the
corresponding stage augmentation map.
-/
@[simp]
theorem mem_zcCompletedGroupAlgebraStageAugmentationIdeal_iff
    {C : ProCGroups.FiniteGroupClass.{u}}
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    {i : ZCCompletedGroupAlgebraIndex C H}
    {x : ZCCompletedGroupAlgebraStage C H i} :
    x ∈ zcCompletedGroupAlgebraStageAugmentationIdeal C H i ↔
      modNCompletedGroupAlgebraStageAugmentationInClass i.1.modulus H C i.2 x = 0 := by
  let : Fact (0 < i.1.modulus) := ⟨i.1.positive⟩
  rw [zcCompletedGroupAlgebraStageAugmentationIdeal, RingHom.mem_ker]

/--
The standard generator \([q]-1\) in one finite stage of \(\mathbb{Z}_C\llbracket H\rrbracket\).
-/
def zcCompletedGroupAlgebraStageAugmentationGenerator
    (i : ZCCompletedGroupAlgebraIndex C H)
    (q : CompletedGroupAlgebraQuotientInClass H C i.2) :
    ZCCompletedGroupAlgebraStage C H i := by
  letI : Fact (0 < i.1.modulus) := ⟨i.1.positive⟩
  exact MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus)
    (CompletedGroupAlgebraQuotientInClass H C i.2) q - 1

/-- A finite-stage standard generator lies in the finite-stage augmentation ideal. -/
theorem zcCompletedGroupAlgebraStageAugmentationGenerator_mem
    (i : ZCCompletedGroupAlgebraIndex C H)
    (q : CompletedGroupAlgebraQuotientInClass H C i.2) :
    zcCompletedGroupAlgebraStageAugmentationGenerator C H i q ∈
      zcCompletedGroupAlgebraStageAugmentationIdeal C H i := by
  let : Fact (0 < i.1.modulus) := ⟨i.1.positive⟩
  rw [mem_zcCompletedGroupAlgebraStageAugmentationIdeal_iff]
  simp only [zcCompletedGroupAlgebraStageAugmentationGenerator, MonoidAlgebra.of_apply, map_sub,
  modNCompletedGroupAlgebraStageAugmentationInClass_single, map_one, sub_self]

/-- The standard generators \([q]-1\), viewed inside the finite-stage augmentation ideal. -/
def zcCompletedGroupAlgebraStageAugmentationGeneratorSubtype
    (i : ZCCompletedGroupAlgebraIndex C H)
    (q : CompletedGroupAlgebraQuotientInClass H C i.2) :
    zcCompletedGroupAlgebraStageAugmentationIdeal C H i :=
  ⟨zcCompletedGroupAlgebraStageAugmentationGenerator C H i q,
    zcCompletedGroupAlgebraStageAugmentationGenerator_mem C H i q⟩

/-- In each finite stage, the augmentation ideal is spanned by the standard generators [q]-1. -/
theorem zcCompletedGroupAlgebraStageAugmentationIdeal_span_standardGenerators_eq_top
    (i : ZCCompletedGroupAlgebraIndex C H) :
    Submodule.span (ZCCompletedGroupAlgebraStage C H i)
      (Set.range (zcCompletedGroupAlgebraStageAugmentationGeneratorSubtype C H i)) = ⊤ := by
  let : Fact (0 < i.1.modulus) := ⟨i.1.positive⟩
  change
    Submodule.span
      (MonoidAlgebra (ModNCompletedCoeff i.1.modulus)
        (CompletedGroupAlgebraQuotientInClass H C i.2))
      (Set.range
        (CompletedGroupAlgebra.groupAlgebraAugmentationGeneratorSubtype
          (ModNCompletedCoeff i.1.modulus)
          (CompletedGroupAlgebraQuotientInClass H C i.2))) = ⊤
  simpa [zcCompletedGroupAlgebraStageAugmentationGeneratorSubtype,
    zcCompletedGroupAlgebraStageAugmentationGenerator,
    zcCompletedGroupAlgebraStageAugmentationIdeal,
    modNCompletedGroupAlgebraStageAugmentationInClass,
    CompletedGroupAlgebra.groupAlgebraAugmentationGeneratorSubtype,
    CompletedGroupAlgebra.groupAlgebraAugmentationGenerator,
    CompletedGroupAlgebra.groupAlgebraAugmentationIdeal,
    CompletedGroupAlgebra.groupAlgebraAugmentation] using
    CompletedGroupAlgebra.groupAlgebraAugmentationGeneratorSubtype_span_eq_top
      (ModNCompletedCoeff i.1.modulus)
      (CompletedGroupAlgebraQuotientInClass H C i.2)

/-- Transition maps preserve the finite-stage augmentation ideals. -/
def zcCompletedGroupAlgebraStageAugmentationIdealTransition
    {i j : ZCCompletedGroupAlgebraIndex C H} (hij : i ≤ j) :
    zcCompletedGroupAlgebraStageAugmentationIdeal C H j →
      zcCompletedGroupAlgebraStageAugmentationIdeal C H i := by
  intro x
  refine ⟨zcCompletedGroupAlgebraTransition C H hij x.1, ?_⟩
  rw [mem_zcCompletedGroupAlgebraStageAugmentationIdeal_iff]
  let : Fact (0 < i.1.modulus) := ⟨i.1.positive⟩
  let : Fact (0 < j.1.modulus) := ⟨j.1.positive⟩
  have hx0 :
      modNCompletedGroupAlgebraStageAugmentationInClass j.1.modulus H C j.2 x.1 = 0 :=
    (mem_zcCompletedGroupAlgebraStageAugmentationIdeal_iff
      (C := C) (H := H) (i := j) (x := x.1)).1 x.2
  change modNCompletedGroupAlgebraStageAugmentationInClass i.1.modulus H C i.2
      (zcCompletedGroupAlgebraTransition C H hij x.1) = 0
  rw [zcCompletedGroupAlgebraTransition, RingHom.comp_apply]
  calc
    modNCompletedGroupAlgebraStageAugmentationInClass i.1.modulus H C i.2
        ((modNCompletedGroupAlgebraStageCoeffMapInClass
          (n := i.1.modulus) (m := j.1.modulus) (G := H) C i.2 hij.1)
          (modNCompletedGroupAlgebraTransitionInClass
            (n := j.1.modulus) (G := H) C hij.2 x.1))
        =
      modNCompletedCoeffMap (n := i.1.modulus) (m := j.1.modulus) hij.1
        (modNCompletedGroupAlgebraStageAugmentationInClass j.1.modulus H C i.2
          (modNCompletedGroupAlgebraTransitionInClass
            (n := j.1.modulus) (G := H) C hij.2 x.1)) := by
        exact congrFun
          (congrArg DFunLike.coe
            (modNCompletedGroupAlgebraStageAugmentationInClass_comp_stageCoeffMap
              (n := i.1.modulus) (m := j.1.modulus) (G := H) C i.2 hij.1))
          (modNCompletedGroupAlgebraTransitionInClass
            (n := j.1.modulus) (G := H) C hij.2 x.1)
    _ =
      modNCompletedCoeffMap (n := i.1.modulus) (m := j.1.modulus) hij.1
        (modNCompletedGroupAlgebraStageAugmentationInClass j.1.modulus H C j.2 x.1) := by
        have hquot := congrFun
          (congrArg DFunLike.coe
            (modNCompletedGroupAlgebraStageAugmentationInClass_compatible
              (n := j.1.modulus) (G := H) C hij.2)) x.1
        rw [RingHom.comp_apply] at hquot
        rw [hquot]
    _ = 0 := by
        rw [hx0]
        exact map_zero _

/--
The transition map between finite-stage augmentation ideals is evaluated by the corresponding
stage transition.
-/
@[simp]
theorem zcCompletedGroupAlgebraStageAugmentationIdealTransition_val
    {i j : ZCCompletedGroupAlgebraIndex C H} (hij : i ≤ j)
    (x : zcCompletedGroupAlgebraStageAugmentationIdeal C H j) :
    ((zcCompletedGroupAlgebraStageAugmentationIdealTransition
        (C := C) (H := H) hij x :
      ZCCompletedGroupAlgebraStage C H i)) =
      zcCompletedGroupAlgebraTransition C H hij x.1 :=
  rfl

/--
The inverse system of finite-stage augmentation ideals of \(\mathbb{Z}_C\llbracket
H\rrbracket\).
-/
def zcCompletedGroupAlgebraAugmentationIdealStageSystem :
    InverseSystem (I := ZCCompletedGroupAlgebraIndex C H) where
  X := fun i => zcCompletedGroupAlgebraStageAugmentationIdeal C H i
  topologicalSpace := fun _ => ⊥
  map := fun {i j} hij =>
    zcCompletedGroupAlgebraStageAugmentationIdealTransition (C := C) (H := H) hij
  continuous_map := by
    intro i j hij
    let : TopologicalSpace (zcCompletedGroupAlgebraStageAugmentationIdeal C H i) := ⊥
    let : TopologicalSpace (zcCompletedGroupAlgebraStageAugmentationIdeal C H j) := ⊥
    let : DiscreteTopology (zcCompletedGroupAlgebraStageAugmentationIdeal C H j) := ⟨rfl⟩
    exact continuous_of_discreteTopology
  map_id := by
    intro i
    funext x
    apply Subtype.ext
    exact congrFun
      (congrArg DFunLike.coe
        (zcCompletedGroupAlgebraTransition_id C H i)) x.1
  map_comp := by
    intro i j k hij hjk
    funext x
    apply Subtype.ext
    exact congrFun
      (congrArg DFunLike.coe
        (zcCompletedGroupAlgebraTransition_comp C H hij hjk)) x.1

/-- Compatible inverse-limit families of finite-stage augmentation-ideal elements. -/
abbrev ZCCompletedGroupAlgebraAugmentationIdealStageFamily : Type u :=
  (zcCompletedGroupAlgebraAugmentationIdealStageSystem C H).inverseLimit

variable [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]

/-- A completed augmentation-ideal element projects to a finite-stage augmentation ideal. -/
def zcCompletedGroupAlgebraAugmentationIdealProjection
    (i : ZCCompletedGroupAlgebraIndex C H) :
    ZCCompletedGroupAlgebraAugmentationIdeal C H →
      zcCompletedGroupAlgebraStageAugmentationIdeal C H i := by
  intro x
  refine ⟨zcCompletedGroupAlgebraProjection C H i x.1, ?_⟩
  rw [mem_zcCompletedGroupAlgebraStageAugmentationIdeal_iff]
  rw [← proCIntegerProj_zcCompletedGroupAlgebraAugmentation_eq_stage C H i x.1]
  have hx0 := congrArg (proCIntegerProj (C := C) i.1)
    ((mem_zcCompletedGroupAlgebraAugmentationIdeal_iff
      (C := C) (H := H) (x := x.1)).1 x.2)
  simpa using hx0

/--
The value of the augmentation-ideal projection is the value of the corresponding finite-stage
projection.
-/
@[simp]
theorem zcCompletedGroupAlgebraAugmentationIdealProjection_val
    (i : ZCCompletedGroupAlgebraIndex C H)
    (x : ZCCompletedGroupAlgebraAugmentationIdeal C H) :
    ((zcCompletedGroupAlgebraAugmentationIdealProjection C H i x :
      ZCCompletedGroupAlgebraStage C H i)) =
      zcCompletedGroupAlgebraProjection C H i x.1 :=
  rfl

/-- Finite-stage projections of a completed augmentation-ideal point are compatible. -/
theorem zcCompletedGroupAlgebraAugmentationIdealProjection_transition
    {i j : ZCCompletedGroupAlgebraIndex C H} (hij : i ≤ j)
    (x : ZCCompletedGroupAlgebraAugmentationIdeal C H) :
    zcCompletedGroupAlgebraStageAugmentationIdealTransition C H hij
        (zcCompletedGroupAlgebraAugmentationIdealProjection C H j x) =
      zcCompletedGroupAlgebraAugmentationIdealProjection C H i x := by
  apply Subtype.ext
  exact x.1.2 i j hij

/-- A completed augmentation-ideal point determines its compatible finite-stage family. -/
def zcCompletedGroupAlgebraAugmentationIdealToStageFamily :
    ZCCompletedGroupAlgebraAugmentationIdeal C H →
      ZCCompletedGroupAlgebraAugmentationIdealStageFamily C H := by
  intro x
  refine ⟨fun i => zcCompletedGroupAlgebraAugmentationIdealProjection C H i x, ?_⟩
  intro i j hij
  exact zcCompletedGroupAlgebraAugmentationIdealProjection_transition C H hij x

/--
The stage family associated to a completed augmentation-ideal element evaluates at `i` as its
augmentation-ideal projection at `i`.
-/
@[simp]
theorem zcCompletedGroupAlgebraAugmentationIdealToStageFamily_apply
    (x : ZCCompletedGroupAlgebraAugmentationIdeal C H)
    (i : ZCCompletedGroupAlgebraIndex C H) :
    (zcCompletedGroupAlgebraAugmentationIdealToStageFamily C H x).1 i =
      zcCompletedGroupAlgebraAugmentationIdealProjection C H i x :=
  rfl

/--
A compatible family of finite-stage augmentation-ideal points determines a completed
augmentation-ideal point.
-/
def zcCompletedGroupAlgebraAugmentationIdealOfStageFamily :
    ZCCompletedGroupAlgebraAugmentationIdealStageFamily C H →
      ZCCompletedGroupAlgebraAugmentationIdeal C H := by
  intro x
  let y : ZCCompletedGroupAlgebra C H :=
    ⟨fun i => (x.1 i).1, by
      intro i j hij
      exact congrArg Subtype.val (x.2 i j hij)⟩
  refine ⟨y, ?_⟩
  rw [mem_zcCompletedGroupAlgebraAugmentationIdeal_iff]
  ext i
  let T := zcCompletedGroupAlgebraTopIndex C H
  let : Fact (0 < i.modulus) := ⟨i.positive⟩
  change
    modNCompletedGroupAlgebraStageAugmentationInClass i.modulus H C T
        ((x.1 (i, T)).1) = 0
  exact (mem_zcCompletedGroupAlgebraStageAugmentationIdeal_iff
    (C := C) (H := H) (i := (i, T)) (x := (x.1 (i, T)).1)).1 (x.1 (i, T)).2

/--
The augmentation-ideal projection of a stage-family element is the corresponding finite-stage
coordinate.
-/
@[simp]
theorem zcCompletedGroupAlgebraAugmentationIdealProjection_ofStageFamily
    (x : ZCCompletedGroupAlgebraAugmentationIdealStageFamily C H)
    (i : ZCCompletedGroupAlgebraIndex C H) :
    zcCompletedGroupAlgebraAugmentationIdealProjection C H i
        (zcCompletedGroupAlgebraAugmentationIdealOfStageFamily C H x) =
      x.1 i := by
  apply Subtype.ext
  rfl

/--
Converting an augmentation-ideal stage family to its underlying stage family recovers the same
compatible coordinates.
-/
@[simp]
theorem zcCompletedGroupAlgebraAugmentationIdealOfStageFamily_toStageFamily
    (x : ZCCompletedGroupAlgebraAugmentationIdeal C H) :
    zcCompletedGroupAlgebraAugmentationIdealOfStageFamily C H
        (zcCompletedGroupAlgebraAugmentationIdealToStageFamily C H x) = x := by
  apply Subtype.ext
  apply Subtype.ext
  funext i
  rfl

/--
Converting a stage-family element to the completed augmentation ideal and back preserves its
finite-stage coordinates.
-/
@[simp]
theorem zcCompletedGroupAlgebraAugmentationIdealToStageFamily_ofStageFamily
    (x : ZCCompletedGroupAlgebraAugmentationIdealStageFamily C H) :
    zcCompletedGroupAlgebraAugmentationIdealToStageFamily C H
        (zcCompletedGroupAlgebraAugmentationIdealOfStageFamily C H x) = x := by
  apply Subtype.ext
  funext i
  apply Subtype.ext
  rfl

/--
The completed augmentation ideal is the inverse limit of its finite-stage augmentation ideals.
-/
def zcCompletedGroupAlgebraAugmentationIdealStageFamilyEquiv :
    ZCCompletedGroupAlgebraAugmentationIdeal C H ≃
      ZCCompletedGroupAlgebraAugmentationIdealStageFamily C H where
  toFun := zcCompletedGroupAlgebraAugmentationIdealToStageFamily C H
  invFun := zcCompletedGroupAlgebraAugmentationIdealOfStageFamily C H
  left_inv := zcCompletedGroupAlgebraAugmentationIdealOfStageFamily_toStageFamily C H
  right_inv := zcCompletedGroupAlgebraAugmentationIdealToStageFamily_ofStageFamily C H

end FiniteStageAugmentationIdeal

end

end FoxDifferential
