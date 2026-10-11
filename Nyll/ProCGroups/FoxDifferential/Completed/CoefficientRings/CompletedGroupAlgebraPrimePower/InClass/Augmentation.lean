/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraPrimePower.InClass.System.Ring.Projection

/-!
# Fox differential: coefficient rings — prime-power completed group algebra — in class —
augmentation

The principal declarations in this module are:

- `primePowerCompletedCoeffSystemInClass`
  The class-restricted coefficient inverse system indexed by \(i = (a,U)\), whose coefficient stage
  is \(\mathrm{ZMod}\,(\ell^a)\).
- `PrimePowerCompletedCoeffCompatibleInClass`
  Compatibility for the class-indexed coefficient tower; the finite quotient component is retained
  only to match the surrounding pro-\(C\) index shape.
- `primePowerCompletedCoeffProjectionInClass_zero`
  The finite-stage projection sends \(0\) to \(0\).
- `primePowerCompletedCoeffProjectionInClass_add`
  The class-indexed prime-power coefficient projection preserves addition.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u

variable (ℓ : ℕ) [Fact (0 < ℓ)]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/--
The class-restricted coefficient inverse system indexed by \(i = (a,U)\), whose coefficient
stage is \(\mathrm{ZMod}\,(\ell^a)\).
-/
def primePowerCompletedCoeffSystemInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    InverseSystem (I := PrimePowerCompletedGroupAlgebraIndexInClass G C) where
  X := fun i => ModNCompletedCoeff (ℓ ^ i.1)
  topologicalSpace := fun _ => ⊥
  map := fun {i j} hij =>
    modNCompletedCoeffMap
      (n := ℓ ^ i.1) (m := ℓ ^ j.1)
      (primePow_dvd_primePow (ℓ := ℓ) hij.1)
  continuous_map := by
    intro i j hij
    let : TopologicalSpace (ModNCompletedCoeff (ℓ ^ i.1)) := ⊥
    let : TopologicalSpace (ModNCompletedCoeff (ℓ ^ j.1)) := ⊥
    let : DiscreteTopology (ModNCompletedCoeff (ℓ ^ j.1)) := ⟨rfl⟩
    exact continuous_of_discreteTopology
  map_id := by
    intro i
    funext x
    exact congrFun
      (congrArg DFunLike.coe
        (modNCompletedCoeffMap_rfl (n := ℓ ^ i.1))) x
  map_comp := by
    intro i j k hij hjk
    funext x
    exact congrFun
      (congrArg DFunLike.coe
        (modNCompletedCoeffMap_comp
          (n := ℓ ^ i.1) (m := ℓ ^ j.1) (k := ℓ ^ k.1)
          (primePow_dvd_primePow (ℓ := ℓ) hij.1)
          (primePow_dvd_primePow (ℓ := ℓ) hjk.1))) x

/--
Compatibility for the class-indexed coefficient tower; the finite quotient component is retained
only to match the surrounding pro-\(C\) index shape.
-/
def PrimePowerCompletedCoeffCompatibleInClass
    (C : ProCGroups.FiniteGroupClass.{u})
    (x : ∀ i : PrimePowerCompletedGroupAlgebraIndexInClass G C,
      ModNCompletedCoeff (ℓ ^ i.1)) : Prop :=
  (primePowerCompletedCoeffSystemInClass ℓ G C).Compatible x

/-- The pro-\(C\)-indexed prime-power completed coefficient inverse limit. -/
abbrev PrimePowerCompletedCoeffInClass (C : ProCGroups.FiniteGroupClass.{u}) : Type _ :=
  {x : ∀ i : PrimePowerCompletedGroupAlgebraIndexInClass G C,
      ModNCompletedCoeff (ℓ ^ i.1) //
    PrimePowerCompletedCoeffCompatibleInClass (ℓ := ℓ) (G := G) C x}

/-- The projection from the pro-\(C\)-indexed coefficient limit to one finite stage. -/
def primePowerCompletedCoeffProjectionInClass
    (C : ProCGroups.FiniteGroupClass.{u}) (i : PrimePowerCompletedGroupAlgebraIndexInClass G C) :
    PrimePowerCompletedCoeffInClass ℓ G C → ModNCompletedCoeff (ℓ ^ i.1) :=
  (primePowerCompletedCoeffSystemInClass ℓ G C).projection i

/--
The zero element of the class-indexed prime-power completed coefficient ring is the compatible
family of finite-stage zero elements.
-/
instance instZeroPrimePowerCompletedCoeffInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    Zero (PrimePowerCompletedCoeffInClass ℓ G C) where
  zero := ⟨fun _ => 0, by
    dsimp [PrimePowerCompletedCoeffCompatibleInClass]
    intro i j hij
    exact map_zero
      (modNCompletedCoeffMap
        (n := ℓ ^ i.1) (m := ℓ ^ j.1)
        (primePow_dvd_primePow (ℓ := ℓ) hij.1))⟩

/--
Addition in the prime-power completed coefficient ring is defined coordinatewise through
finite-stage coefficient additions.
-/
instance instAddPrimePowerCompletedCoeffInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    Add (PrimePowerCompletedCoeffInClass ℓ G C) where
  add x y := ⟨fun i =>
      (show ZMod (ℓ ^ i.1) from x.1 i) + (show ZMod (ℓ ^ i.1) from y.1 i), by
    dsimp [PrimePowerCompletedCoeffCompatibleInClass]
    intro i j hij
    change modNCompletedCoeffMap
        (n := ℓ ^ i.1) (m := ℓ ^ j.1)
        (primePow_dvd_primePow (ℓ := ℓ) hij.1)
        ((show ZMod (ℓ ^ j.1) from x.1 j) + (show ZMod (ℓ ^ j.1) from y.1 j)) =
      (show ZMod (ℓ ^ i.1) from x.1 i) + (show ZMod (ℓ ^ i.1) from y.1 i)
    rw [map_add]
    exact congrArg₂ HAdd.hAdd (x.2 i j hij) (y.2 i j hij)⟩

/--
Negation on the class-indexed prime-power completed coefficient ring is defined coordinatewise
through finite-stage coefficient negations.
-/
instance instNegPrimePowerCompletedCoeffInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    Neg (PrimePowerCompletedCoeffInClass ℓ G C) where
  neg x := ⟨fun i => -(show ZMod (ℓ ^ i.1) from x.1 i), by
    dsimp [PrimePowerCompletedCoeffCompatibleInClass]
    intro i j hij
    change modNCompletedCoeffMap
        (n := ℓ ^ i.1) (m := ℓ ^ j.1)
        (primePow_dvd_primePow (ℓ := ℓ) hij.1)
        (-(show ZMod (ℓ ^ j.1) from x.1 j)) =
      -(show ZMod (ℓ ^ i.1) from x.1 i)
    rw [map_neg]
    exact congrArg Neg.neg (x.2 i j hij)⟩

/--
Subtraction in the class-indexed prime-power completed coefficient ring is defined
coordinatewise through finite-stage coefficient-ring subtractions.
-/
instance instSubPrimePowerCompletedCoeffInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    Sub (PrimePowerCompletedCoeffInClass ℓ G C) where
  sub x y := ⟨fun i =>
      (show ZMod (ℓ ^ i.1) from x.1 i) - (show ZMod (ℓ ^ i.1) from y.1 i), by
    dsimp [PrimePowerCompletedCoeffCompatibleInClass]
    intro i j hij
    change modNCompletedCoeffMap
        (n := ℓ ^ i.1) (m := ℓ ^ j.1)
        (primePow_dvd_primePow (ℓ := ℓ) hij.1)
        ((show ZMod (ℓ ^ j.1) from x.1 j) - (show ZMod (ℓ ^ j.1) from y.1 j)) =
      (show ZMod (ℓ ^ i.1) from x.1 i) - (show ZMod (ℓ ^ i.1) from y.1 i)
    rw [map_sub]
    exact congrArg₂ HSub.hSub (x.2 i j hij) (y.2 i j hij)⟩

omit [Fact (0 < ℓ)] [IsTopologicalGroup G] in
/-- The finite-stage projection sends \(0\) to \(0\). -/
@[simp]
theorem primePowerCompletedCoeffProjectionInClass_zero
    (C : ProCGroups.FiniteGroupClass.{u}) (i : PrimePowerCompletedGroupAlgebraIndexInClass G C) :
    primePowerCompletedCoeffProjectionInClass (ℓ := ℓ) (G := G) C i
        (0 : PrimePowerCompletedCoeffInClass ℓ G C) = 0 := by
  rfl

omit [Fact (0 < ℓ)] [IsTopologicalGroup G] in
/-- The class-indexed prime-power coefficient projection preserves addition. -/
@[simp]
theorem primePowerCompletedCoeffProjectionInClass_add
    (C : ProCGroups.FiniteGroupClass.{u}) (i : PrimePowerCompletedGroupAlgebraIndexInClass G C)
    (x y : PrimePowerCompletedCoeffInClass ℓ G C) :
    primePowerCompletedCoeffProjectionInClass (ℓ := ℓ) (G := G) C i (x + y) =
      primePowerCompletedCoeffProjectionInClass (ℓ := ℓ) (G := G) C i x +
        primePowerCompletedCoeffProjectionInClass (ℓ := ℓ) (G := G) C i y := by
  rfl

omit [Fact (0 < ℓ)] [IsTopologicalGroup G] in
/-- The class-indexed prime-power coefficient projection preserves negation. -/
@[simp]
theorem primePowerCompletedCoeffProjectionInClass_neg
    (C : ProCGroups.FiniteGroupClass.{u}) (i : PrimePowerCompletedGroupAlgebraIndexInClass G C)
    (x : PrimePowerCompletedCoeffInClass ℓ G C) :
    primePowerCompletedCoeffProjectionInClass (ℓ := ℓ) (G := G) C i (-x) =
      -primePowerCompletedCoeffProjectionInClass (ℓ := ℓ) (G := G) C i x := by
  rfl

omit [Fact (0 < ℓ)] [IsTopologicalGroup G] in
/-- The class-indexed prime-power coefficient projection preserves subtraction. -/
@[simp]
theorem primePowerCompletedCoeffProjectionInClass_sub
    (C : ProCGroups.FiniteGroupClass.{u}) (i : PrimePowerCompletedGroupAlgebraIndexInClass G C)
    (x y : PrimePowerCompletedCoeffInClass ℓ G C) :
    primePowerCompletedCoeffProjectionInClass (ℓ := ℓ) (G := G) C i (x - y) =
      primePowerCompletedCoeffProjectionInClass (ℓ := ℓ) (G := G) C i x -
        primePowerCompletedCoeffProjectionInClass (ℓ := ℓ) (G := G) C i y := by
  rfl

/--
The class-restricted prime-power completed group algebra carries a canonical augmentation to the
pro-\(C\)-indexed coefficient limit.
-/
def primePowerCompletedGroupAlgebraAugmentationInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    PrimePowerCompletedGroupAlgebraInClass ℓ G C →
      PrimePowerCompletedCoeffInClass ℓ G C := by
  intro x
  refine ⟨fun i => ?_, ?_⟩
  · exact modNCompletedGroupAlgebraStageAugmentationInClass (ℓ ^ i.1) G C i.2 (x.1 i)
  · dsimp [PrimePowerCompletedCoeffCompatibleInClass]
    intro i j hij
    calc
      modNCompletedCoeffMap
          (n := ℓ ^ i.1) (m := ℓ ^ j.1)
          (primePow_dvd_primePow (ℓ := ℓ) hij.1)
          (modNCompletedGroupAlgebraStageAugmentationInClass (ℓ ^ j.1) G C j.2 (x.1 j))
        =
      modNCompletedGroupAlgebraStageAugmentationInClass (ℓ ^ i.1) G C i.2
        (primePowerCompletedGroupAlgebraTransitionInClass
          (ℓ := ℓ) (G := G) C hij (x.1 j)) := by
          symm
          exact congrFun
            (congrArg DFunLike.coe
              (primePowerCompletedGroupAlgebraStageAugmentationInClass_comp_transition
                (ℓ := ℓ) (G := G) C hij)) (x.1 j)
      _ =
      modNCompletedGroupAlgebraStageAugmentationInClass (ℓ ^ i.1) G C i.2 (x.1 i) := by
          have hx :
              primePowerCompletedGroupAlgebraTransitionInClass (ℓ := ℓ) (G := G) C hij
                  (x.1 j) = x.1 i :=
            x.2 i j hij
          exact congrArg
            (modNCompletedGroupAlgebraStageAugmentationInClass (ℓ ^ i.1) G C i.2) hx

omit [Fact (0 < ℓ)] in
/--
Projecting the class-indexed prime-power completed augmentation to a coefficient stage agrees
with the corresponding finite-stage augmentation.
-/
@[simp]
theorem primePowerCompletedCoeffProjectionInClass_augmentation
    (C : ProCGroups.FiniteGroupClass.{u}) (i : PrimePowerCompletedGroupAlgebraIndexInClass G C)
    (x : PrimePowerCompletedGroupAlgebraInClass ℓ G C) :
    primePowerCompletedCoeffProjectionInClass (ℓ := ℓ) (G := G) C i
        (primePowerCompletedGroupAlgebraAugmentationInClass (ℓ := ℓ) (G := G) C x) =
      modNCompletedGroupAlgebraStageAugmentationInClass (ℓ ^ i.1) G C i.2
        (primePowerCompletedGroupAlgebraProjectionInClass (ℓ := ℓ) (G := G) C i x) := rfl

omit [Fact (0 < ℓ)] in
/--
The class-indexed completed group-algebra augmentation has a canonical section, obtained by
placing each compatible coefficient system on the identity monomial at every finite stage.
-/
theorem primePowerCompletedGroupAlgebraAugmentationInClass_surjective
    (C : ProCGroups.FiniteGroupClass.{u}) :
    Function.Surjective
      (primePowerCompletedGroupAlgebraAugmentationInClass (ℓ := ℓ) (G := G) C) := by
  intro x
  refine ⟨⟨fun i => ?_, ?_⟩, ?_⟩
  · exact MonoidAlgebra.single
      (1 : CompletedGroupAlgebraQuotientInClass G C i.2) (x.1 i)
  · intro i j hij
    change
      primePowerCompletedGroupAlgebraTransitionInClass (ℓ := ℓ) (G := G) C hij
          (MonoidAlgebra.single
            (1 : CompletedGroupAlgebraQuotientInClass G C j.2) (x.1 j)) =
        MonoidAlgebra.single
          (1 : CompletedGroupAlgebraQuotientInClass G C i.2) (x.1 i)
    rw [primePowerCompletedGroupAlgebraTransitionInClass_single]
    have hmapone :
        (OpenNormalSubgroupInClass.map
          (C := C) (G := G)
          (U := OrderDual.ofDual i.2) (V := OrderDual.ofDual j.2) hij.2)
            (1 : CompletedGroupAlgebraQuotientInClass G C j.2) = 1 :=
      (OpenNormalSubgroupInClass.map
        (C := C) (G := G)
        (U := OrderDual.ofDual i.2) (V := OrderDual.ofDual j.2) hij.2).map_one
    rw [hmapone]
    have hxcoeff :
        modNCompletedCoeffMap
          (n := ℓ ^ i.1) (m := ℓ ^ j.1)
          (primePow_dvd_primePow (ℓ := ℓ) hij.1) (x.1 j) = x.1 i := by
      simpa [primePowerCompletedCoeffSystemInClass] using x.2 i j hij
    exact congrArg
      (fun a : ModNCompletedCoeff (ℓ ^ i.1) =>
        MonoidAlgebra.single
          (1 : CompletedGroupAlgebraQuotientInClass G C i.2) a)
      hxcoeff
  · apply Subtype.ext
    funext i
    change
      modNCompletedGroupAlgebraStageAugmentationInClass (ℓ ^ i.1) G C i.2
          (MonoidAlgebra.single
            (1 : CompletedGroupAlgebraQuotientInClass G C i.2) (x.1 i)) =
        x.1 i
    simp only [modNCompletedGroupAlgebraStageAugmentationInClass_single]


end

end FoxDifferential
