/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Ramification.ProfiniteInertiaMap
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Topology.Algebra.MulAction

/-!
# A data-only boundary for profinite ring-action restrictions

The diagram stores ordinary ring/group/action/map/topology data only. In
particular it stores no equivariance, invariance, surjectivity, contraction,
stabilizer-image, or inertia-image proof. These facts must be proved for a
concrete diagram before the ordinary image theorem can be applied.
-/

noncomputable section

namespace SchemeTheory

open scoped Pointwise

universe u v w x

/-- Ordinary data for a restriction of ring actions. No comparison or
image theorem is part of this structure. -/
structure RingActionRestriction where
  /-- The lower ring. -/
  lowerRing : CommRingCat.{u}
  /-- The upper ring. -/
  upperRing : CommRingCat.{v}
  /-- The upper acting group. -/
  upperGroup : GrpCat.{w}
  /-- The lower acting group. -/
  lowerGroup : GrpCat.{x}
  /-- The prescribed action on the upper ring. -/
  upperAction : MulSemiringAction upperGroup.carrier upperRing.carrier
  /-- The prescribed action on the lower ring. -/
  lowerAction : MulSemiringAction lowerGroup.carrier lowerRing.carrier
  /-- The literal coefficient inclusion. -/
  ringMap : lowerRing.carrier →+* upperRing.carrier
  /-- The prescribed group restriction. -/
  groupMap : upperGroup.carrier →* lowerGroup.carrier
  /-- The subgroup that will correct lifts. -/
  kernelGroup : Subgroup upperGroup.carrier
  /-- Its prescribed topology. -/
  kernelTopology : TopologicalSpace kernelGroup

namespace RingActionRestriction

/-- Upper inertia for the diagram's prescribed action. -/
def upperInertia (D : RingActionRestriction) (q : Ideal D.upperRing.carrier) :
    Subgroup D.upperGroup.carrier :=
  let : MulSemiringAction D.upperGroup.carrier D.upperRing.carrier := D.upperAction
  q.inertia D.upperGroup.carrier

/-- Lower inertia for the diagram's prescribed action. -/
def lowerInertia (D : RingActionRestriction) (p : Ideal D.lowerRing.carrier) :
    Subgroup D.lowerGroup.carrier :=
  let : MulSemiringAction D.lowerGroup.carrier D.lowerRing.carrier := D.lowerAction
  p.inertia D.lowerGroup.carrier

/-- Upper decomposition group for the prescribed action. -/
def upperDecomposition (D : RingActionRestriction) (q : Ideal D.upperRing.carrier) :
    Subgroup D.upperGroup.carrier :=
  let : MulSemiringAction D.upperGroup.carrier D.upperRing.carrier := D.upperAction
  MulAction.stabilizer D.upperGroup.carrier q

/-- Lower decomposition group for the prescribed action. -/
def lowerDecomposition (D : RingActionRestriction) (p : Ideal D.lowerRing.carrier) :
    Subgroup D.lowerGroup.carrier :=
  let : MulSemiringAction D.lowerGroup.carrier D.lowerRing.carrier := D.lowerAction
  MulAction.stabilizer D.lowerGroup.carrier p

/-- Every element fixed by the prescribed kernel comes from the literal
lower coefficient map. This is a hypothesis to prove, never stored data. -/
def HasFixedPreimages (D : RingActionRestriction) : Prop :=
  let : MulSemiringAction D.upperGroup.carrier D.upperRing.carrier := D.upperAction
  ∀ b : D.upperRing.carrier,
    (∀ g : D.upperGroup.carrier, D.kernelGroup.carrier g → g • b = b) →
    ∃ a : D.lowerRing.carrier, D.ringMap.toFun a = b

/-- The actual action square, stated before introducing any ring algebra. -/
def IsEquivariant (D : RingActionRestriction) : Prop :=
  let : MulSemiringAction D.upperGroup.carrier D.upperRing.carrier := D.upperAction
  let : MulSemiringAction D.lowerGroup.carrier D.lowerRing.carrier := D.lowerAction
  ∀ g : D.upperGroup.carrier,
    D.ringMap.comp (MulSemiringAction.toRingHom D.lowerGroup.carrier D.lowerRing.carrier
        (D.groupMap.toFun g)) =
      (MulSemiringAction.toRingHom D.upperGroup.carrier D.upperRing.carrier g).comp D.ringMap

/-- Open fixed sets for the prescribed kernel topology and upper action. -/
def HasOpenFixedSets (D : RingActionRestriction) : Prop :=
  let : MulSemiringAction D.upperGroup.carrier D.upperRing.carrier := D.upperAction
  let : TopologicalSpace D.kernelGroup := D.kernelTopology
  ∀ b : D.upperRing.carrier, IsOpen (fun g : D.kernelGroup => (g : D.upperGroup.carrier) • b = b)

/-- The literal ring-map algebra has precisely the supplied fixed preimages. -/
private theorem isInvariant_of_fixedPreimages (D : RingActionRestriction)
    (hfixed : D.HasFixedPreimages) :
    let : MulSemiringAction D.upperGroup.carrier D.upperRing.carrier := D.upperAction
    let : Algebra D.lowerRing.carrier D.upperRing.carrier := D.ringMap.toAlgebra
    Algebra.IsInvariant D.lowerRing.carrier D.upperRing.carrier D.kernelGroup := by
  intro upperAction ringAlgebra
  constructor
  intro b hb
  exact hfixed b (fun g hg => hb ⟨g, hg⟩)

/-- The literal ring-map algebra realizes the supplied contraction. -/
private theorem liesOver_of_contraction (D : RingActionRestriction)
    (p : Ideal D.lowerRing.carrier) (q : Ideal D.upperRing.carrier)
    (hcontract : ∀ a : D.lowerRing.carrier, p.carrier a ↔ q.carrier (D.ringMap.toFun a)) :
    let : Algebra D.lowerRing.carrier D.upperRing.carrier := D.ringMap.toAlgebra
    q.LiesOver p := by
  intro ringAlgebra
  constructor
  apply Ideal.ext
  intro a
  exact hcontract a

/-- Open fixed sets give continuity for the prescribed kernel action on
its discrete coefficient ring, without the lower group or ring algebra. -/
private theorem continuousSMul_of_openFixedSets (D : RingActionRestriction)
    (hopen : D.HasOpenFixedSets) :
    let : MulSemiringAction D.upperGroup.carrier D.upperRing.carrier := D.upperAction
    let : TopologicalSpace D.kernelGroup := D.kernelTopology
    let : TopologicalSpace D.upperRing.carrier := ⊥
    IsTopologicalGroup D.kernelGroup → ContinuousSMul D.kernelGroup D.upperRing.carrier := by
  intro upperAction kernelTopology ringTopology htopological
  have : DiscreteTopology D.upperRing.carrier := ⟨rfl⟩
  exact continuousSMul_iff_stabilizer_isOpen.mpr hopen

/-- A compact zero-dimensional correcting kernel gives both decomposition
and inertia images. The only scalar extension and discrete ring topology
are introduced here, after every field constructor has been eliminated. -/
theorem images_of_profinite (D : RingActionRestriction)
    (p : Ideal D.lowerRing.carrier) (q : Ideal D.upperRing.carrier) [hq : q.IsPrime] :
    let : TopologicalSpace D.kernelGroup := D.kernelTopology
    CompactSpace D.kernelGroup → TotallyDisconnectedSpace D.kernelGroup →
    IsTopologicalGroup D.kernelGroup →
    (∀ a : D.lowerRing.carrier, p.carrier a ↔ q.carrier (D.ringMap.toFun a)) →
    D.HasFixedPreimages → D.HasOpenFixedSets →
    Function.Surjective D.groupMap.toFun →
    (∀ g : D.upperGroup.carrier, D.kernelGroup.carrier g → D.groupMap.toFun g = 1) →
    D.IsEquivariant →
    (D.upperDecomposition q).map D.groupMap = D.lowerDecomposition p ∧
      (D.upperInertia q).map D.groupMap = D.lowerInertia p := by
  intro kernelTopology hcompact hdisconnected htopological
    hcontract hfixed hopen hsurj hker hequiv
  let : MulSemiringAction D.upperGroup.carrier D.upperRing.carrier := D.upperAction
  let : MulSemiringAction D.lowerGroup.carrier D.lowerRing.carrier := D.lowerAction
  let : Algebra D.lowerRing.carrier D.upperRing.carrier := D.ringMap.toAlgebra
  let : TopologicalSpace D.upperRing.carrier := ⊥
  have : DiscreteTopology D.upperRing.carrier := ⟨rfl⟩
  have hcontinuous := continuousSMul_of_openFixedSets D hopen htopological
  have hinvariant := isInvariant_of_fixedPreimages D hfixed
  have hover := liesOver_of_contraction D p q hcontract
  have hcomm (g : D.upperGroup.carrier) (a : D.lowerRing.carrier) :=
    congrArg (fun j : D.lowerRing.carrier →+* D.upperRing.carrier => j.toFun a)
      (hequiv g)
  exact ⟨map_stabilizer_of_surjective_of_profinite D.groupMap D.kernelGroup p q
      hsurj (fun g hg => hker g hg) hcomm,
    map_inertia_of_surjective_of_profinite D.groupMap D.kernelGroup p q
      hsurj (fun g hg => hker g hg) hcomm⟩

end RingActionRestriction

end SchemeTheory
