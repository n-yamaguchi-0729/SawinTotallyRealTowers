/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.ProP.FiniteTransgressionLinear
import Nyll.GaloisCohomology.ProP.FreeProPH2Cocycle
import Nyll.ProCGroups.ProP.ContinuousH1
import Nyll.ProCGroups.FiniteGroups.StandardClasses
import Nyll.ProCGroups.ProC.OpenNormalSubgroups.ProCGroup
import Mathlib.Algebra.Field.ZMod

/-!
# Continuous transgression from an open normal subgroup

The algebraic factor-set construction in `FiniteTransgression` uses a bottom topology on its
finite quotient.  Here the same construction is made directly for the canonical quotient
topology of an open normal subgroup, so that it composes with the maintained inflation map.
-/

open CategoryTheory TopRep ContRepresentation
open scoped Topology

namespace ClassFieldTower.Cohomology

open ProCGroups ProCGroups.ProC
open ClassFieldTower.ProP

noncomputable section

universe u

variable {p : ℕ} [Fact p.Prime]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

local instance continuousTransgressionZModAddCommGroup : AddCommGroup (ZMod p) :=
  (ZMod.instField p).toDivisionRing.toAddCommGroup

local instance continuousTransgressionH1Module
    {q : ℕ} {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] :
    Module (ZMod q) (ContinuousH1ZMod (p := q) (G := H)) :=
  continuousH1ZModModule

/-- Continuous mod-`p` characters of an open normal subgroup fixed by ambient conjugation. -/
def InvariantContinuousH1
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G) :
    Submodule (ZMod p)
      (ContinuousH1ZMod (p := p) (G := (U.1 : Subgroup G))) where
  carrier := {chi | ∀ (g : G) (n : U.1),
    chi (Additive.ofMul (MulAut.conjNormal g n)) = chi (Additive.ofMul n)}
  zero_mem' := by
    intro g n
    rfl
  add_mem' := by
    intro chi psi hchi hpsi g n
    change chi _ + psi _ = chi _ + psi _
    rw [hchi g n, hpsi g n]
  smul_mem' := by
    intro a chi hchi g n
    let evConj : ContinuousH1ZMod (p := p) (G := (U.1 : Subgroup G)) →+ ZMod p :=
      { toFun := fun eta ↦ eta (Additive.ofMul (MulAut.conjNormal g n))
        map_zero' := rfl
        map_add' := fun _ _ ↦ rfl }
    let ev : ContinuousH1ZMod (p := p) (G := (U.1 : Subgroup G)) →+ ZMod p :=
      { toFun := fun eta ↦ eta (Additive.ofMul n)
        map_zero' := rfl
        map_add' := fun _ _ ↦ rfl }
    exact (ZMod.map_smul evConj a chi).trans
      ((congrArg (fun z : ZMod p ↦ a • z) (hchi g n)).trans
        (ZMod.map_smul ev a chi).symm)

/-- Forget continuity while retaining ambient conjugation invariance. -/
def invariantContinuousH1ToFiniteCharacterAddHom
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G) :
    InvariantContinuousH1 U →+
      InvariantFiniteCharacter (p := p) (U.1 : Subgroup G) where
  toFun chi := ⟨Additive.ofMul (characterOfH1 chi.1).toMonoidHom, by
    intro g n
    exact congrArg Multiplicative.ofAdd (chi.2 g n)⟩
  map_zero' := by apply Subtype.ext; rfl
  map_add' := by intros; apply Subtype.ext; rfl

/-- The canonical-topology homogeneous factor-set cochain. -/
noncomputable def continuousTransgressionHomogeneousCochain
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G)
    (chi : InvariantContinuousH1 U) :
    (trivialZModPCochainsLifted p (G ⧸ (U.1 : Subgroup G))).X 2 := by
  let sigma : C(G ⧸ (U.1 : Subgroup G),
      C(G ⧸ (U.1 : Subgroup G),
        C(G ⧸ (U.1 : Subgroup G), ULift.{u} (ZMod p)))) :=
    ⟨fun a ↦ ⟨fun b ↦ ⟨fun c ↦ ULift.up
      (transgressionFactor (U.1 : Subgroup G)
        (characterOfH1 chi.1).toMonoidHom (a⁻¹ * b) (b⁻¹ * c)),
      continuous_of_discreteTopology⟩, continuous_of_discreteTopology⟩,
      continuous_of_discreteTopology⟩
  exact ⟨sigma, by
    intro g
    apply ContinuousMap.ext
    intro a
    apply ContinuousMap.ext
    intro b
    apply ContinuousMap.ext
    intro c
    change ULift.up (transgressionFactor (U.1 : Subgroup G)
      (characterOfH1 chi.1).toMonoidHom
        ((g⁻¹ * a)⁻¹ * (g⁻¹ * b)) ((g⁻¹ * b)⁻¹ * (g⁻¹ * c))) = _
    congr 2 <;> group⟩

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
theorem continuousTransgressionHomogeneousCochain_mem_cycles
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G)
    (chi : InvariantContinuousH1 U) :
    ((trivialZModPCochainsLifted p (G ⧸ (U.1 : Subgroup G))).d 2 3).hom
      (continuousTransgressionHomogeneousCochain U chi) = 0 := by
  change _ = (0 : (TopRep.resolutionX
    (trivialZModPLifted p (G ⧸ (U.1 : Subgroup G))) 4).ρ.invariants)
  apply Subtype.ext
  ext a b c d
  have hd := TopRep.homogeneousCochains.d_apply
    (trivialZModPLifted p (G ⧸ (U.1 : Subgroup G))) 2
      (continuousTransgressionHomogeneousCochain U chi)
  have hp := congrArg (fun tau ↦ tau a b c d) hd
  rw [hp]
  simp only [Nat.reduceAdd, ZeroMemClass.coe_zero, ContinuousMap.zero_apply]
  let e : ULift.{u} (ZMod p) ≃ₗ[ZMod p] ZMod p := ULift.moduleEquiv
  apply e.injective
  change
    transgressionFactor (U.1 : Subgroup G) (characterOfH1 chi.1).toMonoidHom
        (b⁻¹ * c) (c⁻¹ * d) -
      (transgressionFactor (U.1 : Subgroup G) (characterOfH1 chi.1).toMonoidHom
          (a⁻¹ * c) (c⁻¹ * d) -
        (transgressionFactor (U.1 : Subgroup G) (characterOfH1 chi.1).toMonoidHom
            (a⁻¹ * b) (b⁻¹ * d) -
          transgressionFactor (U.1 : Subgroup G) (characterOfH1 chi.1).toMonoidHom
            (a⁻¹ * b) (b⁻¹ * c))) = 0
  have h := transgressionFactor_cocycle (U.1 : Subgroup G)
    (characterOfH1 chi.1).toMonoidHom
    (fun g n ↦ congrArg Multiplicative.ofAdd (chi.2 g n))
    (a⁻¹ * b) (b⁻¹ * c) (c⁻¹ * d)
  simp only [show (a⁻¹ * b) * (b⁻¹ * c) = a⁻¹ * c by group,
    show (b⁻¹ * c) * (c⁻¹ * d) = b⁻¹ * d by group] at h
  abel_nf at h ⊢
  exact h

/-- The canonical-topology factor-set cocycle. -/
noncomputable def continuousTransgressionHomogeneousCocycle
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G)
    (chi : InvariantContinuousH1 U) :
    trivialZModPCocyclesLifted p (G ⧸ (U.1 : Subgroup G)) 2 :=
  homogeneousCocycleOfElement
    (trivialZModPLifted p (G ⧸ (U.1 : Subgroup G))) 2
    (continuousTransgressionHomogeneousCochain U chi)
    (continuousTransgressionHomogeneousCochain_mem_cycles U chi)

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
@[simp]
theorem iCycles_continuousTransgressionHomogeneousCocycle
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G)
    (chi : InvariantContinuousH1 U) :
    (trivialZModPCochainsLifted p (G ⧸ (U.1 : Subgroup G))).iCycles 2
      (continuousTransgressionHomogeneousCocycle U chi) =
        continuousTransgressionHomogeneousCochain U chi :=
  iCycles_homogeneousCocycleOfElement _ _ _ _

/-- Continuous transgression as a degree-two cohomology class. -/
noncomputable def continuousTransgressionClass
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G)
    (chi : InvariantContinuousH1 U) :
    continuousCohomologyZModPLifted p (G ⧸ (U.1 : Subgroup G)) 2 :=
  ContinuousCohomology.π
    (trivialZModPLifted p (G ⧸ (U.1 : Subgroup G))) 2
    (continuousTransgressionHomogeneousCocycle U chi)

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
@[simp]
theorem continuousTransgressionHomogeneousCochain_zero
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G) :
    continuousTransgressionHomogeneousCochain U 0 = 0 := by
  apply Subtype.ext
  ext a b c
  change ULift.up (transgressionFactor (U.1 : Subgroup G)
    ((0 : FiniteCharacter p (U.1 : Subgroup G)).toMul) (a⁻¹ * b) (b⁻¹ * c)) = 0
  rw [transgressionFactor_zero]
  rfl

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
@[simp]
theorem continuousTransgressionHomogeneousCochain_add
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G)
    (chi psi : InvariantContinuousH1 U) :
    continuousTransgressionHomogeneousCochain U (chi + psi) =
      continuousTransgressionHomogeneousCochain U chi +
        continuousTransgressionHomogeneousCochain U psi := by
  apply Subtype.ext
  ext a b c
  change ULift.up (transgressionFactor (U.1 : Subgroup G)
    ((Additive.ofMul (characterOfH1 chi.1).toMonoidHom :
      FiniteCharacter p (U.1 : Subgroup G)) +
      Additive.ofMul (characterOfH1 psi.1).toMonoidHom).toMul
      (a⁻¹ * b) (b⁻¹ * c)) = _
  rw [transgressionFactor_add]
  rfl

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
@[simp]
theorem continuousTransgressionHomogeneousCocycle_zero
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G) :
    continuousTransgressionHomogeneousCocycle U 0 = 0 := by
  apply topModule_mono_injective_lifted
    ((trivialZModPCochainsLifted p (G ⧸ (U.1 : Subgroup G))).iCycles 2)
  rw [iCycles_continuousTransgressionHomogeneousCocycle, map_zero,
    continuousTransgressionHomogeneousCochain_zero]

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
@[simp]
theorem continuousTransgressionHomogeneousCocycle_add
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G)
    (chi psi : InvariantContinuousH1 U) :
    continuousTransgressionHomogeneousCocycle U (chi + psi) =
      continuousTransgressionHomogeneousCocycle U chi +
        continuousTransgressionHomogeneousCocycle U psi := by
  apply topModule_mono_injective_lifted
    ((trivialZModPCochainsLifted p (G ⧸ (U.1 : Subgroup G))).iCycles 2)
  rw [iCycles_continuousTransgressionHomogeneousCocycle, map_add,
    iCycles_continuousTransgressionHomogeneousCocycle,
    iCycles_continuousTransgressionHomogeneousCocycle,
    continuousTransgressionHomogeneousCochain_add]

/-- Continuous transgression is additive. -/
noncomputable def continuousTransgressionAddHom
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G) :
    InvariantContinuousH1 U →+
      continuousCohomologyZModPLifted p (G ⧸ (U.1 : Subgroup G)) 2 where
  toFun := continuousTransgressionClass U
  map_zero' := by
    unfold continuousTransgressionClass
    rw [continuousTransgressionHomogeneousCocycle_zero, map_zero]
  map_add' := by
    intro chi psi
    unfold continuousTransgressionClass
    rw [continuousTransgressionHomogeneousCocycle_add, map_add]

/-- Continuous transgression as a `ZMod p`-linear map. -/
noncomputable def continuousTransgressionLinearMap
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G) :
    InvariantContinuousH1 U →ₗ[ZMod p]
      continuousCohomologyZModPLifted p (G ⧸ (U.1 : Subgroup G)) 2 :=
  (continuousTransgressionAddHom U).toZModLinearMap p

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
@[simp]
theorem continuousTransgressionLinearMap_apply
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G)
    (chi : InvariantContinuousH1 U) :
    continuousTransgressionLinearMap U chi = continuousTransgressionClass U chi :=
  rfl

end

end ClassFieldTower.Cohomology
