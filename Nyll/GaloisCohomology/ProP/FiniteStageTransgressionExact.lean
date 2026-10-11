/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.ProP.FiniteStageTransgressionLinear
import Nyll.GaloisCohomology.ProP.FiniteTransgressionExact
import Nyll.ProCGroups.ProP.ContinuousH1
import Mathlib.Algebra.Field.ZMod

/-!
# Exactness of finite-stage transgression

At an open finite quotient stage, every abstract mod-`p` character is continuous.  This file
therefore upgrades finite transgression exactness to the continuous degree-one characters of the
ambient finite quotient: their restriction range is exactly the kernel of finite transgression.
-/

open scoped Topology

namespace ClassFieldTower.ProP

open ProCGroups ProCGroups.ProC
open ClassFieldTower.Cohomology

noncomputable section

universe u

variable {p : ℕ} [Fact p.Prime]
variable {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
variable [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]

local instance finiteStageExactCanonicalZModAddCommGroup : AddCommGroup (ZMod p) :=
  (ZMod.instField p).toDivisionRing.toAddCommGroup

local instance finiteStageContinuousH1Module
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) F) :
    Module (ZMod p)
      (ContinuousH1ZMod (p := p) (G := F ⧸ (U.1 : Subgroup F))) :=
  continuousH1ZModModule

/-- Regard an abstract character of an open finite quotient as a continuous degree-one
character. -/
def continuousH1OfFiniteStageCharacter
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) F)
    (ψ : FiniteCharacter p (F ⧸ (U.1 : Subgroup F))) :
    ContinuousH1ZMod (p := p) (G := F ⧸ (U.1 : Subgroup F)) where
  toFun g := (ψ.toMul g.toMul).toAdd
  map_zero' := by
    change (ψ.toMul 1).toAdd = 0
    rw [map_one]
    rfl
  map_add' := by
    intro g h
    change (ψ.toMul (g.toMul * h.toMul)).toAdd =
      (ψ.toMul g.toMul).toAdd + (ψ.toMul h.toMul).toAdd
    rw [map_mul, toAdd_mul]
  continuous_toFun := continuous_of_discreteTopology

omit [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F] in
@[simp]
theorem characterOfH1_continuousH1OfFiniteStageCharacter
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) F)
    (ψ : FiniteCharacter p (F ⧸ (U.1 : Subgroup F))) :
    Additive.ofMul
        (characterOfH1 (continuousH1OfFiniteStageCharacter U ψ)).toMonoidHom =
      ψ := by
  rfl

/-- Restriction from continuous degree-one characters of an ambient finite quotient to
conjugation-invariant characters of the image of `R`. -/
def finiteStageContinuousCharacterRestrictionAddHom
    (R : ClosedSubgroup F) [R.Normal]
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) F) :
    ContinuousH1ZMod (p := p) (G := F ⧸ (U.1 : Subgroup F)) →+
      InvariantFiniteCharacter (p := p) (finiteStageImage R U) where
  toFun ψ := finiteCharacterRestrictionAddHom (p := p) (finiteStageImage R U)
    (Additive.ofMul (characterOfH1 ψ).toMonoidHom)
  map_zero' := by
    apply Subtype.ext
    rfl
  map_add' := by
    intro ψ φ
    apply Subtype.ext
    rfl

/-- Linear restriction from continuous degree-one characters of an ambient finite quotient. -/
noncomputable def finiteStageContinuousCharacterRestrictionLinearMap
    (R : ClosedSubgroup F) [R.Normal]
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) F) :
    ContinuousH1ZMod (p := p) (G := F ⧸ (U.1 : Subgroup F)) →ₗ[ZMod p]
      InvariantFiniteCharacter (p := p) (finiteStageImage R U) :=
  (finiteStageContinuousCharacterRestrictionAddHom R U).toZModLinearMap p

omit [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F] in
@[simp]
theorem finiteStageContinuousCharacterRestrictionLinearMap_realize
    (R : ClosedSubgroup F) [R.Normal]
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) F)
    (ψ : FiniteCharacter p (F ⧸ (U.1 : Subgroup F))) :
    finiteStageContinuousCharacterRestrictionLinearMap R U
        (continuousH1OfFiniteStageCharacter U ψ) =
      finiteCharacterRestrictionLinearMap (p := p) (finiteStageImage R U) ψ := by
  rfl

omit [T2Space F] [TotallyDisconnectedSpace F] in
/-- At a finite quotient stage, continuous restriction is exact at invariant characters:
its range is the kernel of finite transgression. -/
theorem finiteStageContinuousCharacterRestriction_range_eq_transgression_ker
    (R : ClosedSubgroup F) [R.Normal]
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) F) :
    LinearMap.range (finiteStageContinuousCharacterRestrictionLinearMap R U) =
      LinearMap.ker
        (finiteTransgressionLinearMap (p := p) (finiteStageImage R U)) := by
  rw [← finiteCharacterRestriction_range_eq_transgression_ker
    (p := p) (finiteStageImage R U)]
  ext χ
  constructor
  · rintro ⟨ψ, rfl⟩
    exact ⟨Additive.ofMul (characterOfH1 ψ).toMonoidHom, rfl⟩
  · rintro ⟨ψ, rfl⟩
    exact ⟨continuousH1OfFiniteStageCharacter U ψ, by simp⟩

end

end ClassFieldTower.ProP
