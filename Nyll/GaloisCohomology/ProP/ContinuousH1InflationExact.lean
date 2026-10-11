/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.ProP.ContinuousTransgressionExact
import Nyll.ProCGroups.Topologies.QuotientMaps
import Mathlib.Algebra.Field.ZMod

/-!
# Exactness of continuous degree-one inflation and restriction

For an open normal subgroup `U`, continuous mod-`p` characters of `G / U` inflate to
continuous characters of `G`.  Their range is exactly the kernel of restriction to `U`.
-/

open scoped Topology

namespace ClassFieldTower.Cohomology

open ProCGroups ProCGroups.ProC
open ClassFieldTower.ProP

noncomputable section

universe u

variable {p : ℕ} [Fact p.Prime]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

local instance continuousH1InflationZModAddCommGroup : AddCommGroup (ZMod p) :=
  (ZMod.instField p).toDivisionRing.toAddCommGroup

local instance continuousH1InflationModule
    {q : ℕ} {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] :
    Module (ZMod q) (ContinuousH1ZMod (p := q) (G := H)) :=
  continuousH1ZModModule

/-- Pull a continuous degree-one character on `G / U` back along the quotient projection. -/
def continuousH1InflationAddHom
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G) :
    ContinuousH1ZMod (p := p) (G := G ⧸ (U.1 : Subgroup G)) →+
      ContinuousH1ZMod (p := p) (G := G) where
  toFun chi := h1OfCharacter
    ((characterOfH1 chi).comp (OpenNormalSubgroupInClass.quotientProj U))
  map_zero' := by
    ext g
    rfl
  map_add' := by
    intro chi psi
    ext g
    rfl

/-- Continuous degree-one inflation as a `ZMod p`-linear map. -/
noncomputable def continuousH1InflationLinearMap
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G) :
    ContinuousH1ZMod (p := p) (G := G ⧸ (U.1 : Subgroup G)) →ₗ[ZMod p]
      ContinuousH1ZMod (p := p) (G := G) :=
  (continuousH1InflationAddHom U).toZModLinearMap p

@[simp]
theorem continuousH1InflationLinearMap_apply
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G)
    (chi : ContinuousH1ZMod (p := p) (G := G ⧸ (U.1 : Subgroup G)))
    (g : G) :
    continuousH1InflationLinearMap U chi (Additive.ofMul g) =
      chi (Additive.ofMul (OpenNormalSubgroupInClass.quotientProj U g)) :=
  by
    simp only [continuousH1InflationLinearMap, AddMonoidHom.coe_toZModLinearMap]
    rfl

@[simp]
theorem continuousH1InflationLinearMap_zero
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G) :
    continuousH1InflationLinearMap U 0 = 0 :=
  map_zero (continuousH1InflationLinearMap U)

/-- Degree-one inflation is injective because the quotient projection is surjective. -/
theorem continuousH1InflationLinearMap_injective
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G) :
    Function.Injective (continuousH1InflationLinearMap U) := by
  intro chi psi h
  ext q
  obtain ⟨g, rfl⟩ := OpenNormalSubgroupInClass.quotientProj_surjective U q
  have hg := DFunLike.congr_fun h (Additive.ofMul g)
  rw [continuousH1InflationLinearMap_apply,
    continuousH1InflationLinearMap_apply] at hg
  change chi (Additive.ofMul (OpenNormalSubgroupInClass.quotientProj U g)) =
    psi (Additive.ofMul (OpenNormalSubgroupInClass.quotientProj U g))
  exact hg

/-- Inflated degree-one characters restrict trivially to the kernel of the quotient map. -/
theorem continuousCharacterRestriction_continuousH1Inflation_eq_zero
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G)
    (chi : ContinuousH1ZMod (p := p) (G := G ⧸ (U.1 : Subgroup G))) :
    continuousCharacterRestrictionLinearMap U
        (continuousH1InflationLinearMap U chi) = 0 := by
  apply Subtype.ext
  ext n
  change (continuousH1InflationLinearMap U chi)
    (Additive.ofMul (Additive.toMul n).1) = 0
  rw [continuousH1InflationLinearMap_apply,
    OpenNormalSubgroupInClass.quotientProj_eq_one_iff.mpr (Additive.toMul n).2]
  exact chi.map_zero

/-- The continuous degree-one inflation--restriction sequence is exact at ambient
characters. -/
theorem continuousH1Inflation_range_eq_characterRestriction_ker
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G) :
    LinearMap.range (continuousH1InflationLinearMap U) =
      LinearMap.ker (continuousCharacterRestrictionLinearMap U) := by
  ext psi
  constructor
  · rintro ⟨chi, rfl⟩
    rw [LinearMap.mem_ker]
    exact continuousCharacterRestriction_continuousH1Inflation_eq_zero U chi
  · intro hpsi
    rw [LinearMap.mem_ker] at hpsi
    have hker : (U.1 : Subgroup G) ≤ (characterOfH1 psi).toMonoidHom.ker := by
      intro g hg
      have hvalue := congrArg
        (fun chi : InvariantContinuousH1 U ↦ chi.1 (Additive.ofMul ⟨g, hg⟩)) hpsi
      change psi (Additive.ofMul g) = 0 at hvalue
      change Multiplicative.ofAdd (psi (Additive.ofMul g)) = 1
      rw [hvalue]
      rfl
    let quotientCharacter :
        G ⧸ (U.1 : Subgroup G) →ₜ* Multiplicative (ZMod p) :=
      ProCGroups.QuotientGroup.liftₜ (U.1 : Subgroup G) (characterOfH1 psi) hker
    refine ⟨h1OfCharacter quotientCharacter, ?_⟩
    ext g
    change (continuousH1InflationLinearMap U (h1OfCharacter quotientCharacter))
      (Additive.ofMul (Additive.toMul g)) = psi g
    rw [continuousH1InflationLinearMap_apply]
    change (quotientCharacter (OpenNormalSubgroupInClass.quotientProj U
      (Additive.toMul g))).toAdd = psi g
    rw [OpenNormalSubgroupInClass.quotientProj_apply,
      ProCGroups.QuotientGroup.liftₜ_apply_mk]
    rfl

end

end ClassFieldTower.Cohomology
