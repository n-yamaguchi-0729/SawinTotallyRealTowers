/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.ProP.ContinuousH1CupProductRestriction
import Nyll.ProCGroups.Cohomology.ContinuousMapFiniteStage
import Nyll.ProCGroups.FiniteGroups.StandardClasses

/-!
# Finite-stage realization of the canonical continuous H¹ cup

Two continuous mod-`p` characters of a pro-`p` group factor through one
common finite `p`-group quotient.  Restriction naturality then identifies
their canonical cup with inflation of the cup of the descended characters.
-/

open scoped Topology

namespace ClassFieldTower.Cohomology

open ProCGroups ProCGroups.ProC
open ClassFieldTower.ProP

noncomputable section

universe u

variable {p : ℕ} [Fact p.Prime]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G]

/-- Two continuous mod-`p` characters, and their canonical degree-two cup,
descend to one common finite `p`-group quotient. -/
theorem exists_finiteStage_continuousH1Cup
    (hG : HasOpenNormalBasisInClass (FiniteGroupClass.pGroup p) G)
    (χ ψ : ContinuousH1ZMod (p := p) (G := G)) :
    ∃ U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G,
      ∃ χU ψU : ContinuousH1ZMod
          (p := p) (G := G ⧸ (U.1 : Subgroup G)),
        continuousH1ZModRestriction
            (OpenNormalSubgroupInClass.quotientProj U) χU = χ ∧
          continuousH1ZModRestriction
            (OpenNormalSubgroupInClass.quotientProj U) ψU = ψ ∧
          (continuousCohomologyZModPMapLifted p
              (OpenNormalSubgroupInClass.quotientProj U) 2).hom
              (continuousH1CupProductLifted χU ψU) =
            continuousH1CupProductLifted χ ψ := by
  let ρ : G → ZMod p × ZMod p :=
    fun g ↦ (χ (Additive.ofMul g), ψ (Additive.ofMul g))
  have hρ : Continuous ρ :=
    χ.continuous_toFun.prodMk ψ.continuous_toFun
  obtain ⟨U, ρU, _hρU, hfac⟩ :=
    exists_openNormalSubgroupInClass_factor_continuousMap_finite
      (FiniteGroupClass.pGroup_formation p) hG ρ hρ
  let Q := G ⧸ (U.1 : Subgroup G)
  let q : G →ₜ* Q := OpenNormalSubgroupInClass.quotientProj U
  let _ : DiscreteTopology Q :=
    QuotientGroup.discreteTopology
      (openNormalSubgroup_isOpen (G := G) U.1)
  have hρU (g : G) : ρU (q g) = ρ g :=
    (congrFun hfac g).symm
  have hfst_one : (ρU 1).1 = 0 := by
    rw [← map_one q]
    exact (congrArg Prod.fst (hρU 1)).trans χ.map_zero
  have hsnd_one : (ρU 1).2 = 0 := by
    rw [← map_one q]
    exact (congrArg Prod.snd (hρU 1)).trans ψ.map_zero
  have hfst_mul (a b : Q) :
      (ρU (a * b)).1 = (ρU a).1 + (ρU b).1 := by
    obtain ⟨g, rfl⟩ :=
      OpenNormalSubgroupInClass.quotientProj_surjective U a
    obtain ⟨h, rfl⟩ :=
      OpenNormalSubgroupInClass.quotientProj_surjective U b
    rw [← map_mul q]
    rw [congrArg Prod.fst (hρU (g * h)),
      congrArg Prod.fst (hρU g), congrArg Prod.fst (hρU h)]
    exact χ.map_add (Additive.ofMul g) (Additive.ofMul h)
  have hsnd_mul (a b : Q) :
      (ρU (a * b)).2 = (ρU a).2 + (ρU b).2 := by
    obtain ⟨g, rfl⟩ :=
      OpenNormalSubgroupInClass.quotientProj_surjective U a
    obtain ⟨h, rfl⟩ :=
      OpenNormalSubgroupInClass.quotientProj_surjective U b
    rw [← map_mul q]
    rw [congrArg Prod.snd (hρU (g * h)),
      congrArg Prod.snd (hρU g), congrArg Prod.snd (hρU h)]
    exact ψ.map_add (Additive.ofMul g) (Additive.ofMul h)
  let χU : ContinuousH1ZMod (p := p) (G := Q) :=
    { toFun := fun a ↦ (ρU (Additive.toMul a)).1
      map_zero' := hfst_one
      map_add' := fun a b ↦ hfst_mul (Additive.toMul a) (Additive.toMul b)
      continuous_toFun := continuous_of_discreteTopology }
  let ψU : ContinuousH1ZMod (p := p) (G := Q) :=
    { toFun := fun a ↦ (ρU (Additive.toMul a)).2
      map_zero' := hsnd_one
      map_add' := fun a b ↦ hsnd_mul (Additive.toMul a) (Additive.toMul b)
      continuous_toFun := continuous_of_discreteTopology }
  have hχ :
      continuousH1ZModRestriction q χU = χ := by
    ext g
    exact congrArg Prod.fst (hρU (Additive.toMul g))
  have hψ :
      continuousH1ZModRestriction q ψU = ψ := by
    ext g
    exact congrArg Prod.snd (hρU (Additive.toMul g))
  refine ⟨U, χU, ψU, hχ, hψ, ?_⟩
  rw [continuousCohomologyZModPMapLifted_continuousH1Cup, hχ, hψ]

end

end ClassFieldTower.Cohomology
