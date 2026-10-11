/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.ProP.ContinuousTransgression
import Nyll.GaloisCohomology.ProP.H2FiniteStageFamily

/-!
# Continuous transgression is killed by degree-two inflation

For an open normal subgroup, every continuous transgression class lies in the kernel of
degree-two inflation.  The proof uses an explicit continuous homogeneous primitive after
inflation.
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

/-- Degree-two inflation from an open finite quotient. -/
noncomputable def degreeTwoInflationLinearMap
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G) :
    continuousCohomologyZModPLifted p (G ⧸ (U.1 : Subgroup G)) 2 →ₗ[ZMod p]
      continuousCohomologyZModPLifted p G 2 :=
  (continuousCohomologyZModPMapLifted p
    (OpenNormalSubgroupInClass.quotientProj U) 2).hom.toLinearMap

/-- The kernel residue is continuous when the normal subgroup is open. -/
private noncomputable def quotientSectionResidueContinuousMap
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G) :
    C(G, (U.1 : Subgroup G)) where
  toFun := quotientSectionResidue (U.1 : Subgroup G)
  continuous_toFun := by
    apply Continuous.subtype_mk
    change Continuous (fun g : G ↦
      g * (Quotient.out (OpenNormalSubgroupInClass.quotientProj U g))⁻¹)
    exact continuous_id.mul
      ((continuous_of_discreteTopology.comp
        (OpenNormalSubgroupInClass.quotientProj U).continuous_toFun).inv)

/-- The inhomogeneous residue value of a continuous invariant character. -/
private noncomputable def continuousResidueValue
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G)
    (chi : InvariantContinuousH1 U) : C(G, ZMod p) where
  toFun g := chi.1 (Additive.ofMul (quotientSectionResidue (U.1 : Subgroup G) g))
  continuous_toFun := chi.1.continuous_toFun.comp
    (quotientSectionResidueContinuousMap U).continuous_toFun

/-- A homogeneous primitive for the inflation of a transgression cocycle. -/
private noncomputable def continuousTransgressionInflationPrimitive
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G)
    (chi : InvariantContinuousH1 U) :
    (trivialZModPCochainsLifted p G).X 1 := by
  let v := continuousResidueValue U chi
  let sigma : C(G, C(G, ULift.{u} (ZMod p))) := ContinuousMap.curry
    ⟨fun ab : G × G ↦ ULift.up (-v (ab.1⁻¹ * ab.2)), by fun_prop⟩
  exact ⟨sigma, by
    intro g
    apply ContinuousMap.ext
    intro a
    apply ContinuousMap.ext
    intro b
    change ULift.up (-v ((g⁻¹ * a)⁻¹ * (g⁻¹ * b))) =
      ULift.up (-v (a⁻¹ * b))
    congr 3
    group⟩

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
private theorem continuousTransgressionInflationPrimitive_boundary
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G)
    (chi : InvariantContinuousH1 U) :
    ((trivialZModPCochainsLifted p G).d 1 2).hom
        (continuousTransgressionInflationPrimitive U chi) =
      (((trivialZModPCochainsMapLifted p
        (OpenNormalSubgroupInClass.quotientProj U)).f 2).hom
          (continuousTransgressionHomogeneousCochain U chi)) := by
  apply Subtype.ext
  ext a b c
  have hd := TopRep.homogeneousCochains.d_apply
    (trivialZModPLifted p G) 1
      (continuousTransgressionInflationPrimitive U chi)
  have hp := congrArg (fun tau ↦ tau a b c) hd
  rw [hp]
  simp only [Nat.reduceAdd, Functor.mapHomologicalComplex_obj_X]
  change ULift.up (-continuousResidueValue U chi (b⁻¹ * c)) -
      (ULift.up (-continuousResidueValue U chi (a⁻¹ * c)) -
        ULift.up (-continuousResidueValue U chi (a⁻¹ * b))) = ULift.up _
  apply ULift.ext
  change -continuousResidueValue U chi (b⁻¹ * c) -
      (-continuousResidueValue U chi (a⁻¹ * c) -
        -continuousResidueValue U chi (a⁻¹ * b)) = _
  have h := character_quotientSectionResidue_mul
    (U.1 : Subgroup G) (characterOfH1 chi.1).toMonoidHom
    (fun g n ↦ congrArg Multiplicative.ofAdd (chi.2 g n))
    (a⁻¹ * b) (b⁻¹ * c)
  have habc : (a⁻¹ * b) * (b⁻¹ * c) = a⁻¹ * c := by group
  rw [habc] at h
  change continuousResidueValue U chi (a⁻¹ * c) =
    continuousResidueValue U chi (a⁻¹ * b) +
      continuousResidueValue U chi (b⁻¹ * c) + _ at h
  rw [h]
  abel

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- Every continuous transgression class dies under degree-two inflation. -/
theorem degreeTwoInflation_continuousTransgression_eq_zero
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G)
    (chi : InvariantContinuousH1 U) :
    degreeTwoInflationLinearMap U (continuousTransgressionLinearMap U chi) = 0 := by
  let z := continuousTransgressionHomogeneousCocycle U chi
  let zinfl := (trivialZModPCocyclesMapLifted p
    (OpenNormalSubgroupInClass.quotientProj U) 2).hom z
  have hboundary :
      ((trivialZModPCochainsLifted p G).toCycles 1 2).hom
          (continuousTransgressionInflationPrimitive U chi) = zinfl := by
    apply topModule_mono_injective_lifted
      ((trivialZModPCochainsLifted p G).iCycles 2)
    calc
      _ = ((trivialZModPCochainsLifted p G).d 1 2).hom
          (continuousTransgressionInflationPrimitive U chi) := by
        exact ConcreteCategory.congr_hom
          ((trivialZModPCochainsLifted p G).toCycles_i 1 2) _
      _ = (((trivialZModPCochainsMapLifted p
          (OpenNormalSubgroupInClass.quotientProj U)).f 2).hom
            (continuousTransgressionHomogeneousCochain U chi)) :=
        continuousTransgressionInflationPrimitive_boundary U chi
      _ = ((trivialZModPCochainsLifted p G).iCycles 2).hom zinfl := by
        symm
        change ((trivialZModPCochainsLifted p G).iCycles 2).hom
          ((trivialZModPCocyclesMapLifted p
            (OpenNormalSubgroupInClass.quotientProj U) 2).hom z) = _
        rw [← ConcreteCategory.comp_apply]
        rw [HomologicalComplex.cyclesMap_i]
        rw [ConcreteCategory.comp_apply]
        rw [iCycles_continuousTransgressionHomogeneousCocycle]
        rfl
  change (continuousCohomologyZModPMapLifted p
    (OpenNormalSubgroupInClass.quotientProj U) 2).hom
      (ContinuousCohomology.π
        (trivialZModPLifted p (G ⧸ (U.1 : Subgroup G))) 2 z) = 0
  have hnat := ConcreteCategory.congr_hom
    (trivialZModPLifted_π_naturality p
      (OpenNormalSubgroupInClass.quotientProj U) 2) z
  change ConcreteCategory.hom
    (ContinuousCohomology.π
      (trivialZModPLifted p (G ⧸ (U.1 : Subgroup G))) 2 ≫
        continuousCohomologyZModPMapLifted p
          (OpenNormalSubgroupInClass.quotientProj U) 2) z = 0
  rw [hnat]
  change ContinuousCohomology.π (trivialZModPLifted p G) 2 zinfl = 0
  rw [← hboundary]
  exact ConcreteCategory.congr_hom
    ((trivialZModPCochainsLifted p G).toCycles_comp_homologyπ 1 2) _

end

end ClassFieldTower.Cohomology
