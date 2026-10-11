/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.ProP.ContinuousTransgressionPrimitive

/-!
# Continuous inflation--transgression exactness in degree two

For an open normal subgroup, continuous transgression has range exactly the kernel of
degree-two inflation.  The reverse inclusion is proved at cochain level by restricting a
continuous primitive of the inflated cocycle.
-/

open CategoryTheory TopRep ContRepresentation
open scoped Topology

namespace ClassFieldTower.Cohomology

open ProCGroups ProCGroups.ProC
open ClassFieldTower.ProP
open ClassFieldTower.ProP.FreeProPH2Cocycle

noncomputable section

universe u

variable {p : ℕ} [Fact p.Prime]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
private theorem normalizedCocycle_sub
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (z w : trivialZModPCocyclesLifted p H 2) (g h : H) :
    normalizedCocycle (z - w) g h =
      normalizedCocycle z g h - normalizedCocycle w g h := by
  unfold normalizedCocycle
  change
    ((((trivialZModPCochainsLifted p H).iCycles 2).hom (z - w)).1 1 g (g * h) -
      (((trivialZModPCochainsLifted p H).iCycles 2).hom (z - w)).1 1 1 1) = _
  rw [map_sub]
  change
    ((((trivialZModPCochainsLifted p H).iCycles 2).hom z).1 1 g (g * h) -
        (((trivialZModPCochainsLifted p H).iCycles 2).hom w).1 1 g (g * h)) -
      ((((trivialZModPCochainsLifted p H).iCycles 2).hom z).1 1 1 1 -
        (((trivialZModPCochainsLifted p H).iCycles 2).hom w).1 1 1 1) =
      ((((trivialZModPCochainsLifted p H).iCycles 2).hom z).1 1 g (g * h) -
        (((trivialZModPCochainsLifted p H).iCycles 2).hom z).1 1 1 1) -
      ((((trivialZModPCochainsLifted p H).iCycles 2).hom w).1 1 g (g * h) -
        (((trivialZModPCochainsLifted p H).iCycles 2).hom w).1 1 1 1)
  abel

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
private theorem normalizedCocycle_continuousTransgression
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G)
    (chi : InvariantContinuousH1 U)
    (q r : G ⧸ (U.1 : Subgroup G)) :
    normalizedCocycle (continuousTransgressionHomogeneousCocycle U chi) q r =
      ULift.up (transgressionFactor (U.1 : Subgroup G)
        (characterOfH1 chi.1).toMonoidHom q r) -
      ULift.up (transgressionFactor (U.1 : Subgroup G)
        (characterOfH1 chi.1).toMonoidHom 1 1) := by
  unfold normalizedCocycle
  change (((trivialZModPCochainsLifted p
      (G ⧸ (U.1 : Subgroup G))).iCycles 2).hom
        (continuousTransgressionHomogeneousCocycle U chi)).1 1 q (q * r) -
      (((trivialZModPCochainsLifted p
        (G ⧸ (U.1 : Subgroup G))).iCycles 2).hom
          (continuousTransgressionHomogeneousCocycle U chi)).1 1 1 1 = _
  rw [show ((trivialZModPCochainsLifted p
      (G ⧸ (U.1 : Subgroup G))).iCycles 2).hom
        (continuousTransgressionHomogeneousCocycle U chi) =
      continuousTransgressionHomogeneousCochain U chi by
    exact iCycles_continuousTransgressionHomogeneousCocycle U chi]
  change ULift.up (transgressionFactor (U.1 : Subgroup G)
      (characterOfH1 chi.1).toMonoidHom (1⁻¹ * q) (q⁻¹ * (q * r))) -
    ULift.up (transgressionFactor (U.1 : Subgroup G)
      (characterOfH1 chi.1).toMonoidHom (1⁻¹ * 1) (1⁻¹ * 1)) = _
  simp only [inv_one, one_mul, inv_mul_cancel_left]

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- A reconstructed invariant character transgresses to the original quotient cocycle class. -/
theorem continuousTransgressionClass_invariantContinuousH1OfInflationPrimitive
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G)
    (z : trivialZModPCocyclesLifted p (G ⧸ (U.1 : Subgroup G)) 2)
    (c : (trivialZModPCochainsLifted p G).X 1)
    (hc : ((trivialZModPCochainsLifted p G).d 1 2).hom c =
      (((trivialZModPCochainsMapLifted p
        (OpenNormalSubgroupInClass.quotientProj U)).f 2).hom
          (((trivialZModPCochainsLifted p
            (G ⧸ (U.1 : Subgroup G))).iCycles 2).hom z))) :
    continuousTransgressionClass U
        (invariantContinuousH1OfInflationPrimitive U z c hc) =
      ContinuousCohomology.π
        (trivialZModPLifted p (G ⧸ (U.1 : Subgroup G))) 2 z := by
  let : Finite (G ⧸ (U.1 : Subgroup G)) := U.2.1
  let : DiscreteTopology (G ⧸ (U.1 : Subgroup G)) :=
    QuotientGroup.discreteTopology (openNormalSubgroup_isOpen (G := G) U.1)
  let chi := invariantContinuousH1OfInflationPrimitive U z c hc
  let t := continuousTransgressionHomogeneousCocycle U chi
  let w := t - z
  let b := inflationPrimitiveQuotientCorrection U c
  have hnormalized (q r : G ⧸ (U.1 : Subgroup G)) :
      normalizedCocycle w q r =
        -normalizedInflationPrimitiveValue c (Quotient.out q) -
          normalizedInflationPrimitiveValue c (Quotient.out r) +
          normalizedInflationPrimitiveValue c (Quotient.out (q * r)) +
          normalizedInflationPrimitiveValue c
            (Quotient.out (1 : G ⧸ (U.1 : Subgroup G))) := by
    rw [show w = t - z by rfl, normalizedCocycle_sub,
      normalizedCocycle_continuousTransgression]
    dsimp only [chi]
    rw [reconstructed_transgressionFactor U z c hc q r,
      reconstructed_transgressionFactor U z c hc 1 1,
      normalizedCocycle_one_left]
    simp only [one_mul]
    abel
  have hb (q r : G ⧸ (U.1 : Subgroup G)) :
      b (q * r) = b q + b r + normalizedCocycle w q r := by
    change normalizedInflationPrimitiveValue c (Quotient.out (q * r)) -
        normalizedInflationPrimitiveValue c
          (Quotient.out (1 : G ⧸ (U.1 : Subgroup G))) =
      (normalizedInflationPrimitiveValue c (Quotient.out q) -
          normalizedInflationPrimitiveValue c
            (Quotient.out (1 : G ⧸ (U.1 : Subgroup G)))) +
        (normalizedInflationPrimitiveValue c (Quotient.out r) -
          normalizedInflationPrimitiveValue c
            (Quotient.out (1 : G ⧸ (U.1 : Subgroup G)))) +
          normalizedCocycle w q r
    rw [hnormalized]
    abel
  let K := trivialZModPCochainsLifted p (G ⧸ (U.1 : Subgroup G))
  let primitive : K.X 1 := homogeneousPrimitive w b
  have hboundary : (K.d 1 2).hom primitive = (K.iCycles 2).hom w :=
    homogeneousPrimitive_boundary w b hb
  have hwCycles : (K.toCycles 1 2).hom primitive = w := by
    apply topModule_mono_injective_lifted (K.iCycles 2)
    calc
      (K.iCycles 2).hom ((K.toCycles 1 2).hom primitive) =
          (K.d 1 2).hom primitive := by
        exact ConcreteCategory.congr_hom (K.toCycles_i 1 2) primitive
      _ = (K.iCycles 2).hom w := hboundary
  have hwzero : ContinuousCohomology.π
      (trivialZModPLifted p (G ⧸ (U.1 : Subgroup G))) 2 w = 0 := by
    rw [← hwCycles]
    exact ConcreteCategory.congr_hom (K.toCycles_comp_homologyπ 1 2) primitive
  change ContinuousCohomology.π
      (trivialZModPLifted p (G ⧸ (U.1 : Subgroup G))) 2 t =
    ContinuousCohomology.π
      (trivialZModPLifted p (G ⧸ (U.1 : Subgroup G))) 2 z
  change ContinuousCohomology.π
      (trivialZModPLifted p (G ⧸ (U.1 : Subgroup G))) 2 (t - z) = 0 at hwzero
  rw [map_sub] at hwzero
  exact sub_eq_zero.mp hwzero

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- Continuous Hochschild--Serre exactness at degree two for an open normal subgroup. -/
theorem continuousTransgression_range_eq_degreeTwoInflation_ker
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G) :
    LinearMap.range (continuousTransgressionLinearMap U) =
      LinearMap.ker (degreeTwoInflationLinearMap U) := by
  ext x
  constructor
  · rintro ⟨chi, rfl⟩
    rw [LinearMap.mem_ker]
    exact degreeTwoInflation_continuousTransgression_eq_zero U chi
  · intro hx
    rw [LinearMap.mem_ker] at hx
    let z := ProP.PresentationH2Aux.targetCocycleSection x
    let zinfl := (trivialZModPCocyclesMapLifted p
      (OpenNormalSubgroupInClass.quotientProj U) 2).hom z
    have hzinflzero : ContinuousCohomology.π (trivialZModPLifted p G) 2 zinfl = 0 := by
      have hnat := ConcreteCategory.congr_hom
        (trivialZModPLifted_π_naturality p
          (OpenNormalSubgroupInClass.quotientProj U) 2) z
      change ConcreteCategory.hom
        (trivialZModPCocyclesMapLifted p
            (OpenNormalSubgroupInClass.quotientProj U) 2 ≫
          ContinuousCohomology.π (trivialZModPLifted p G) 2) z = 0
      rw [← hnat]
      change degreeTwoInflationLinearMap U
        (ContinuousCohomology.π
          (trivialZModPLifted p (G ⧸ (U.1 : Subgroup G))) 2 z) = 0
      rw [ProP.PresentationH2Aux.targetCocycleSection_π]
      exact hx
    obtain ⟨c, hc⟩ := exists_boundary_of_homologyπ_apply_eq_zero
      (trivialZModPLifted p G) 1 zinfl hzinflzero
    have hc' : ((trivialZModPCochainsLifted p G).d 1 2).hom c =
        (((trivialZModPCochainsMapLifted p
          (OpenNormalSubgroupInClass.quotientProj U)).f 2).hom
            (((trivialZModPCochainsLifted p
              (G ⧸ (U.1 : Subgroup G))).iCycles 2).hom z)) := by
      rw [hc]
      change ((trivialZModPCochainsLifted p G).iCycles 2).hom
          ((trivialZModPCocyclesMapLifted p
            (OpenNormalSubgroupInClass.quotientProj U) 2).hom z) = _
      rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i,
        ConcreteCategory.comp_apply]
      rfl
    refine ⟨invariantContinuousH1OfInflationPrimitive U z c hc', ?_⟩
    rw [continuousTransgressionLinearMap_apply]
    calc
      continuousTransgressionClass U
          (invariantContinuousH1OfInflationPrimitive U z c hc') =
        ContinuousCohomology.π
          (trivialZModPLifted p (G ⧸ (U.1 : Subgroup G))) 2 z :=
            continuousTransgressionClass_invariantContinuousH1OfInflationPrimitive
              U z c hc'
      _ = x := by
        exact ProP.PresentationH2Aux.targetCocycleSection_π x

end

end ClassFieldTower.Cohomology
