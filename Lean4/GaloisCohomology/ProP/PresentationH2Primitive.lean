/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import GaloisCohomology.ProP.FreeProPH2
import GaloisCohomology.ProP.FiniteTransgressionKernel
import Mathlib.Algebra.Field.ZMod

set_option autoImplicit false
/-!
# Primitive selection for presentation degree-two classes

This file linearly selects homogeneous cocycle representatives and, after restriction to the
finite-basis free pro-`p` source, linearly selects degree-one primitives.  It also records the
pointwise boundary and normalization identities used by the presentation five-term argument.
-/

open scoped Topology

namespace ClassFieldTower.ProP

open CategoryTheory Limits TopRep ContRepresentation
open ProCGroups ProCGroups.ProC

noncomputable section

namespace PresentationH2Aux

universe u

variable {p : ℕ}

theorem homologyπ_surjective
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (A : TopRep.{u} (ZMod p) G) (n : ℕ) :
    Function.Surjective (ContinuousCohomology.π A n) := by
  let K := TopRep.homogeneousCochains A
  let S := K.sc n
  have hleft : Function.Surjective S.leftHomologyπ := by
    let c : CokernelCofork S.toCycles :=
      CokernelCofork.ofπ (TopModuleCat.cokerπ S.toCycles)
        (TopModuleCat.comp_cokerπ S.toCycles)
    let hc : IsColimit c := TopModuleCat.isColimitCoker S.toCycles
    let d : CokernelCofork S.toCycles :=
      CokernelCofork.ofπ S.leftHomologyπ S.leftHomologyData.wπ
    let hd : IsColimit d := S.leftHomologyData.hπ
    let e : c.pt ≅ d.pt := hc.coconePointUniqueUpToIso hd
    have he : TopModuleCat.cokerπ S.toCycles ≫ e.hom = S.leftHomologyπ := by
      have he' := hc.comp_coconePointUniqueUpToIso_hom hd WalkingParallelPair.one
      change TopModuleCat.cokerπ S.toCycles ≫ e.hom = S.leftHomologyπ at he'
      exact he'
    intro y
    obtain ⟨x, hx⟩ := TopModuleCat.cokerπ_surjective S.toCycles (e.inv y)
    refine ⟨x, ?_⟩
    rw [← he]
    change e.hom (TopModuleCat.cokerπ S.toCycles x) = y
    rw [hx]
    simp
  have hiso : Function.Surjective S.leftHomologyIso.hom :=
    (ConcreteCategory.bijective_of_isIso S.leftHomologyIso.hom).2
  intro y
  obtain ⟨z, hz⟩ := hiso y
  obtain ⟨x, hx⟩ := hleft z
  refine ⟨x, ?_⟩
  change S.leftHomologyIso.hom (S.leftHomologyπ x) = y
  rw [hx, hz]

variable [Fact p.Prime]

/-- A linear choice of a cocycle representative for each continuous cohomology class. -/
noncomputable def homologyRepresentativeSection
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (A : TopRep.{u} (ZMod p) G) (n : ℕ) :
    continuousCohomology n A →ₗ[ZMod p]
      ContinuousCohomology.cocycles A n :=
  Classical.choose <|
    (ContinuousCohomology.π A n).hom.toLinearMap.exists_rightInverse_of_surjective <|
      LinearMap.range_eq_top.2 (homologyπ_surjective A n)

theorem homologyRepresentativeSection_rightInverse
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (A : TopRep.{u} (ZMod p) G) (n : ℕ) :
    (ContinuousCohomology.π A n).hom.toLinearMap.comp
        (homologyRepresentativeSection A n) = LinearMap.id :=
  Classical.choose_spec <|
    (ContinuousCohomology.π A n).hom.toLinearMap.exists_rightInverse_of_surjective <|
      LinearMap.range_eq_top.2 (homologyπ_surjective A n)

theorem freeBoundary_surjective
    {d : ℕ}
    (sourceData :
      FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u}
        (FiniteGroupClass.pGroup p))
    (hbasis : Cardinal.mk sourceData.basis = d) :
    Function.Surjective
      ((Cohomology.trivialZModPCochainsLifted p sourceData.carrier).toCycles 1 2).hom := by
  intro z
  have hz : ContinuousCohomology.π
      (Cohomology.trivialZModPLifted p sourceData.carrier) 2 z = 0 := by
    exact freeProP_continuousCohomologyZModPLifted_degree_two_π_apply_eq_zero
      sourceData hbasis z
  obtain ⟨c, hc⟩ := Cohomology.exists_boundary_of_homologyπ_apply_eq_zero
    (Cohomology.trivialZModPLifted p sourceData.carrier) 1 z hz
  refine ⟨c, ?_⟩
  apply Cohomology.topModule_mono_injective_lifted
    ((Cohomology.trivialZModPCochainsLifted p sourceData.carrier).iCycles 2)
  calc
    _ = ((Cohomology.trivialZModPCochainsLifted p sourceData.carrier).d 1 2).hom c := by
      have hcomp := ConcreteCategory.congr_hom
        ((Cohomology.trivialZModPCochainsLifted p sourceData.carrier).toCycles_i 1 2) c
      exact hcomp
    _ = _ := hc

/-- A linear choice of degree-one primitives for degree-two cocycles on the free source. -/
noncomputable def freePrimitiveSection
    {d : ℕ}
    (sourceData :
      FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u}
        (FiniteGroupClass.pGroup p))
    (hbasis : Cardinal.mk sourceData.basis = d) :
    Cohomology.trivialZModPCocyclesLifted p sourceData.carrier 2 →ₗ[ZMod p]
      (Cohomology.trivialZModPCochainsLifted p sourceData.carrier).X 1 :=
  Classical.choose <|
    ((Cohomology.trivialZModPCochainsLifted p sourceData.carrier).toCycles 1 2).hom.toLinearMap
      |>.exists_rightInverse_of_surjective <|
        LinearMap.range_eq_top.2 (freeBoundary_surjective sourceData hbasis)

theorem freePrimitiveSection_rightInverse
    {d : ℕ}
    (sourceData :
      FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u}
        (FiniteGroupClass.pGroup p))
    (hbasis : Cardinal.mk sourceData.basis = d) :
    ((Cohomology.trivialZModPCochainsLifted p sourceData.carrier).toCycles 1 2).hom.toLinearMap.comp
        (freePrimitiveSection sourceData hbasis) = LinearMap.id :=
  Classical.choose_spec <|
    ((Cohomology.trivialZModPCochainsLifted p sourceData.carrier).toCycles 1 2).hom.toLinearMap
      |>.exists_rightInverse_of_surjective <|
        LinearMap.range_eq_top.2 (freeBoundary_surjective sourceData hbasis)

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
variable {d r : ℕ}
variable {sourceData :
  FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u}
    (FiniteGroupClass.pGroup p)}

/-- The chosen target degree-two cocycle representative. -/
noncomputable def targetCocycleSection :
    Cohomology.continuousCohomologyZModPLifted p G 2 →ₗ[ZMod p]
      Cohomology.trivialZModPCocyclesLifted p G 2 :=
  homologyRepresentativeSection (Cohomology.trivialZModPLifted p G) 2

/-- Pull the chosen target representative back to the free presentation source. -/
noncomputable def presentationPulledCocycle
    (P : FiniteProPPresentation p d r sourceData G) :
    Cohomology.continuousCohomologyZModPLifted p G 2 →ₗ[ZMod p]
      Cohomology.trivialZModPCocyclesLifted p sourceData.carrier 2 :=
  (Cohomology.trivialZModPCocyclesMapLifted p P.quotient 2).hom.toLinearMap.comp
    targetCocycleSection

/-- The chosen free-source primitive of the pulled-back target cocycle. -/
noncomputable def presentationPrimitive
    (P : FiniteProPPresentation p d r sourceData G) :
    Cohomology.continuousCohomologyZModPLifted p G 2 →ₗ[ZMod p]
      (Cohomology.trivialZModPCochainsLifted p sourceData.carrier).X 1 :=
  (freePrimitiveSection sourceData P.basisCard).comp
    (presentationPulledCocycle P)

theorem presentationPrimitive_toCycles
    (P : FiniteProPPresentation p d r sourceData G)
    (x : Cohomology.continuousCohomologyZModPLifted p G 2) :
    ((Cohomology.trivialZModPCochainsLifted p sourceData.carrier).toCycles 1 2).hom
        (presentationPrimitive P x) = presentationPulledCocycle P x := by
  have h := LinearMap.congr_fun
    (freePrimitiveSection_rightInverse sourceData P.basisCard)
      (presentationPulledCocycle P x)
  exact h

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
theorem targetCocycleSection_π
    (x : Cohomology.continuousCohomologyZModPLifted p G 2) :
    ContinuousCohomology.π (Cohomology.trivialZModPLifted p G) 2
        (targetCocycleSection x) = x := by
  have h := LinearMap.congr_fun
    (homologyRepresentativeSection_rightInverse
      (Cohomology.trivialZModPLifted p G) 2) x
  exact h

theorem presentationPrimitive_boundary
    (P : FiniteProPPresentation p d r sourceData G)
    (x : Cohomology.continuousCohomologyZModPLifted p G 2) :
    ((Cohomology.trivialZModPCochainsLifted p sourceData.carrier).d 1 2).hom
        (presentationPrimitive P x) =
      ((Cohomology.trivialZModPCochainsLifted p sourceData.carrier).iCycles 2).hom
        (presentationPulledCocycle P x) := by
  calc
    _ = ((Cohomology.trivialZModPCochainsLifted p sourceData.carrier).iCycles 2).hom
        (((Cohomology.trivialZModPCochainsLifted p sourceData.carrier).toCycles 1 2).hom
          (presentationPrimitive P x)) := by
      have hcomp := ConcreteCategory.congr_hom
        ((Cohomology.trivialZModPCochainsLifted p sourceData.carrier).toCycles_i 1 2)
          (presentationPrimitive P x)
      exact hcomp.symm
    _ = _ := congrArg _ (presentationPrimitive_toCycles P x)

theorem presentationPulledCocycle_apply
    (P : FiniteProPPresentation p d r sourceData G)
    (x : Cohomology.continuousCohomologyZModPLifted p G 2)
    (f₀ f₁ f₂ : sourceData.carrier) :
    (((Cohomology.trivialZModPCochainsLifted p sourceData.carrier).iCycles 2).hom
        (presentationPulledCocycle P x)).1 f₀ f₁ f₂ =
      (((Cohomology.trivialZModPCochainsLifted p G).iCycles 2).hom
        (targetCocycleSection x)).1 (P.quotient f₀) (P.quotient f₁) (P.quotient f₂) := by
  have h := ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i
      (Cohomology.trivialZModPCochainsMapLifted p P.quotient) 2)
      (targetCocycleSection x)
  change
    ((Cohomology.trivialZModPCochainsLifted p sourceData.carrier).iCycles 2).hom
        (presentationPulledCocycle P x) =
      ((Cohomology.trivialZModPCochainsMapLifted p P.quotient).f 2).hom
        (((Cohomology.trivialZModPCochainsLifted p G).iCycles 2).hom
          (targetCocycleSection x)) at h
  rw [h]
  rfl

omit [Fact p.Prime] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
theorem homogeneousTwoCocycleEquation
    (z : Cohomology.trivialZModPCocyclesLifted p G 2)
    (x₀ x₁ x₂ x₃ : G) :
    (((Cohomology.trivialZModPCochainsLifted p G).iCycles 2).hom z).1 x₁ x₂ x₃ -
        (((Cohomology.trivialZModPCochainsLifted p G).iCycles 2).hom z).1 x₀ x₂ x₃ +
        (((Cohomology.trivialZModPCochainsLifted p G).iCycles 2).hom z).1 x₀ x₁ x₃ -
      (((Cohomology.trivialZModPCochainsLifted p G).iCycles 2).hom z).1 x₀ x₁ x₂ = 0 := by
  let C := Cohomology.trivialZModPCochainsLifted p G
  let z₀ : C.X 2 := (C.iCycles 2).hom z
  have hz : (C.d 2 3).hom z₀ = 0 := by
    have hzRaw := ConcreteCategory.congr_hom
      (C.iCycles_d (i := 2) (j := 3)) z
    change (C.d 2 3).hom ((C.iCycles 2).hom z) = 0 at hzRaw
    simpa only [z₀] using hzRaw
  have hzEval := congrArg (fun τ : C.X 3 ↦ τ.1 x₀ x₁ x₂ x₃) hz
  have hd := TopRep.homogeneousCochains.d_apply
    (Cohomology.trivialZModPLifted p G) 2 z₀
  have hdEval := congrArg (fun τ ↦ τ x₀ x₁ x₂ x₃) hd
  rw [hdEval] at hzEval
  simp [C, z₀, TopRep.d_succ, TopRep.d_zero, TopRep.hom_sub,
    ContIntertwiningMap.sub_apply, coind₁ι_toFun, coind₁Map_toFun] at hzEval
  abel_nf at hzEval ⊢
  exact hzEval

omit [Fact p.Prime] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
theorem homogeneousTwoCocycle_leftInvariant
    (z : Cohomology.trivialZModPCocyclesLifted p G 2)
    (g x₀ x₁ x₂ : G) :
    (((Cohomology.trivialZModPCochainsLifted p G).iCycles 2).hom z).1
        (g * x₀) (g * x₁) (g * x₂) =
      (((Cohomology.trivialZModPCochainsLifted p G).iCycles 2).hom z).1 x₀ x₁ x₂ := by
  let X := Cohomology.trivialZModPLifted p G
  let C := Cohomology.trivialZModPCochainsLifted p G
  let z₀ := (C.iCycles 2).hom z
  change (TopRep.resolutionX X 3).ρ.invariants at z₀
  have h := congrArg (fun τ ↦ τ (g * x₀) (g * x₁) (g * x₂)) (z₀.2 g)
  change z₀.1 (g⁻¹ * (g * x₀)) (g⁻¹ * (g * x₁)) (g⁻¹ * (g * x₂)) =
    z₀.1 (g * x₀) (g * x₁) (g * x₂) at h
  simpa only [inv_mul_cancel_left] using h.symm

omit [Fact p.Prime] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
theorem homogeneousTwoCocycle_one_one
    (z : Cohomology.trivialZModPCocyclesLifted p G 2) (g : G) :
    (((Cohomology.trivialZModPCochainsLifted p G).iCycles 2).hom z).1 1 1 g =
      (((Cohomology.trivialZModPCochainsLifted p G).iCycles 2).hom z).1 1 1 1 := by
  have h := homogeneousTwoCocycleEquation z 1 1 1 g
  simpa only [sub_self, zero_add, sub_eq_zero] using h

omit [Fact p.Prime] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
theorem homogeneousTwoCocycle_one_diag
    (z : Cohomology.trivialZModPCocyclesLifted p G 2) (g : G) :
    (((Cohomology.trivialZModPCochainsLifted p G).iCycles 2).hom z).1 1 g g =
      (((Cohomology.trivialZModPCochainsLifted p G).iCycles 2).hom z).1 1 1 1 := by
  have h := homogeneousTwoCocycleEquation z 1 g g g
  have hinv := homogeneousTwoCocycle_leftInvariant z g 1 1 1
  simp only [mul_one] at hinv
  rw [hinv] at h
  abel_nf at h
  have hz :
      (((Cohomology.trivialZModPCochainsLifted p G).iCycles 2).hom z).1 1 1 1 -
        (((Cohomology.trivialZModPCochainsLifted p G).iCycles 2).hom z).1 1 g g = 0 := by
    simpa [sub_eq_add_neg] using h
  exact (sub_eq_zero.mp hz).symm

theorem presentationPrimitive_boundary_apply
    (P : FiniteProPPresentation p d r sourceData G)
    (x : Cohomology.continuousCohomologyZModPLifted p G 2)
    (f₀ f₁ f₂ : sourceData.carrier) :
    (presentationPrimitive P x).1 f₁ f₂ -
        ((presentationPrimitive P x).1 f₀ f₂ -
          (presentationPrimitive P x).1 f₀ f₁) =
      (((Cohomology.trivialZModPCochainsLifted p G).iCycles 2).hom
        (targetCocycleSection x)).1 (P.quotient f₀) (P.quotient f₁) (P.quotient f₂) := by
  have hb := congrArg (fun τ ↦ τ.1 f₀ f₁ f₂)
    (presentationPrimitive_boundary P x)
  have hd := TopRep.homogeneousCochains.d_apply
    (Cohomology.trivialZModPLifted p sourceData.carrier) 1
      (presentationPrimitive P x)
  have hdpoint := congrArg (fun τ ↦ τ f₀ f₁ f₂) hd
  rw [hdpoint, presentationPulledCocycle_apply P x f₀ f₁ f₂] at hb
  simpa [TopRep.d_succ, TopRep.d_zero, TopRep.hom_sub,
    ContIntertwiningMap.sub_apply, coind₁ι_toFun, coind₁Map_toFun] using hb

theorem presentationPrimitive_leftInvariant
    (P : FiniteProPPresentation p d r sourceData G)
    (x : Cohomology.continuousCohomologyZModPLifted p G 2)
    (a f g : sourceData.carrier) :
    (presentationPrimitive P x).1 (a⁻¹ * f) (a⁻¹ * g) =
      (presentationPrimitive P x).1 f g := by
  have hc := (presentationPrimitive P x).2 a
  have h := congrArg (fun τ ↦ τ f g) hc
  have h' :
      (Cohomology.trivialZModPLifted p sourceData.carrier).ρ a
          ((presentationPrimitive P x).1 (a⁻¹ * f) (a⁻¹ * g)) =
        (presentationPrimitive P x).1 f g := by
    simpa only [ContRepresentation.coind₁_apply_apply] using h
  exact
    (Cohomology.trivialZModPLifted_action
      p sourceData.carrier a _).symm.trans h'

end PresentationH2Aux

end

end ClassFieldTower.ProP
