/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import GaloisCohomology.ProP.ContinuousH1CupProduct
import GaloisCohomology.ProP.DiscreteH2ShortComplexComparison
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

set_option autoImplicit false
/-!
# Continuous and ordinary degree-two cohomology of a discrete group

For a discrete group in the base universe, the explicit homogeneous and
inhomogeneous comparison induces an additive equivalence in degree two.
The ordinary coefficient object is exactly the trivial `Int`-representation
on `ULift (ZMod p)` used by finite Kummer coefficient change.
-/

open CategoryTheory TopRep
open ClassFieldTower.ProP

namespace ClassFieldTower.Cohomology

noncomputable section

variable {p : ℕ}
variable {Q : Type} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
variable [DiscreteTopology Q]

/-- The comparison short-complex isomorphism, with the canonical
`sc 2 ≅ sc' 1 2 3` identification included. -/
noncomputable def discreteH2MappedShortComplexIso :
    ((trivialZModPCochainsLifted p Q).sc 2).map
        (continuousCochainsToAddCommGrp p) ≅
      (groupCohomology.shortComplexH2
          (ordinaryTrivialZModPLifted (p := p) (Q := Q))).map
        ordinaryCochainsToAddCommGrp :=
  (continuousCochainsToAddCommGrp p).mapShortComplex.mapIso
      ((trivialZModPCochainsLifted p Q).isoSc' 1 2 3
        (by simp) (by simp)) ≪≫
    discreteH2ShortComplexIso (p := p) (Q := Q)

/-- The canonical additive-group isomorphism from lifted continuous
degree-two cohomology to ordinary degree-two group cohomology. -/
noncomputable def discreteContinuousH2AddCommGrpIso :
    (continuousCochainsToAddCommGrp p).obj
        (continuousCohomologyZModPLifted p Q 2) ≅
      ordinaryCochainsToAddCommGrp.obj
        (groupCohomology
          (ordinaryTrivialZModPLifted (p := p) (Q := Q)) 2) := by
  let K := trivialZModPCochainsLifted p Q
  let S := groupCohomology.shortComplexH2
    (ordinaryTrivialZModPLifted (p := p) (Q := Q))
  change
    (continuousCochainsToAddCommGrp p).obj ((K.sc 2).homology) ≅
      ordinaryCochainsToAddCommGrp.obj
        (groupCohomology
          (ordinaryTrivialZModPLifted (p := p) (Q := Q)) 2)
  exact
    ((K.sc 2).mapHomologyIso (continuousCochainsToAddCommGrp p)).symm ≪≫
      ShortComplex.homologyMapIso
        (discreteH2MappedShortComplexIso (p := p) (Q := Q)) ≪≫
      S.mapHomologyIso ordinaryCochainsToAddCommGrp ≪≫
      ordinaryCochainsToAddCommGrp.mapIso S.moduleCatHomologyIso ≪≫
      ordinaryCochainsToAddCommGrp.mapIso
        (groupCohomology.H2Iso
          (ordinaryTrivialZModPLifted (p := p) (Q := Q))).symm

/-- Continuous homogeneous and ordinary inhomogeneous degree-two
cohomology are additively equivalent for a discrete group. -/
noncomputable def discreteContinuousH2AddEquiv :
    continuousCohomologyZModPLifted p Q 2 ≃+
      groupCohomology
        (ordinaryTrivialZModPLifted (p := p) (Q := Q)) 2 :=
  (discreteContinuousH2AddCommGrpIso (p := p) (Q := Q)).addCommGroupIsoToAddEquiv

/-- The inhomogeneous cochain obtained from the canonical character cup. -/
def ordinaryH1CupTwoCochain
    (chi psi : ContinuousH1ZMod (p := p) (G := Q)) :
    Q × Q → ULift (ZMod p) :=
  fun gh ↦ ULift.up
    (chi (Additive.ofMul gh.1) * psi (Additive.ofMul gh.2))

omit [DiscreteTopology Q] in
/-- The explicit homogeneous cup cochain dehomogenizes to the standard
inhomogeneous cup formula. -/
theorem dehomogenizeTwo_continuousH1Cup
    (chi psi : ContinuousH1ZMod (p := p) (G := Q)) :
    dehomogenizeTwo
        (continuousH1CupHomogeneousTwoCochainLifted chi psi) =
      ordinaryH1CupTwoCochain chi psi := by
  funext gh
  change
    ULift.up
        (chi (Additive.ofMul (1⁻¹ * gh.1)) *
          psi (Additive.ofMul (gh.1⁻¹ * (gh.1 * gh.2)))) =
      ULift.up
        (chi (Additive.ofMul gh.1) * psi (Additive.ofMul gh.2))
  simp

/-- The ordinary inhomogeneous two-cocycle represented by the canonical
character cup formula. -/
noncomputable def ordinaryH1CupTwoCocycle
    (chi psi : ContinuousH1ZMod (p := p) (G := Q)) :
    groupCohomology.cocycles₂
      (ordinaryTrivialZModPLifted (p := p) (Q := Q)) := by
  refine ⟨ordinaryH1CupTwoCochain chi psi, ?_⟩
  rw [groupCohomology.cocycles₂, LinearMap.mem_ker]
  rw [← dehomogenizeTwo_continuousH1Cup]
  rw [← dehomogenizeTwo_d]
  rw [continuousH1CupHomogeneousTwoCochainLifted_mem_cycles]
  rfl

/-- The ordinary degree-two class represented by the canonical character
cup formula. -/
noncomputable def ordinaryH1CupClass
    (chi psi : ContinuousH1ZMod (p := p) (G := Q)) :
    groupCohomology
      (ordinaryTrivialZModPLifted (p := p) (Q := Q)) 2 :=
  groupCohomology.H2π
    (ordinaryTrivialZModPLifted (p := p) (Q := Q))
    (ordinaryH1CupTwoCocycle chi psi)

/-- The short-complex comparison carries a homology class represented by
a homogeneous cycle to the class of its dehomogenized ordinary cycle. -/
theorem discreteH2ShortComplexIso_homologyπ :
    (((trivialZModPCochainsLifted p Q).sc' 1 2 3).map
        (continuousCochainsToAddCommGrp p)).homologyπ ≫
      (ShortComplex.homologyMapIso
        (discreteH2ShortComplexIso (p := p) (Q := Q))).hom =
    ShortComplex.cyclesMap
        (discreteH2ShortComplexIso (p := p) (Q := Q)).hom ≫
      ((groupCohomology.shortComplexH2
          (ordinaryTrivialZModPLifted (p := p) (Q := Q))).map
        ordinaryCochainsToAddCommGrp).homologyπ :=
  ShortComplex.homologyπ_naturality _

/-- The mapped short-complex comparison sends a continuous class to its mapped cycle class. -/
theorem discreteH2MappedShortComplexIso_homologyπ_apply
    (z : (((trivialZModPCochainsLifted p Q).sc 2).map
      (continuousCochainsToAddCommGrp p)).cycles) :
    (ShortComplex.homologyMapIso
        (discreteH2MappedShortComplexIso (p := p) (Q := Q))).hom
        (((((trivialZModPCochainsLifted p Q).sc 2).map
          (continuousCochainsToAddCommGrp p)).homologyπ) z) =
      (((groupCohomology.shortComplexH2
          (ordinaryTrivialZModPLifted (p := p) (Q := Q))).map
        ordinaryCochainsToAddCommGrp).homologyπ)
        ((ShortComplex.cyclesMap
          (discreteH2MappedShortComplexIso (p := p) (Q := Q)).hom) z) := by
  exact congrArg (fun f ↦ f z) (ShortComplex.homologyπ_naturality
    (discreteH2MappedShortComplexIso (p := p) (Q := Q)).hom)

/-- The mapped representative is the dehomogenized ordinary two-cochain. -/
theorem discreteH2MappedShortComplexIso_cyclesMap_cochain
    (z : (((trivialZModPCochainsLifted p Q).sc 2).map
      (continuousCochainsToAddCommGrp p)).cycles) :
    (((groupCohomology.shortComplexH2
        (ordinaryTrivialZModPLifted (p := p) (Q := Q))).map
      ordinaryCochainsToAddCommGrp).iCycles)
        ((ShortComplex.cyclesMap
          (discreteH2MappedShortComplexIso (p := p) (Q := Q)).hom) z) =
      dehomogenizeTwo
        (((((trivialZModPCochainsLifted p Q).sc 2).map
          (continuousCochainsToAddCommGrp p)).iCycles) z) := by
  change
    ((ShortComplex.cyclesMap
      (discreteH2MappedShortComplexIso (p := p) (Q := Q)).hom ≫
        ((groupCohomology.shortComplexH2
          (ordinaryTrivialZModPLifted (p := p) (Q := Q))).map
            ordinaryCochainsToAddCommGrp).iCycles) z) = _
  rw [ShortComplex.cyclesMap_i]
  rfl

/-- The discrete comparison sends the continuous cup to the ordinary cup class. -/
theorem discreteContinuousH2AddEquiv_continuousH1Cup
    (chi psi : ContinuousH1ZMod (p := p) (G := Q)) :
    discreteContinuousH2AddEquiv (continuousH1CupProductLifted chi psi) =
      ordinaryH1CupClass chi psi := by
  change
    (discreteContinuousH2AddCommGrpIso (p := p) (Q := Q)).hom
        (ContinuousCohomology.π (trivialZModPLifted p Q) 2
          (continuousH1CupHomogeneousTwoCocycleLifted chi psi)) =
      groupCohomology.H2π
        (ordinaryTrivialZModPLifted (p := p) (Q := Q))
        (ordinaryH1CupTwoCocycle chi psi)
  apply (ConcreteCategory.bijective_of_isIso (groupCohomology.H2Iso
    (ordinaryTrivialZModPLifted (p := p) (Q := Q))).hom).1
  simp only [groupCohomology.H2π, CategoryTheory.ConcreteCategory.comp_apply,
    groupCohomology.π_comp_H2Iso_hom_apply, Iso.inv_hom_id_apply]
  let cupClassMapped :
      (continuousCochainsToAddCommGrp p).obj
        (((trivialZModPCochainsLifted p Q).sc 2).homology) :=
    ContinuousCohomology.π (trivialZModPLifted p Q) 2
      (continuousH1CupHomogeneousTwoCocycleLifted chi psi)
  let SO := groupCohomology.shortComplexH2
    (ordinaryTrivialZModPLifted (p := p) (Q := Q))
  let FO := ordinaryCochainsToAddCommGrp
  let cupCycle : SO.moduleCatLeftHomologyData.K :=
    ordinaryH1CupTwoCocycle chi psi
  change
    (groupCohomology.H2Iso
      (ordinaryTrivialZModPLifted (p := p) (Q := Q))).hom
      ((((((trivialZModPCochainsLifted p Q).sc 2).mapHomologyIso
          (continuousCochainsToAddCommGrp p)).symm ≪≫
        ShortComplex.homologyMapIso
          (discreteH2MappedShortComplexIso (p := p) (Q := Q)) ≪≫
        (groupCohomology.shortComplexH2
          (ordinaryTrivialZModPLifted (p := p) (Q := Q))).mapHomologyIso
            ordinaryCochainsToAddCommGrp ≪≫
        ordinaryCochainsToAddCommGrp.mapIso
          (groupCohomology.shortComplexH2
            (ordinaryTrivialZModPLifted (p := p) (Q := Q))).moduleCatHomologyIso ≪≫
        ordinaryCochainsToAddCommGrp.mapIso
          (groupCohomology.H2Iso
            (ordinaryTrivialZModPLifted (p := p) (Q := Q))).symm).hom)
        cupClassMapped) =
      SO.moduleCatLeftHomologyData.π cupCycle
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  have hH
      (x : SO.moduleCatLeftHomologyData.H) :
      (groupCohomology.H2Iso
        (ordinaryTrivialZModPLifted (p := p) (Q := Q))).hom
          (FO.map
            (groupCohomology.H2Iso
              (ordinaryTrivialZModPLifted (p := p) (Q := Q))).inv x) = x := by
    change
      (groupCohomology.H2Iso
        (ordinaryTrivialZModPLifted (p := p) (Q := Q))).hom
          ((groupCohomology.H2Iso
            (ordinaryTrivialZModPLifted (p := p) (Q := Q))).inv x) = x
    exact Iso.inv_hom_id_apply _ x
  let cupH : SO.moduleCatLeftHomologyData.H :=
    SO.moduleCatHomologyIso.hom
      ((SO.mapHomologyIso FO).hom
        ((ShortComplex.homologyMapIso
          (discreteH2MappedShortComplexIso (p := p) (Q := Q))).hom
          ((((trivialZModPCochainsLifted p Q).sc 2).mapHomologyIso
            (continuousCochainsToAddCommGrp p)).inv cupClassMapped)))
  change
    (groupCohomology.H2Iso
      (ordinaryTrivialZModPLifted (p := p) (Q := Q))).hom
        (FO.map
          (groupCohomology.H2Iso
            (ordinaryTrivialZModPLifted (p := p) (Q := Q))).inv cupH) =
      SO.moduleCatLeftHomologyData.π cupCycle
  rw [hH]
  change
    SO.moduleCatHomologyIso.hom
      ((SO.mapHomologyIso FO).hom
        ((ShortComplex.homologyMapIso
          (discreteH2MappedShortComplexIso (p := p) (Q := Q))).hom
          ((((trivialZModPCochainsLifted p Q).sc 2).mapHomologyIso
            (continuousCochainsToAddCommGrp p)).inv
            (ContinuousCohomology.π (trivialZModPLifted p Q) 2
              (continuousH1CupHomogeneousTwoCocycleLifted chi psi))))) =
      SO.moduleCatLeftHomologyData.π cupCycle
  let z : (((trivialZModPCochainsLifted p Q).sc 2).map
      (continuousCochainsToAddCommGrp p)).cycles := (((trivialZModPCochainsLifted p Q).sc 2).mapCyclesIso
    (continuousCochainsToAddCommGrp p)).inv (continuousH1CupHomogeneousTwoCocycleLifted chi psi)
  have hz :
      (((trivialZModPCochainsLifted p Q).sc 2).mapHomologyIso
        (continuousCochainsToAddCommGrp p)).inv
          cupClassMapped =
        ((((trivialZModPCochainsLifted p Q).sc 2).map
          (continuousCochainsToAddCommGrp p)).homologyπ) z := by
    let S := (trivialZModPCochainsLifted p Q).sc 2
    let F := continuousCochainsToAddCommGrp p
    let h := S.homologyData.left
    have hnat :
        (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
          (S.mapCyclesIso F).hom ≫ F.map S.homologyπ := by
      erw [h.mapHomologyIso_eq, h.mapCyclesIso_eq]
      change
        ((S.map F).homologyπ ≫ (h.map F).homologyIso.hom) ≫
            F.map h.homologyIso.inv =
          (h.map F).cyclesIso.hom ≫
            (F.map h.cyclesIso.inv ≫ F.map S.homologyπ)
      rw [(h.map F).homologyπ_comp_homologyIso_hom]
      erw [Category.assoc, cancel_epi]
      have hMapped :
          F.map h.π ≫ F.map h.homologyIso.inv =
            F.map h.cyclesIso.inv ≫ F.map S.homologyπ := by
        simpa only [F.map_comp] using
          congrArg (fun k ↦ F.map k) h.π_comp_homologyIso_inv
      have hOwner :
          (F.map h.π ≫ F.map h.homologyIso.inv =
              F.map h.cyclesIso.inv ≫ F.map S.homologyπ) =
            ((h.map F).π ≫ F.map h.homologyIso.inv =
              F.map h.cyclesIso.inv ≫ F.map S.homologyπ) := by
        rfl
      exact hOwner.mp hMapped
    have hz' := congrArg (fun f ↦ f z) hnat
    have hzcycle :
        (S.mapCyclesIso F).hom z =
          continuousH1CupHomogeneousTwoCocycleLifted chi psi := by
      dsimp only [z]
      exact Iso.inv_hom_id_apply _ _
    have hforget :
        (F.map S.homologyπ)
            (continuousH1CupHomogeneousTwoCocycleLifted chi psi) =
          cupClassMapped := by
      rfl
    apply (ConcreteCategory.bijective_of_isIso (S.mapHomologyIso F).hom).1
    rw [Iso.inv_hom_id_apply, ← hforget]
    simp only [CategoryTheory.ConcreteCategory.comp_apply] at hz'
    rw [hzcycle] at hz'
    exact hz'.symm
  rw [hz, discreteH2MappedShortComplexIso_homologyπ_apply]
  let zo := (ShortComplex.cyclesMap
    (discreteH2MappedShortComplexIso (p := p) (Q := Q)).hom) z
  let ho := SO.homologyData.left
  have hnatO :
      (SO.map FO).homologyπ ≫ (SO.mapHomologyIso FO).hom =
        (SO.mapCyclesIso FO).hom ≫ FO.map SO.homologyπ := by
    erw [ho.mapHomologyIso_eq, ho.mapCyclesIso_eq]
    change
      ((SO.map FO).homologyπ ≫ (ho.map FO).homologyIso.hom) ≫
          FO.map ho.homologyIso.inv =
        (ho.map FO).cyclesIso.hom ≫
          (FO.map ho.cyclesIso.inv ≫ FO.map SO.homologyπ)
    rw [(ho.map FO).homologyπ_comp_homologyIso_hom]
    erw [Category.assoc, cancel_epi]
    have hMapped :
        FO.map ho.π ≫ FO.map ho.homologyIso.inv =
          FO.map ho.cyclesIso.inv ≫ FO.map SO.homologyπ := by
      simpa only [FO.map_comp] using
        congrArg (fun k ↦ FO.map k) ho.π_comp_homologyIso_inv
    have hOwner :
        (FO.map ho.π ≫ FO.map ho.homologyIso.inv =
            FO.map ho.cyclesIso.inv ≫ FO.map SO.homologyπ) =
          ((ho.map FO).π ≫ FO.map ho.homologyIso.inv =
            FO.map ho.cyclesIso.inv ≫ FO.map SO.homologyπ) := by
      rfl
    exact hOwner.mp hMapped
  have hzo := congrArg (fun f ↦ f zo) hnatO
  have hzo' : (SO.mapHomologyIso FO).hom ((SO.map FO).homologyπ zo) =
      (FO.map SO.homologyπ) ((SO.mapCyclesIso FO).hom zo) := by
    simpa only [CategoryTheory.ConcreteCategory.comp_apply] using hzo
  rw [hzo']
  have hforgetO : (FO.map SO.homologyπ) ((SO.mapCyclesIso FO).hom zo) =
      SO.homologyπ ((SO.mapCyclesIso FO).hom zo) := by
    rfl
  rw [hforgetO, ShortComplex.π_moduleCatCyclesIso_hom_apply]
  congr 1
  apply (ModuleCat.mono_iff_injective
    (groupCohomology.shortComplexH2
      (ordinaryTrivialZModPLifted (p := p) (Q := Q))).moduleCatLeftHomologyData.i).1
    inferInstance
  rw [ShortComplex.moduleCatCyclesIso_hom_i_apply]
  have hSOi : SO.iCycles ((SO.mapCyclesIso FO).hom zo) = (SO.map FO).iCycles zo := by
    change
      (FO.map SO.iCycles) ((SO.mapCyclesIso FO).hom zo) =
        (SO.map FO).iCycles zo
    have h := congrArg (fun f ↦ f zo) (SO.mapCyclesIso_hom_iCycles FO)
    exact h
  rw [hSOi]
  dsimp only [zo]
  rw [discreteH2MappedShortComplexIso_cyclesMap_cochain]
  let KS := (trivialZModPCochainsLifted p Q).sc 2
  let KF := continuousCochainsToAddCommGrp p
  have hKi : (KS.map KF).iCycles z = (KF.map KS.iCycles)
      (continuousH1CupHomogeneousTwoCocycleLifted chi psi) := by
    have h := congrArg (fun f ↦ f z) (KS.mapCyclesIso_hom_iCycles KF)
    rw [CategoryTheory.ConcreteCategory.comp_apply] at h
    have hzcycle : (KS.mapCyclesIso KF).hom z =
        continuousH1CupHomogeneousTwoCocycleLifted chi psi := by
      dsimp only [z, KS, KF]
      exact Iso.inv_hom_id_apply _ _
    rw [hzcycle] at h
    exact h.symm
  rw [hKi]
  have hCup : (KF.map KS.iCycles) (continuousH1CupHomogeneousTwoCocycleLifted chi psi) =
      continuousH1CupHomogeneousTwoCochainLifted chi psi := by
    change
      (trivialZModPCochainsLifted p Q).iCycles 2
          (continuousH1CupHomogeneousTwoCocycleLifted chi psi) =
        continuousH1CupHomogeneousTwoCochainLifted chi psi
    exact iCycles_continuousH1CupHomogeneousTwoCocycleLifted chi psi
  rw [hCup, dehomogenizeTwo_continuousH1Cup]
  rfl

end

end ClassFieldTower.Cohomology
