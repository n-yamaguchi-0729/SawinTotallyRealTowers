/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import GaloisCohomology.ProP.DiscreteH2Comparison
import GaloisCohomology.ProP.DiscreteH2ShortComplexComparison
import GaloisCohomology.ProP.DiscreteH2CochainComparison
import GaloisCohomology.ProP.TrivialZModP
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic

set_option autoImplicit false

/-!
# Discrete degree-two comparison on arbitrary representatives

The existing comparison is evaluated on every lifted homogeneous two-cocycle.
The representative is its actual dehomogenization, with no cup-product or
normalization restriction and no extra comparison assumption.
-/

open CategoryTheory CategoryTheory.Limits TopRep

namespace ClassFieldTower.Cohomology

noncomputable section

private theorem mapHomologyIso_homologyπ
    {C : Type*} [Category C] [HasZeroMorphisms C]
    (S : ShortComplex C) (F : C ⥤ AddCommGrpCat) [F.PreservesZeroMorphisms]
    [S.HasHomology] [(S.map F).HasHomology] [F.PreservesLeftHomologyOf S] :
    (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
      (S.mapCyclesIso F).hom ≫ F.map S.homologyπ := by
  let h := S.homologyData.left
  erw [h.mapHomologyIso_eq, h.mapCyclesIso_eq]
  change
    ((S.map F).homologyπ ≫ (h.map F).homologyIso.hom) ≫
        F.map h.homologyIso.inv =
      (h.map F).cyclesIso.hom ≫
        (F.map h.cyclesIso.inv ≫ F.map S.homologyπ)
  rw [(h.map F).homologyπ_comp_homologyIso_hom]
  erw [Category.assoc, cancel_epi]
  change F.map h.π ≫ F.map h.homologyIso.inv =
    F.map h.cyclesIso.inv ≫ F.map S.homologyπ
  simpa only [F.map_comp] using congrArg (fun k ↦ F.map k) h.π_comp_homologyIso_inv

private theorem mapHomologyIso_homologyπ_inv_apply
    {C : Type*} [Category C] [HasZeroMorphisms C]
    (S : ShortComplex C) (F : C ⥤ AddCommGrpCat) [F.PreservesZeroMorphisms]
    [S.HasHomology] [(S.map F).HasHomology] [F.PreservesLeftHomologyOf S]
    (z : F.obj S.cycles) :
    (S.mapHomologyIso F).inv (F.map S.homologyπ z) =
      (S.map F).homologyπ ((S.mapCyclesIso F).inv z) := by
  apply (ConcreteCategory.bijective_of_isIso (S.mapHomologyIso F).hom).1
  rw [Iso.inv_hom_id_apply]
  have h := congrArg (fun f ↦ f ((S.mapCyclesIso F).inv z))
    (mapHomologyIso_homologyπ S F)
  simpa only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply] using h.symm

variable {p : ℕ}
variable {Q : Type} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
variable [DiscreteTopology Q]

/-- The ordinary two-cocycle obtained by dehomogenizing an actual lifted
homogeneous two-cocycle. -/
def dehomogenizedTwoCocycle (z : trivialZModPCocyclesLifted p Q 2) :
    groupCohomology.cocycles₂ (ordinaryTrivialZModPLifted (p := p) (Q := Q)) := by
  refine ⟨dehomogenizeTwo (((trivialZModPCochainsLifted p Q).iCycles 2).hom z), ?_⟩
  rw [groupCohomology.cocycles₂, LinearMap.mem_ker, ← dehomogenizeTwo_d]
  have hz := ConcreteCategory.congr_hom
    ((trivialZModPCochainsLifted p Q).iCycles_d 2 3) z
  change ((trivialZModPCochainsLifted p Q).d 2 3).hom
    (((trivialZModPCochainsLifted p Q).iCycles 2).hom z) = 0 at hz
  rw [hz]
  rfl

/-- The discrete comparison evaluates an arbitrary continuous class represented
by a lifted homogeneous two-cocycle as its ordinary dehomogenized class. -/
theorem discreteContinuousH2AddEquiv_π
    (z₀ : trivialZModPCocyclesLifted p Q 2) :
    discreteContinuousH2AddEquiv
      (ContinuousCohomology.π (trivialZModPLifted p Q) 2 z₀) =
    groupCohomology.H2π (ordinaryTrivialZModPLifted (p := p) (Q := Q))
      (dehomogenizedTwoCocycle z₀) := by
  let SO := groupCohomology.shortComplexH2
    (ordinaryTrivialZModPLifted (p := p) (Q := Q))
  let FO := ordinaryCochainsToAddCommGrp
  let mappedClass :
      (continuousCochainsToAddCommGrp p).obj
        (((trivialZModPCochainsLifted p Q).sc 2).homology) :=
    ContinuousCohomology.π (trivialZModPLifted p Q) 2 z₀
  let ordinaryCycle : SO.moduleCatLeftHomologyData.K := dehomogenizedTwoCocycle z₀
  change
    (groupCohomology.H2Iso
      (ordinaryTrivialZModPLifted (p := p) (Q := Q))).inv
      (SO.moduleCatHomologyIso.hom
        ((SO.mapHomologyIso FO).hom
          ((ShortComplex.homologyMapIso
            (discreteH2MappedShortComplexIso (p := p) (Q := Q))).hom
            ((((trivialZModPCochainsLifted p Q).sc 2).mapHomologyIso
              (continuousCochainsToAddCommGrp p)).inv mappedClass)))) =
    (groupCohomology.H2Iso
      (ordinaryTrivialZModPLifted (p := p) (Q := Q))).inv
      (SO.moduleCatLeftHomologyData.π ordinaryCycle)
  congr 1
  let z : (((trivialZModPCochainsLifted p Q).sc 2).map
      (continuousCochainsToAddCommGrp p)).cycles := (((trivialZModPCochainsLifted p Q).sc 2).mapCyclesIso
    (continuousCochainsToAddCommGrp p)).inv (z₀)
  have hz :
      (((trivialZModPCochainsLifted p Q).sc 2).mapHomologyIso
        (continuousCochainsToAddCommGrp p)).inv mappedClass =
      ((((trivialZModPCochainsLifted p Q).sc 2).map
        (continuousCochainsToAddCommGrp p)).homologyπ) z :=
    mapHomologyIso_homologyπ_inv_apply
      ((trivialZModPCochainsLifted p Q).sc 2) (continuousCochainsToAddCommGrp p) z₀
  rw [hz, discreteH2MappedShortComplexIso_homologyπ_apply]
  let zo := (ShortComplex.cyclesMap
    (discreteH2MappedShortComplexIso (p := p) (Q := Q)).hom) z
  have hnatO := mapHomologyIso_homologyπ SO FO
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
      (z₀) := by
    have h := congrArg (fun f ↦ f z) (KS.mapCyclesIso_hom_iCycles KF)
    rw [CategoryTheory.ConcreteCategory.comp_apply] at h
    have hzcycle : (KS.mapCyclesIso KF).hom z =
        z₀ := by
      dsimp only [z, KS, KF]
      exact Iso.inv_hom_id_apply _ _
    rw [hzcycle] at h
    exact h.symm
  rw [hKi]
  have hCochain : (KF.map KS.iCycles) (z₀) =
      ((trivialZModPCochainsLifted p Q).iCycles 2).hom z₀ := by
    change
      (trivialZModPCochainsLifted p Q).iCycles 2
          (z₀) =
        ((trivialZModPCochainsLifted p Q).iCycles 2).hom z₀
    rfl
  rw [hCochain]
  rfl

end

end ClassFieldTower.Cohomology
