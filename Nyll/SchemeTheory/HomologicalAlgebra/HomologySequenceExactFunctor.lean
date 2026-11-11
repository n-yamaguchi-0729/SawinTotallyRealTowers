/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Exact functors and the actual connecting morphism

The existing homology comparison preserves the cycle inclusion, homology projection and
opcycle projection. Applying an exact functor to the original snake diagram therefore
preserves its connecting morphism. The comparison uses the same diagram and its actual
pullback projections; it does not select a new connecting map.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

namespace CategoryTheory.ShortComplex

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
variable (S : ShortComplex C) (F : C ⥤ D) [F.Additive]
variable [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The opcycle comparison retains the original quotient projection. -/
theorem pOpcycles_mapOpcyclesIso_hom :
    (S.map F).pOpcycles ≫ (S.mapOpcyclesIso F).hom = F.map S.pOpcycles :=
  (S.rightHomologyData.map F).pOpcycles_comp_opcyclesIso_hom

/-- The existing homology comparison retains the original projection of cycles. -/
theorem homologyπ_mapHomologyIso_hom :
    (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
      (S.mapCyclesIso F).hom ≫ F.map S.homologyπ := by
  let h := S.leftHomologyData
  let eH : (S.map F).homology ≅ F.obj h.H := (h.map F).homologyIso
  let eK : (S.map F).cycles ≅ F.obj h.K := (h.map F).cyclesIso
  have hπ : (S.map F).homologyπ ≫ eH.hom = eK.hom ≫ F.map h.π :=
    (h.map F).homologyπ_comp_homologyIso_hom
  rw [h.mapHomologyIso_eq F, h.mapCyclesIso_eq F]
  change (S.map F).homologyπ ≫ (eH.hom ≫ F.map h.homologyIso.inv) =
    (eK.hom ≫ F.map h.cyclesIso.inv) ≫ F.map S.homologyπ
  rw [← assoc, hπ, assoc, assoc]
  rw [← F.map_comp, h.π_comp_homologyIso_inv, F.map_comp]

/-- The existing homology comparison retains the original inclusion into opcycles. -/
theorem mapHomologyIso_hom_homologyι :
    (S.mapHomologyIso F).hom ≫ F.map S.homologyι =
      (S.map F).homologyι ≫ (S.mapOpcyclesIso F).hom := by
  let h := S.rightHomologyData
  let eH : (S.map F).homology ≅ F.obj h.H := (h.map F).homologyIso
  let eQ : (S.map F).opcycles ≅ F.obj h.Q := (h.map F).opcyclesIso
  have hι : eH.hom ≫ F.map h.ι = (S.map F).homologyι ≫ eQ.hom :=
    (h.map F).homologyIso_hom_comp_ι
  rw [← S.mapHomologyIso'_eq_mapHomologyIso F,
    h.mapHomologyIso'_eq F, h.mapOpcyclesIso_eq F]
  change (eH.hom ≫ F.map h.homologyIso.inv) ≫ F.map S.homologyι =
    (S.map F).homologyι ≫ (eQ.hom ≫ F.map h.opcyclesIso.inv)
  rw [assoc, ← F.map_comp, h.homologyIso_inv_comp_homologyι, F.map_comp,
    ← assoc, hι, assoc]

end CategoryTheory.ShortComplex

namespace HomologicalComplex

variable {C D ι : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
variable {c : ComplexShape ι} (F : C ⥤ D) [F.Additive]
variable [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The opcycle-to-cycle differential is preserved by the actual homology comparisons. -/
theorem map_opcyclesToCycles (K : HomologicalComplex C c) (i j : ι) :
    ((F.mapHomologicalComplex c).obj K).opcyclesToCycles i j ≫
        ((K.sc j).mapCyclesIso F).hom =
      ((K.sc i).mapOpcyclesIso F).hom ≫ F.map (K.opcyclesToCycles i j) := by
  let K' := (F.mapHomologicalComplex c).obj K
  let eC : K'.cycles j ≅ F.obj (K.cycles j) := (K.sc j).mapCyclesIso F
  let eO : K'.opcycles i ≅ F.obj (K.opcycles i) := (K.sc i).mapOpcyclesIso F
  have hC : eC.hom ≫ F.map (K.iCycles j) = K'.iCycles j :=
    (K.sc j).mapCyclesIso_hom_iCycles F
  have hP : K'.pOpcycles i ≫ eO.hom = F.map (K.pOpcycles i) :=
    (K.sc i).pOpcycles_mapOpcyclesIso_hom F
  change K'.opcyclesToCycles i j ≫ eC.hom = eO.hom ≫ F.map (K.opcyclesToCycles i j)
  apply (cancel_epi (K'.pOpcycles i)).1
  apply (cancel_mono (F.map (K.iCycles j))).1
  calc
    (K'.pOpcycles i ≫ (K'.opcyclesToCycles i j ≫ eC.hom)) ≫ F.map (K.iCycles j) =
      K'.pOpcycles i ≫ K'.opcyclesToCycles i j ≫ K'.iCycles j := by
        rw [assoc, assoc, hC]
    _ = F.map (K.d i j) := K'.pOpcycles_opcyclesToCycles_iCycles i j
    _ = (K'.pOpcycles i ≫ (eO.hom ≫ F.map (K.opcyclesToCycles i j))) ≫
        F.map (K.iCycles j) := by
      rw [← assoc, hP, ← F.map_comp, ← F.map_comp, assoc,
        K.pOpcycles_opcyclesToCycles_iCycles]

end HomologicalComplex

namespace CategoryTheory.ShortComplex.ShortExact

variable {C D ι : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
variable {c : ComplexShape ι} {S : ShortComplex (HomologicalComplex C c)}
variable (hS : S.ShortExact) (F : C ⥤ D) [F.Additive]
variable [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- An exact functor carries the original connecting map to the mapped short exact sequence. -/
theorem map_δ_eq (i j : ι) (hij : c.Rel i j) :
    (hS.map_of_exact (F.mapHomologicalComplex c)).δ i j hij ≫
        ((S.X₁.sc j).mapHomologyIso F).hom =
      ((S.X₃.sc i).mapHomologyIso F).hom ≫ F.map (hS.δ i j hij) := by
  let T := S.map (F.mapHomologicalComplex c)
  have hT : T.ShortExact := hS.map_of_exact (F.mapHomologicalComplex c)
  let Z := HomologicalComplex.HomologySequence.snakeInput hS i j hij
  let p : Z.P ⟶ S.X₂.opcycles i := pullback.fst _ _
  let q : Z.P ⟶ S.X₃.homology i := pullback.snd _ _
  let a : Z.P ⟶ S.X₁.cycles j := Z.φ₁
  let eH₃ : T.X₃.homology i ≅ F.obj (S.X₃.homology i) :=
    (S.X₃.sc i).mapHomologyIso F
  let eH₁ : T.X₁.homology j ≅ F.obj (S.X₁.homology j) :=
    (S.X₁.sc j).mapHomologyIso F
  let eO₂ : T.X₂.opcycles i ≅ F.obj (S.X₂.opcycles i) :=
    (S.X₂.sc i).mapOpcyclesIso F
  let eO₃ : T.X₃.opcycles i ≅ F.obj (S.X₃.opcycles i) :=
    (S.X₃.sc i).mapOpcyclesIso F
  let eC₁ : T.X₁.cycles j ≅ F.obj (S.X₁.cycles j) := (S.X₁.sc j).mapCyclesIso F
  let eC₂ : T.X₂.cycles j ≅ F.obj (S.X₂.cycles j) := (S.X₂.sc j).mapCyclesIso F
  have hp : p ≫ HomologicalComplex.opcyclesMap S.g i = q ≫ S.X₃.homologyι i :=
    pullback.condition
  have ha : a ≫ HomologicalComplex.cyclesMap S.f j =
      p ≫ S.X₂.opcyclesToCycles i j := Z.φ₁_L₂_f
  have hq : q ≫ hS.δ i j hij = a ≫ S.X₁.homologyπ j := Z.snd_δ
  have hO : HomologicalComplex.opcyclesMap T.g i ≫ eO₃.hom =
      eO₂.hom ≫ F.map (HomologicalComplex.opcyclesMap S.g i) :=
    ShortComplex.mapOpcyclesIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor C c i).map S.g) F
  have hC : HomologicalComplex.cyclesMap T.f j ≫ eC₂.hom =
      eC₁.hom ≫ F.map (HomologicalComplex.cyclesMap S.f j) :=
    ShortComplex.mapCyclesIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor C c j).map S.f) F
  have hι : eH₃.hom ≫ F.map (S.X₃.homologyι i) =
      T.X₃.homologyι i ≫ eO₃.hom :=
    (S.X₃.sc i).mapHomologyIso_hom_homologyι F
  have hd : T.X₂.opcyclesToCycles i j ≫ eC₂.hom =
      eO₂.hom ≫ F.map (S.X₂.opcyclesToCycles i j) :=
    HomologicalComplex.map_opcyclesToCycles F S.X₂ i j
  have hπ : T.X₁.homologyπ j ≫ eH₁.hom =
      eC₁.hom ≫ F.map (S.X₁.homologyπ j) :=
    (S.X₁.sc j).homologyπ_mapHomologyIso_hom F
  have h₂ : (F.map p ≫ eO₂.inv) ≫ HomologicalComplex.opcyclesMap T.g i =
      (F.map q ≫ eH₃.inv) ≫ T.X₃.homologyι i := by
    apply (cancel_mono eO₃.hom).1
    simp only [assoc, hO, ← hι, Iso.inv_hom_id_assoc]
    rw [← F.map_comp, hp, F.map_comp]
  have h₁ : (F.map a ≫ eC₁.inv) ≫ HomologicalComplex.cyclesMap T.f j =
      (F.map p ≫ eO₂.inv) ≫ T.X₂.opcyclesToCycles i j := by
    apply (cancel_mono eC₂.hom).1
    simp only [assoc, hC, hd, Iso.inv_hom_id_assoc]
    rw [← F.map_comp, ha, F.map_comp]
  have hδ := hT.δ_eq' i j hij (F.map q ≫ eH₃.inv)
    (F.map p ≫ eO₂.inv) (F.map a ≫ eC₁.inv) h₂ h₁
  have : Epi Z.L₁.g := Z.epi_L₁_g
  have : Epi q := Abelian.epi_pullback_of_epi_f Z.L₁.g Z.v₀₁.τ₃
  apply (cancel_epi eH₃.inv).1
  apply (cancel_epi (F.map q)).1
  change F.map q ≫ (eH₃.inv ≫ (hT.δ i j hij ≫ eH₁.hom)) =
    F.map q ≫ (eH₃.inv ≫ (eH₃.hom ≫ F.map (hS.δ i j hij)))
  rw [Iso.inv_hom_id_assoc]
  calc
    F.map q ≫ (eH₃.inv ≫ (hT.δ i j hij ≫ eH₁.hom)) =
        ((F.map q ≫ eH₃.inv) ≫ hT.δ i j hij) ≫ eH₁.hom := by
      rw [assoc, assoc]
    _ = ((F.map a ≫ eC₁.inv) ≫ T.X₁.homologyπ j) ≫ eH₁.hom :=
      congrArg (fun f => f ≫ eH₁.hom) hδ
    _ = F.map a ≫ F.map (S.X₁.homologyπ j) := by
      rw [assoc, assoc, hπ, Iso.inv_hom_id_assoc]
    _ = F.map q ≫ F.map (hS.δ i j hij) := by
      rw [← F.map_comp, ← hq, F.map_comp]

end CategoryTheory.ShortComplex.ShortExact
