/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.CategoryTheory.Abelian.Ext
public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic

/-!
# The actual projective-resolution comparison for group cohomology

These are the existing linear Yoneda map and its Ext comparison, with their original public
names and construction. They depend only on a group, not on finiteness or commutativity. Keeping
the calculation here lets both the finite-cyclic comparison and native Shapiro use the same
resolution-independent homology map.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite

namespace ClassFieldTower.Cohomology

universe u

variable {R G : Type u} [CommRing R] [Group G]

/-- The contravariant cochain map induced by a map of projective resolutions. -/
def resolutionLinearYonedaMap
    {X X' : Rep R G} {f : X ⟶ X'}
    (P : ProjectiveResolution X) (P' : ProjectiveResolution X')
    (phi : ProjectiveResolution.Hom P P' f) (A : Rep R G) :
    P'.complex.linearYonedaObj R A ⟶ P.complex.linearYonedaObj R A :=
  (HomologicalComplex.unopFunctor
      (ModuleCat.{u} R) (ComplexShape.down ℕ)).map
    (((((linearYoneda R (Rep R G)).obj A).rightOp.mapHomologicalComplex
      (ComplexShape.down ℕ)).map phi.hom).op)

@[simp]
theorem resolutionLinearYonedaMap_f
    {X X' : Rep R G} {f : X ⟶ X'}
    (P : ProjectiveResolution X) (P' : ProjectiveResolution X')
    (phi : ProjectiveResolution.Hom P P' f) (A : Rep R G) (n : ℕ) :
    (resolutionLinearYonedaMap P P' phi A).f n =
      ModuleCat.ofHom (Linear.leftComp R A (phi.hom.f n)) := rfl

theorem resolution_isoExt_hom_naturality
    {X X' : Rep R G} {f : X ⟶ X'}
    (P : ProjectiveResolution X) (P' : ProjectiveResolution X')
    (phi : ProjectiveResolution.Hom P P' f) (A : Rep R G) (i : ℕ) :
    (((_root_.Ext R (Rep R G) i).map f.op).app A) ≫ (P.isoExt i A).hom =
      (P'.isoExt i A).hom ≫
        HomologicalComplex.homologyMap
          (resolutionLinearYonedaMap P P' phi A) i := by
  dsimp [ProjectiveResolution.isoExt, _root_.Ext]
  have h := ProjectiveResolution.isoLeftDerivedObj_inv_naturality
    f P P' phi.hom phi.hom_f_zero_comp_π_f_zero
      ((linearYoneda R (Rep R G)).obj A).rightOp i
  have hUnop := congr_arg Quiver.Hom.unop h
  have hLeftDerivedRaw :
      ((((linearYoneda R (Rep R G)).obj A).rightOp.leftDerived i).map f).unop ≫
        (P.isoLeftDerivedObj
          ((linearYoneda R (Rep R G)).obj A).rightOp i).inv.unop =
      (P'.isoLeftDerivedObj
          ((linearYoneda R (Rep R G)).obj A).rightOp i).inv.unop ≫
        ((((linearYoneda R (Rep R G)).obj A).rightOp.mapHomologicalComplex
            (ComplexShape.down ℕ) ⋙
          HomologicalComplex.homologyFunctor
            (ModuleCat R)ᵒᵖ (ComplexShape.down ℕ) i).map phi.hom).unop := by
    simpa only [unop_comp] using hUnop
  let FP := ((linearYoneda R (Rep R G)).obj A).rightOp.mapHomologicalComplex
    (ComplexShape.down ℕ)
  let KP := FP.obj P.complex
  let KP' := FP.obj P'.complex
  let eP : KP.unop.homology i ≅
      unop ((HomologicalComplex.homologyFunctor
        (ModuleCat R)ᵒᵖ (ComplexShape.down ℕ) i).obj KP) :=
    by
      simpa only [HomologicalComplex.homologyFunctor_obj] using KP.homologyUnop i
  let eP' : KP'.unop.homology i ≅
      unop ((HomologicalComplex.homologyFunctor
        (ModuleCat R)ᵒᵖ (ComplexShape.down ℕ) i).obj KP') :=
    by
      simpa only [HomologicalComplex.homologyFunctor_obj] using KP'.homologyUnop i
  let hMap : KP'.unop.homology i ⟶ KP.unop.homology i := by
    change
      (P'.complex.linearYonedaObj R A).homology i ⟶
        (P.complex.linearYonedaObj R A).homology i
    exact HomologicalComplex.homologyMap
      (resolutionLinearYonedaMap P P' phi A) i
  have hOp := HomologicalComplex.homologyOp_hom_naturality
    (resolutionLinearYonedaMap P P' phi A) i
  have hOp' := congr_arg Quiver.Hom.unop hOp
  have hNaturality :
      eP'.hom ≫
        ((((linearYoneda R (Rep R G)).obj A).rightOp.mapHomologicalComplex
              (ComplexShape.down ℕ) ⋙
            HomologicalComplex.homologyFunctor
              (ModuleCat R)ᵒᵖ (ComplexShape.down ℕ) i).map phi.hom).unop =
        hMap ≫ eP.hom := by
    change
      (HomologicalComplex.homologyMap
          ((HomologicalComplex.opFunctor
            (ModuleCat.{u} R) (ComplexShape.up ℕ)).map
              (resolutionLinearYonedaMap P P' phi A).op) i ≫
        (HomologicalComplex.homologyOp
          (P'.complex.linearYonedaObj R A) i).hom).unop =
      ((HomologicalComplex.homologyOp
          (P.complex.linearYonedaObj R A) i).hom ≫
        (HomologicalComplex.homologyMap
          (resolutionLinearYonedaMap P P' phi A) i).op).unop
    exact hOp'
  change
    ((((linearYoneda R (Rep R G)).obj A).rightOp.leftDerived i).map f).unop ≫
        (P.isoLeftDerivedObj
          ((linearYoneda R (Rep R G)).obj A).rightOp i).inv.unop ≫
        eP.inv =
      (P'.isoLeftDerivedObj
          ((linearYoneda R (Rep R G)).obj A).rightOp i).inv.unop ≫
        eP'.inv ≫
        hMap
  rw [← Category.assoc, hLeftDerivedRaw]
  simp only [Category.assoc]
  apply (cancel_epi
    (P'.isoLeftDerivedObj
      ((linearYoneda R (Rep R G)).obj A).rightOp i).inv.unop).mpr
  apply (cancel_epi eP'.hom).mp
  rw [
    ← Category.assoc, hNaturality, Category.assoc, Iso.hom_inv_id,
    Category.comp_id, Iso.hom_inv_id_assoc]

theorem groupCohomologyIso_hom_naturality
    (P P' : ProjectiveResolution (Rep.trivial R G R))
    (phi : ProjectiveResolution.Hom P P' (𝟙 _))
    (A : Rep R G) (i : ℕ) :
    (groupCohomologyIso A i P).hom =
      (groupCohomologyIso A i P').hom ≫
        HomologicalComplex.homologyMap
          (resolutionLinearYonedaMap P P' phi A) i := by
  have hIsoExt :
      (P.isoExt i A).hom =
        (P'.isoExt i A).hom ≫
          HomologicalComplex.homologyMap
            (resolutionLinearYonedaMap P P' phi A) i := by
    simpa only [op_id, CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]
      using resolution_isoExt_hom_naturality P P' phi A i
  change
    (groupCohomologyIsoExt A i).hom ≫ (P.isoExt i A).hom =
      ((groupCohomologyIsoExt A i).hom ≫ (P'.isoExt i A).hom) ≫
        HomologicalComplex.homologyMap
          (resolutionLinearYonedaMap P P' phi A) i
  rw [hIsoExt, Category.assoc]

/-- The existing comparison with the bar resolution is its actual cochain homology map. -/
theorem groupCohomologyIso_bar_hom_eq_homologyMap
    (A : Rep R G) (n : ℕ) :
    (groupCohomologyIso A n (Rep.barResolution R G)).hom =
      HomologicalComplex.homologyMap
        (groupCohomology.inhomogeneousCochainsIso A).hom n := by
  change
    (groupCohomologyIsoExt A n).hom ≫
        (Rep.barResolution.extIso R G A n).hom = _
  rw [show groupCohomologyIsoExt A n =
    isoOfQuasiIsoAt
        (HomotopyEquiv.ofIso
          (groupCohomology.inhomogeneousCochainsIso A)).hom n ≪≫
      (Rep.barResolution.extIso R G A n).symm from rfl]
  simp only [Iso.trans_hom]
  let e := Rep.barResolution.extIso R G A n
  let q := isoOfQuasiIsoAt
    (HomotopyEquiv.ofIso
      (groupCohomology.inhomogeneousCochainsIso A)).hom n
  calc
    ((q.hom ≫ e.inv) ≫ e.hom) =
        q.hom ≫ (e.inv ≫ e.hom) :=
      Category.assoc q.hom e.inv e.hom
    _ = q.hom ≫ 𝟙 _ :=
      congrArg (fun f ↦ q.hom ≫ f) e.inv_hom_id
    _ = q.hom := Category.comp_id q.hom
    _ = _ := isoOfQuasiIsoAt_hom _ _

end ClassFieldTower.Cohomology
