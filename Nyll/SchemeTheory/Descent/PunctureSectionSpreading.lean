/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Descent.AffineTransitionHom
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.Topology.Sheaves.Stalks

/-!
# Spreading a morphism from a retrocompact part of a local spectrum

Base change the actual stalk inverse system by a retrocompact open. Its
stages are quasi-compact and quasi-separated. Finite-presentation Hom
descent then spreads the given morphism to the overlap with an actual
neighborhood, retaining the original morphism on the local spectrum.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- The actual map from the local-spectrum overlap to the overlap with an
open neighborhood of the chosen point. -/
def stalkOverlapToNeighborhood
    (X : Scheme.{u}) (x : X) (U N : X.Opens) (hxN : x ∈ N) :
    pullback (X.fromSpecStalk x) U.ι ⟶ pullback N.ι U.ι :=
  pullback.lift
    (pullback.fst (X.fromSpecStalk x) U.ι ≫ N.fromSpecStalkOfMem x hxN)
    (pullback.snd (X.fromSpecStalk x) U.ι)
    (by
      rw [Category.assoc, Opens.fromSpecStalkOfMem_ι]
      exact pullback.condition)

/-- A morphism on the retrocompact part of the actual local spectrum
spreads to the intersection with an open neighborhood. The target needs
only to be locally of finite presentation over the affine base. -/
theorem exists_open_overlap_extension_fromSpecStalk
    {X Y : Scheme.{u}} [IsAffine X]
    (f : Y ⟶ X) [LocallyOfFinitePresentation f]
    (U : X.Opens) [QuasiCompact U.ι] (x : X)
    (a : pullback (X.fromSpecStalk x) U.ι ⟶ Y)
    (ha : a ≫ f = pullback.snd (X.fromSpecStalk x) U.ι ≫ U.ι) :
    ∃ (N : X.Opens) (hxN : x ∈ N) (b : pullback N.ι U.ι ⟶ Y),
      b ≫ f = pullback.snd N.ι U.ι ≫ U.ι ∧
        stalkOverlapToNeighborhood X x U N hxN ≫ b = a := by
  let F : (OpenNhds x)ᵒᵖ ⥤ CommRingCat.{u} :=
    (OpenNhds.inclusion x).op ⋙ X.presheaf
  let D : (OpenNhds x)ᵒᵖᵒᵖ ⥤ Over X :=
    { obj i := Over.mk
        (Spec.map (X.presheaf.map (homOfLE (show i.unop.unop.1 ≤ ⊤ from le_top)).op) ≫
          X.isoSpec.inv)
      map h := Over.homMk (Spec.map (F.map h.unop)) (by
        change Spec.map (X.presheaf.map ((OpenNhds.inclusion x).map h.unop.unop).op) ≫
            (Spec.map (X.presheaf.map (homOfLE le_top).op) ≫ X.isoSpec.inv) =
          Spec.map (X.presheaf.map (homOfLE le_top).op) ≫ X.isoSpec.inv
        rw [← Category.assoc, ← Spec.map_comp, ← X.presheaf.map_comp]
        rfl)
      map_id i := by
        apply Over.OverMorphism.ext
        exact (F.op ⋙ Scheme.Spec).map_id i
      map_comp h k := by
        apply Over.OverMorphism.ext
        exact (F.op ⋙ Scheme.Spec).map_comp h k }
  let c : Cone D :=
    { pt := Over.mk (X.fromSpecStalk x)
      π :=
        { app i := Over.homMk
            (Spec.map (X.presheaf.germ i.unop.unop.1 x i.unop.unop.2)) (by
              change Spec.map (X.presheaf.germ i.unop.unop.1 x i.unop.unop.2) ≫
                  (Spec.map (X.presheaf.map (homOfLE le_top).op) ≫ X.isoSpec.inv) =
                X.fromSpecStalk x
              rw [← Category.assoc, ← Spec.map_comp, TopCat.Presheaf.germ_res,
                ← Scheme.fromSpecStalk_toSpecΓ, Category.assoc,
                Scheme.toSpecΓ_isoSpec_inv, Category.comp_id])
          naturality i j h := by
            apply Over.OverMorphism.ext
            exact (Scheme.Spec.mapCone (colimit.cocone F).op).π.naturality h } }
  have hc : IsLimit c :=
    isLimitOfReflects (Over.forget X)
      (isLimitOfPreserves Scheme.Spec (colimit.isColimit F).op)
  have : ∀ {i j : (OpenNhds x)ᵒᵖᵒᵖ} (h : i ⟶ j),
      IsAffineHom (D.map h).left :=
    fun h ↦ inferInstanceAs (IsAffineHom (Spec.map (F.map h.unop)))
  have : ∀ i : (OpenNhds x)ᵒᵖᵒᵖ, CompactSpace (D.obj i).left :=
    fun i ↦ inferInstanceAs (CompactSpace (Spec (F.obj i.unop)))
  have : ∀ i : (OpenNhds x)ᵒᵖᵒᵖ, QuasiSeparatedSpace (D.obj i).left :=
    fun i ↦ inferInstanceAs (QuasiSeparatedSpace (Spec (F.obj i.unop)))
  let E : (OpenNhds x)ᵒᵖᵒᵖ ⥤ Scheme.{u} := AffineTransitionHom.diagram D U.ι
  let s : Cone E := AffineTransitionHom.cone D c U.ι
  let t : E ⟶ (Functor.const (OpenNhds x)ᵒᵖᵒᵖ).obj X :=
    AffineTransitionHom.projection D U.ι
  have hs : IsLimit s := AffineTransitionHom.coneIsLimit D c hc U.ι
  have : ∀ {i j : (OpenNhds x)ᵒᵖᵒᵖ} (h : i ⟶ j), IsAffineHom (E.map h) :=
    fun h ↦ AffineTransitionHom.diagram_map_isAffineHom D U.ι h
  have : ∀ i : (OpenNhds x)ᵒᵖᵒᵖ, CompactSpace (E.obj i) :=
    AffineTransitionHom.diagram_obj_compactSpace D U.ι
  have : ∀ i : (OpenNhds x)ᵒᵖᵒᵖ, QuasiSeparatedSpace (E.obj i) :=
    AffineTransitionHom.diagram_obj_quasiSeparatedSpace D U.ι
  have hcompat : s.π ≫ t = (Functor.const (OpenNhds x)ᵒᵖᵒᵖ).map (a ≫ f) := by
    apply NatTrans.ext
    funext i
    change s.π.app i ≫ (pullback.snd (D.obj i).hom U.ι ≫ U.ι) = a ≫ f
    rw [← Category.assoc, AffineTransitionHom.cone_map_snd, ha]
    rfl
  obtain ⟨i, b, hb, hbf⟩ :=
    Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation E t f s hs a hcompat
  let N : X.Opens := i.unop.unop.1
  have hxN : x ∈ N := i.unop.unop.2
  have hN : N.toSpecΓ ≫ (D.obj i).hom = N.ι := by
    change N.toSpecΓ ≫
      (Spec.map (X.presheaf.map (homOfLE le_top).op) ≫ X.isoSpec.inv) = N.ι
    rw [← Category.assoc, Opens.toSpecΓ_SpecMap_presheaf_map_top,
      Category.assoc, Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]
  let k : pullback N.ι U.ι ⟶ pullback (D.obj i).hom U.ι :=
    pullback.lift (pullback.fst N.ι U.ι ≫ N.toSpecΓ) (pullback.snd N.ι U.ι)
      (by rw [Category.assoc, hN]; exact pullback.condition)
  let j : pullback (X.fromSpecStalk x) U.ι ⟶ pullback N.ι U.ι :=
    stalkOverlapToNeighborhood X x U N hxN
  have hjfst : j ≫ pullback.fst N.ι U.ι =
      pullback.fst (X.fromSpecStalk x) U.ι ≫ N.fromSpecStalkOfMem x hxN :=
    pullback.lift_fst _ _ _
  have hjsnd : j ≫ pullback.snd N.ι U.ι =
      pullback.snd (X.fromSpecStalk x) U.ι := pullback.lift_snd _ _ _
  have hksnd : k ≫ pullback.snd (D.obj i).hom U.ι = pullback.snd N.ι U.ι :=
    pullback.lift_snd _ _ _
  have hjk : j ≫ k = s.π.app i := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, hjfst,
        Category.assoc, Opens.fromSpecStalkOfMem_toSpecΓ]
      exact (AffineTransitionHom.cone_map_fst D c U.ι i).symm
    · rw [Category.assoc, hksnd, hjsnd]
      exact (AffineTransitionHom.cone_map_snd D c U.ι i).symm
  refine ⟨N, hxN, k ≫ b, ?_, ?_⟩
  · rw [Category.assoc, hbf]
    change k ≫ (pullback.snd (D.obj i).hom U.ι ≫ U.ι) =
      pullback.snd N.ι U.ι ≫ U.ι
    rw [← Category.assoc, hksnd]
  · change j ≫ (k ≫ b) = a
    rw [← Category.assoc, hjk]
    exact hb

end AlgebraicGeometry.Scheme
