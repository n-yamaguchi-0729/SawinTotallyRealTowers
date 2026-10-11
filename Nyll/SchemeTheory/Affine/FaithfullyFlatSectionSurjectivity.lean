/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Affine.AffinizationDescent
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.RingTheory.Flat.FaithfullyFlat.Descent

/-!
# Faithfully flat descent of surjectivity on actual global sections

The two flat global-section pushouts give the actual pushout square for
the map of sections induced by a morphism over the base. Surjectivity
then descends along the faithfully flat map of section rings.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CommRingCat

universe u

/-- Surjectivity descends across an actual faithfully flat ring pushout. -/
theorem surjective_of_isPushout_of_faithfullyFlat
    {R S A B : CommRingCat.{u}} (f : R ⟶ S) (g : R ⟶ A)
    (i : S ⟶ B) (j : A ⟶ B) (h : IsPushout f g i j)
    (hg : g.hom.FaithfullyFlat) (hj : Function.Surjective j) :
    Function.Surjective f := by
  let : Algebra R S := f.hom.toAlgebra
  let : Algebra R A := g.hom.toAlgebra
  let : Algebra S B := i.hom.toAlgebra
  let : Algebra A B := j.hom.toAlgebra
  let : Algebra R B := (g ≫ j).hom.toAlgebra
  have : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R S B :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom h.w).symm
  have hAlgebra : Algebra.IsPushout R S A B :=
    CommRingCat.isPushout_iff_isPushout.mp h
  exact RingHom.FaithfullyFlat.codescendsAlong_surjective
    (R := R) (S := S) (R' := A) (S' := B) hg hj

end CommRingCat

namespace AlgebraicGeometry

universe u

/-- Surjectivity of the actual map on global sections is detected after
an affine faithfully flat base change of the common affine base. -/
theorem surjective_appTop_of_affine_faithfullyFlat_baseChange
    {Y X S T : Scheme.{u}} (h : Y ⟶ X) (f : X ⟶ S) (g : T ⟶ S)
    [IsAffine S] [IsAffine T] [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact (h ≫ f)] [QuasiSeparated (h ≫ f)] [Flat g] [Surjective g]
    (hSurjective : Function.Surjective
      (pullback.map (h ≫ f) g f g h (𝟙 T) (𝟙 S)
        (by rw [Category.comp_id]) (by rw [Category.id_comp, Category.comp_id])).appTop) :
    Function.Surjective h.appTop := by
  let t : pullback (h ≫ f) g ⟶ pullback f g :=
    pullback.map (h ≫ f) g f g h (𝟙 T) (𝟙 S)
      (by rw [Category.comp_id]) (by rw [Category.id_comp, Category.comp_id])
  have ht₁ : t ≫ pullback.fst f g = pullback.fst (h ≫ f) g ≫ h :=
    pullback.lift_fst _ _ _
  have ht₂ : t ≫ pullback.snd f g = pullback.snd (h ≫ f) g := by
    exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have hSquare : h.appTop ≫ (pullback.fst (h ≫ f) g).appTop =
      (pullback.fst f g).appTop ≫ t.appTop := by
    rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, ht₁]
  have hBottom : (pullback.snd (h ≫ f) g).appTop =
      (pullback.snd f g).appTop ≫ t.appTop := by
    rw [← Scheme.Hom.comp_appTop, ht₂]
  have hOuter := isPushout_appTop_of_flat (h ≫ f) g
  rw [Scheme.Hom.comp_appTop, hBottom] at hOuter
  have hPushout : IsPushout h.appTop (pullback.fst f g).appTop
      (pullback.fst (h ≫ f) g).appTop t.appTop :=
    hOuter.of_left hSquare (isPushout_appTop_of_flat f g)
  have hFpqc := fpqc_SpecMap_pullback_fst_appTop f g
  have hFaithful : (pullback.fst f g).appTop.hom.FaithfullyFlat :=
    (flat_and_surjective_SpecMap_iff (pullback.fst f g).appTop).mp
      ⟨hFpqc.1.2, hFpqc.1.1⟩
  exact CommRingCat.surjective_of_isPushout_of_faithfullyFlat
    h.appTop (pullback.fst f g).appTop (pullback.fst (h ≫ f) g).appTop t.appTop
    hPushout hFaithful hSurjective

end AlgebraicGeometry
