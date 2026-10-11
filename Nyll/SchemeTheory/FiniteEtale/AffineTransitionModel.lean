/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.FiniteEtale.FilteredColimitSpec
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-!
# Finite-etale models for arbitrary inverse systems of affine schemes

The global-sections cocone of the actual affine limit is colimiting. Descend
the cover through that ring cocone and transfer it back with `isoSpec` and
the canonical pullback-composition isomorphisms. Recovery is along the
original cone projection, without integrality or injectivity assumptions.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.FiniteEtale

local instance finiteEtaleHasPullbacksAlongTransition
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.HasPullbacksAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) f :=
  ⟨fun _ _ ↦ inferInstance⟩

local instance finiteEtaleStableUnderBaseChangeAlongTransition
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.IsStableUnderBaseChangeAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) f :=
  ⟨fun h hf ↦ MorphismProperty.of_isPullback
    (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) h hf⟩

/-- A finite-etale cover of an actual cofiltered limit of affine schemes
descends to an actual stage, with recovery along the original cone map. -/
theorem exists_affine_inverse_limit_model
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i : I, IsAffine (D.obj i)] (X : FiniteEtale c.pt) :
    ∃ (i : I) (Xᵢ : FiniteEtale (D.obj i)),
      Nonempty ((FiniteEtale.pullback (c.π.app i)).obj Xᵢ ≅ X) := by
  have : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  have : ∀ i : I, CompactSpace (D.obj i) := fun _ ↦ inferInstance
  have : ∀ i : I, QuasiSeparatedSpace (D.obj i) := fun _ ↦ inferInstance
  have : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f) :=
    fun f ↦ isAffineHom_of_isAffine (D.map f)
  let cR : Cocone (D.op ⋙ Scheme.Γ) := Scheme.Γ.mapCocone c.op
  have hcR : IsColimit cR := (nonempty_isColimit_Γ_mapCocone D c hc).some
  let XR : FiniteEtale (Spec Γ(c.pt, ⊤)) :=
    (FiniteEtale.pullback c.pt.isoSpec.inv).obj X
  obtain ⟨i, Xᵢ, ⟨he⟩⟩ := exists_filtered_colimit_spec_model
    (D.op ⋙ Scheme.Γ) cR hcR XR
  let q : Spec Γ(c.pt, ⊤) ⟶ Spec Γ(D.obj i.unop, ⊤) :=
    Spec.map (c.π.app i.unop).appTop
  have hq : c.π.app i.unop ≫ (D.obj i.unop).isoSpec.hom = c.pt.isoSpec.hom ≫ q :=
    (Scheme.isoSpec_hom_naturality (X := c.pt) (Y := D.obj i.unop)
      (c.π.app i.unop)).symm
  let p₁ : FiniteEtale.pullback (c.π.app i.unop ≫ (D.obj i.unop).isoSpec.hom) ≅
      FiniteEtale.pullback (D.obj i.unop).isoSpec.hom ⋙
        FiniteEtale.pullback (c.π.app i.unop) :=
    MorphismProperty.Over.pullbackComp
      (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) (Q := ⊤)
      (c.π.app i.unop) (D.obj i.unop).isoSpec.hom
  let p₂ : FiniteEtale.pullback (c.π.app i.unop ≫ (D.obj i.unop).isoSpec.hom) ≅
      FiniteEtale.pullback (c.pt.isoSpec.hom ≫ q) :=
    MorphismProperty.Over.pullbackCongr
      (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) (Q := ⊤) hq
  let p₃ : FiniteEtale.pullback (c.pt.isoSpec.hom ≫ q) ≅
      FiniteEtale.pullback q ⋙ FiniteEtale.pullback c.pt.isoSpec.hom :=
    MorphismProperty.Over.pullbackComp
      (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) (Q := ⊤) c.pt.isoSpec.hom q
  let E : FiniteEtale c.pt ≌ FiniteEtale (Spec Γ(c.pt, ⊤)) :=
    MorphismProperty.Over.pullbackIso
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) ⊤ c.pt.isoSpec
  have he' : (FiniteEtale.pullback q).obj Xᵢ ≅ XR := he
  refine ⟨i.unop, (FiniteEtale.pullback (D.obj i.unop).isoSpec.hom).obj Xᵢ, ⟨?_⟩⟩
  exact (p₁.app Xᵢ).symm ≪≫ p₂.app Xᵢ ≪≫ p₃.app Xᵢ ≪≫
    (FiniteEtale.pullback c.pt.isoSpec.hom).mapIso he' ≪≫ (E.unitIso.app X).symm

end AlgebraicGeometry.FiniteEtale
