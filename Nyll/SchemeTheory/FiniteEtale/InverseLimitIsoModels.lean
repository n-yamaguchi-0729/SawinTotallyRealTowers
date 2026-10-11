/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.FiniteEtale.InverseLimitIsoDescent

/-!
# Isomorphisms between finite-etale models at a later stage

Combine actual Hom descent, eventual invertibility, and pullback-composition
coherence. The resulting isomorphism recovers the originally supplied map.
-/

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.FiniteEtale

local instance finiteEtaleOverCategoryIsoModels (X : Scheme.{u}) :
    Category (MorphismProperty.Over
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) ⊤ X) := instCategory X

local instance finiteEtaleHasPullbacksAlongIsoModels
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.HasPullbacksAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) f :=
  ⟨fun _ _ ↦ inferInstance⟩

local instance finiteEtaleStableUnderBaseChangeAlongIsoModels
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.IsStableUnderBaseChangeAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) f :=
  ⟨fun h hf ↦ MorphismProperty.of_isPullback
    (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) h hf⟩

private theorem isIso_of_recovered_iso
    {C₀ C₁ C₂ : Type*} [Category* C₀] [Category* C₁] [Category* C₂]
    (F : C₀ ⥤ C₂) (U : C₀ ⥤ C₁) (V : C₁ ⥤ C₂) (e : F ≅ U ⋙ V)
    {A B : C₀} (a : F.obj A ≅ F.obj B) (b : U.obj A ⟶ U.obj B)
    (hb : e.hom.app A ≫ V.map b = a.hom ≫ e.hom.app B) : IsIso (V.map b) := by
  have hb' : V.map b = e.inv.app A ≫ a.hom ≫ e.hom.app B := by
    calc
      V.map b = e.inv.app A ≫ (e.hom.app A ≫ V.map b) := by
        rw [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
      _ = e.inv.app A ≫ a.hom ≫ e.hom.app B := by rw [hb]
  rw [hb']
  infer_instance

private theorem extend_recovered_map
    {C₀ C₁ C₂ C₃ : Type*}
    [Category* C₀] [Category* C₁] [Category* C₂] [Category* C₃]
    (F : C₀ ⥤ C₃) (U : C₀ ⥤ C₁) (W : C₁ ⥤ C₂)
    (V : C₁ ⥤ C₃) (V' : C₂ ⥤ C₃) (T : C₀ ⥤ C₂)
    (e : F ≅ U ⋙ V) (e' : V ≅ W ⋙ V') (E : T ≅ U ⋙ W)
    (eT : F ≅ T ⋙ V')
    (hcomp : ∀ Q : C₀, V'.map (E.inv.app Q) ≫ eT.inv.app Q =
      e'.inv.app (U.obj Q) ≫ e.inv.app Q)
    {A B : C₀} (a : F.obj A ⟶ F.obj B) (b : U.obj A ⟶ U.obj B)
    (hb : e.hom.app A ≫ V.map b = a ≫ e.hom.app B) :
    eT.hom.app A ≫ V'.map (E.hom.app A ≫ W.map b ≫ E.inv.app B) =
      a ≫ eT.hom.app B := by
  have hb' : V.map b ≫ e.inv.app B = e.inv.app A ≫ a := by
    apply (cancel_epi (e.hom.app A)).mp
    rw [← Category.assoc, hb, Category.assoc, Iso.hom_inv_id_app,
      Category.comp_id, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  have hn : V'.map (W.map b) ≫ e'.inv.app (U.obj B) =
      e'.inv.app (U.obj A) ≫ V.map b := e'.inv.naturality b
  have hcancel : V'.map (E.hom.app A) ≫ V'.map (E.inv.app A) = 𝟙 (V'.obj (T.obj A)) := by
    rw [← V'.map_comp, Iso.hom_inv_id_app, V'.map_id]
  have H : V'.map (E.hom.app A ≫ W.map b ≫ E.inv.app B) ≫ eT.inv.app B =
      eT.inv.app A ≫ a := by
    rw [V'.map_comp, V'.map_comp]
    calc
      (V'.map (E.hom.app A) ≫ V'.map (W.map b) ≫ V'.map (E.inv.app B)) ≫
          eT.inv.app B =
          V'.map (E.hom.app A) ≫ V'.map (W.map b) ≫
            (V'.map (E.inv.app B) ≫ eT.inv.app B) := by
        simp only [Category.assoc]
      _ = V'.map (E.hom.app A) ≫ V'.map (W.map b) ≫
          (e'.inv.app (U.obj B) ≫ e.inv.app B) := by rw [hcomp B]
      _ = V'.map (E.hom.app A) ≫ e'.inv.app (U.obj A) ≫
          V.map b ≫ e.inv.app B := by
        rw [← Category.assoc (V'.map (W.map b)), hn]
        simp only [Category.assoc]
      _ = V'.map (E.hom.app A) ≫ e'.inv.app (U.obj A) ≫ e.inv.app A ≫ a := by
        rw [hb']
      _ = V'.map (E.hom.app A) ≫ (V'.map (E.inv.app A) ≫ eT.inv.app A) ≫ a := by
        rw [hcomp A]
        simp only [Category.assoc]
      _ = eT.inv.app A ≫ a := by
        simp only [Category.assoc]
        rw [← Category.assoc (V'.map (E.hom.app A)) (V'.map (E.inv.app A)),
          hcancel, Category.id_comp]
  apply (cancel_mono (eT.inv.app B)).mp
  rw [Category.assoc, H, ← Category.assoc, Iso.hom_inv_id_app,
    Category.id_comp, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]

/-- A recovered stage isomorphism retains its recovery at every later stage. -/
theorem exists_inverse_limit_stage_iso_later
    {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)
    {i j k : I} (hji : j ⟶ i) (hkj : k ⟶ j)
    (A B : FiniteEtale (D.obj i))
    (a : (FiniteEtale.pullback (c.π.app i)).obj A ≅
      (FiniteEtale.pullback (c.π.app i)).obj B)
    (b : (FiniteEtale.pullback (D.map hji)).obj A ≅
      (FiniteEtale.pullback (D.map hji)).obj B)
    (hb : (inverseLimitPullbackComparison D c hji).hom.app A ≫
        (FiniteEtale.pullback (c.π.app j)).map b.hom =
      a.hom ≫ (inverseLimitPullbackComparison D c hji).hom.app B) :
    ∃ b' : (FiniteEtale.pullback (D.map (hkj ≫ hji))).obj A ≅
        (FiniteEtale.pullback (D.map (hkj ≫ hji))).obj B,
      (inverseLimitPullbackComparison D c (hkj ≫ hji)).hom.app A ≫
          (FiniteEtale.pullback (c.π.app k)).map b'.hom =
        a.hom ≫ (inverseLimitPullbackComparison D c (hkj ≫ hji)).hom.app B := by
  let F : FiniteEtale (D.obj i) ⥤ FiniteEtale c.pt := FiniteEtale.pullback (c.π.app i)
  let U : FiniteEtale (D.obj i) ⥤ FiniteEtale (D.obj j) := FiniteEtale.pullback (D.map hji)
  let V : FiniteEtale (D.obj j) ⥤ FiniteEtale c.pt := FiniteEtale.pullback (c.π.app j)
  let W : FiniteEtale (D.obj j) ⥤ FiniteEtale (D.obj k) := FiniteEtale.pullback (D.map hkj)
  let V' : FiniteEtale (D.obj k) ⥤ FiniteEtale c.pt := FiniteEtale.pullback (c.π.app k)
  let T : FiniteEtale (D.obj i) ⥤ FiniteEtale (D.obj k) :=
    FiniteEtale.pullback (D.map (hkj ≫ hji))
  let e : F ≅ U ⋙ V := inverseLimitPullbackComparison D c hji
  let e' : V ≅ W ⋙ V' := inverseLimitPullbackComparison D c hkj
  let E : T ≅ U ⋙ W := MorphismProperty.Over.pullbackComp
    (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) (Q := ⊤)
    (D.map hkj) (D.map hji) (D.map (hkj ≫ hji)) (D.map_comp hkj hji)
  let eT : F ≅ T ⋙ V' := inverseLimitPullbackComparison D c (hkj ≫ hji)
  refine ⟨E.app A ≪≫ W.mapIso b ≪≫ (E.app B).symm, ?_⟩
  exact extend_recovered_map F U W V V' T e e' E eT
    (inverseLimitPullbackComparison_inv_comp D c hji hkj) a.hom b.hom hb

/-- An isomorphism of limit pullbacks is induced by an actual isomorphism
of the two native models at a later original stage. -/
theorem exists_inverse_limit_stage_iso
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (h : i ⟶ j), IsAffineHom (D.map h)]
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (i : I) (A B : FiniteEtale (D.obj i))
    (a : (FiniteEtale.pullback (c.π.app i)).obj A ≅
      (FiniteEtale.pullback (c.π.app i)).obj B) :
    ∃ (j : I) (hji : j ⟶ i)
      (b : (FiniteEtale.pullback (D.map hji)).obj A ≅
        (FiniteEtale.pullback (D.map hji)).obj B),
      (inverseLimitPullbackComparison D c hji).hom.app A ≫
          (FiniteEtale.pullback (c.π.app j)).map b.hom =
        a.hom ≫ (inverseLimitPullbackComparison D c hji).hom.app B := by
  let F : FiniteEtale (D.obj i) ⥤ FiniteEtale c.pt := FiniteEtale.pullback (c.π.app i)
  obtain ⟨j, hji, b, hb⟩ := exists_inverse_limit_stage_hom D c hc i A B a.hom
  let U : FiniteEtale (D.obj i) ⥤ FiniteEtale (D.obj j) := FiniteEtale.pullback (D.map hji)
  let V : FiniteEtale (D.obj j) ⥤ FiniteEtale c.pt := FiniteEtale.pullback (c.π.app j)
  let e : F ≅ U ⋙ V := inverseLimitPullbackComparison D c hji
  have : IsIso (V.map b) := isIso_of_recovered_iso F U V e a b hb
  obtain ⟨k, hkj, hk⟩ := exists_inverse_limit_stage_isIso D c hc j b
  let W : FiniteEtale (D.obj j) ⥤ FiniteEtale (D.obj k) := FiniteEtale.pullback (D.map hkj)
  let V' : FiniteEtale (D.obj k) ⥤ FiniteEtale c.pt := FiniteEtale.pullback (c.π.app k)
  let T : FiniteEtale (D.obj i) ⥤ FiniteEtale (D.obj k) :=
    FiniteEtale.pullback (D.map (hkj ≫ hji))
  let e' : V ≅ W ⋙ V' := inverseLimitPullbackComparison D c hkj
  let E : T ≅ U ⋙ W := MorphismProperty.Over.pullbackComp
    (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) (Q := ⊤)
    (D.map hkj) (D.map hji) (D.map (hkj ≫ hji)) (D.map_comp hkj hji)
  let eT : F ≅ T ⋙ V' := inverseLimitPullbackComparison D c (hkj ≫ hji)
  have : IsIso (W.map b) := hk
  let b' : T.obj A ≅ T.obj B := E.app A ≪≫ asIso (W.map b) ≪≫ (E.app B).symm
  refine ⟨k, hkj ≫ hji, b', ?_⟩
  exact extend_recovered_map F U W V V' T e e' E eT
    (inverseLimitPullbackComparison_inv_comp D c hji hkj) a.hom b hb

end AlgebraicGeometry.FiniteEtale
