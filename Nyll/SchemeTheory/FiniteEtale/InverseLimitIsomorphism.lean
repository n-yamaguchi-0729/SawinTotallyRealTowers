/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.FiniteEtale.InverseLimitHom
import Nyll.SchemeTheory.FiniteEtale.InverseLimitEquality
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.NatIso

/-!
# Isomorphisms and finite equation families at inverse-system stages

Native Hom descent supplies an inverse map, and native eventual equality
makes both inverse equations hold at a common actual stage. No projection
is assumed faithfully flat, surjective, or faithful on finite-etale covers.
-/

noncomputable section

universe u v

open CategoryTheory Limits

namespace AlgebraicGeometry.FiniteEtale

local instance finiteEtaleOverCategoryLimitIso (X : Scheme.{u}) :
    Category (MorphismProperty.Over
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) ⊤ X) := instCategory X

local instance finiteEtaleHasPullbacksAlongLimitIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.HasPullbacksAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) f :=
  ⟨fun _ _ ↦ inferInstance⟩

local instance finiteEtaleStableUnderBaseChangeAlongLimitIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.IsStableUnderBaseChangeAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) f :=
  ⟨fun h hf ↦ MorphismProperty.of_isPullback
    (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) h hf⟩

private theorem map_eq_of_comparison
    {C₀ C₁ : Type*} [Category* C₀] [Category* C₁]
    {F G : C₀ ⥤ C₁} (e : F ≅ G) {A B : C₀} (a b : A ⟶ B)
    (h : G.map a = G.map b) : F.map a = F.map b := by
  apply (cancel_mono (e.hom.app B)).mp
  rw [e.hom.naturality, e.hom.naturality, h]

private theorem inverse_equations_of_comparison
    {C₀ C₁ C₂ : Type*} [Category* C₀] [Category* C₁] [Category* C₂]
    (F : C₀ ⥤ C₂) (U : C₀ ⥤ C₁) (V : C₁ ⥤ C₂) (e : F ≅ U ⋙ V)
    {A B : C₀} (a : A ⟶ B) [IsIso (F.map a)] (b : U.obj B ⟶ U.obj A)
    (hb : e.hom.app B ≫ V.map b = inv (F.map a) ≫ e.hom.app A) :
    V.map (U.map a ≫ b) = 𝟙 (V.obj (U.obj A)) ∧
      V.map (b ≫ U.map a) = 𝟙 (V.obj (U.obj B)) := by
  let eA : F.obj A ≅ V.obj (U.obj A) := e.app A
  let eB : F.obj B ≅ V.obj (U.obj B) := e.app B
  have hn : F.map a ≫ eB.hom = eA.hom ≫ V.map (U.map a) :=
    e.hom.naturality a
  have hb' : eB.hom ≫ V.map b = inv (F.map a) ≫ eA.hom := hb
  constructor
  · apply (cancel_epi eA.hom).mp
    rw [V.map_comp, Category.comp_id, ← Category.assoc, ← hn,
      Category.assoc, hb', ← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  · apply (cancel_epi eB.hom).mp
    rw [V.map_comp, Category.comp_id, ← Category.assoc, hb',
      Category.assoc, ← hn, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (h : i ⟶ j), IsAffineHom (D.map h)]
    [∀ i : I, CompactSpace (D.obj i)]

include hc

/-- A finite collection of equalities of native finite-etale morphisms
holds after one common transition if it holds over the actual limit. -/
theorem exists_inverse_limit_stage_map_eq_family
    (i : I) {K : Type v} [Finite K] (A B : K → FiniteEtale (D.obj i))
    (a b : ∀ k : K, A k ⟶ B k)
    (hab : ∀ k : K, (FiniteEtale.pullback (c.π.app i)).map (a k) =
      (FiniteEtale.pullback (c.π.app i)).map (b k)) :
    ∃ (j : I) (hji : j ⟶ i), ∀ k : K,
      (FiniteEtale.pullback (D.map hji)).map (a k) =
        (FiniteEtale.pullback (D.map hji)).map (b k) := by
  classical
  choose j hji heq using fun k : K ↦
    exists_inverse_limit_stage_map_eq D c hc i (a k) (b k) (hab k)
  obtain ⟨l, hli, hlj, hcomp⟩ := IsCofiltered.wideCospan hji
  refine ⟨l, hli, ?_⟩
  intro k
  let e : FiniteEtale.pullback (D.map hli) ≅
      FiniteEtale.pullback (D.map (hji k)) ⋙ FiniteEtale.pullback (D.map (hlj k)) :=
    MorphismProperty.Over.pullbackComp
      (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) (Q := ⊤)
      (D.map (hlj k)) (D.map (hji k)) (D.map hli)
      (by rw [← D.map_comp, hcomp k])
  exact map_eq_of_comparison e (a k) (b k)
    (congrArg (FiniteEtale.pullback (D.map (hlj k))).map (heq k))

/-- A morphism of finite-etale models which becomes an isomorphism over
the limit is an isomorphism after an actual later transition. The inverse
and both inverse equations are constructed by descent. -/
theorem exists_inverse_limit_stage_isIso
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (i : I) {A B : FiniteEtale (D.obj i)} (a : A ⟶ B)
    [IsIso ((FiniteEtale.pullback (c.π.app i)).map a)] :
    ∃ (j : I) (hji : j ⟶ i), IsIso ((FiniteEtale.pullback (D.map hji)).map a) := by
  let F : FiniteEtale (D.obj i) ⥤ FiniteEtale c.pt := FiniteEtale.pullback (c.π.app i)
  obtain ⟨j, hji, b, hb⟩ := exists_inverse_limit_stage_hom D c hc i B A (inv (F.map a))
  let U : FiniteEtale (D.obj i) ⥤ FiniteEtale (D.obj j) := FiniteEtale.pullback (D.map hji)
  let V : FiniteEtale (D.obj j) ⥤ FiniteEtale c.pt := FiniteEtale.pullback (c.π.app j)
  let e : F ≅ U ⋙ V := inverseLimitPullbackComparison D c hji
  obtain ⟨hleft, hright⟩ := inverse_equations_of_comparison F U V e a b hb
  let Q : Bool → FiniteEtale (D.obj j)
    | false => U.obj A
    | true => U.obj B
  let z : ∀ ε : Bool, Q ε ⟶ Q ε := fun ε ↦ by
    cases ε
    · exact U.map a ≫ b
    · exact b ≫ U.map a
  have hz : ∀ ε : Bool, V.map (z ε) = V.map (𝟙 (Q ε)) := by
    intro ε
    cases ε
    · change V.map (U.map a ≫ b) = V.map (𝟙 (U.obj A))
      exact hleft.trans (V.map_id (U.obj A)).symm
    · change V.map (b ≫ U.map a) = V.map (𝟙 (U.obj B))
      exact hright.trans (V.map_id (U.obj B)).symm
  obtain ⟨k, hkj, hk⟩ := exists_inverse_limit_stage_map_eq_family
    D c hc j Q Q z (fun ε ↦ 𝟙 (Q ε)) hz
  let W := FiniteEtale.pullback (D.map hkj)
  have hleftk : W.map (U.map a) ≫ W.map b = 𝟙 (W.obj (U.obj A)) := by
    have H := hk false
    change W.map (U.map a ≫ b) = W.map (𝟙 (U.obj A)) at H
    exact (W.map_comp (U.map a) b).symm.trans (H.trans (W.map_id (U.obj A)))
  have hrightk : W.map b ≫ W.map (U.map a) = 𝟙 (W.obj (U.obj B)) := by
    have H := hk true
    change W.map (b ≫ U.map a) = W.map (𝟙 (U.obj B)) at H
    exact (W.map_comp b (U.map a)).symm.trans (H.trans (W.map_id (U.obj B)))
  let ek : W.obj (U.obj A) ≅ W.obj (U.obj B) :=
    ⟨W.map (U.map a), W.map b, hleftk, hrightk⟩
  have hIso : IsIso (W.map (U.map a)) := ek.isIso_hom
  let E : FiniteEtale.pullback (D.map (hkj ≫ hji)) ≅ U ⋙ W :=
    MorphismProperty.Over.pullbackComp
      (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) (Q := ⊤)
      (D.map hkj) (D.map hji) (D.map (hkj ≫ hji)) (D.map_comp hkj hji)
  exact ⟨k, hkj ≫ hji, (NatIso.isIso_map_iff E a).mpr hIso⟩

end AlgebraicGeometry.FiniteEtale
