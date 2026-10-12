/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
import Nyll.SchemeTheory.WeilRestriction.FiniteEtale
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.CategoryTheory.Yoneda

/-!
# Fullness from descent of finite etale sections

The actual finite etale internal Hom represents a morphism after base
change by a section. Descending that section and evaluating it gives the
original morphism. This supplies a shared proof for geometric and Henselian
section-descent theorems.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

namespace AlgebraicGeometry.FiniteEtale

/-- Descent of sections of every finite etale cover implies fullness of
the canonical pullback functor, by the actual finite etale internal Hom. -/
theorem pullback_full_of_section_descent
    {X S : Scheme.{u}} (f : X ⟶ S)
    (h : ∀ (W : FiniteEtale S) (a : X ⟶ W.left), a ≫ W.hom = f →
      ∃ s : S ⟶ W.left, s ≫ W.hom = 𝟙 S ∧ f ≫ s = a) :
    (FiniteEtale.pullback f).Full where
  map_surjective {A B} φ := by
    let i := f
    let U : Over S := A.toComma
    let V : Over S := B.toComma
    let T : Over S := Over.mk i
    let T₁ : Over S := Over.mk (𝟙 S)
    let W : FiniteEtale S :=
      SchemeTheory.WeilRestriction.finiteEtaleInternalHomRepresenter S A B
    let e : (SchemeTheory.WeilRestriction.relativeInternalHomFunctor U V).RepresentableBy
        W.toComma := SchemeTheory.WeilRestriction.finiteEtaleInternalHomRepresentable S A B
    let pA : U.left ⟶ S := U.hom
    let pB : V.left ⟶ S := V.hom
    let φ₀ : Limits.pullback pA i ⟶ Limits.pullback pB i := φ.left
    let q : Limits.pullback pA i ≅ Limits.pullback i pA := pullbackSymmetry pA i
    have hφ : φ₀ ≫ pullback.snd pB i = pullback.snd pA i :=
      MorphismProperty.Over.w φ
    have hφB : (φ₀ ≫ pullback.fst pB i) ≫ pB = pullback.snd pA i ≫ i := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hφ]
    have hc₀ : (q.inv ≫ φ₀ ≫ pullback.fst pB i) ≫ pB =
        pullback.fst i pA ≫ i := by
      rw [Category.assoc, hφB, ← Category.assoc, pullbackSymmetry_inv_comp_snd]
    let c₀ : T ⊗ U ⟶ V := Over.homMk
      (q.inv ≫ φ₀ ≫ pullback.fst pB i) hc₀
    let s₀ : T ⟶ W.toComma := e.homEquiv.symm c₀
    obtain ⟨s, hs, hsi⟩ :=
      h W s₀.left s₀.w
    let σ : T₁ ⟶ W.toComma := Over.homMk s hs
    let d : T ⟶ T₁ := Over.homMk i (Category.comp_id i)
    have hd : d ≫ σ = s₀ := CategoryTheory.Over.OverMorphism.ext hsi
    let c : T₁ ⊗ U ⟶ V := e.homEquiv σ
    have hn : e.homEquiv (d ≫ σ) = (d ▷ U) ≫ c := e.homEquiv_comp d σ
    have heq : e.homEquiv (d ≫ σ) = e.homEquiv s₀ :=
      congrArg (fun z : T ⟶ W.toComma ↦ e.homEquiv z) hd
    have hc : (d ▷ U) ≫ c = c₀ :=
      hn.symm.trans (heq.trans (e.homEquiv.apply_symm_apply c₀))
    let a : U ⟶ V := (λ_ U).inv ≫ c
    have ht : pullback.fst pA i ≫ (λ_ U).inv.left =
        q.hom ≫ (d ▷ U).left := by
      let l : U.left ⟶ Limits.pullback (𝟙 S) pA := (λ_ U).inv.left
      let k : Limits.pullback i pA ⟶ Limits.pullback (𝟙 S) pA := (d ▷ U).left
      have hl₁ : l ≫ pullback.fst (𝟙 S) pA = pA :=
        Over.leftUnitor_inv_left_fst U
      have hl₂ : l ≫ pullback.snd (𝟙 S) pA = 𝟙 U.left :=
        Over.leftUnitor_inv_left_snd U
      have hk₁ : k ≫ pullback.fst (𝟙 S) pA = pullback.fst i pA ≫ i :=
        Over.whiskerRight_left_fst (R := U) d
      have hk₂ : k ≫ pullback.snd (𝟙 S) pA = pullback.snd i pA :=
        Over.whiskerRight_left_snd (R := U) d
      have hq₁ : q.hom ≫ pullback.fst i pA = pullback.snd pA i :=
        pullbackSymmetry_hom_comp_fst pA i
      have hq₂ : q.hom ≫ pullback.snd i pA = pullback.fst pA i :=
        pullbackSymmetry_hom_comp_snd pA i
      change pullback.fst pA i ≫ l = q.hom ≫ k
      apply pullback.hom_ext
      · rw [Category.assoc, hl₁, Category.assoc, hk₁, ← Category.assoc, hq₁]
        exact (pullback.condition :
          pullback.fst pA i ≫ pA = pullback.snd pA i ≫ i)
      · rw [Category.assoc, hl₂, Category.comp_id, Category.assoc, hk₂, hq₂]
    have ha : pullback.fst pA i ≫ a.left = φ₀ ≫ pullback.fst pB i := by
      calc
        pullback.fst pA i ≫ a.left =
            (pullback.fst pA i ≫ (λ_ U).inv.left) ≫ c.left :=
          (Category.assoc _ _ _).symm
        _ = q.hom ≫ ((d ▷ U) ≫ c).left := by
          rw [ht, Over.comp_left, Category.assoc]
        _ = q.hom ≫ c₀.left := congrArg (fun z : T ⊗ U ⟶ V ↦ q.hom ≫ z.left) hc
        _ = φ₀ ≫ pullback.fst pB i := by
          change q.hom ≫ q.inv ≫ φ₀ ≫ pullback.fst pB i =
            φ₀ ≫ pullback.fst pB i
          rw [Iso.hom_inv_id_assoc]
    let aFE : A ⟶ B := MorphismProperty.Over.homMk a.left a.w
    let m : Limits.pullback pA i ⟶ Limits.pullback pB i :=
      ((FiniteEtale.pullback i).map aFE).left
    have hm₁ : m ≫ pullback.fst pB i = pullback.fst pA i ≫ a.left :=
      pullback.lift_fst _ _ _
    have hm₂ : m ≫ pullback.snd pB i = pullback.snd pA i :=
      pullback.lift_snd _ _ _
    refine ⟨aFE, ?_⟩
    apply MorphismProperty.Over.Hom.ext
    change m = φ₀
    exact pullback.hom_ext (hm₁.trans ha) (hm₂.trans hφ.symm)

end AlgebraicGeometry.FiniteEtale
