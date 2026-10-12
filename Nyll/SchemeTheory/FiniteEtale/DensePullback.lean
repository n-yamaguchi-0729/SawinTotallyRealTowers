/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
public import Nyll.SchemeTheory.Morphisms.DominantBaseChange
public import Nyll.SchemeTheory.Morphisms.UnramifiedHomExt
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Faithful pullback along a dominant morphism

Finite étale morphisms are open, so the projection from their pullback along
a dominant map is still dominant. Two arrows between finite étale schemes
which agree on that pullback agree globally: their relative equalizer is
both open and closed. Neither reducedness nor a Noetherian hypothesis on
the base is needed.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.FiniteEtale

/-- Pullback of finite étale schemes along any dominant morphism is faithful. -/
lemma pullback_faithful_of_isDominant {T S : Scheme.{u}} (j : T ⟶ S) [IsDominant j] :
    (FiniteEtale.pullback j).Faithful where
  map_injective {A B} f g hfg := by
    let i : Over.mk (Limits.pullback.fst A.hom j ≫ A.hom) ⟶ A.toComma :=
      Over.homMk (Limits.pullback.fst A.hom j) rfl
    let : IsDominant i.left :=
      isDominant_pullback_fst_of_isOpenMap A.hom j A.hom.isOpenMap
    have hleft : ((FiniteEtale.pullback j).map f).left =
        ((FiniteEtale.pullback j).map g).left :=
      congrArg (fun k : (FiniteEtale.pullback j).obj A ⟶
        (FiniteEtale.pullback j).obj B ↦ k.left) hfg
    have hcomp : Limits.pullback.fst A.hom j ≫ f.left =
        Limits.pullback.fst A.hom j ≫ g.left := by
      have hf : Limits.pullback.fst A.hom j ≫ f.left =
          ((FiniteEtale.pullback j).map f).left ≫ Limits.pullback.fst B.hom j :=
        (Limits.pullback.lift_fst _ _ _).symm
      have hg : ((FiniteEtale.pullback j).map g).left ≫
          Limits.pullback.fst B.hom j =
          Limits.pullback.fst A.hom j ≫ g.left :=
        Limits.pullback.lift_fst _ _ _
      exact hf.trans ((congrArg (fun a ↦ a ≫ Limits.pullback.fst B.hom j) hleft).trans hg)
    have hOver : f.hom = g.hom :=
      AlgebraicGeometry.Over.hom_ext_of_isDominant_of_unramified f.hom g.hom i
        (CategoryTheory.Over.OverMorphism.ext hcomp)
    apply MorphismProperty.Over.Hom.ext
    exact congrArg (fun a : A.toComma ⟶ B.toComma ↦ a.left) hOver

end AlgebraicGeometry.FiniteEtale
