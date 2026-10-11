/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729

This native left-leg version uses Mathlib's Limits.pullback.map, pullbackSymmetry,
and Over.pullback APIs. Mathlib's Over/Pullback.lean is Copyright (c) 2021
Bhavik Mehta; authors Bhavik Mehta and Andrew Yang; Apache 2.0.
Pinned source:
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/CategoryTheory/Comma/Over/Pullback.lean
-/

import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# Pullback in over categories using left projections

The left-projection pullback functor on over categories is defined together with its
object and morphism formulas. A natural isomorphism compares it with the usual
over-category pullback functor.
-/

universe v u

namespace CategoryTheory.Over

open CategoryTheory Limits

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

noncomputable section

/-- Pullback over the first factor, retaining the native objects `Limits.pullback c g.hom`.
The standard `Over.pullback c` uses the factors in the opposite order. -/
def pullbackLeft {X B : C} (c : X ⟶ B) : Over B ⥤ Over X where
  obj g := Over.mk (Limits.pullback.fst c g.hom)
  map {g h} k :=
    Over.homMk
      (Limits.pullback.map c g.hom c h.hom (𝟙 X) k.left (𝟙 B)
        ((Category.comp_id c).trans (Category.id_comp c).symm)
        ((Category.comp_id g.hom).trans (Over.w k).symm))
      (by
        simp only [Over.mk_hom]
        exact (Limits.pullback.lift_fst _ _ _).trans (Category.comp_id _))
  map_id g := by
    apply Over.OverMorphism.ext
    simp only [Over.homMk_left, Over.id_left]
    exact Limits.pullback.map_id
  map_comp {g h k} a b := by
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, Over.homMk_left]
    symm
    refine (Limits.pullback.map_comp (𝟙 X) (𝟙 X) a.left b.left (𝟙 B) (𝟙 B)
      ((Category.comp_id c).trans (Category.id_comp c).symm)
      ((Category.comp_id g.hom).trans (Over.w a).symm)
      ((Category.comp_id c).trans (Category.id_comp c).symm)
      ((Category.comp_id h.hom).trans (Over.w b).symm)).trans ?_
    apply Limits.pullback.hom_ext <;>
      simp only [Limits.pullback.lift_fst, Limits.pullback.lift_snd, Category.comp_id]

@[simp]
theorem pullbackLeft_obj_left {X B : C} (c : X ⟶ B) (g : Over B) :
    ((pullbackLeft c).obj g).left = Limits.pullback c g.hom := rfl

@[simp]
theorem pullbackLeft_obj_hom {X B : C} (c : X ⟶ B) (g : Over B) :
    ((pullbackLeft c).obj g).hom = Limits.pullback.fst c g.hom := rfl

@[simp]
theorem pullbackLeft_map_left {X B : C} (c : X ⟶ B) {g h : Over B} (k : g ⟶ h) :
    ((pullbackLeft c).map k).left =
      Limits.pullback.map c g.hom c h.hom (𝟙 X) k.left (𝟙 B)
        ((Category.comp_id c).trans (Category.id_comp c).symm)
        ((Category.comp_id g.hom).trans (Over.w k).symm) := rfl

/-- The native left-leg construction is naturally isomorphic to the existing
Mathlib Limits.pullback functor; the comparison is the usual Limits.pullback symmetry. -/
def pullbackLeftIsoPullback {X B : C} (c : X ⟶ B) :
    pullbackLeft c ≅ Over.pullback c :=
  NatIso.ofComponents
    (fun g => Over.isoMk (pullbackSymmetry c g.hom)
      (pullbackSymmetry_hom_comp_snd c g.hom))
    (fun {g h} k => by
      have hleft (a : Over B) :
          (Over.isoMk (f := (pullbackLeft c).obj a)
            (g := (Over.pullback c).obj a) (pullbackSymmetry c a.hom)
            (pullbackSymmetry_hom_comp_snd c a.hom)).hom.left =
              (pullbackSymmetry c a.hom).hom := by
        rfl
      let M : Limits.pullback c g.hom ⟶ Limits.pullback c h.hom :=
        Limits.pullback.map c g.hom c h.hom (𝟙 X) k.left (𝟙 B)
          ((Category.comp_id c).trans (Category.id_comp c).symm)
          ((Category.comp_id g.hom).trans (Over.w k).symm)
      let N : Limits.pullback g.hom c ⟶ Limits.pullback h.hom c :=
        Limits.pullback.lift (Limits.pullback.fst g.hom c ≫ k.left)
          (Limits.pullback.snd g.hom c)
          ((Category.assoc _ _ _).trans
            ((congrArg (fun l => Limits.pullback.fst g.hom c ≫ l) (Over.w k)).trans
              Limits.pullback.condition))
      have mfst : M ≫ Limits.pullback.fst c h.hom = Limits.pullback.fst c g.hom :=
        (Limits.pullback.lift_fst _ _ _).trans (Category.comp_id _)
      have msnd : M ≫ Limits.pullback.snd c h.hom =
          Limits.pullback.snd c g.hom ≫ k.left :=
        Limits.pullback.lift_snd _ _ _
      have nfst : N ≫ Limits.pullback.fst h.hom c =
          Limits.pullback.fst g.hom c ≫ k.left :=
        Limits.pullback.lift_fst _ _ _
      have nsnd : N ≫ Limits.pullback.snd h.hom c = Limits.pullback.snd g.hom c :=
        Limits.pullback.lift_snd _ _ _
      have hnatural : M ≫ (pullbackSymmetry c h.hom).hom =
          (pullbackSymmetry c g.hom).hom ≫ N := by
        apply Limits.pullback.hom_ext
        · exact
            ((Category.assoc _ _ _).trans
              ((congrArg (fun l => M ≫ l) (pullbackSymmetry_hom_comp_fst c h.hom)).trans
                msnd)).trans
              (((Category.assoc _ _ _).trans
                ((congrArg (fun l => (pullbackSymmetry c g.hom).hom ≫ l) nfst).trans
                  (pullbackSymmetry_hom_comp_fst_assoc c g.hom k.left))).symm)
        · exact
            ((Category.assoc _ _ _).trans
              ((congrArg (fun l => M ≫ l) (pullbackSymmetry_hom_comp_snd c h.hom)).trans
                mfst)).trans
              (((Category.assoc _ _ _).trans
                ((congrArg (fun l => (pullbackSymmetry c g.hom).hom ≫ l) nsnd).trans
                  (pullbackSymmetry_hom_comp_snd c g.hom))).symm)
      apply Over.OverMorphism.ext
      simp only [Over.comp_left, hleft,
        pullbackLeft_map_left, Over.pullback_map_left]
      exact hnatural)

end

end CategoryTheory.Over
