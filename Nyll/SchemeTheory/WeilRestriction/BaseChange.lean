/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.WeilRestriction.Sheaf
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# Base change for relative internal Hom

Restriction from schemes over `S` to schemes over `S'` identifies the relative
internal Hom with the internal Hom of the two pullbacks. The comparison is
obtained from pullback pasting and the adjunction between composition and base
change. Consequently, a representing scheme pulls back to a representing scheme.
-/


@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped MonoidalCategory

noncomputable section

universe u

namespace SchemeTheory.WeilRestriction

variable {S S' : Scheme.{u}}

/-- The canonical isomorphism between taking a fibre product after base change and composing
the test scheme with the base-change morphism. -/
def tensorBaseChangeLeftIso (f : S' ⟶ S) (U : Over S) (T : Over S') :
    pullback T.hom (pullback.snd U.hom f) ≅ pullback (T.hom ≫ f) U.hom :=
  ((pullbackSymmetry T.hom (pullback.snd U.hom f)).trans
    (pullbackLeftPullbackSndIso U.hom f T.hom)).trans
      (pullbackSymmetry U.hom (T.hom ≫ f))

lemma tensorBaseChangeLeftIso_hom_fst
    (f : S' ⟶ S) (U : Over S) (T : Over S') :
    (tensorBaseChangeLeftIso f U T).hom ≫ pullback.fst (T.hom ≫ f) U.hom =
      pullback.fst T.hom (pullback.snd U.hom f) := by
  simp only [tensorBaseChangeLeftIso, Iso.trans_hom, Category.assoc,
    pullbackSymmetry_hom_comp_fst, pullbackLeftPullbackSndIso_hom_snd,
    pullbackSymmetry_hom_comp_snd]

lemma tensorBaseChangeLeftIso_hom_snd
    (f : S' ⟶ S) (U : Over S) (T : Over S') :
    (tensorBaseChangeLeftIso f U T).hom ≫ pullback.snd (T.hom ≫ f) U.hom =
      pullback.snd T.hom (pullback.snd U.hom f) ≫ pullback.fst U.hom f := by
  simp only [tensorBaseChangeLeftIso, Iso.trans_hom, Category.assoc,
    pullbackSymmetry_hom_comp_snd, pullbackLeftPullbackSndIso_hom_fst,
    pullbackSymmetry_hom_comp_fst_assoc]

/-- Pushing a fibre product with a pulled-back scheme to the original base agrees with forming
the fibre product there. -/
def mapTensorPullbackIso (f : S' ⟶ S) (U : Over S) (T : Over S') :
    (Over.map f).obj (T ⊗ (Over.pullback f).obj U) ≅ (Over.map f).obj T ⊗ U :=
  Over.isoMk (tensorBaseChangeLeftIso f U T) (by
    change (tensorBaseChangeLeftIso f U T).hom ≫
        (pullback.fst (T.hom ≫ f) U.hom ≫ (T.hom ≫ f)) =
      (pullback.fst T.hom (pullback.snd U.hom f) ≫ T.hom) ≫ f
    rw [← Category.assoc, tensorBaseChangeLeftIso_hom_fst, Category.assoc])

@[reassoc]
lemma mapTensorPullbackIso_hom_left_fst
    (f : S' ⟶ S) (U : Over S) (T : Over S') :
    (mapTensorPullbackIso f U T).hom.left ≫ pullback.fst (T.hom ≫ f) U.hom =
      pullback.fst T.hom (pullback.snd U.hom f) :=
  tensorBaseChangeLeftIso_hom_fst f U T

@[reassoc]
lemma mapTensorPullbackIso_hom_left_snd
    (f : S' ⟶ S) (U : Over S) (T : Over S') :
    (mapTensorPullbackIso f U T).hom.left ≫ pullback.snd (T.hom ≫ f) U.hom =
      pullback.snd T.hom (pullback.snd U.hom f) ≫ pullback.fst U.hom f :=
  tensorBaseChangeLeftIso_hom_snd f U T

/-- Composition to `S` commutes with product by the pullback of a fixed `S`-scheme. -/
def tensorRightBaseChangeIso (f : S' ⟶ S) (U : Over S) :
    MonoidalCategory.tensorRight ((Over.pullback f).obj U) ⋙ Over.map f ≅
      Over.map f ⋙ MonoidalCategory.tensorRight U :=
  NatIso.ofComponents (mapTensorPullbackIso f U) (fun {T T'} g ↦ by
    apply Over.OverMorphism.ext
    change (g ▷ (Over.pullback f).obj U).left ≫ (mapTensorPullbackIso f U T').hom.left =
      (mapTensorPullbackIso f U T).hom.left ≫ ((Over.map f).map g ▷ U).left
    apply pullback.hom_ext
    · have hleft :
          (g ▷ (Over.pullback f).obj U).left ≫
              pullback.fst T'.hom (pullback.snd U.hom f) =
            pullback.fst T.hom (pullback.snd U.hom f) ≫ g.left := by
        simpa only [Over.pullback_obj_hom] using
          (Over.whiskerRight_left_fst (R := (Over.pullback f).obj U) g)
      have hright :
          (((Over.map f).map g) ▷ U).left ≫
              pullback.fst (T'.hom ≫ f) U.hom =
            pullback.fst (T.hom ≫ f) U.hom ≫ g.left := by
        simpa only [Over.map_obj_hom, Over.map_map_left] using
          (Over.whiskerRight_left_fst (R := U) ((Over.map f).map g))
      simp only [Over.map_obj_hom]
      rw [Category.assoc, mapTensorPullbackIso_hom_left_fst]
      rw [hleft]
      rw [Category.assoc, hright]
      rw [← Category.assoc, mapTensorPullbackIso_hom_left_fst]
    · have hleft :
          (g ▷ (Over.pullback f).obj U).left ≫
              pullback.snd T'.hom (pullback.snd U.hom f) =
            pullback.snd T.hom (pullback.snd U.hom f) := by
        simpa only [Over.pullback_obj_hom] using
          (Over.whiskerRight_left_snd (R := (Over.pullback f).obj U) g)
      have hright :
          (((Over.map f).map g) ▷ U).left ≫
              pullback.snd (T'.hom ≫ f) U.hom =
            pullback.snd (T.hom ≫ f) U.hom := by
        simpa only [Over.map_obj_hom] using
          (Over.whiskerRight_left_snd (R := U) ((Over.map f).map g))
      simp only [Over.map_obj_hom]
      rw [Category.assoc, mapTensorPullbackIso_hom_left_snd]
      rw [← Category.assoc, hleft]
      rw [Category.assoc, hright]
      exact (mapTensorPullbackIso_hom_left_snd f U T).symm)

/-- Restriction to schemes over `S'` is the internal Hom of the pulled-back schemes. -/
def relativeInternalHomBaseChangeIso (f : S' ⟶ S) (U V : Over S) :
    (Over.map f).op ⋙ relativeInternalHomFunctor U V ≅
      relativeInternalHomFunctor ((Over.pullback f).obj U) ((Over.pullback f).obj V) :=
  (Functor.associator (Over.map f).op (MonoidalCategory.tensorRight U).op
    (yoneda.obj V)).symm.trans <|
    (Functor.isoWhiskerRight (NatIso.op (tensorRightBaseChangeIso f U))
      (yoneda.obj V)).trans <|
      (Functor.associator (MonoidalCategory.tensorRight ((Over.pullback f).obj U)).op
        (Over.map f).op (yoneda.obj V)).trans <|
        Functor.isoWhiskerLeft (MonoidalCategory.tensorRight ((Over.pullback f).obj U)).op
          ((Over.mapPullbackAdj f).representableBy V).toIso.symm

/-- A relative internal Hom representer remains a representer after arbitrary base change. -/
def relativeInternalHomRepresentableBaseChange (f : S' ⟶ S) {U V W : Over S}
    (h : (relativeInternalHomFunctor U V).RepresentableBy W) :
    (relativeInternalHomFunctor ((Over.pullback f).obj U)
      ((Over.pullback f).obj V)).RepresentableBy ((Over.pullback f).obj W) :=
  ((Over.mapPullbackAdj f).representableBy W).ofIso <|
    (Functor.isoWhiskerLeft (Over.map f).op h.toIso).trans
      (relativeInternalHomBaseChangeIso f U V)

end SchemeTheory.WeilRestriction
