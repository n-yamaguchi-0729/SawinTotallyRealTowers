/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Affine.WeilRestriction.GluedRepresentable
public import Nyll.SchemeTheory.WeilRestriction.Congr
public import Mathlib.RingTheory.Etale.Finite
public import Nyll.SchemeTheory.FiniteEtale.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Finite étale internal Hom over an affine scheme

The global sections of a finite étale scheme over an affine base form a
finite étale algebra. The naturality square of `isoSpec` identifies the
original relative scheme with the pullback of the spectrum of this algebra.
Pulling back the algebraic internal Hom representer and transporting its two
arguments therefore gives an internal Hom over any affine base scheme.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace SchemeTheory.WeilRestriction

variable (S : Scheme.{u}) [IsAffine S]

/-- Global sections with the algebra structure induced by the structure morphism. -/
def affineFiniteEtaleAlgebra (U : FiniteEtale S) :
    CommAlgCat.FiniteEtale.{u} Γ(S, ⊤) := by
  letI : IsAffineHom U.hom := U.prop.toIsFinite.toIsAffineHom
  letI : IsAffine U.left :=
    @isAffine_of_isAffineHom U.left S U.hom
      (@IsFinite.toIsAffineHom _ _ U.hom U.prop.toIsFinite)
      ‹IsAffine S›
  letI : IsAffine ((Functor.fromPUnit S).obj U.right) := ‹IsAffine S›
  letI : Algebra Γ(S, ⊤) Γ(U.left, ⊤) := U.hom.appTop.hom.toAlgebra
  have hRing : RingHom.FiniteEtale U.hom.appTop.hom :=
    ((HasAffineProperty.iff_of_isAffine
      (P := (@IsFiniteEtale : MorphismProperty Scheme.{u}))
      (Q := affineAnd RingHom.FiniteEtale) (f := U.hom)).mp U.prop).2
  have hAlg : Algebra.FiniteEtale Γ(S, ⊤) Γ(U.left, ⊤) := hRing
  exact
    { obj := CommAlgCat.of Γ(S, ⊤) Γ(U.left, ⊤)
      property := ⟨hAlg.toFinite, hAlg.toEtale⟩ }

/-- The naturality square of `isoSpec` presents a finite étale object as a pullback. -/
def affineFiniteEtaleSpecPullbackIso (U : FiniteEtale S) :
    (FiniteEtale.forget S).obj U ≅
      (Over.pullback S.isoSpec.hom).obj
        (SchemeTheory.Affine.specAOver
          (R := Γ(S, ⊤)) (A := affineFiniteEtaleAlgebra S U)) := by
  letI : IsAffineHom U.hom := U.prop.toIsFinite.toIsAffineHom
  letI : IsAffine U.left :=
    @isAffine_of_isAffineHom U.left S U.hom
      (@IsFinite.toIsAffineHom _ _ U.hom U.prop.toIsFinite)
      ‹IsAffine S›
  letI : IsAffine ((Functor.fromPUnit S).obj U.right) := ‹IsAffine S›
  letI : IsAffine ((𝟭 Scheme.{u}).obj U.left) := ‹IsAffine U.left›
  let h : IsPullback U.left.isoSpec.hom U.hom
      (Spec.map U.hom.appTop) S.isoSpec.hom :=
    IsPullback.of_horiz_isIso ⟨Scheme.isoSpec_hom_naturality U.hom⟩
  exact Over.isoMk h.isoPullback h.isoPullback_hom_snd

/-- A finite étale representer of relative internal Hom over an affine base. -/
def affineFiniteEtaleInternalHomRepresenter (U V : FiniteEtale S) : FiniteEtale S :=
  (FiniteEtale.pullback S.isoSpec.hom).obj
    (SchemeTheory.Affine.finiteEtaleInternalHomGlued
      (R := Γ(S, ⊤))
      (A := affineFiniteEtaleAlgebra S U) (B := affineFiniteEtaleAlgebra S V))

/-- The constructed finite étale object represents relative internal Hom. -/
def affineFiniteEtaleInternalHomRepresentable (U V : FiniteEtale S) :
    (relativeInternalHomFunctor
      ((FiniteEtale.forget S).obj U) ((FiniteEtale.forget S).obj V)).RepresentableBy
        ((FiniteEtale.forget S).obj (affineFiniteEtaleInternalHomRepresenter S U V)) :=
  (SchemeTheory.Affine.finiteEtaleInternalHomGluedBaseChangeRepresentable
    (R := Γ(S, ⊤))
    (A := affineFiniteEtaleAlgebra S U) (B := affineFiniteEtaleAlgebra S V)
    S.isoSpec.hom).ofIso <|
      relativeInternalHomIso
        (affineFiniteEtaleSpecPullbackIso S U).symm
        (affineFiniteEtaleSpecPullbackIso S V).symm

end SchemeTheory.WeilRestriction
