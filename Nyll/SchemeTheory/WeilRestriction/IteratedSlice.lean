/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Yoneda

/-!
# Relative representers on an iterated slice

A representation on schemes over `U`, obtained by composition along `U ⟶ S`,
also gives a representation on the slice of `Over S` over `U ⟶ S`.
This is the form needed to glue local representers within the category `Over S`.
-/


@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace SchemeTheory.WeilRestriction

/-- Regard a local relative representer as a representer on the corresponding iterated slice. -/
def representableByIteratedSlice {S U : Scheme.{u}} (f : U ⟶ S)
    (F : (Over S)ᵒᵖ ⥤ Type u) (W : Over U)
    (h : ((Over.map f).op ⋙ F).RepresentableBy W) :
    ((Over.forget (Over.mk f)).op ⋙ F).RepresentableBy
      ((Over.iteratedSliceEquiv (Over.mk f)).inverse.obj W) := by
  let E : Over (Over.mk f) ≌ Over U := Over.iteratedSliceEquiv (Over.mk f)
  have hforget : E.inverse ⋙ Over.forget (Over.mk f) = Over.map f :=
    Over.iteratedSliceBackward_forget (Over.mk f)
  let e : E.functor ⋙ Over.map f ≅ Over.forget (Over.mk f) := by
    rw [← hforget]
    exact (Functor.associator E.functor E.inverse (Over.forget (Over.mk f))).symm.trans <|
      (Functor.isoWhiskerRight E.unitIso.symm (Over.forget (Over.mk f))).trans
        (Functor.leftUnitor (Over.forget (Over.mk f)))
  refine (E.toAdjunction.representableBy W).ofIso ?_
  exact (Functor.isoWhiskerLeft E.functor.op h.toIso).trans <|
    (Functor.associator E.functor.op (Over.map f).op F).symm.trans <|
      Functor.isoWhiskerRight (NatIso.op e.symm) F

end SchemeTheory.WeilRestriction
