/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Yoneda

/-!
# Restricting local relative representers

If a presheaf on schemes over `S` is represented after restriction to schemes
over `X`, then its restriction along `Y ⟶ X ⟶ S` is represented by the pullback
of that local representer to `Y`. This transfers local representers to refinements
of a cover.
-/


@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace SchemeTheory.WeilRestriction

/-- Restriction along a composite is represented by the pullback of a local representer. -/
def representableByRestrictionBaseChange {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ X)
    (F : (Over S)ᵒᵖ ⥤ Type u) (W : Over X)
    (h : ((Over.map f).op ⋙ F).RepresentableBy W) :
    ((Over.map (g ≫ f)).op ⋙ F).RepresentableBy ((Over.pullback g).obj W) :=
  ((Over.mapPullbackAdj g).representableBy W).ofIso <|
    (Functor.isoWhiskerLeft (Over.map g).op h.toIso).trans <|
      (Functor.associator (Over.map g).op (Over.map f).op F).symm.trans <|
        Functor.isoWhiskerRight (NatIso.op (Over.mapComp g f)) F

end SchemeTheory.WeilRestriction
