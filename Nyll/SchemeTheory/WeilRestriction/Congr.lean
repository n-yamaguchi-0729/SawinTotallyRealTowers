/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.WeilRestriction.Sheaf
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Yoneda

/-!
# Changing the arguments of relative internal Hom

Isomorphisms of the source and target induce a natural isomorphism of relative
internal Hom presheaves. This identifies geometric pullbacks with their affine
tensor-product presentations when constructing local representers.
-/


@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace SchemeTheory.WeilRestriction

/-- Relative internal Hom is contravariant in its source and covariant in its target. -/
def relativeInternalHomIso {S : Scheme.{u}} {U U' V V' : Over S}
    (eU : U ≅ U') (eV : V ≅ V') :
    relativeInternalHomFunctor U V ≅ relativeInternalHomFunctor U' V' :=
  (Functor.isoWhiskerRight
    (NatIso.op ((MonoidalCategory.tensoringRight (Over S)).mapIso eU.symm))
    (yoneda.obj V)).trans <|
      Functor.isoWhiskerLeft (MonoidalCategory.tensorRight U').op (yoneda.mapIso eV)

end SchemeTheory.WeilRestriction
