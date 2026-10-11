/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver

/-!
# Relative internal Hom as a sheaf

For schemes `U` and `V` over `S`, the relative internal Hom presheaf sends
`T` to morphisms over `S` from `T ×ₛ U` to `V`. It is a sheaf for the topology
induced on `Over S` by any subcanonical topology on schemes.

The key observation is that product with `U` is pullback to `U` followed by
composition with its structure morphism. Both functors are continuous for the
induced topologies, without any affineness or finiteness assumptions.
-/


@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace SchemeTheory.WeilRestriction

/-- The presheaf of morphisms over `S` from `T ×ₛ U` to `V`. -/
abbrev relativeInternalHomFunctor {S : Scheme.{u}} (U V : Over S) :
    (Over S)ᵒᵖ ⥤ Type u :=
  (MonoidalCategory.tensorRight U).op ⋙ yoneda.obj V

/-- Product with `U` is base change to `U` followed by composition to the base. -/
def tensorRightIsoPullbackMap {S : Scheme.{u}} (U : Over S) :
    MonoidalCategory.tensorRight U ≅ Over.pullback U.hom ⋙ Over.map U.hom :=
  NatIso.ofComponents
    (fun T ↦ Over.isoMk (Iso.refl (pullback T.hom U.hom)) (by
      exact (pullback.condition :
        pullback.fst T.hom U.hom ≫ T.hom =
          pullback.snd T.hom U.hom ≫ U.hom).symm))
    (fun f ↦ by ext; rfl)

/-- Product with a fixed scheme over `S` is continuous for the induced topology. -/
lemma continuous_tensorRight (J : GrothendieckTopology Scheme.{u})
    {S : Scheme.{u}} (U : Over S) :
    (MonoidalCategory.tensorRight U).IsContinuous (J.over S) (J.over S) := by
  let : (Over.pullback U.hom ⋙ Over.map U.hom).IsContinuous
      (J.over S) (J.over S) :=
    Functor.isContinuous_comp (Over.pullback U.hom) (Over.map U.hom)
      (J.over S) (J.over U.left) (J.over S)
  exact Functor.isContinuous_of_iso (tensorRightIsoPullbackMap U).symm
    (J.over S) (J.over S)

/-- Relative internal Hom is a sheaf for every subcanonical topology on schemes. -/
lemma relativeInternalHom_isSheaf (J : GrothendieckTopology Scheme.{u}) [J.Subcanonical]
    {S : Scheme.{u}} (U V : Over S) :
    Presheaf.IsSheaf (J.over S) (relativeInternalHomFunctor U V) := by
  let : (MonoidalCategory.tensorRight U).IsContinuous (J.over S) (J.over S) :=
    continuous_tensorRight J U
  exact Functor.op_comp_isSheaf_of_isSheaf
    (F := MonoidalCategory.tensorRight U) (J := J.over S) (K := J.over S)
    (yoneda.obj V)
    (by
      rw [isSheaf_iff_isSheaf_of_type]
      exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
        (J := J.over S) (yoneda.obj V))

end SchemeTheory.WeilRestriction
