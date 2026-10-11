/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Yoneda

/-!
# Recovering a representer after pullback along a monomorphism

Postcomposition with a monomorphism is fully faithful on slice categories.
The unit of its pullback adjunction is therefore invertible. Restricting a
representation of `T ↦ Hom(i⁎ T, V)` to the smaller slice recovers `V` by
uniqueness of representing objects.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.FiniteEtale

/-- If the presheaf obtained by precomposing `Hom(-, V)` with pullback along a
monomorphism is represented by `W`, then pulling `W` back gives `V`.
No finiteness, étaleness, or surjectivity hypothesis is needed. -/
def pullbackIsoOfRepresentable {X Y : Scheme.{u}} (i : X ⟶ Y) [Mono i]
    (V : Over X) (W : Over Y)
    (h : ((Over.pullback i).op ⋙ yoneda.obj V).RepresentableBy W) :
    (Over.pullback i).obj W ≅ V := by
  let hmap : (Over.map i).FullyFaithful := {
    preimage {A B} f := Over.homMk f.left (by
      apply (cancel_mono i).mp
      simpa only [Over.map_obj_hom, Category.assoc] using Over.w f)
    map_preimage f := Over.OverMorphism.ext rfl
    preimage_map f := Over.OverMorphism.ext rfl
  }
  let : (Over.map i).Full := hmap.full
  let : (Over.map i).Faithful := hmap.faithful
  let adj := Over.mapPullbackAdj i
  let e : (Over.map i).op ⋙ yoneda.obj W ≅ yoneda.obj V :=
    (Functor.isoWhiskerLeft (Over.map i).op h.toIso) ≪≫
      (Functor.associator (Over.map i).op (Over.pullback i).op (yoneda.obj V)).symm ≪≫
      Functor.isoWhiskerRight (NatIso.op (asIso adj.unit)) (yoneda.obj V) ≪≫
      Functor.leftUnitor (yoneda.obj V)
  exact ((adj.representableBy W).ofIso e).uniqueUpToIso
    (Functor.RepresentableBy.yoneda V)

end AlgebraicGeometry.FiniteEtale
