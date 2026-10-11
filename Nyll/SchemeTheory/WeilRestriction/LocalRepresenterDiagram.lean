/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.WeilRestriction.LocalRepresenters
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Equifibered

/-!
# The diagram of local representing objects

Representers of restrictions of a fixed presheaf form a diagram over the base
diagram. Its transition maps come from the representing equivalences, so their
identity, composition, and pullback properties are consequences rather than
additional gluing assumptions.
-/


@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v w uJ vJ

namespace SchemeTheory.WeilRestriction

variable {C : Type u} [Category.{v} C] {J : Type uJ} [Category.{vJ} J]
  (F : Cᵒᵖ ⥤ Type w) (D : J ⥤ C) (W : ∀ j : J, Over (D.obj j))
  (h : ∀ j : J, (sliceRestriction F (D.obj j)).RepresentableBy (W j))

/-- Local representers form a functor, with the transition maps determined by
their universal elements. -/
def localRepresenterDiagram : J ⥤ C where
  obj j := (W j).left
  map {i j} f := localRepresenterMap (h i) (h j) (D.map f)
  map_id i := by
    rw [D.map_id, localRepresenterMap_id]
  map_comp f g := by
    rw [D.map_comp, localRepresenterMap_comp]

/-- The structure maps of local representers form a natural transformation
to the base diagram. -/
def localRepresenterProjection : localRepresenterDiagram F D W h ⟶ D where
  app j := (W j).hom
  naturality i j f := localRepresenterMap_w (h i) (h j) (D.map f)

/-- Every transition square of the diagram of local representers is a pullback. -/
lemma localRepresenterProjection_equifibered [HasPullbacks C] :
    (localRepresenterProjection F D W h).Equifibered := by
  intro i j f
  exact localRepresenterMap_isPullback (h i) (h j) (D.map f)

end SchemeTheory.WeilRestriction
