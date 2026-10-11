/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Cancelling an etale second morphism

If the second map of a factorization is etale, its graph is an open
immersion into the base change of the composite. Flatness, local finite
presentation, and geometric reducedness of the composite therefore hold
for the first map as well. The graph and its open immersion are constructed
from the actual diagonal; no graph or comparison is supplied as input.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

/-- An open subscheme of a geometrically reduced scheme remains geometrically
reduced over the same base. -/
lemma GeometricallyReduced.comp_of_isOpenImmersion
    {U X S : Scheme.{u}} (i : U ⟶ X) (f : X ⟶ S)
    [IsOpenImmersion i] [GeometricallyReduced f] :
    GeometricallyReduced (i ≫ f) := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr ?_⟩
  intro K _ y
  let j : pullback (i ≫ f) y ⟶ pullback f y :=
    pullback.map (i ≫ f) y f y i (𝟙 _) (𝟙 _)
      (Category.comp_id (i ≫ f))
      ((Category.comp_id y).trans (Category.id_comp y).symm)
  have : IsOpenImmersion j :=
    MorphismProperty.pullbackMap (P := @IsOpenImmersion)
      (f := i ≫ f) (g := y) (f' := f) (g' := y)
      (inferInstance : IsOpenImmersion i)
      (inferInstance : IsOpenImmersion (𝟙 (Spec (CommRingCat.of K))))
      rfl (Category.id_comp y).symm
  have : IsReduced (pullback f y) :=
    GeometricallyReduced.geometrically_isReduced (f := f) y
      (pullback.fst f y) (pullback.snd f y) (IsPullback.of_hasPullback f y)
  exact isReduced_of_isOpenImmersion j

/-- Flatness, local finite presentation, and geometric reducedness descend
through etale postcomposition by expressing the first map as its open graph
followed by the base change of the composite. -/
lemma flat_finitePresentation_geometricallyReduced_of_comp_etale
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [Etale g] [Flat (f ≫ g)] [LocallyOfFinitePresentation (f ≫ g)]
    [GeometricallyReduced (f ≫ g)] :
    Flat f ∧ LocallyOfFinitePresentation f ∧ GeometricallyReduced f := by
  let graph : X ⟶ pullback (f ≫ g) g :=
    pullback.lift (𝟙 X) f ((Category.id_comp (f ≫ g)).trans rfl)
  have : IsOpenImmersion graph :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion)
      (pullback_lift_diagonal_isPullback f g)
      (inferInstance : IsOpenImmersion (pullback.diagonal g))
  have hFactor : graph ≫ pullback.snd (f ≫ g) g = f :=
    pullback.lift_snd _ _ _
  have hFlat : Flat (graph ≫ pullback.snd (f ≫ g) g) := inferInstance
  have hPresentation : LocallyOfFinitePresentation
      (graph ≫ pullback.snd (f ≫ g) g) := inferInstance
  have hReduced : GeometricallyReduced (graph ≫ pullback.snd (f ≫ g) g) :=
    GeometricallyReduced.comp_of_isOpenImmersion graph (pullback.snd (f ≫ g) g)
  exact ⟨hFactor ▸ hFlat, hFactor ▸ hPresentation, hFactor ▸ hReduced⟩

end AlgebraicGeometry
