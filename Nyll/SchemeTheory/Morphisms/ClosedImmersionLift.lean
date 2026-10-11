/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Properties

/-!
# Factoring a map from a reduced scheme through a closed immersion

Set-theoretic containment suffices: the pullback is a surjective closed immersion
into the reduced source, hence an isomorphism. In particular this applies to
points valued in any field, without an algebraic closure hypothesis.
-/

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.IsClosedImmersion

/-- A map from a reduced scheme factors through a closed immersion if its image
is contained in the closed subscheme's image. -/
lemma exists_lift_of_isReduced_of_range_subset
    {X Z Y : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (f : Y ⟶ X) [IsReduced Y] (h : Set.range f ⊆ Set.range i) :
    ∃ g : Y ⟶ Z, g ≫ i = f := by
  have : Surjective (pullback.snd i f) := by
    constructor
    intro y
    obtain ⟨z, hz⟩ := h ⟨y, rfl⟩
    obtain ⟨a, _, ha⟩ := Scheme.Pullback.exists_preimage_pullback z y hz
    exact ⟨a, ha⟩
  have : IsIso (pullback.snd i f) :=
    isIso_of_isClosedImmersion_of_surjective (pullback.snd i f)
  refine ⟨inv (pullback.snd i f) ≫ pullback.fst i f, ?_⟩
  rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]

end AlgebraicGeometry.IsClosedImmersion
