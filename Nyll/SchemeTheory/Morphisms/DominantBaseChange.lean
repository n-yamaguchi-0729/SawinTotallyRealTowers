/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.Topology.Maps.Basic

/-!
# Dominance under open base change

The range of a pullback projection is the inverse image of the range of the
other morphism. Since an open map pulls dense sets back to dense sets,
base change along an open morphism preserves dominance.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Base change along a morphism with open underlying map preserves dominance. -/
lemma isDominant_pullback_fst_of_isOpenMap {X Y S : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (hf : IsOpenMap f) [IsDominant g] :
    IsDominant (pullback.fst f g) := by
  rw [isDominant_iff, DenseRange, Scheme.Pullback.range_fst]
  exact g.denseRange.preimage hf

end AlgebraicGeometry
