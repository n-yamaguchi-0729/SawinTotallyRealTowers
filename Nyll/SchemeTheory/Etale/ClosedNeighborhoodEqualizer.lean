/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Etale.ClosedNeighborhoodLift
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Equalizing maps after refining a closed-subscheme neighborhood

Two maps from a closed subscheme into an unramified scheme, equal at a
chosen point, become equal after an étale refinement of the ambient scheme
through which the point lifts. We pull back the open diagonal to form their
equality locus, then apply the constructed neighborhood lifting theorem.
The test scheme may be any nonempty one-point scheme.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace AlgebraicGeometry.Etale

/-- Maps into a locally finite type formally unramified scheme that agree at a point
agree on the closed restriction of a pointed ambient étale refinement. -/
theorem exists_refinement_equalizing_of_closedImmersion
    {X Z W B P : Scheme.{u}} [Subsingleton P] [Nonempty P]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (f : W ⟶ B) [FormallyUnramified f] [LocallyOfFiniteType f]
    (a b : Z ⟶ W) (hab : a ≫ f = b ≫ f)
    (p : P ⟶ Z) (hp : p ≫ a = p ≫ b) :
    ∃ (V : Scheme.{u}) (g : V ⟶ X), Etale g ∧
      pullback.fst i g ≫ a = pullback.fst i g ≫ b ∧
      ∃ q : P ⟶ pullback i g, q ≫ pullback.fst i g = p := by
  let pair : Z ⟶ pullback f f := pullback.lift a b hab
  let d : pullback pair (pullback.diagonal f) ⟶ Z := pullback.fst pair (pullback.diagonal f)
  have hd : d ≫ a = d ≫ b := by
    have h₁ := congrArg (fun t => t ≫ pullback.fst f f)
      (pullback.condition (f := pair) (g := pullback.diagonal f))
    have h₂ := congrArg (fun t => t ≫ pullback.snd f f)
      (pullback.condition (f := pair) (g := pullback.diagonal f))
    simp only [pair, Category.assoc, pullback.lift_fst, pullback.lift_snd,
      pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id] at h₁ h₂
    exact h₁.trans h₂.symm
  let w : P ⟶ pullback pair (pullback.diagonal f) :=
    pullback.lift p (p ≫ a) (by
      apply pullback.hom_ext
      · simp only [pair, Category.assoc, pullback.lift_fst, pullback.diagonal_fst,
          Category.comp_id]
      · simp only [pair, Category.assoc, pullback.lift_snd, pullback.diagonal_snd,
          Category.comp_id]
        exact hp.symm)
  obtain ⟨V, _, g, hg, h, _, hf, q, hq⟩ :=
    exists_neighborhood_lift_of_closedImmersion i d w
  refine ⟨V, g, hg, ?_, q, ?_⟩
  · rw [← hf, Category.assoc, hd, ← Category.assoc, hf]
  · rw [← hf, ← Category.assoc, hq]
    exact pullback.lift_fst _ _ _

end AlgebraicGeometry.Etale
