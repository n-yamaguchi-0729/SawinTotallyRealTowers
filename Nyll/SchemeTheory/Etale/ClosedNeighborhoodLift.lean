/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Etale.AffineClosedLift
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# Lifting pointed étale neighborhoods across closed immersions

Choose an affine open in the ambient scheme containing the image of the
point, then an affine open in the restricted étale neighborhood. The affine
lifting theorem supplies an ambient étale scheme; the pullback pasting
isomorphism identifies its restriction with the chosen open neighborhood.

The construction works for any nonempty one-point test scheme, hence for
geometric points without imposing a base field on the ambient scheme.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits AlgebraicGeometry TensorProduct

namespace AlgebraicGeometry.Etale

private theorem exists_affineCover_factor
    {P W : Scheme.{u}} [Subsingleton P] [Nonempty P] (w : P ⟶ W) :
    ∃ (a : W.affineCover.I₀) (w' : P ⟶ W.affineCover.X a),
      w' ≫ W.affineCover.f a = w := by
  obtain ⟨a, x, hx⟩ := W.affineCover.exists_eq (w (Classical.choice ‹Nonempty P›))
  have hrange : Set.range w ⊆ Set.range (W.affineCover.f a) := by
    rintro y ⟨p, rfl⟩
    exact ⟨x, hx.trans (congrArg w (Subsingleton.elim _ p))⟩
  exact ⟨a, IsOpenImmersion.lift (W.affineCover.f a) w hrange,
    IsOpenImmersion.lift_fac (W.affineCover.f a) w hrange⟩

/-- A pointed étale neighborhood of a closed subscheme contains an open neighborhood
which is the restriction of an affine étale scheme over the ambient scheme.
The chosen point factors through that restriction. -/
theorem exists_neighborhood_lift_of_closedImmersion
    {X Z W P : Scheme.{u}} [Subsingleton P] [Nonempty P]
    (i : Z ⟶ X) [IsClosedImmersion i] (f : W ⟶ Z) [Etale f] (w : P ⟶ W) :
    ∃ (V : Scheme.{u}) (_ : IsAffine V) (g : V ⟶ X), Etale g ∧
      ∃ h : pullback i g ⟶ W, IsOpenImmersion h ∧
        h ≫ f = pullback.fst i g ∧ ∃ p : P ⟶ pullback i g, p ≫ h = w := by
  obtain ⟨a, x, hx⟩ := exists_affineCover_factor (w ≫ f ≫ i)
  let j : X.affineCover.X a ⟶ X := X.affineCover.f a
  let i₀ : pullback i j ⟶ X.affineCover.X a := pullback.snd i j
  let k : pullback i j ⟶ Z := pullback.fst i j
  let z : P ⟶ pullback i j := pullback.lift (w ≫ f) x hx.symm
  let q : P ⟶ pullback f k := pullback.lift w z (pullback.lift_fst _ _ _).symm
  obtain ⟨b, y, hy⟩ := exists_affineCover_factor q
  let l : (pullback f k).affineCover.X b ⟶ pullback f k := (pullback f k).affineCover.f b
  let f₀ : (pullback f k).affineCover.X b ⟶ pullback i j := l ≫ pullback.snd f k
  obtain ⟨V, _, g₀, hg₀, e, he⟩ := exists_affine_lift_of_closedImmersion i₀ f₀
  have : Etale g₀ := hg₀
  let E : pullback i₀ g₀ ≅ pullback i (g₀ ≫ j) := pullbackLeftPullbackSndIso i j g₀
  let h : pullback i (g₀ ≫ j) ⟶ W := E.inv ≫ e.hom ≫ l ≫ pullback.fst f k
  refine ⟨V, inferInstance, g₀ ≫ j, inferInstance, h, inferInstance, ?_,
    y ≫ e.inv ≫ E.hom, ?_⟩
  · change (E.inv ≫ e.hom ≫ l ≫ pullback.fst f k) ≫ f = _
    rw [Category.assoc, Category.assoc, Category.assoc, pullback.condition]
    rw [← Category.assoc l, ← Category.assoc e.hom, he]
    exact pullbackLeftPullbackSndIso_inv_fst i j g₀
  · simp only [h, Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc, hy]
    exact pullback.lift_fst _ _ _

end AlgebraicGeometry.Etale
