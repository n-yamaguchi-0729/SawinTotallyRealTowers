/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Descent.AffineCocycle
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# The overlap isomorphism associated with a descent action

An action of the cover groupoid on a scheme over the cover gives an actual
isomorphism between the two overlap pullbacks. Its inverse is obtained by
exchanging the two cover coordinates and applying the same action.

The only hypotheses are the action's compatibility with its projection,
unit law, and associativity law. In particular, no geometric property of
the cover morphism is required. The isomorphism preserves both coordinates
over the cover's self-pullback and restricts to the identity on the diagonal.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

variable {X Y W : Scheme.{u}} (f : Y ⟶ X) (p : W ⟶ Y)
  (a : pullback f (p ≫ f) ⟶ W)
  (ha : a ≫ p = pullback.fst f (p ≫ f))

/-- Exchange the cover coordinates and act on the scheme coordinate. -/
def pullbackActionFlip : pullback f (p ≫ f) ⟶ pullback f (p ≫ f) :=
  pullback.lift (pullback.snd f (p ≫ f) ≫ p) a (by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, ha])

private lemma pullbackActionFlip_fst : pullbackActionFlip f p a ha ≫ pullback.fst f (p ≫ f) =
    pullback.snd f (p ≫ f) ≫ p :=
  pullback.lift_fst _ _ _

private lemma pullbackActionFlip_snd : pullbackActionFlip f p a ha ≫ pullback.snd f (p ≫ f) = a :=
  pullback.lift_snd _ _ _

variable
  (hunit : pullback.lift (f := f) (g := p ≫ f) p (𝟙 W)
    (Category.id_comp (p ≫ f)).symm ≫ a = 𝟙 W)
  (hassoc : pullbackActionStep f (p ≫ f) a (by rw [← Category.assoc, ha]) ≫ a =
    pullbackSkipMiddle f (p ≫ f) ≫ a)

include hunit hassoc

private lemma pullbackActionFlip_action :
    pullbackActionFlip f p a ha ≫ a = pullback.snd f (p ≫ f) := by
  let d : W ⟶ pullback f (p ≫ f) :=
    pullback.lift p (𝟙 W) (Category.id_comp (p ≫ f)).symm
  let t : pullback f (p ≫ f) ⟶ pullback f (pullback.fst f (p ≫ f) ≫ f) :=
    pullback.lift (pullback.snd f (p ≫ f) ≫ p) (𝟙 _) (by
      rw [Category.id_comp, Category.assoc, pullback.condition])
  have htStep : t ≫ pullbackActionStep f (p ≫ f) a (by rw [← Category.assoc, ha]) =
      pullbackActionFlip f p a ha := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullbackActionStep, pullback.lift_fst, t,
        pullbackActionFlip_fst]
    · simp only [Category.assoc, pullbackActionStep, pullback.lift_snd, t,
        pullback.lift_snd_assoc, Category.id_comp, pullbackActionFlip_snd]
  have htSkip : t ≫ pullbackSkipMiddle f (p ≫ f) = pullback.snd f (p ≫ f) ≫ d := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullbackSkipMiddle, pullback.lift_fst, t, d]
    · simp only [Category.assoc, pullbackSkipMiddle, pullback.lift_snd, t, d,
        pullback.lift_snd_assoc, Category.id_comp, Category.comp_id]
  calc
    pullbackActionFlip f p a ha ≫ a =
        t ≫ (pullbackActionStep f (p ≫ f) a (by rw [← Category.assoc, ha]) ≫ a) := by
      rw [← Category.assoc, htStep]
    _ = t ≫ (pullbackSkipMiddle f (p ≫ f) ≫ a) := congrArg (t ≫ ·) hassoc
    _ = pullback.snd f (p ≫ f) ≫ (d ≫ a) := by rw [← Category.assoc, htSkip, Category.assoc]
    _ = pullback.snd f (p ≫ f) := by rw [show d ≫ a = 𝟙 W from hunit, Category.comp_id]

/-- The unit and associativity laws make the action flip an involution. -/
lemma pullbackActionFlip_sq : pullbackActionFlip f p a ha ≫ pullbackActionFlip f p a ha = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackActionFlip_fst, ← Category.assoc, pullbackActionFlip_snd, ha,
      Category.id_comp]
  · rw [Category.assoc, pullbackActionFlip_snd, pullbackActionFlip_action f p a ha hunit hassoc,
      Category.id_comp]

/-- The overlap isomorphism of an action, constructed from its unit and associativity laws. -/
def pullbackActionOverlapIso : pullback f (p ≫ f) ≅ pullback (p ≫ f) f :=
  { hom := pullbackActionFlip f p a ha
    inv := pullbackActionFlip f p a ha
    hom_inv_id := pullbackActionFlip_sq f p a ha hunit hassoc
    inv_hom_id := pullbackActionFlip_sq f p a ha hunit hassoc } ≪≫ pullbackSymmetry f (p ≫ f)

/-- The first coordinate of the overlap map is the action itself. -/
lemma pullbackActionOverlapIso_hom_fst : (pullbackActionOverlapIso f p a ha hunit hassoc).hom ≫
    pullback.fst (p ≫ f) f = a := by
  rw [pullbackActionOverlapIso, Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_fst,
    pullbackActionFlip_snd]

/-- The second coordinate is the original point's image on the cover. -/
lemma pullbackActionOverlapIso_hom_snd : (pullbackActionOverlapIso f p a ha hunit hassoc).hom ≫
    pullback.snd (p ≫ f) f = pullback.snd f (p ≫ f) ≫ p := by
  rw [pullbackActionOverlapIso, Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_snd,
    pullbackActionFlip_fst]

/-- The inverse's cover coordinate is the image of its scheme coordinate. -/
lemma pullbackActionOverlapIso_inv_fst : (pullbackActionOverlapIso f p a ha hunit hassoc).inv ≫
    pullback.fst f (p ≫ f) = pullback.fst (p ≫ f) f ≫ p := by
  rw [pullbackActionOverlapIso, Iso.trans_inv, Category.assoc, pullbackActionFlip_fst,
    ← Category.assoc, pullbackSymmetry_inv_comp_snd]

/-- The inverse applies the same action after exchanging the input coordinates. -/
lemma pullbackActionOverlapIso_inv_snd : (pullbackActionOverlapIso f p a ha hunit hassoc).inv ≫
    pullback.snd f (p ≫ f) = (pullbackSymmetry f (p ≫ f)).inv ≫ a := by
  rw [pullbackActionOverlapIso, Iso.trans_inv, Category.assoc, pullbackActionFlip_snd]

/-- Explicit pullback-lift formula for the forward overlap map. -/
lemma pullbackActionOverlapIso_hom_eq_lift : (pullbackActionOverlapIso f p a ha hunit hassoc).hom =
    pullback.lift a (pullback.snd f (p ≫ f) ≫ p) (by
      rw [← Category.assoc, ha, Category.assoc, pullback.condition]) := by
  apply pullback.hom_ext
  · rw [pullbackActionOverlapIso_hom_fst, pullback.lift_fst]
  · rw [pullbackActionOverlapIso_hom_snd, pullback.lift_snd]

/-- The overlap isomorphism lies over the cover's self-pullback. -/
lemma pullbackActionOverlapIso_over :
    (pullbackActionOverlapIso f p a ha hunit hassoc).hom ≫
      pullback.lift (f := f) (g := f) (pullback.fst (p ≫ f) f ≫ p)
        (pullback.snd (p ≫ f) f) (by rw [Category.assoc, pullback.condition]) =
    pullback.lift (f := f) (g := f) (pullback.fst f (p ≫ f))
      (pullback.snd f (p ≫ f) ≫ p) (by rw [Category.assoc, pullback.condition]) := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullbackActionOverlapIso_hom_fst,
      ha, pullback.lift_fst]
  · rw [Category.assoc, pullback.lift_snd, pullbackActionOverlapIso_hom_snd, pullback.lift_snd]

/-- The overlap isomorphism restricts to the identity over the diagonal. -/
lemma pullbackActionOverlapIso_diagonal :
    pullback.lift (f := f) (g := p ≫ f) p (𝟙 W)
        (Category.id_comp (p ≫ f)).symm ≫ (pullbackActionOverlapIso f p a ha hunit hassoc).hom =
      pullback.lift (f := p ≫ f) (g := f) (𝟙 W) p (Category.id_comp (p ≫ f)) := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackActionOverlapIso_hom_fst, hunit, pullback.lift_fst]
  · rw [Category.assoc, pullbackActionOverlapIso_hom_snd, pullback.lift_snd_assoc,
      Category.id_comp, pullback.lift_snd]

end AlgebraicGeometry
