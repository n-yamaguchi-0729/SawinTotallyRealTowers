/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Etale.IntegralRefinement
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Base change of actual Zariski-local factorizations

Pull back the existing neighborhoods and their actual lifts, then use the
native pullback universal property. In particular the original integral
refinement's local factorizations remain available on every affine chart
of a nonaffine base.
-/

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- An actual local factorization survives arbitrary base change. The new
local lift is constructed by the pullback universal property. -/
theorem Scheme.Hom.ZariskiLocallyFactorsThrough.baseChange
    {T U X Y : Scheme.{u}} {g : T ⟶ X} {f : U ⟶ X}
    (hlocal : g.ZariskiLocallyFactorsThrough f) (k : Y ⟶ X) :
    (pullback.snd g k).ZariskiLocallyFactorsThrough (pullback.snd f k) := by
  intro x
  let P : Scheme.{u} := pullback g k
  let p : P ⟶ T := pullback.fst g k
  let q : P ⟶ Y := pullback.snd g k
  obtain ⟨V, hx, a, ha⟩ := hlocal (p x)
  let W : P.Opens := p ⁻¹ᵁ V
  let b : W.toScheme ⟶ V.toScheme := p.resLE V W le_rfl
  have hb : b ≫ V.ι = W.ι ≫ p := Scheme.Hom.resLE_comp_ι p le_rfl
  let t : W.toScheme ⟶ Y := W.ι ≫ q
  have hcompat : (b ≫ a) ≫ f = t ≫ k := by
    calc
      (b ≫ a) ≫ f = b ≫ (a ≫ f) := Category.assoc b a f
      _ = b ≫ (V.ι ≫ g) := congrArg (fun z : V.toScheme ⟶ X => b ≫ z) ha
      _ = (b ≫ V.ι) ≫ g := (Category.assoc b V.ι g).symm
      _ = (W.ι ≫ p) ≫ g := congrArg (fun z : W.toScheme ⟶ T => z ≫ g) hb
      _ = W.ι ≫ (p ≫ g) := Category.assoc W.ι p g
      _ = W.ι ≫ (q ≫ k) :=
        congrArg (fun z : P ⟶ X => W.ι ≫ z) (pullback.condition (f := g) (g := k))
      _ = t ≫ k := (Category.assoc W.ι q k).symm
  let d : W.toScheme ⟶ pullback f k := pullback.lift (b ≫ a) t hcompat
  refine ⟨W, hx, d, ?_⟩
  exact pullback.lift_snd (b ≫ a) t hcompat

end AlgebraicGeometry
