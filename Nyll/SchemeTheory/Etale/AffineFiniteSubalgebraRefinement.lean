/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Etale.AffineLocalFactorDescent
import Nyll.SchemeTheory.Etale.IntegralRefinement
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
# Actual finite subalgebras retaining the original local factorizations

The existing affine finite-presentation descent produces a finite stage
with an actual map to the original integral algebra. Taking that map's
image produces a finite subalgebra of the original algebra. Its spectrum
inherits the local factorizations by pulling back their actual open sets.

This supplies local finite subalgebras for global submodule extension; it
does not reconstruct affine descent or assert that the subalgebras already
extend compatibly across a nonaffine base.
-/

noncomputable section

universe u

open CategoryTheory Opposite Algebra

namespace AlgebraicGeometry

/-- Pulling back the actual neighborhoods and their lifts preserves
Zariski-local factorization through a fixed morphism. -/
theorem Scheme.Hom.ZariskiLocallyFactorsThrough.precomp {S T U X : Scheme.{u}}
    {g : T ⟶ X} {f : U ⟶ X} (h : g.ZariskiLocallyFactorsThrough f) (k : S ⟶ T) :
    (k ≫ g).ZariskiLocallyFactorsThrough f := by
  intro x
  obtain ⟨V, hx, a, ha⟩ := h (k x)
  let W : S.Opens := k ⁻¹ᵁ V
  let b : W.toScheme ⟶ V.toScheme := k.resLE V W le_rfl
  have hb : b ≫ V.ι = W.ι ≫ k := Scheme.Hom.resLE_comp_ι k le_rfl
  refine ⟨W, hx, b ≫ a, ?_⟩
  calc
    (b ≫ a) ≫ f = b ≫ (a ≫ f) := Category.assoc b a f
    _ = b ≫ (V.ι ≫ g) := congrArg (fun m : V.toScheme ⟶ X => b ≫ m) ha
    _ = (b ≫ V.ι) ≫ g := (Category.assoc b V.ι g).symm
    _ = (W.ι ≫ k) ≫ g := congrArg (fun m : W.toScheme ⟶ T => m ≫ g) hb
    _ = W.ι ≫ (k ≫ g) := Category.assoc W.ι k g

namespace AffineIntegralLimit

/-- Actual local factorizations of the original integral spectrum descend
to a finite subalgebra inside the original algebra, rather than merely to
an abstract finite-presentation stage mapping to it. -/
theorem exists_finite_subalgebra_locally_factors
    {R B : Type u} [CommRing R] [CommRing B] [Algebra R B] [Algebra.IsIntegral R B]
    {U : Scheme.{u}} (f : U ⟶ Spec (CommRingCat.of R)) [LocallyOfFinitePresentation f]
    (hlocal : (Spec.map (CommRingCat.ofHom (algebraMap R B))).ZariskiLocallyFactorsThrough f) :
    ∃ C : Subalgebra R B, Module.Finite R C ∧
      (Spec.map (CommRingCat.ofHom (algebraMap R C))).ZariskiLocallyFactorsThrough f := by
  obtain ⟨i, hi⟩ := exists_stage_locally_factors f hlocal
  let η : i.unop.stage →ₐ[R] B := i.unop.map
  let C : Subalgebra R B := η.range
  have : Module.Finite R i.unop.stage := i.unop.finite
  have hC : Module.Finite R C :=
    Module.Finite.of_surjective η.rangeRestrict.toLinearMap η.rangeRestrict_surjective
  let k : Spec (CommRingCat.of C) ⟶ (diagram R B).obj i :=
    Spec.map (CommRingCat.ofHom η.rangeRestrict.toRingHom)
  have hcomp : k ≫ (baseMap R B).app i =
      Spec.map (CommRingCat.ofHom (algebraMap R C)) := by
    change Spec.map (CommRingCat.ofHom η.rangeRestrict.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R i.unop.stage)) =
      Spec.map (CommRingCat.ofHom (algebraMap R C))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun φ : R →+* C => Spec.map (CommRingCat.ofHom φ))
      η.rangeRestrict.comp_algebraMap
  refine ⟨C, hC, ?_⟩
  rw [← hcomp]
  exact hi.precomp k

end AffineIntegralLimit

end AlgebraicGeometry
