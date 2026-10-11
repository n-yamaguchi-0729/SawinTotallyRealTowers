/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Etale.AffineFiniteSubalgebraRefinement
import Nyll.SchemeTheory.Etale.LocalFactorBaseChange
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
import Mathlib.RingTheory.IntegralClosure.Algebra.Defs

/-!
# Finite subalgebras on each actual affine base chart

Start with the original integral morphism and its existing local lifts.
On an affine base chart, its actual map on sections supplies the integral
algebra. The literal source section spectrum maps to the actual pullback
through the native affine-chart square. Base change of the original local
lifts and finite-image descent then produce a finite subalgebra inside the
original direct-image sections on this chart.
-/

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- Every affine chart of the original base has a finite subalgebra of the
actual integral direct-image sections whose spectrum retains the original
cover's local factorizations after base change to that chart. -/
theorem Scheme.Hom.ZariskiLocallyFactorsThrough.exists_finite_subalgebra_on_affine
    {T U X : Scheme.{u}} (g : T ⟶ X) [IsIntegralHom g]
    (f : U ⟶ X) [LocallyOfFinitePresentation f]
    (hlocal : g.ZariskiLocallyFactorsThrough f) (V : X.AffineZariskiSite) :
    let : Algebra Γ(X, V.1) Γ(T, g ⁻¹ᵁ V.1) := (g.app V.1).hom.toAlgebra
    ∃ C : Subalgebra Γ(X, V.1) Γ(T, g ⁻¹ᵁ V.1),
      Module.Finite Γ(X, V.1) C ∧
        (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V.1) C))).ZariskiLocallyFactorsThrough
          (pullback.snd f V.2.fromSpec) := by
  intro algebra
  let R : CommRingCat.{u} := Γ(X, V.1)
  let B : CommRingCat.{u} := Γ(T, g ⁻¹ᵁ V.1)
  have hIntegral : (algebraMap R B).IsIntegral := g.isIntegral_app V.1 V.2
  have : Algebra.IsIntegral R B := algebraMap_isIntegral_iff.mp hIntegral
  let k : Spec R ⟶ X := V.2.fromSpec
  let a : Spec B ⟶ T := (V.2.preimage g).fromSpec
  let p : Spec B ⟶ Spec R := Spec.map (g.app V.1)
  have hp : p ≫ k = a ≫ g :=
    (congrArg (fun z : R ⟶ B => Spec.map z ≫ k) (g.app_eq_appLE (U := V.1))).trans
      (IsAffineOpen.SpecMap_appLE_fromSpec g V.2 (V.2.preimage g) le_rfl)
  let d : Spec B ⟶ pullback g k := pullback.lift a p hp.symm
  have hD : (d ≫ pullback.snd g k).ZariskiLocallyFactorsThrough (pullback.snd f k) :=
    (hlocal.baseChange k).precomp d
  have hdp : d ≫ pullback.snd g k = p := pullback.lift_snd a p hp.symm
  have hP : p.ZariskiLocallyFactorsThrough (pullback.snd f k) :=
    Eq.mp (congrArg (fun z : Spec B ⟶ Spec R =>
      z.ZariskiLocallyFactorsThrough (pullback.snd f k)) hdp) hD
  exact AffineIntegralLimit.exists_finite_subalgebra_locally_factors
    (R := R) (B := B) (pullback.snd f k) hP

end AlgebraicGeometry
