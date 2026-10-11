/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Etale.AffineLocalFactorDescent
import Nyll.SchemeTheory.Etale.IntegralRefinement
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.RingTheory.IntegralClosure.Algebra.Defs


/-!
# Finite-FP refinements of étale covers over affine bases

The integral refinement of a surjective étale cover over an affine base
has an affine source. Its actual `isoSpec` and the native `Spec.preimage`
map supply the integral algebra to which finite-FP local-factor descent
applies. Thus the finite refinement is constructed from the original cover,
without a local-factorization or limit premise in the final statement.

This proves the affine-base case of the finite-presentation refinement in
Stacks Project, Tag 09Z0. Arbitrary qcqs-base globalization and proper base
change are separate remaining steps.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite Algebra

namespace AlgebraicGeometry

private theorem locally_factors_precomp {S T U X : Scheme.{u}}
    {g : T ⟶ X} {f : U ⟶ X} (h : g.ZariskiLocallyFactorsThrough f) (k : S ⟶ T) :
    (k ≫ g).ZariskiLocallyFactorsThrough f := by
  intro x
  obtain ⟨V, hx, a, ha⟩ := h (k x)
  let W : S.Opens := k ⁻¹ᵁ V
  let b : W.toScheme ⟶ V.toScheme := k.resLE V W le_rfl
  have hb : b ≫ V.ι = W.ι ≫ k := Scheme.Hom.resLE_comp_ι k le_rfl
  refine ⟨W, hx, b ≫ a, ?_⟩
  calc
    (b ≫ a) ≫ f = b ≫ (a ≫ f) := Category.assoc _ _ _
    _ = b ≫ (V.ι ≫ g) := congrArg (fun m : V.toScheme ⟶ X => b ≫ m) ha
    _ = (b ≫ V.ι) ≫ g := (Category.assoc _ _ _).symm
    _ = (W.ι ≫ k) ≫ g := congrArg (fun m : W.toScheme ⟶ T => m ≫ g) hb
    _ = W.ι ≫ (k ≫ g) := Category.assoc _ _ _

/-- A surjective étale cover of an arbitrary affine scheme has a finite,
finitely presented surjective refinement which Zariski locally factors
through that cover. No compactness or separatedness of the cover source is required. -/
theorem Etale.exists_finitePresentation_refinement_spec
    (R : Type u) [CommRing R] {U : Scheme.{u}}
    (f : U ⟶ Spec (CommRingCat.of R)) [Etale f] [Surjective f] :
    ∃ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of R)),
      IsFinite q ∧ LocallyOfFinitePresentation q ∧ Surjective q ∧
        q.ZariskiLocallyFactorsThrough f := by
  obtain ⟨T, g, hgI, hgS, hgLocal⟩ := Etale.exists_integral_refinement f
  have : IsIntegralHom g := hgI
  have : Surjective g := hgS
  have : IsAffine T := isAffine_of_isAffineHom g
  let B : CommRingCat.{u} := Γ(T, ⊤)
  let e : T ≅ Spec B := T.isoSpec
  let φ : CommRingCat.of R ⟶ B := Spec.preimage (e.inv ≫ g)
  let : Algebra R B := φ.hom.toAlgebra
  have hmap : Spec.map (CommRingCat.ofHom (algebraMap R B)) = e.inv ≫ g := by
    change Spec.map (Spec.preimage (e.inv ≫ g)) = e.inv ≫ g
    exact Spec.map_preimage _
  have hcompI : IsIntegralHom (e.inv ≫ g) := inferInstance
  have hspecI : IsIntegralHom (Spec.map (CommRingCat.ofHom (algebraMap R B))) := by
    rw [hmap]
    exact hcompI
  have hringI : (algebraMap R B).IsIntegral := IsIntegralHom.SpecMap_iff.mp hspecI
  have : Algebra.IsIntegral R B := algebraMap_isIntegral_iff.mp hringI
  have hcompS : Surjective (e.inv ≫ g) := inferInstance
  have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap R B))) := by
    rw [hmap]
    exact hcompS
  have hlocal : (Spec.map (CommRingCat.ofHom (algebraMap R B))).ZariskiLocallyFactorsThrough f := by
    rw [hmap]
    exact locally_factors_precomp hgLocal e.inv
  obtain ⟨i, hi⟩ := AffineIntegralLimit.exists_stage_locally_factors
    (R := R) (B := B) f hlocal
  exact ⟨(AffineIntegralLimit.diagram R B).obj i, (AffineIntegralLimit.baseMap R B).app i,
    inferInstance, inferInstance, inferInstance, hi⟩

end AlgebraicGeometry
