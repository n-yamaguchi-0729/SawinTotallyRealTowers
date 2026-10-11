/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.AffineScheme
import Nyll.SchemeTheory.RingTheory.Descent.SmoothAtPrimeNormality


/-!
# Integral closure of source stalks under smooth morphisms

For a smooth morphism to an affine scheme whose global section ring is a domain and
integrally closed, every source stalk has these properties. The proof uses the smooth
algebra on an affine source chart and its prime localization.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs.Smooth_isDomain_and_isIntegrallyClosed_stalk

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

theorem _root_.AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk
    {U S : Scheme.{u}} (f : U ⟶ S) [Smooth f]
    [IsAffine S] [IsDomain Γ(S, ⊤)] [IsIntegrallyClosed Γ(S, ⊤)] (y : U) :
    IsDomain (U.presheaf.stalk y) ∧ IsIntegrallyClosed (U.presheaf.stalk y) := by
  obtain ⟨W, hW, hyW, -⟩ := exists_isAffineOpen_mem_and_subset (X := U) (x := y) (U := ⊤) trivial
  have hle : W ≤ f ⁻¹ᵁ ⊤ := by simp
  let _ : Algebra Γ(S, ⊤) Γ(U, W) := (f.appLE ⊤ W hle).hom.toAlgebra
  let _ : Algebra.Smooth Γ(S, ⊤) Γ(U, W) := Smooth.smooth_appLE f (isAffineOpen_top S) hW hle
  let _ : Algebra Γ(U, W) (U.presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk U.presheaf (⟨y, hyW⟩ : W)
  let _ : IsLocalization.AtPrime (U.presheaf.stalk y) (hW.primeIdealOf ⟨y, hyW⟩).asIdeal :=
    hW.isLocalization_stalk ⟨y, hyW⟩
  exact (open _root_.Algebra.Smooth in
    isDomain_and_isIntegrallyClosed_of_isIntegrallyClosed_of_isLocalization_atPrime
      Γ(S, ⊤) Γ(U, W)
      (hW.primeIdealOf ⟨y, hyW⟩).asIdeal (U.presheaf.stalk y))
end AlgebraicCurves.Geometry.Schemes.Proofs.Smooth_isDomain_and_isIntegrallyClosed_stalk
end ProofImplementation
