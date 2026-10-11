/-
Copyright (c) 2026 Naganori Yamaguchi (local additions and compilation).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

This library builds on Anthropic's Fermat's Last Theorem in Lean 4;
no direct Anthropic source-file match is established for this module.
Upstream NOTICE (Copyright 2026 Anthropic, PBC): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
Repository maintainer: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
-/

import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechTwist
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechGradedModule
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCech_GradedModule_nonempty_HEquiv_FD
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCech_Twist_finite_cohomology

/-!
Finite Cech cohomology of a shifted free graded module on projective space.
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Cech.Proofs.ProjSpaceCech_GradedModule_finite_cohomology_FD

universe u

noncomputable section

open Finset Function MvPolynomial

theorem _root_.ProjSpaceCech.GradedModule.finite_cohomology_FD (R : Type u) [CommRing R] (n : ℕ)
    (d₀ : ℤ) (i : ℕ) :
    Module.Finite R (ProjSpaceCech.GradedModule.H (ProjSpaceCech.GradedModule.FD R n d₀) i) :=
  by
  obtain ⟨e⟩ := ProjSpaceCech.GradedModule.nonempty_HEquiv_FD R n d₀ i
  have := ProjSpaceCech.Twist.finite_cohomology R n d₀ i
  exact Module.Finite.equiv e

end
end AlgebraicCurves.Cohomology.Cech.Proofs.ProjSpaceCech_GradedModule_finite_cohomology_FD
end ProofImplementation
