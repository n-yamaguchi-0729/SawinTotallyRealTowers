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
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCech_GradedModule_nonempty_HEquiv_pi
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCech_GradedModule_finite_cohomology_FD

/-!
Finite Cech cohomology of a finite product of shifted free graded modules.
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Cech.Proofs.ProjSpaceCech_GradedModule_finite_cohomology_pi_FD

universe u

noncomputable section

open Finset Function MvPolynomial

theorem _root_.ProjSpaceCech.GradedModule.finite_cohomology_pi_FD (R : Type u) [CommRing R] (n :
    ℕ) {ι : Type} [Fintype ι] (d₀ : ι → ℤ) (i : ℕ) :
    Module.Finite R (ProjSpaceCech.GradedModule.H (ProjSpaceCech.GradedModule.pi (fun k =>
      ProjSpaceCech.GradedModule.FD R n (d₀ k))) i) :=
  by
  have : ∀ k, Module.Finite R (ProjSpaceCech.GradedModule.H (ProjSpaceCech.GradedModule.FD R n (d₀
    k)) i) :=
    fun k => ProjSpaceCech.GradedModule.finite_cohomology_FD R n (d₀ k) i
  obtain ⟨e⟩ := ProjSpaceCech.GradedModule.nonempty_HEquiv_pi (fun k =>
    ProjSpaceCech.GradedModule.FD R n (d₀ k)) i
  exact Module.Finite.equiv e.symm

end
end AlgebraicCurves.Cohomology.Cech.Proofs.ProjSpaceCech_GradedModule_finite_cohomology_pi_FD
end ProofImplementation
