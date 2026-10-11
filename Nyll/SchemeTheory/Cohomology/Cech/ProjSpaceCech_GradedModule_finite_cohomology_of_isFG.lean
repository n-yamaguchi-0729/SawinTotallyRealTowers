/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ProjSpaceCech_GradedModule_finite_cohomology_of_isFG.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechTwist
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechGradedModule
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCech_GradedModule_Presentation_finite_H_of_ses
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCech_GradedModule_Presentation_ker_isFG
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCech_GradedModule_finite_cohomology_pi_FD

/-!
Finite Cech cohomology of a finitely generated graded module over a noetherian ring.
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Cech.Proofs
namespace ProjSpaceCech_GradedModule_finite_cohomology_of_isFG

universe u

noncomputable section

open Finset Function MvPolynomial

namespace ProjSpaceCech
open _root_.ProjSpaceCech
open _root_.ProjSpaceCech

section Main

variable {R : Type u} [CommRing R] {n : ℕ}

namespace GradedModule
open _root_.ProjSpaceCech.GradedModule
end GradedModule
open scoped _root_.ProjSpaceCech.GradedModule in
theorem GradedModule.finite_cohomology_of_isFG' [IsNoetherianRing R] (D : GradedModule R n)
    (hD : GradedModule.IsFG D) (i : ℕ) :
    Module.Finite R (GradedModule.H D i) := by
  suffices h : ∀ i, ∀ (D' : GradedModule R n), GradedModule.IsFG D' →
      Module.Finite R (GradedModule.H D' i) from h i D hD
  intro i
  induction i using Nat.strong_decreasing_induction with
  | base =>
    refine ⟨n, fun m hm D' _ => ?_⟩
    have := GradedModule.subsingleton_cohomology_of_lt D' hm
    infer_instance
  | step i IH =>
    intro D' ⟨σ⟩
    refine GradedModule.Presentation.finite_H_of_ses σ i ?_ ?_
    · exact GradedModule.finite_cohomology_pi_FD R n σ.d₀ i
    · exact IH (i + 1) (Nat.lt_succ_self i) σ.ker (GradedModule.Presentation.ker_isFG σ)

end Main

end ProjSpaceCech

theorem _root_.ProjSpaceCech.GradedModule.finite_cohomology_of_isFG {R : Type u} [CommRing R]
    [IsNoetherianRing R] {n : ℕ} (D : ProjSpaceCech.GradedModule R n)
    (hD : ProjSpaceCech.GradedModule.IsFG D) (i : ℕ) : Module.Finite R
      (ProjSpaceCech.GradedModule.H D i) :=
  ProjSpaceCech.GradedModule.finite_cohomology_of_isFG' D hD i

end
end ProjSpaceCech_GradedModule_finite_cohomology_of_isFG
end AlgebraicCurves.Cohomology.Cech.Proofs
end ProofImplementation
