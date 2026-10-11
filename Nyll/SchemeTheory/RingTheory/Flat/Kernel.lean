/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Module_Flat_ker_of_surjective_of_flat.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Exact.Basic
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.RingTheory.Flat.Basic
import Nyll.SchemeTheory.RingTheory.Flat.TensorInjectivity

/-!
# Module Flat ker of surjective of flat
-/

/-! Flatness of the kernel of a surjection between flat modules. -/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs.Module_Flat_ker_of_surjective_of_flat

universe u

open TensorProduct

theorem _root_.Module.Flat.ker_of_surjective_of_flat
    {R : Type u} [CommRing R] {M P : Type u}
    [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    [Module.Flat R M] [Module.Flat R P] (g : M →ₗ[R] P) (hg : Function.Surjective g) :
    Module.Flat R (LinearMap.ker g) := by
  classical
  rw [Module.Flat.iff_rTensor_preserves_injective_linearMap]
  intro N N' _ _ _ _ ι hι
  have hpure : ∀ (A : Type u) [AddCommGroup A] [Module R A],
      Function.Injective ((LinearMap.ker g).subtype.lTensor A) := fun A _ _ =>
    Module.Flat.lTensor_injective_of_exact_of_surjective_of_flat (LinearMap.ker g).subtype g
      (Submodule.subtype_injective _) (LinearMap.exact_subtype_ker_map g) hg A
  have h2 : Function.Injective ((ι.rTensor M) ∘ₗ ((LinearMap.ker g).subtype.lTensor N)) :=
    (Module.Flat.rTensor_preserves_injective_linearMap ι hι).comp (hpure N)
  have hsq : (ι.rTensor M) ∘ₗ ((LinearMap.ker g).subtype.lTensor N) =
      ((LinearMap.ker g).subtype.lTensor N') ∘ₗ (ι.rTensor (LinearMap.ker g)) := by
    rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
  rw [hsq] at h2
  exact Function.Injective.of_comp h2
end AlgebraicCurves.Foundations.Algebra.Proofs.Module_Flat_ker_of_surjective_of_flat
end ProofImplementation
