/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Module_Flat_lTensor_injective_of_exact_of_surjective_of_flat.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Exact.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Flat.Basic

/-!
# Module Flat l Tensor injective of exact of surjective of flat
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs.ModuleFlatLTensorInjectiveExact

universe u

open TensorProduct

namespace UE1Aux

theorem sq {R : Type u} [CommRing R] {X Y X' Y' : Type u}
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    [AddCommGroup X'] [Module R X'] [AddCommGroup Y'] [Module R Y']
    (a : X →ₗ[R] X') (b : Y →ₗ[R] Y') (t : X ⊗[R] Y) :
    b.lTensor X' (a.rTensor Y t) = a.rTensor Y' (b.lTensor X t) := by
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor,
    LinearMap.rTensor_comp_lTensor]

theorem chase {R : Type u} [CommRing R] {N M P A K F : Type u}
    [AddCommGroup N] [Module R N] [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    [AddCommGroup A] [Module R A] [AddCommGroup K] [Module R K] [AddCommGroup F] [Module R F]
    (f : N →ₗ[R] M) (g : M →ₗ[R] P) (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) [Module.Flat R P]
    (ι : K →ₗ[R] F) (π : F →ₗ[R] A) (hι : Function.Injective ι) (hιπ : Function.Exact ι π)
    (hπ : Function.Surjective π) [Module.Flat R F] :
    Function.Injective (f.lTensor A) := by
  have colP : Function.Injective (ι.rTensor P) :=
    Module.Flat.rTensor_preserves_injective_linearMap ι hι
  have rowF : Function.Injective (f.lTensor F) :=
    Module.Flat.lTensor_preserves_injective_linearMap f hf
  have rowK : Function.Exact (f.lTensor K) (g.lTensor K) := lTensor_exact K hfg hg
  have colM : Function.Exact (ι.rTensor M) (π.rTensor M) := rTensor_exact M hιπ hπ
  have colN : Function.Exact (ι.rTensor N) (π.rTensor N) := rTensor_exact N hιπ hπ
  have colN' : Function.Surjective (π.rTensor N) := LinearMap.rTensor_surjective N hπ
  have hgf : g ∘ₗ f = 0 := hfg.linearMap_comp_eq_zero
  refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
  obtain ⟨y, rfl⟩ := colN' x
  rw [sq] at hx
  obtain ⟨z, hz⟩ := (colM _).mp hx
  have hz0 : g.lTensor K z = 0 := by
    apply colP
    rw [map_zero, ← sq, hz, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hgf,
      LinearMap.lTensor_zero, LinearMap.zero_apply]
  obtain ⟨w, hw⟩ := (rowK z).mp hz0
  have hwy : ι.rTensor N w = y := by
    apply rowF
    rw [sq, hw, hz]
  rw [← hwy]
  exact colN.apply_apply_eq_zero w

end UE1Aux

theorem _root_.Module.Flat.lTensor_injective_of_exact_of_surjective_of_flat
    {R : Type u} [CommRing R] {N M P : Type u}
    [AddCommGroup N] [Module R N] [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    (f : N →ₗ[R] M) (g : M →ₗ[R] P) (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) [Module.Flat R P]
    (A : Type u) [AddCommGroup A] [Module R A] :
    Function.Injective (f.lTensor A) :=
  UE1Aux.chase (K := LinearMap.ker (Finsupp.linearCombination R (id : A → A))) f g hf hfg hg
    (LinearMap.ker (Finsupp.linearCombination R (id : A → A))).subtype
    (Finsupp.linearCombination R (id : A → A))
    (Submodule.injective_subtype _)
    (LinearMap.exact_subtype_ker_map (Finsupp.linearCombination R (id : A → A)))
    (Finsupp.linearCombination_id_surjective R A)
end AlgebraicCurves.Foundations.Algebra.Proofs.ModuleFlatLTensorInjectiveExact
end ProofImplementation
