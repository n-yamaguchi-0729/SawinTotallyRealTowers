/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted from the proof and theorem statement at pinned revision
aa2d8b34692b16c70f699536de0d8e75b9a3e9ef:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Algebra_TensorProduct_descent_datum_trans_symm_of_apply_tmul.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_TensorProduct_descent_datum_trans_symm_of_apply_tmul.lean
Upstream NOTICE and per-file ATTRIBUTION (including earlier FLT and Mathlib notices):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
See SchemeTheory/ANTHROPIC_FLT_SOURCE.md for retained notices.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Tensor-product comparisons in algebra descent

The comparison of two given tensor-product identifications respects scalars and
homogeneous pieces, and identifies its invariant elements with the original equalizer.
-/

universe u

open TensorProduct Algebra.TensorProduct

/-- Two compatible tensor-product identifications induce a scalar-compatible graded
descent comparison, and its invariants form the equalizer of the two maps. -/
theorem Algebra.TensorProduct.descent_datum_trans_symm_of_apply_tmul
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S']
    (A' : Type u) [CommRing A'] [Algebra S A'] [Algebra S' A'] [IsScalarTower S S' A']
    (𝒜' : ℕ → Submodule S' A')
    (A'' : Type u) [CommRing A''] [Algebra (S' ⊗[S] S') A''] [Algebra S A'']
    [IsScalarTower S (S' ⊗[S] S') A'']
    (𝒜'' : ℕ → Submodule (S' ⊗[S] S') A'')
    (ϑ₁ ϑ₂ : A' →ₐ[S] A'')
    (hϑ₁lin : ∀ (s : S') (a : A'), ϑ₁ (s • a) = algebraMap (S' ⊗[S] S') A'' (s ⊗ₜ 1) * ϑ₁ a)
    (hϑ₂lin : ∀ (s : S') (a : A'), ϑ₂ (s • a) = algebraMap (S' ⊗[S] S') A'' (1 ⊗ₜ s) * ϑ₂ a)
    (hϑ₁deg : ∀ n, ∀ a ∈ 𝒜' n, ϑ₁ a ∈ 𝒜'' n)
    (hspan₂ : ∀ n, 𝒜'' n ≤ Submodule.span (S' ⊗[S] S') (ϑ₂ '' (𝒜' n : Set A')))
    (β₁ : A' ⊗[S] S' ≃ₐ[S] A'')
    (hβ₁ : ∀ (a : A') (t : S'), β₁ (a ⊗ₜ t) = ϑ₁ a * algebraMap (S' ⊗[S] S') A'' (1 ⊗ₜ t))
    (β₂ : S' ⊗[S] A' ≃ₐ[S] A'')
    (hβ₂ : ∀ (s : S') (a : A'), β₂ (s ⊗ₜ a) = algebraMap (S' ⊗[S] S') A'' (s ⊗ₜ 1) * ϑ₂ a) :
    let φ : A' ⊗[S] S' ≃ₐ[S] S' ⊗[S] A' := β₁.trans β₂.symm
    φ.toAlgHom.comp (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S S' A') (AlgHom.id S S')) =
        Algebra.TensorProduct.map (AlgHom.id S S') (IsScalarTower.toAlgHom S S' A') ∧
      (∀ (n : ℕ) (a : A'), a ∈ 𝒜' n → ∀ t : S',
        φ (a ⊗ₜ t) ∈ ((𝒜' n).restrictScalars S).baseChange S') ∧
      (∀ a : A',
        a ∈ AlgHom.equalizer (φ.toAlgHom.comp
            (Algebra.TensorProduct.includeLeft : A' →ₐ[S] A' ⊗[S] S'))
              (Algebra.TensorProduct.includeRight : A' →ₐ[S] S' ⊗[S] A') ↔
          ϑ₁ a = ϑ₂ a) := by
  intro φ
  have hφ : ∀ x, φ x = β₂.symm (β₁ x) := fun _ => rfl
  have e1 : ∀ s t : S', β₁ (algebraMap S' A' s ⊗ₜ t) =
      algebraMap (S' ⊗[S] S') A'' (s ⊗ₜ t) := fun s t => by
    rw [hβ₁, Algebra.algebraMap_eq_smul_one (A := A') s, hϑ₁lin, map_one, mul_one, ← map_mul,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have e2 : ∀ s t : S', β₂ (s ⊗ₜ algebraMap S' A' t) =
      algebraMap (S' ⊗[S] S') A'' (s ⊗ₜ t) := fun s t => by
    rw [hβ₂, Algebra.algebraMap_eq_smul_one (A := A') t, hϑ₂lin, map_one, mul_one, ← map_mul,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hβ₂st : ∀ s t : S', β₂.symm (algebraMap (S' ⊗[S] S') A'' (s ⊗ₜ t)) =
      s ⊗ₜ algebraMap S' A' t :=
    fun s t => by rw [AlgEquiv.symm_apply_eq, e2]
  have hβ₂ϑ : ∀ a : A', β₂.symm (ϑ₂ a) = 1 ⊗ₜ a := fun a => by
    rw [AlgEquiv.symm_apply_eq, hβ₂, ← Algebra.TensorProduct.one_def, map_one, one_mul]
  refine ⟨?_, ?_, ?_⟩
  · refine Algebra.TensorProduct.ext' fun s t => ?_
    change φ (algebraMap S' A' s ⊗ₜ t) = s ⊗ₜ algebraMap S' A' t
    rw [hφ, AlgEquiv.symm_apply_eq, e1, e2]
  · intro n a ha t
    set P : Submodule S' (S' ⊗[S] A') := ((𝒜' n).restrictScalars S).baseChange S' with hP
    have hstab : ∀ (s c : S') (z : S' ⊗[S] A'), z ∈ P → (s ⊗ₜ[S] algebraMap S' A' c) * z ∈ P := by
      intro s c z hz
      rw [hP, Submodule.baseChange_eq_span] at hz ⊢
      induction hz using Submodule.span_induction with
      | mem z h =>
        obtain ⟨m, hm, rfl⟩ := h
        change (s ⊗ₜ[S] algebraMap S' A' c) * ((1 : S') ⊗ₜ[S] (m : A')) ∈ _
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← Algebra.smul_def,
          ← mul_one s, ← smul_eq_mul, ← _root_.TensorProduct.smul_tmul']
        refine Submodule.smul_mem _ s (Submodule.subset_span ⟨c • m, ?_, rfl⟩)
        exact (𝒜' n).smul_mem c hm
      | zero => rw [mul_zero]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
      | smul r x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hx
    have hstab' : ∀ (u : S' ⊗[S] S') (z : S' ⊗[S] A'), z ∈ P →
        β₂.symm (algebraMap (S' ⊗[S] S') A'' u) * z ∈ P := by
      intro u z hz
      induction u using _root_.TensorProduct.inductionOn with
      | tmul s c => rw [hβ₂st]; exact hstab s c z hz
      | add u₁ u₂ h₁ h₂ => rw [map_add, map_add, add_mul]; exact Submodule.add_mem _ h₁ h₂
    have key : ∀ y ∈ Submodule.span (S' ⊗[S] S') (ϑ₂ '' (𝒜' n : Set A')), β₂.symm y ∈ P := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y h =>
        obtain ⟨a', ha', rfl⟩ := h
        rw [hβ₂ϑ, hP]
        exact Submodule.tmul_mem_baseChange_of_mem 1 ha'
      | zero => rw [map_zero]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
      | smul u y _ hy => rw [Algebra.smul_def, map_mul]; exact hstab' u _ hy
    rw [hφ, hβ₁]
    refine key _ (hspan₂ n ?_)
    rw [mul_comm, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (hϑ₁deg n a ha)
  · intro a
    rw [AlgHom.mem_equalizer]
    change φ (a ⊗ₜ 1) = 1 ⊗ₜ a ↔ ϑ₁ a = ϑ₂ a
    rw [hφ, AlgEquiv.symm_apply_eq, hβ₁, hβ₂, ← Algebra.TensorProduct.one_def,
      map_one, mul_one, one_mul]
