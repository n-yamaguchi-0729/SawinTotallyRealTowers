/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted from the proof and theorem statement at pinned revision
aa2d8b34692b16c70f699536de0d8e75b9a3e9ef:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Algebra_bijective_tensorProduct_equalizer_of_faithfullyFlat_of_cocycle.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_bijective_tensorProduct_equalizer_of_faithfullyFlat_of_cocycle.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (including earlier FLT and Mathlib notices):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
See SchemeTheory/ANTHROPIC_FLT_SOURCE.md for copied notices and exact local changes.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Tactic.SplitIfs
import Nyll.SchemeTheory.RingTheory.Descent.FaithfullyFlatAlgebraEqualizer

/-!
# Homogeneous invariants of faithfully flat algebra descent

The degree-preserving hypothesis makes every homogeneous component of an invariant
upstairs element invariant. The ungraded bijectivity statement is reused directly;
its proof is not duplicated in this file.
-/

universe u

open TensorProduct Algebra.TensorProduct

theorem Algebra.bijective_tensorProduct_equalizer_of_faithfullyFlat_of_cocycle
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S']
    [Module.FaithfullyFlat S S']
    (A' : Type u) [CommRing A'] [Algebra S A'] [Algebra S' A'] [IsScalarTower S S' A']
    (𝒜' : ℕ → Submodule S' A') [GradedAlgebra 𝒜']
    (φ : A' ⊗[S] S' ≃ₐ[S] S' ⊗[S] A')
    (hφlin : φ.toAlgHom.comp
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S S' A') (AlgHom.id S S')) =
      Algebra.TensorProduct.map (AlgHom.id S S') (IsScalarTower.toAlgHom S S' A'))
    (hφdeg : ∀ (n : ℕ) (a : A'), a ∈ 𝒜' n → ∀ t : S',
      φ (a ⊗ₜ t) ∈ ((𝒜' n).restrictScalars S).baseChange S')
    (hφcoc : (Algebra.TensorProduct.map (AlgHom.id S S') φ.toAlgHom).comp
        ((Algebra.TensorProduct.assoc S S S S' A' S').toAlgHom.comp
          (Algebra.TensorProduct.map φ.toAlgHom (AlgHom.id S S'))) =
      (Algebra.TensorProduct.map (AlgHom.id S S')
        (Algebra.TensorProduct.comm S A' S').toAlgHom).comp
        ((Algebra.TensorProduct.assoc S S S S' A' S').toAlgHom.comp
          ((Algebra.TensorProduct.map φ.toAlgHom (AlgHom.id S S')).comp
            ((Algebra.TensorProduct.assoc S S S A' S' S').symm.toAlgHom.comp
              ((Algebra.TensorProduct.map (AlgHom.id S A')
                (Algebra.TensorProduct.comm S S' S').toAlgHom).comp
                (Algebra.TensorProduct.assoc S S S A' S' S').toAlgHom)))))
    :
    let A : Subalgebra S A' :=
      AlgHom.equalizer (φ.toAlgHom.comp (Algebra.TensorProduct.includeLeft : A' →ₐ[S] A' ⊗[S] S'))
        (Algebra.TensorProduct.includeRight : A' →ₐ[S] S' ⊗[S] A')
    Function.Bijective (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom S S' A') A.val
      (fun s a => Commute.all (algebraMap S' A' s) (A.val a))) ∧
      (∀ a ∈ A, ∀ n : ℕ, (DirectSum.decompose 𝒜' a n : A') ∈ A) := by
  intro A
  classical
  refine ⟨Algebra.bijective_tensorProduct_equalizer_of_faithfullyFlat_of_descentDatum
    S' A' φ hφlin hφcoc, ?_⟩
  intro a ha n
  let π : A' →ₗ[S] A' :=
    { toFun := fun x => (DirectSum.decompose 𝒜' x n : A')
      map_add' := fun x y => by
        simp only [DirectSum.decompose_add, DirectSum.add_apply, AddMemClass.coe_add]
      map_smul' := fun s x => by
        rw [RingHom.id_apply, ← IsScalarTower.algebraMap_smul S' s x,
          ← IsScalarTower.algebraMap_smul S' s]
        rw [DirectSum.decompose_smul]; rfl }
  have hπ : ∀ x, π x = (DirectSum.decompose 𝒜' x n : A') := fun _ => rfl
  have hπm : ∀ (m : ℕ) (y : S' ⊗[S] A'), y ∈ ((𝒜' m).restrictScalars S).baseChange S' →
      π.baseChange S' y = if m = n then y else 0 := by
    intro m y hy
    rw [Submodule.baseChange_eq_span] at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, hx, rfl⟩ := hy
      replace hx : x ∈ 𝒜' m := hx
      rw [TensorProduct.mk_apply, LinearMap.baseChange_tmul, hπ]
      by_cases hmn : m = n
      · subst hmn; rw [ite_eq_left rfl, DirectSum.decompose_of_mem_same 𝒜' hx]
      · rw [ite_eq_right hmn, DirectSum.decompose_of_mem_ne 𝒜' hx hmn, TensorProduct.tmul_zero]
    | zero => simp only [map_zero, ite_self]
    | add y z _ _ hy hz => rw [map_add, hy, hz]; split_ifs <;> simp only [add_zero]
    | smul s y _ hy => rw [map_smul, hy]; split_ifs <;> simp only [smul_zero]
  have hinv : φ (a ⊗ₜ[S] 1) = (1 : S') ⊗ₜ[S] a := (AlgHom.mem_equalizer _ _ a).mp ha
  have hsum : a = ∑ m ∈ (DirectSum.decompose 𝒜' a).support, (DirectSum.decompose 𝒜' a m : A') :=
    (DirectSum.sum_support_decompose 𝒜' a).symm
  have hL : π.baseChange S' (φ (a ⊗ₜ[S] 1)) = φ ((DirectSum.decompose 𝒜' a n : A') ⊗ₜ[S] 1) := by
    conv_lhs => rw [hsum]
    rw [TensorProduct.sum_tmul, map_sum, map_sum]
    rw [Finset.sum_congr rfl (fun m _ => hπm m _ (hφdeg m _ (Subtype.mem _) 1))]
    rw [Finset.sum_ite_eq']
    split_ifs with hn
    · rfl
    · rw [DFinsupp.notMem_support_iff.mp hn];
        simp only [ZeroMemClass.coe_zero, TensorProduct.zero_tmul, map_zero]
  have hR : π.baseChange S' ((1 : S') ⊗ₜ[S] a) =
      (1 : S') ⊗ₜ[S] (DirectSum.decompose 𝒜' a n : A') := by
    rw [LinearMap.baseChange_tmul, hπ]
  apply (AlgHom.mem_equalizer _ _ _).mpr
  change φ ((DirectSum.decompose 𝒜' a n : A') ⊗ₜ[S] 1) =
    (1 : S') ⊗ₜ[S] (DirectSum.decompose 𝒜' a n : A')
  rw [← hL, ← hR, hinv]
