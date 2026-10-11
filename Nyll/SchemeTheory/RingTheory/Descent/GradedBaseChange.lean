/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted from the proof and theorem statement at pinned revision
aa2d8b34692b16c70f699536de0d8e75b9a3e9ef:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_GradedAlgebra_bijective_tensorProduct_lift_of_forall_isBaseChange.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GradedAlgebra_bijective_tensorProduct_lift_of_forall_isBaseChange.lean
Upstream NOTICE and per-file ATTRIBUTION (including earlier FLT and Mathlib notices):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
See SchemeTheory/ANTHROPIC_FLT_SOURCE.md for retained notices.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Scalar extension assembled from homogeneous pieces

The inverse is defined on each homogeneous component and extended through the direct sum.
-/

open TensorProduct DirectSum

universe u

namespace SchemeTheory.GradedBaseChange

variable {S : Type u} [CommRing S] (T : Type u) [CommRing T] [Algebra S T]
  (A : Type u) [CommRing A] [Algebra S A] (𝓐 : ℕ → Submodule S A) [GradedAlgebra 𝓐]
  (B : Type u) [CommRing B] [Algebra T B] [Algebra S B] [IsScalarTower S T B]
  (𝓑 : ℕ → Submodule T B) [GradedAlgebra 𝓑]
  (ϑ : A →ₐ[S] B) (hϑdeg : ∀ n, ∀ x ∈ 𝓐 n, ϑ x ∈ 𝓑 n)

private abbrev piece (n : ℕ) : 𝓐 n →ₗ[S] (𝓑 n).restrictScalars S :=
  ϑ.toLinearMap.restrict (p := 𝓐 n) (q := (𝓑 n).restrictScalars S) (hϑdeg n)

private abbrev φ : A ⊗[S] T →ₐ[S] B :=
  Algebra.TensorProduct.lift ϑ (IsScalarTower.toAlgHom S T B) (fun _ _ => Commute.all _ _)

private theorem φ_tmul (a : A) (t : T) : φ T A B ϑ (a ⊗ₜ[S] t) = t • ϑ a := by
  rw [Algebra.TensorProduct.lift_tmul, IsScalarTower.coe_toAlgHom', Algebra.smul_def, mul_comm]

private noncomputable def incl (n : ℕ) : T ⊗[S] ↥(𝓐 n) →ₗ[S] A ⊗[S] T :=
  (TensorProduct.map (𝓐 n).subtype LinearMap.id) ∘ₗ (TensorProduct.comm S T ↥(𝓐 n)).toLinearMap

omit [GradedAlgebra 𝓐] in
private theorem incl_tmul (n : ℕ) (t : T) (a : 𝓐 n) :
    incl T A 𝓐 n (t ⊗ₜ[S] a) = (a : A) ⊗ₜ[S] t := by
  simp only [incl, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    TensorProduct.comm_tmul, TensorProduct.map_tmul, Submodule.subtype_apply, LinearMap.id_apply]

omit [GradedAlgebra 𝓐] in
private theorem φ_incl_smul (n : ℕ) (t : T) (z : T ⊗[S] ↥(𝓐 n)) :
    φ T A B ϑ (incl T A 𝓐 n (t • z)) = t • φ T A B ϑ (incl T A 𝓐 n z) := by
  induction z using _root_.TensorProduct.inductionOn with
  | tmul t' a =>
    rw [TensorProduct.smul_tmul', incl_tmul, incl_tmul, φ_tmul, φ_tmul, smul_eq_mul, mul_smul]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

variable (hbc : ∀ n, IsBaseChange T (piece T A 𝓐 B 𝓑 ϑ hϑdeg n))

private noncomputable def ψn (n : ℕ) : ↥(𝓑 n) →ₗ[S] A ⊗[S] T :=
  (incl T A 𝓐 n) ∘ₗ (((hbc n).equiv.symm.toLinearMap.restrictScalars S) ∘ₗ
    ({ toFun := fun x => ⟨x.1, x.2⟩, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl } :
      ↥(𝓑 n) →ₗ[S] ↥((𝓑 n).restrictScalars S)))

private noncomputable def ψ : B →ₗ[S] A ⊗[S] T :=
  (DirectSum.toModule S ℕ (A ⊗[S] T) (ψn T A 𝓐 B 𝓑 ϑ hϑdeg hbc)) ∘ₗ
    ((DirectSum.decomposeLinearEquiv 𝓑).toLinearMap.restrictScalars S)

omit [GradedAlgebra 𝓐] in
private theorem ψ_of_mem {b : B} {n : ℕ} (hb : b ∈ 𝓑 n) :
    ψ T A 𝓐 B 𝓑 ϑ hϑdeg hbc b = ψn T A 𝓐 B 𝓑 ϑ hϑdeg hbc n ⟨b, hb⟩ := by
  simp only [ψ, LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearEquiv.coe_toLinearMap,
    DirectSum.decomposeLinearEquiv_apply, DirectSum.decompose_of_mem 𝓑 hb]
  exact DirectSum.toModule_lof (M := fun n => ↥(𝓑 n)) S n (⟨b, hb⟩ : ↥(𝓑 n))

omit [GradedAlgebra 𝓐] [GradedAlgebra 𝓑] in
private theorem φ_ψn (n : ℕ) (x : ↥((𝓑 n).restrictScalars S)) :
    φ T A B ϑ (incl T A 𝓐 n ((hbc n).equiv.symm x)) = (x : B) := by
  induction x using (hbc n).inductionOn with
  | tmul m =>
    rw [IsBaseChange.equiv_symm_apply, incl_tmul, φ_tmul, one_smul]
    rfl
  | smul t y hy =>
    rw [LinearEquiv.map_smul, φ_incl_smul, hy]
    rfl
  | add y₁ y₂ h₁ h₂ =>
    rw [map_add, map_add, map_add, h₁, h₂]
    rfl

omit [GradedAlgebra 𝓐] in
private theorem φ_ψ (b : B) : φ T A B ϑ (ψ T A 𝓐 B 𝓑 ϑ hϑdeg hbc b) = b := by
  classical
  conv_rhs => rw [← DirectSum.sum_support_decompose 𝓑 b]
  conv_lhs => rw [← DirectSum.sum_support_decompose 𝓑 b]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [ψ_of_mem T A 𝓐 B 𝓑 ϑ hϑdeg hbc (DirectSum.decompose 𝓑 b n).2]
  exact φ_ψn T A 𝓐 B 𝓑 ϑ hϑdeg hbc n ⟨_, (DirectSum.decompose 𝓑 b n).2⟩

omit [GradedAlgebra 𝓐] in
private theorem ψ_φ_tmul_of_mem {a : A} {n : ℕ} (ha : a ∈ 𝓐 n) (t : T) :
    ψ T A 𝓐 B 𝓑 ϑ hϑdeg hbc (φ T A B ϑ (a ⊗ₜ[S] t)) = a ⊗ₜ[S] t := by
  rw [φ_tmul]
  have hmem : t • ϑ a ∈ 𝓑 n := Submodule.smul_mem _ _ (hϑdeg n a ha)
  rw [ψ_of_mem T A 𝓐 B 𝓑 ϑ hϑdeg hbc hmem]
  have heq : (⟨t • ϑ a, hmem⟩ : ↥((𝓑 n).restrictScalars S)) =
      t • piece T A 𝓐 B 𝓑 ϑ hϑdeg n ⟨a, ha⟩ := rfl
  simp only [ψn, LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearEquiv.coe_toLinearMap]
  change incl T A 𝓐 n ((hbc n).equiv.symm (⟨t • ϑ a, hmem⟩ : ↥((𝓑 n).restrictScalars S))) =
    a ⊗ₜ[S] t
  rw [heq, LinearEquiv.map_smul, IsBaseChange.equiv_symm_apply, TensorProduct.smul_tmul',
    smul_eq_mul, mul_one, incl_tmul]

private theorem ψ_φ (z : A ⊗[S] T) : ψ T A 𝓐 B 𝓑 ϑ hϑdeg hbc (φ T A B ϑ z) = z := by
  classical
  induction z using _root_.TensorProduct.inductionOn with
  | tmul a t =>
    conv_lhs => rw [← DirectSum.sum_support_decompose 𝓐 a]
    conv_rhs => rw [← DirectSum.sum_support_decompose 𝓐 a]
    rw [TensorProduct.sum_tmul, map_sum, map_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    exact ψ_φ_tmul_of_mem T A 𝓐 B 𝓑 ϑ hϑdeg hbc (DirectSum.decompose 𝓐 a n).2 t
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end SchemeTheory.GradedBaseChange

open SchemeTheory.GradedBaseChange in
/-- Degreewise base-change equivalences assemble to a bijective scalar-extension map
on the whole graded algebra. -/
theorem GradedAlgebra.bijective_tensorProduct_lift_of_forall_isBaseChange
    {S : Type u} [CommRing S] (T : Type u) [CommRing T] [Algebra S T]
    (A : Type u) [CommRing A] [Algebra S A] (𝓐 : ℕ → Submodule S A) [GradedAlgebra 𝓐]
    (B : Type u) [CommRing B] [Algebra T B] [Algebra S B] [IsScalarTower S T B]
    (𝓑 : ℕ → Submodule T B) [GradedAlgebra 𝓑]
    (ϑ : A →ₐ[S] B) (hϑdeg : ∀ n, ∀ x ∈ 𝓐 n, ϑ x ∈ 𝓑 n)
    (hbc : ∀ n, IsBaseChange T ((ϑ.toLinearMap.restrict (p := 𝓐 n)
      (q := (𝓑 n).restrictScalars S) (hϑdeg n))
      : 𝓐 n →ₗ[S] (𝓑 n).restrictScalars S)) :
    Function.Bijective
      (Algebra.TensorProduct.lift ϑ (IsScalarTower.toAlgHom S T B) (fun _ _ => Commute.all _ _) :
        A ⊗[S] T →ₐ[S] B) := by
  refine ⟨fun x y hxy => ?_, fun b => ⟨ψ T A 𝓐 B 𝓑 ϑ hϑdeg hbc b, φ_ψ T A 𝓐 B 𝓑 ϑ hϑdeg hbc b⟩⟩
  have := congrArg (ψ T A 𝓐 B 𝓑 ϑ hϑdeg hbc) hxy
  rwa [ψ_φ, ψ_φ] at this
