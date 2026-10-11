/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted from the proof and theorem statement at pinned revision
aa2d8b34692b16c70f699536de0d8e75b9a3e9ef:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Module_FaithfullyFlat_isBaseChange_eqLocus_of_descentDatum.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_FaithfullyFlat_isBaseChange_eqLocus_of_descentDatum.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (including earlier FLT and Mathlib notices):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
See SchemeTheory/ANTHROPIC_FLT_SOURCE.md for copied notices and exact local changes.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.Tactic.Convert

/-!
# Effective faithfully flat descent for a module datum

The invariant submodule of an arbitrary compatible tensor descent datum base-changes
back to the given module. This differs from the canonical Amitsur equalizer of an
already descended module. Public assumptions and conclusions are those of the pinned
upstream theorem; implementation-only coaction helpers are private.
-/

namespace SchemeTheory.RingTheory.Descent.FaithfullyFlatModuleDatum

open TensorProduct

namespace Invariants

universe u v w

section Defs

variable {A : Type u} [CommRing A] {B : Type v} [CommRing B] [Algebra A B]
  {N : Type w} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
  (φ : N ⊗[A] B ≃ₗ[A] B ⊗[A] N)

private noncomputable def δ : N →ₗ[A] B ⊗[A] N :=
  (φ : N ⊗[A] B →ₗ[A] B ⊗[A] N) ∘ₗ (TensorProduct.mk A N B).flip 1

variable (A B N) in
private noncomputable def ι : N →ₗ[A] B ⊗[A] N := TensorProduct.mk A B N 1

private noncomputable def Msub : Submodule A N := LinearMap.eqLocus (δ φ) (ι A B N)

omit [Module B N] [IsScalarTower A B N] in
private theorem δ_apply (n : N) : δ φ n = φ (n ⊗ₜ 1) := rfl

omit [Module B N] [IsScalarTower A B N] in
private theorem mem_Msub {n : N} : n ∈ Msub φ ↔ φ (n ⊗ₜ 1) = 1 ⊗ₜ n := Iff.rfl

private theorem δ_smul_of_mem (hφ₁ : ∀ (b : B) (x : N ⊗[A] B), φ (b • x) = b • φ x)
    {m : N} (hm : m ∈ Msub φ) (b : B) : δ φ (b • m) = b ⊗ₜ m := by
  rw [δ_apply, show (b • m) ⊗ₜ[A] (1 : B) = b • (m ⊗ₜ[A] (1 : B)) from
    (TensorProduct.smul_tmul' b m (1 : B)).symm, hφ₁, (mem_Msub φ).mp hm, TensorProduct.smul_tmul',
    smul_eq_mul, mul_one]

omit [Module B N] [IsScalarTower A B N] in
private theorem lTensor_δ_δ
    (hcoc : (φ : N ⊗[A] B →ₗ[A] B ⊗[A] N).lTensor B ∘ₗ (TensorProduct.assoc A B N B).toLinearMap ∘ₗ
        (φ : N ⊗[A] B →ₗ[A] B ⊗[A] N).rTensor B =
      (TensorProduct.comm A N B).toLinearMap.lTensor B ∘ₗ
        (TensorProduct.assoc A B N B).toLinearMap ∘ₗ
        (φ : N ⊗[A] B →ₗ[A] B ⊗[A] N).rTensor B ∘ₗ (TensorProduct.assoc A N B B).symm.toLinearMap ∘ₗ
        (TensorProduct.comm A B B).toLinearMap.lTensor N ∘ₗ
          (TensorProduct.assoc A N B B).toLinearMap)
    (n : N) : (δ φ).lTensor B (δ φ n) = (ι A B N).lTensor B (δ φ n) := by
  have h := LinearMap.congr_fun hcoc ((n ⊗ₜ[A] (1 : B)) ⊗ₜ[A] (1 : B))
  have e1 : ∀ z : B ⊗[A] N, (φ : N ⊗[A] B →ₗ[A] B ⊗[A] N).lTensor B
      (TensorProduct.assoc A B N B (z ⊗ₜ (1 : B))) = (δ φ).lTensor B z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [add_tmul, map_add, hx, hy]
    | tmul b n' => rfl
  have e2 : ∀ z : B ⊗[A] N, (TensorProduct.comm A N B).toLinearMap.lTensor B
      (TensorProduct.assoc A B N B (z ⊗ₜ (1 : B))) = (ι A B N).lTensor B z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [add_tmul, map_add, hx, hy]
    | tmul b n' => rfl
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
    TensorProduct.assoc_tmul, TensorProduct.comm_tmul, TensorProduct.assoc_symm_tmul] at h
  rw [e1, e2] at h
  exact h

private theorem tmul_one_injective :
    Function.Injective (fun n : N => n ⊗ₜ[A] (1 : B)) := by
  intro m n h
  apply Algebra.TensorProduct.mk_one_injective_of_isScalarTower (R := A) (S := B) N
  simpa only [TensorProduct.mk_apply, TensorProduct.comm_tmul] using
    congrArg (TensorProduct.comm A N B) h

end Defs

section Main

variable {A : Type u} [CommRing A] (B : Type v) [CommRing B]
  [Algebra A B] [Module.FaithfullyFlat A B]
  {N : Type w} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
  (φ : N ⊗[A] B ≃ₗ[A] B ⊗[A] N)

private theorem isBaseChange_Msub (hφ₁ : ∀ (b : B) (x : N ⊗[A] B), φ (b • x) = b • φ x)
    (hcoc : (φ : N ⊗[A] B →ₗ[A] B ⊗[A] N).lTensor B ∘ₗ (TensorProduct.assoc A B N B).toLinearMap ∘ₗ
        (φ : N ⊗[A] B →ₗ[A] B ⊗[A] N).rTensor B =
      (TensorProduct.comm A N B).toLinearMap.lTensor B ∘ₗ
        (TensorProduct.assoc A B N B).toLinearMap ∘ₗ
        (φ : N ⊗[A] B →ₗ[A] B ⊗[A] N).rTensor B ∘ₗ (TensorProduct.assoc A N B B).symm.toLinearMap ∘ₗ
        (TensorProduct.comm A B B).toLinearMap.lTensor N ∘ₗ
          (TensorProduct.assoc A N B B).toLinearMap) :
    IsBaseChange B (Msub φ).subtype := by
  let θ : B ⊗[A] Msub φ →ₗ[B] N := (Msub φ).subtype.liftBaseChange B
  let κ : B ⊗[A] Msub φ →ₗ[A] B ⊗[A] N := (Msub φ).subtype.lTensor B
  have hδθ : ∀ y, δ φ (θ y) = κ y := by
    intro y
    induction y using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b m =>
      simp only [θ, κ, LinearMap.liftBaseChange_tmul,
        LinearMap.lTensor_tmul, Submodule.subtype_apply]
      exact δ_smul_of_mem φ hφ₁ m.2 b
  have hκ : Function.Injective κ :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (Msub φ).injective_subtype
  have hδ : Function.Injective (δ φ) := φ.injective.comp tmul_one_injective
  have hθ : Function.Bijective θ := by
    constructor
    · intro y₁ y₂ h
      apply hκ
      rw [← hδθ, ← hδθ, h]
    · intro n
      have hmem : δ φ n ∈ LinearMap.eqLocus (TensorProduct.AlgebraTensorModule.lTensor A B (δ φ))
          (TensorProduct.AlgebraTensorModule.lTensor A B (ι A B N)) := by
        change TensorProduct.AlgebraTensorModule.lTensor A B (δ φ) (δ φ n) =
          TensorProduct.AlgebraTensorModule.lTensor A B (ι A B N) (δ φ n)
        have := lTensor_δ_δ φ hcoc n
        convert this using 1 <;> rfl
      rw [Module.Flat.eqLocus_lTensor_eq] at hmem
      have hmemκ : δ φ n ∈ LinearMap.range κ := hmem
      obtain ⟨y, hy⟩ := hmemκ
      exact ⟨y, hδ ((hδθ y).trans hy)⟩
  refine IsBaseChange.of_equiv (LinearEquiv.ofBijective θ hθ) fun m => ?_
  change (1 : B) • (m : N) = (m : N)
  exact one_smul B (m : N)

omit [Module.FaithfullyFlat A B] in
private theorem φ_tmul_of_mem (hφ₁ : ∀ (b : B) (x : N ⊗[A] B), φ (b • x) = b • φ x)
    (hφ₂ : ∀ (b : B) (x : N ⊗[A] B),
      φ ((LinearMap.mulLeft A b).lTensor N x) = (DistribSMul.toLinearMap A N b).lTensor B (φ x))
    (b b' : B) (m : N) (hm : φ (m ⊗ₜ 1) = 1 ⊗ₜ m) :
    φ ((b • m) ⊗ₜ[A] b') = b ⊗ₜ[A] (b' • m) := by
  have h1 : (b • m) ⊗ₜ[A] b' = (LinearMap.mulLeft A b').lTensor N ((b • m) ⊗ₜ[A] (1 : B)) := by
    rw [LinearMap.lTensor_tmul, LinearMap.mulLeft_apply, mul_one]
  rw [h1, hφ₂, ← δ_apply, δ_smul_of_mem φ hφ₁ hm,
    LinearMap.lTensor_tmul, DistribSMul.toLinearMap_apply]

end Main

end Invariants

universe u v w

theorem _root_.Module.FaithfullyFlat.isBaseChange_eqLocus_of_descentDatum
    {A : Type u} [CommRing A] (B : Type v) [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B]
    {N : Type w} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    (φ : TensorProduct A N B ≃ₗ[A] TensorProduct A B N)
    (hφ₁ : ∀ (b : B) (x : TensorProduct A N B), φ (b • x) = b • φ x)
    (hφ₂ : ∀ (b : B) (x : TensorProduct A N B),
      φ ((LinearMap.mulLeft A b).lTensor N x) = (DistribSMul.toLinearMap A N b).lTensor B (φ x))
    (hcocycle :
      (φ : TensorProduct A N B →ₗ[A] TensorProduct A B N).lTensor B ∘ₗ
          (TensorProduct.assoc A B N B).toLinearMap ∘ₗ
          (φ : TensorProduct A N B →ₗ[A] TensorProduct A B N).rTensor B =
        (TensorProduct.comm A N B).toLinearMap.lTensor B ∘ₗ
          (TensorProduct.assoc A B N B).toLinearMap ∘ₗ
          (φ : TensorProduct A N B →ₗ[A] TensorProduct A B N).rTensor B ∘ₗ
          (TensorProduct.assoc A N B B).symm.toLinearMap ∘ₗ
          (TensorProduct.comm A B B).toLinearMap.lTensor N ∘ₗ
          (TensorProduct.assoc A N B B).toLinearMap) :
    IsBaseChange B (LinearMap.eqLocus
        ((φ : TensorProduct A N B →ₗ[A] TensorProduct A B N) ∘ₗ (TensorProduct.mk A N B).flip 1)
        (TensorProduct.mk A B N 1)).subtype ∧
      ∀ (b b' : B) (m : N), φ (m ⊗ₜ[A] 1) = 1 ⊗ₜ[A] m →
        φ ((b • m) ⊗ₜ[A] b') = b ⊗ₜ[A] (b' • m) :=
  ⟨Invariants.isBaseChange_Msub B φ hφ₁ hcocycle,
    fun b b' m hm => Invariants.φ_tmul_of_mem B φ hφ₁ hφ₂ b b' m hm⟩

end SchemeTheory.RingTheory.Descent.FaithfullyFlatModuleDatum
