/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted from the proof and theorem statement at pinned revision
aa2d8b34692b16c70f699536de0d8e75b9a3e9ef:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Algebra_bijective_tensorProduct_equalizer_of_faithfullyFlat_of_descentDatum.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_bijective_tensorProduct_equalizer_of_faithfullyFlat_of_descentDatum.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (including earlier FLT and Mathlib notices):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
See SchemeTheory/ANTHROPIC_FLT_SOURCE.md for copied notices and exact local changes.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Tactic.Ext
import Nyll.SchemeTheory.RingTheory.Descent.FaithfullyFlatModuleDatum

/-!
# Effective faithfully flat descent for an algebra datum

The equalizer subalgebra of a compatible algebra descent datum recovers the upstairs
algebra after base change. The proof obtains its underlying module isomorphism from
`Module.FaithfullyFlat.isBaseChange_eqLocus_of_descentDatum`.
-/

universe u

open TensorProduct Algebra.TensorProduct

theorem Algebra.bijective_tensorProduct_equalizer_of_faithfullyFlat_of_descentDatum
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S']
    [Module.FaithfullyFlat S S']
    (A' : Type u) [CommRing A'] [Algebra S A'] [Algebra S' A'] [IsScalarTower S S' A']
    (φ : A' ⊗[S] S' ≃ₐ[S] S' ⊗[S] A')
    (hφlin : φ.toAlgHom.comp
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S S' A') (AlgHom.id S S')) =
      Algebra.TensorProduct.map (AlgHom.id S S') (IsScalarTower.toAlgHom S S' A'))
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
      (fun s a => Commute.all (algebraMap S' A' s) (A.val a))) := by
  intro A
  classical
  set φL : A' ⊗[S] S' ≃ₗ[S] S' ⊗[S] A' := φ.toLinearEquiv
  have φL_apply : ∀ x, φL x = φ x := fun _ => rfl
  have hlin : ∀ (s t : S'), φ (algebraMap S' A' s ⊗ₜ[S] t) = s ⊗ₜ[S] algebraMap S' A' t := by
    intro s t
    exact AlgHom.congr_fun hφlin (s ⊗ₜ[S] t)
  have hleft : ∀ (s : S') (y : S' ⊗[S] A'), (s ⊗ₜ[S] (1 : A')) * y = s • y := by
    intro s y
    induction y using _root_.TensorProduct.inductionOn with
    | tmul t a =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, _root_.TensorProduct.smul_tmul',
        smul_eq_mul]
    | add y z hy hz => rw [mul_add, hy, hz, smul_add]
  have hright : ∀ (b : S') (y : S' ⊗[S] A'),
      ((1 : S') ⊗ₜ[S] algebraMap S' A' b) * y = (DistribSMul.toLinearMap S A' b).lTensor S' y := by
    intro b y
    induction y using _root_.TensorProduct.inductionOn with
    | tmul t a =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, LinearMap.lTensor_tmul];
        rw [DistribSMul.toLinearMap_apply, Algebra.smul_def]
    | add y z hy hz => rw [mul_add, hy, hz, map_add]
  have hφ₁ : ∀ (b : S') (x : A' ⊗[S] S'), φL (b • x) = b • φL x := by
    intro b x
    induction x using _root_.TensorProduct.inductionOn with
    | tmul a t =>
      rw [φL_apply, φL_apply, _root_.TensorProduct.smul_tmul', Algebra.smul_def,
        show (algebraMap S' A' b * a) ⊗ₜ[S] t = (algebraMap S' A' b ⊗ₜ[S] (1 : S')) * (a ⊗ₜ[S] t) by
          rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul],
        map_mul, hlin, map_one, hleft]
    | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]
  have hφ₂ : ∀ (b : S') (x : A' ⊗[S] S'),
      φL ((LinearMap.mulLeft S b).lTensor A' x) =
        (DistribSMul.toLinearMap S A' b).lTensor S' (φL x) := by
    intro b x
    induction x using _root_.TensorProduct.inductionOn with
    | tmul a t =>
      rw [LinearMap.lTensor_tmul, LinearMap.mulLeft_apply, φL_apply, φL_apply,
        show a ⊗ₜ[S] (b * t) = ((1 : A') ⊗ₜ[S] b) * (a ⊗ₜ[S] t) by
          rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul],
        map_mul, show (1 : A') = algebraMap S' A' 1 from (map_one _).symm, hlin, ← hright]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  have agree_mapL : ∀ w : S' ⊗[S] (A' ⊗[S] S'),
      Algebra.TensorProduct.map (AlgHom.id S S') φ.toAlgHom w =
        (φL : A' ⊗[S] S' →ₗ[S] S' ⊗[S] A').lTensor S' w := by
    intro w
    induction w using _root_.TensorProduct.inductionOn with
    | tmul s v => rw [Algebra.TensorProduct.map_tmul, LinearMap.lTensor_tmul]; rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have agree_mapR : ∀ w : (A' ⊗[S] S') ⊗[S] S',
      Algebra.TensorProduct.map φ.toAlgHom (AlgHom.id S S') w =
        (φL : A' ⊗[S] S' →ₗ[S] S' ⊗[S] A').rTensor S' w := by
    intro w
    induction w using _root_.TensorProduct.inductionOn with
    | tmul v s => rw [Algebra.TensorProduct.map_tmul, LinearMap.rTensor_tmul]; rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have agree_commL : ∀ w : S' ⊗[S] (A' ⊗[S] S'),
      Algebra.TensorProduct.map (AlgHom.id S S') (Algebra.TensorProduct.comm S A' S').toAlgHom w =
        (_root_.TensorProduct.comm S A' S').toLinearMap.lTensor S' w := by
    intro w
    induction w using _root_.TensorProduct.inductionOn with
    | tmul s v => rw [Algebra.TensorProduct.map_tmul, LinearMap.lTensor_tmul]; congr 1
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have agree_commN : ∀ w : A' ⊗[S] (S' ⊗[S] S'),
      Algebra.TensorProduct.map (AlgHom.id S A') (Algebra.TensorProduct.comm S S' S').toAlgHom w =
        (_root_.TensorProduct.comm S S' S').toLinearMap.lTensor A' w := by
    intro w
    induction w using _root_.TensorProduct.inductionOn with
    | tmul a v => rw [Algebra.TensorProduct.map_tmul, LinearMap.lTensor_tmul]; congr 1
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have agree_assoc1 : ∀ w : (S' ⊗[S] A') ⊗[S] S',
      (Algebra.TensorProduct.assoc S S S S' A' S') w =
        (_root_.TensorProduct.assoc S S' A' S') w := by
    intro w
    induction w using _root_.TensorProduct.inductionOn with
    | tmul v s =>
      induction v using _root_.TensorProduct.inductionOn with
      | tmul t a => rfl
      | add x y hx hy => rw [_root_.TensorProduct.add_tmul, map_add, map_add, hx, hy]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have agree_assoc2 : ∀ w : (A' ⊗[S] S') ⊗[S] S',
      (Algebra.TensorProduct.assoc S S S A' S' S') w =
        (_root_.TensorProduct.assoc S A' S' S') w := by
    intro w
    induction w using _root_.TensorProduct.inductionOn with
    | tmul v s =>
      induction v using _root_.TensorProduct.inductionOn with
      | tmul a t => rfl
      | add x y hx hy => rw [_root_.TensorProduct.add_tmul, map_add, map_add, hx, hy]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have agree_assoc2s : ∀ w : A' ⊗[S] (S' ⊗[S] S'),
      (Algebra.TensorProduct.assoc S S S A' S' S').symm w =
        (_root_.TensorProduct.assoc S A' S' S').symm w := by
    intro w
    apply (Algebra.TensorProduct.assoc S S S A' S' S').injective
    rw [AlgEquiv.apply_symm_apply, agree_assoc2, LinearEquiv.apply_symm_apply]
  have hcoc :
      (φL : A' ⊗[S] S' →ₗ[S] S' ⊗[S] A').lTensor S' ∘ₗ
          (_root_.TensorProduct.assoc S S' A' S').toLinearMap ∘ₗ
          (φL : A' ⊗[S] S' →ₗ[S] S' ⊗[S] A').rTensor S' =
        (_root_.TensorProduct.comm S A' S').toLinearMap.lTensor S' ∘ₗ
          (_root_.TensorProduct.assoc S S' A' S').toLinearMap ∘ₗ
          (φL : A' ⊗[S] S' →ₗ[S] S' ⊗[S] A').rTensor S' ∘ₗ
          (_root_.TensorProduct.assoc S A' S' S').symm.toLinearMap ∘ₗ
          (_root_.TensorProduct.comm S S' S').toLinearMap.lTensor A' ∘ₗ
          (_root_.TensorProduct.assoc S A' S' S').toLinearMap := by
    apply LinearMap.ext
    intro w
    have key := AlgHom.congr_fun hφcoc w
    simp only [AlgHom.coe_comp, Function.comp_apply] at key
    change
      (φL : A' ⊗[S] S' →ₗ[S] S' ⊗[S] A').lTensor S'
          ((_root_.TensorProduct.assoc S S' A' S')
            ((φL : A' ⊗[S] S' →ₗ[S] S' ⊗[S] A').rTensor S' w)) =
        (_root_.TensorProduct.comm S A' S').toLinearMap.lTensor S'
          ((_root_.TensorProduct.assoc S S' A' S')
            ((φL : A' ⊗[S] S' →ₗ[S] S' ⊗[S] A').rTensor S'
              ((_root_.TensorProduct.assoc S A' S' S').symm
                ((_root_.TensorProduct.comm S S' S').toLinearMap.lTensor A'
                  ((_root_.TensorProduct.assoc S A' S' S') w)))))
    rw [← agree_mapR, ← agree_assoc1, ← agree_mapL, ← agree_assoc2, ← agree_commN,
      ← agree_assoc2s, ← agree_mapR,
      ← agree_assoc1, ← agree_commL]
    exact key
  obtain ⟨hbc, -⟩ := Module.FaithfullyFlat.isBaseChange_eqLocus_of_descentDatum S' φL hφ₁ hφ₂ hcoc
  have hEq : LinearMap.eqLocus
      ((φL : A' ⊗[S] S' →ₗ[S] S' ⊗[S] A') ∘ₗ (_root_.TensorProduct.mk S A' S').flip 1)
      (_root_.TensorProduct.mk S S' A' 1) = A.toSubmodule := by
    ext a
    simp only [LinearMap.mem_eqLocus, LinearMap.coe_comp, Function.comp_apply, LinearMap.flip_apply,
      _root_.TensorProduct.mk_apply, Subalgebra.mem_toSubmodule]
    change φ (a ⊗ₜ[S] 1) = (1 : S') ⊗ₜ[S] a ↔ a ∈ A
    rw [AlgHom.mem_equalizer]
    rfl
  rw [hEq] at hbc
  let f : S' ⊗[S] ↥A →ₐ[S] A' :=
    Algebra.TensorProduct.lift (IsScalarTower.toAlgHom S S' A') A.val
      (fun s a => Commute.all (algebraMap S' A' s) (A.val a))
  have hfun : ∀ x : S' ⊗[S] ↥A, f x = hbc.equiv x := by
    intro x
    induction x using _root_.TensorProduct.inductionOn with
    | tmul s a =>
      calc
        f (s ⊗ₜ[S] a) = algebraMap S' A' s * (a : A') :=
          Algebra.TensorProduct.lift_tmul (IsScalarTower.toAlgHom S S' A') A.val
            (fun t b => Commute.all (algebraMap S' A' t) (A.val b)) s a
        _ = s • (a : A') := (Algebra.smul_def s (a : A')).symm
        _ = hbc.equiv (s ⊗ₜ[S] a) := (hbc.equiv_tmul s a).symm
    | add x y hx hy =>
      exact (map_add f x y).trans
        ((congrArg₂ (fun a b : A' => a + b) hx hy).trans (map_add hbc.equiv x y).symm)
  have hf : (f : S' ⊗[S] ↥A → A') = hbc.equiv := funext hfun
  change Function.Bijective (f : S' ⊗[S] ↥A → A')
  exact hf.symm ▸ hbc.equiv.bijective
