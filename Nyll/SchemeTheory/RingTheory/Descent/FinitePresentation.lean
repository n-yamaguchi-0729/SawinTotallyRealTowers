/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT proof and public statement, pinned revision:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Algebra_FinitePresentation_of_faithfullyFlat_of_finitePresentation.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_FinitePresentation_of_faithfullyFlat_of_finitePresentation.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (including earlier FLT and Mathlib notices):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
See SchemeTheory/ANTHROPIC_FLT_SOURCE.md for copied notices and local changes.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Tactic.Choose
import Nyll.SchemeTheory.RingTheory.Descent.FaithfullyFlatOnOpenImage
import Nyll.SchemeTheory.RingTheory.Descent.FiniteType
import Nyll.SchemeTheory.RingTheory.Flat.FiniteSubalgebra

/-!
# Faithfully flat descent of finite presentation

Finite generation of the kernel of a polynomial presentation descends through faithfully
flat base change. Combined with finite-type descent, this proves descent of finite
presentation.
-/

universe u v w

open TensorProduct PrimeSpectrum

noncomputable section

namespace FaithfullyFlatFinitePresentation

open FaithfullyFlatFiniteType

section EndGame

variable {A' A B' : Type*} [CommRing A'] [CommRing A] [CommRing B'] [Algebra A' A] [Algebra A' B']

lemma ker_includeRight_le_map (h : Function.Surjective (algebraMap A' A)) :
    RingHom.ker (Algebra.TensorProduct.includeRight : B' →ₐ[A'] A ⊗[A'] B').toRingHom ≤
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' B') := by
  intro b hb
  rw [RingHom.mem_ker] at hb
  change (1 : A) ⊗ₜ[A'] b = 0 at hb
  let g : A' →ₗ[A'] A := Algebra.linearMap A' A
  have hex := rTensor_exact B' (LinearMap.exact_subtype_ker_map g) h
  have h1 : (LinearMap.rTensor B' g) ((1 : A') ⊗ₜ b) = 0 := by
    rw [LinearMap.rTensor_tmul, Algebra.linearMap_apply, map_one]
    exact hb
  obtain ⟨y, hy⟩ := (hex ((1 : A') ⊗ₜ b)).mp h1
  have hlid : b = TensorProduct.lid A' B' ((LinearMap.rTensor B' (LinearMap.ker g).subtype) y) := by
    rw [hy, TensorProduct.lid_tmul, one_smul]
  rw [hlid]
  clear hlid hy h1 hb
  induction y using TensorProduct.inductionOn with
  | tmul q b' =>
    rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, Submodule.subtype_apply, Algebra.smul_def]
    refine Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
    exact q.2
  | add x y hx hy => rw [map_add, map_add]; exact Ideal.add_mem _ hx hy

lemma exists_fg_le_of_le_map {S : Type*} [CommRing S] (φ : A' →+* S) (I : Ideal A') (N : Ideal S)
    (hN : N.FG) (h : N ≤ I.map φ) : ∃ I₀ : Ideal A', I₀ ≤ I ∧ I₀.FG ∧ N ≤ I₀.map φ := by
  classical
  obtain ⟨s, rfl⟩ := hN
  have key : ∀ x ∈ s, ∃ U : Finset A', (↑U : Set A') ⊆ I ∧
      x ∈ (Ideal.span (↑U : Set A')).map φ := by
    intro x hx
    have hx' : x ∈ Submodule.span S (φ '' (I : Set A')) := h (Ideal.subset_span hx)
    obtain ⟨T, hT, hxT⟩ := Submodule.mem_span_finite_of_mem_span hx'
    obtain ⟨U, hU, rfl⟩ := Finset.subset_set_image_iff.mp hT
    refine ⟨U, hU, ?_⟩
    rw [Ideal.map_span, ← Finset.coe_image]
    exact hxT
  choose U hUI hxU using key
  refine ⟨Ideal.span (↑(s.attach.biUnion fun x ↦ U x.1 x.2) : Set A'), ?_, ⟨_, rfl⟩, ?_⟩
  · refine Ideal.span_le.mpr fun a ha ↦ ?_
    simp only [Finset.coe_biUnion, Finset.mem_coe, Finset.mem_attach,
      Set.iUnion_true, Set.mem_iUnion] at ha
    obtain ⟨x, hx⟩ := ha
    exact hUI x.1 x.2 hx
  · refine Ideal.span_le.mpr fun x hx ↦ ?_
    refine Ideal.map_mono ?_ (hxU x hx)
    refine Ideal.span_mono fun a ha ↦ ?_
    simp only [Finset.coe_biUnion, Finset.mem_coe, Finset.mem_attach,
      Set.iUnion_true, Set.mem_iUnion]
    exact ⟨⟨x, hx⟩, ha⟩

variable (A B') in
/-- The tensor-product algebra map induced by factoring the scalar map through the quotient by J. -/
def θ (J : Ideal A') (hJ : J ≤ RingHom.ker (algebraMap A' A)) :
    (A' ⧸ J) ⊗[A'] B' →ₐ[A'] A ⊗[A'] B' :=
  Algebra.TensorProduct.map
    (Ideal.Quotient.liftₐ J (Algebra.ofId A' A) fun a ha ↦ hJ (x := a) ha) (AlgHom.id A' B')

lemma θ_tmul (J : Ideal A') (hJ : J ≤ RingHom.ker (algebraMap A' A)) (a : A') (b : B') :
    θ A B' J hJ (Ideal.Quotient.mk J a ⊗ₜ b) = algebraMap A' A a ⊗ₜ b := by
  rw [θ, Algebra.TensorProduct.map_tmul]
  rfl

lemma θ_includeRight (J : Ideal A') (hJ : J ≤ RingHom.ker (algebraMap A' A)) (b : B') :
    θ A B' J hJ (Algebra.TensorProduct.includeRight b) = (1 : A) ⊗ₜ b := by
  rw [Algebra.TensorProduct.includeRight_apply, ← map_one (Ideal.Quotient.mk J), θ_tmul, map_one]

lemma θ_injective (J : Ideal A')
    (hJ : J ≤ RingHom.ker (algebraMap A' A))
    (hker : RingHom.ker (Algebra.TensorProduct.includeRight : B' →ₐ[A'] A ⊗[A'] B').toRingHom ≤
      J.map (algebraMap A' B')) :
    Function.Injective (θ A B' J hJ) := by
  rw [RingHom.injective_iff_ker_eq_bot, eq_bot_iff]
  intro x hx
  obtain ⟨b, rfl⟩ := Algebra.TensorProduct.includeRight_surjective
    (S := A' ⧸ J) B' Ideal.Quotient.mk_surjective x
  rw [RingHom.mem_ker] at hx
  change θ A B' J hJ (Algebra.TensorProduct.includeRight b) = 0 at hx
  rw [θ_includeRight] at hx
  have hb : b ∈ J.map (algebraMap A' B') := hker (by
    rw [RingHom.mem_ker]; exact hx)
  have : J.map (algebraMap A' B') ≤
      RingHom.ker (Algebra.TensorProduct.includeRight : B' →ₐ[A'] (A' ⧸ J) ⊗[A'] B').toRingHom := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change (1 : A' ⧸ J) ⊗ₜ[A'] (algebraMap A' B' a) = 0
    rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one,
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.mpr ha, TensorProduct.zero_tmul]
  exact this hb

lemma θ_smul_eq_zero (J : Ideal A') (hJ : J ≤ RingHom.ker (algebraMap A' A)) (a : A')
    (ha : algebraMap A' A a = 0) (x : (A' ⧸ J) ⊗[A'] B') :
    θ A B' J hJ (Ideal.Quotient.mk J a • x) = 0 := by
  induction x using TensorProduct.inductionOn with
  | tmul c b =>
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [TensorProduct.smul_tmul', smul_eq_mul, ← map_mul, θ_tmul, map_mul, ha, zero_mul,
      TensorProduct.zero_tmul]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, add_zero]

theorem ker_fg_of_faithfullyFlat_baseChange (h : Function.Surjective (algebraMap A' A))
    [Module.Flat A' B'] [Algebra.FinitePresentation A' B']
    [Module.FaithfullyFlat A (A ⊗[A'] B')] [Algebra.FinitePresentation A' (A ⊗[A'] B')] :
    (RingHom.ker (algebraMap A' A)).FG := by
  classical
  set Q := RingHom.ker (algebraMap A' A) with hQdef
  have hkfg : (RingHom.ker
      (Algebra.TensorProduct.includeRight : B' →ₐ[A'] A ⊗[A'] B').toRingHom).FG :=
    Algebra.FinitePresentation.ker_fG_of_surjective
      _ (Algebra.TensorProduct.includeRight_surjective B' h)
  obtain ⟨J₁, hJ₁Q, hJ₁fg, hkerJ₁⟩ :=
    exists_fg_le_of_le_map (algebraMap A' B') Q _ hkfg (ker_includeRight_le_map h)
  obtain ⟨𝔞, h𝔞⟩ :=
    PrimeSpectrum.exists_ideal_range_comap_of_flat_of_finitePresentation (A₀ := A') (B₀ := B')
  have hland : ∀ 𝔭 : PrimeSpectrum A, comap (algebraMap A' A) 𝔭 ∈
      Set.range (comap (algebraMap A' B')) := by
    intro 𝔭
    obtain ⟨𝔔, h𝔔⟩ := comap_surjective_of_faithfullyFlat (A := A) (B := A ⊗[A'] B') 𝔭
    refine ⟨comap (Algebra.TensorProduct.includeRight : B' →ₐ[A'] A ⊗[A'] B').toRingHom 𝔔, ?_⟩
    apply PrimeSpectrum.ext
    rw [← h𝔔]
    simp only [comap_asIdeal, Ideal.comap_comap]
    congr 1
    ext b
    change (1 : A) ⊗ₜ[A'] (algebraMap A' B' b) = algebraMap A' A b ⊗ₜ[A'] (1 : B')
    rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul,
      Algebra.smul_def, mul_one]
  have h𝔞A : 𝔞.map (algebraMap A' A) = ⊤ := by
    by_contra hne
    obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ hne
    have hmem := hland ⟨𝔪, h𝔪.isPrime⟩
    rw [h𝔞] at hmem
    exact hmem (Ideal.map_le_iff_le_comap.mp hle)
  obtain ⟨a₀, ha₀𝔞, ha₀⟩ : ∃ a₀ ∈ 𝔞, algebraMap A' A a₀ = 1 :=
    (Ideal.mem_map_iff_of_surjective _ h).mp (h𝔞A ▸ Submodule.mem_top)
  set y := a₀ - 1 with hydef
  have hyQ : y ∈ Q := by rw [hQdef, RingHom.mem_ker, hydef, map_sub, ha₀, map_one, sub_self]
  set J : Ideal A' := J₁ ⊔ Ideal.span {y}
  have hJQ : J ≤ Q := sup_le hJ₁Q ((Ideal.span_singleton_le_iff_mem _).mpr hyQ)
  have hJfg : J.FG := Submodule.FG.sup hJ₁fg (Submodule.fg_span_singleton y)
  have : Module.FaithfullyFlat (A' ⧸ J) ((A' ⧸ J) ⊗[A'] B') := by
    refine Module.Flat.faithfullyFlat_baseChange_of_map_eq_top
      𝔞 (fun p hp ↦ (h𝔞 p).mpr hp) (A' ⧸ J) ?_
    rw [Ideal.eq_top_iff_one]
    have : Ideal.Quotient.mk J a₀ = 1 := by
      rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk J), ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
      exact le_sup_right (b := Ideal.span {y}) (Ideal.mem_span_singleton_self _)
    rw [← this]
    exact Ideal.mem_map_of_mem _ ha₀𝔞
  have hθ : Function.Injective (θ A B' J hJQ) :=
    θ_injective J hJQ (hkerJ₁.trans (Ideal.map_mono le_sup_left))
  let πJ : (A' ⧸ J) →ₐ[A'] A := Ideal.Quotient.liftₐ J (Algebra.ofId A' A) fun a ha ↦ hJQ ha
  let QJ : Ideal (A' ⧸ J) := RingHom.ker πJ.toRingHom
  have hQJ : Subsingleton (QJ ⊗[A' ⧸ J] ((A' ⧸ J) ⊗[A'] B')) := by
    refine ⟨fun z₁ z₂ ↦ ?_⟩
    have hinj : Function.Injective
        (LinearMap.rTensor ((A' ⧸ J) ⊗[A'] B') (Submodule.subtype QJ)) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective
    have hzero : ∀ z : QJ ⊗[A' ⧸ J] ((A' ⧸ J) ⊗[A'] B'),
        (TensorProduct.lid _ _ (LinearMap.rTensor _ (Submodule.subtype QJ) z)) = 0 := by
      intro z
      apply hθ
      rw [map_zero (θ A B' J hJQ)]
      induction z using TensorProduct.inductionOn with
      | tmul q x =>
        obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (q : A' ⧸ J)
        have ha0 : algebraMap A' A a = 0 := by
          have := q.2
          rw [RingHom.mem_ker] at this
          rw [← ha] at this
          exact this
        rw [LinearMap.rTensor_tmul, Submodule.subtype_apply, TensorProduct.lid_tmul, ← ha]
        exact θ_smul_eq_zero J hJQ a ha0 x
      | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, add_zero]
    apply hinj
    apply (TensorProduct.lid _ _).injective
    rw [hzero, hzero]
  have := hQJ
  have hQJ0 : Subsingleton QJ :=
    Module.FaithfullyFlat.rTensor_reflects_triviality (A' ⧸ J) ((A' ⧸ J) ⊗[A'] B') QJ
  have hQJ : Q ≤ J := by
    intro q hq
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have hmem : Ideal.Quotient.mk J q ∈ QJ := by
      rw [RingHom.mem_ker]
      rw [hQdef, RingHom.mem_ker] at hq
      exact hq
    have := hQJ0.elim ⟨_, hmem⟩ ⟨0, QJ.zero_mem⟩
    exact congrArg Subtype.val this
  rw [le_antisymm hQJ hJQ] at *
  exact hJfg

end EndGame

section Assembly

theorem ker_fg_of_descent (P : Type*) (A : Type*) (B : Type*) [CommRing P] [CommRing A] [CommRing B]
    [Algebra P A] [Algebra A B] [Algebra P B] [IsScalarTower P A B]
    (hπ : Function.Surjective (algebraMap P A))
    [Module.FaithfullyFlat A B] [Algebra.FinitePresentation P B]
    (A₁ : Type*) [CommRing A₁] [Algebra A₁ A] (B₁ : Type*) [CommRing B₁] [Algebra A₁ B₁]
    [Module.Flat A₁ B₁] [Algebra.FinitePresentation A₁ B₁]
    (e : A ⊗[A₁] B₁ ≃ₐ[A] B)
    (R₁ : Type*) [CommRing R₁] [Algebra R₁ P] [Algebra R₁ A₁] [IsNoetherianRing R₁]
    (hρ : Function.Surjective (algebraMap R₁ A₁))
    (hcompat : ∀ r : R₁, algebraMap A₁ A (algebraMap R₁ A₁ r) =
      algebraMap P A (algebraMap R₁ P r)) :
    (RingHom.ker (algebraMap P A)).FG := by
  classical
  have hK₁ : (RingHom.ker (algebraMap R₁ A₁)).FG := IsNoetherian.noetherian _
  let I₁ : Ideal P := (RingHom.ker (algebraMap R₁ A₁)).map (algebraMap R₁ P)
  have hI₁fg : I₁.FG := hK₁.map _
  have hI₁ : I₁ ≤ RingHom.ker (algebraMap P A) := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [RingHom.mem_ker] at hr
    rw [Ideal.mem_comap, RingHom.mem_ker, ← hcompat, hr, map_zero]
  let A' := P ⧸ I₁
  have hkerσ : RingHom.ker (algebraMap R₁ A₁) ≤
      RingHom.ker ((Ideal.Quotient.mk I₁).comp (algebraMap R₁ P)) := by
    intro r hr
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ hr
  let σ : A₁ →+* A' := ((algebraMap R₁ A₁).liftOfSurjective hρ) ⟨_, hkerσ⟩
  have hσ : ∀ r : R₁, σ (algebraMap R₁ A₁ r) = Ideal.Quotient.mk I₁ (algebraMap R₁ P r) := fun r ↦
    RingHom.liftOfSurjective_comp_apply (algebraMap R₁ A₁) hρ ⟨_, hkerσ⟩ r
  let algA₁A' : Algebra A₁ A' := σ.toAlgebra
  let τ : A' →ₐ[P] A := Ideal.Quotient.liftₐ I₁ (Algebra.ofId P A) fun a ha ↦ hI₁ ha
  let algA'A : Algebra A' A := τ.toRingHom.toAlgebra
  have : IsScalarTower P A' A := IsScalarTower.of_algebraMap_eq fun p ↦ (τ.commutes p).symm
  have hτ : Function.Surjective (algebraMap A' A) := fun a ↦ by
    obtain ⟨p, rfl⟩ := hπ a
    exact ⟨Ideal.Quotient.mk I₁ p, τ.commutes p⟩
  have : IsScalarTower A₁ A' A := IsScalarTower.of_algebraMap_eq fun x ↦ by
    obtain ⟨r, rfl⟩ := hρ x
    change algebraMap A₁ A (algebraMap R₁ A₁ r) = τ (σ (algebraMap R₁ A₁ r))
    rw [hσ, hcompat]
    exact (τ.commutes (algebraMap R₁ P r)).symm
  let algA'B : Algebra A' B := ((algebraMap A B).comp (algebraMap A' A)).toAlgebra
  have : IsScalarTower A' A B := IsScalarTower.of_algebraMap_eq fun r ↦
    show algebraMap A' B r = algebraMap A B (algebraMap A' A r) from rfl
  have : IsScalarTower P A' B := IsScalarTower.of_algebraMap_eq fun p ↦ by
    change algebraMap P B p = algebraMap A B (algebraMap A' A (algebraMap P A' p))
    rw [← IsScalarTower.algebraMap_apply P A' A, ← IsScalarTower.algebraMap_apply P A B]
  have : Algebra.FinitePresentation A' B :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation P A' B
  let Ξ : A ⊗[A'] (A' ⊗[A₁] B₁) ≃ₐ[A] B :=
    (Algebra.TensorProduct.cancelBaseChange A₁ A' A A B₁).trans e
  have : Module.FaithfullyFlat A (A ⊗[A'] (A' ⊗[A₁] B₁)) :=
    Module.FaithfullyFlat.of_linearEquiv (R := A) (M := B) Ξ.toLinearEquiv
  let Ξ' : B ≃ₐ[A'] A ⊗[A'] (A' ⊗[A₁] B₁) := (Ξ.restrictScalars A').symm
  have : Algebra.FinitePresentation A' (A ⊗[A'] (A' ⊗[A₁] B₁)) :=
    Algebra.FinitePresentation.equiv (R := A') (A := B) (B := A ⊗[A'] (A' ⊗[A₁] B₁)) Ξ'
  have hQ : (RingHom.ker (algebraMap A' A)).FG :=
    ker_fg_of_faithfullyFlat_baseChange (A' := A') (A := A) (B' := A' ⊗[A₁] B₁) hτ
  have hker : RingHom.ker (algebraMap P A) =
      (RingHom.ker (algebraMap A' A)).comap (Ideal.Quotient.mk I₁) := by
    rw [RingHom.comap_ker, IsScalarTower.algebraMap_eq P A' A]; rfl
  rw [hker]
  refine Ideal.fg_of_fg_map_of_fg_inf_ker_of_surjective
    (f := Ideal.Quotient.mk I₁) ?_ ?_ Ideal.Quotient.mk_surjective
  · rwa [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
  · rw [inf_eq_right.mpr (Ideal.ker_le_comap _)]
    rwa [Ideal.mk_ker]

theorem ker_fg_of_model (P : Type*) (A : Type*) (B : Type*) [CommRing P] [CommRing A] [CommRing B]
    [Algebra P A] [Algebra A B] [Algebra P B] [IsScalarTower P A B]
    (hπ : Function.Surjective (algebraMap P A))
    [Module.FaithfullyFlat A B] [Algebra.FinitePresentation P B]
    (R₀ : Type*) [CommRing R₀] [Algebra R₀ P] [Algebra R₀ A]
    [IsScalarTower R₀ P A] [IsNoetherianRing R₀]
    (Bq : Type*) [CommRing Bq] [Algebra R₀ Bq] [Algebra.FinitePresentation R₀ Bq]
    (Φ : A ⊗[R₀] Bq ≃ₐ[A] B) :
    (RingHom.ker (algebraMap P A)).FG := by
  classical
  have : Module.Flat A (A ⊗[R₀] Bq) := Module.Flat.of_linearEquiv Φ.toLinearEquiv
  obtain ⟨A₁, hA₁fg, -, hA₁flat⟩ :=
    Module.Flat.exists_fg_subalgebra_flat_tensorProduct (R₀ := R₀) (R := A) (B₀ := Bq) ∅
  have := hA₁flat
  obtain ⟨s₁, hs₁⟩ := hA₁fg
  have hπ2 : ∀ a : A, ∃ p : P, algebraMap P A p = a := hπ
  choose ℓ hℓ using hπ2
  let R₁ : Subalgebra R₀ P := Algebra.adjoin R₀ (↑(s₁.image ℓ) : Set P)
  let πR₀ : P →ₐ[R₀] A := IsScalarTower.toAlgHom R₀ P A
  have hrange : (πR₀.comp R₁.val).range = A₁ := by
    rw [AlgHom.range_comp, Subalgebra.range_val, AlgHom.map_adjoin,
      ← hs₁, Finset.coe_image, ← Set.image_comp]
    congr 1
    have hright : πR₀ ∘ ℓ = id := funext hℓ
    rw [hright, Set.image_id]
  let ρ : R₁ →ₐ[R₀] A₁ := (πR₀.comp R₁.val).codRestrict A₁ fun r ↦ hrange.le ⟨r, rfl⟩
  have hρ : Function.Surjective ρ := by
    rintro ⟨a, ha⟩
    obtain ⟨r, hr⟩ := hrange.ge ha
    exact ⟨r, Subtype.ext hr⟩
  let algR₁A₁ : Algebra R₁ A₁ := ρ.toRingHom.toAlgebra
  have : Algebra.FiniteType R₀ R₁ := ⟨(Subalgebra.fg_top R₁).mpr (Subalgebra.fg_adjoin_finset _)⟩
  have : IsNoetherianRing R₁ := Algebra.FiniteType.isNoetherianRing R₀ R₁
  exact ker_fg_of_descent P A B hπ A₁ (A₁ ⊗[R₀] Bq)
    ((Algebra.TensorProduct.cancelBaseChange R₀ A₁ A A Bq).trans Φ) R₁ hρ fun r ↦
      show algebraMap A₁ A (algebraMap R₁ A₁ r) = algebraMap P A (algebraMap R₁ P r) from rfl

theorem ker_fg_of_lifts (P : Type*) (A : Type*) (B : Type*) [CommRing P] [CommRing A] [CommRing B]
    [Algebra P A] [Algebra A B] [Algebra P B] [IsScalarTower P A B]
    (hπ : Function.Surjective (algebraMap P A))
    [Module.FaithfullyFlat A B] [Algebra.FinitePresentation P B]
    (R₀ : Type*) [CommRing R₀] [Algebra R₀ P] [Algebra R₀ A]
    [IsScalarTower R₀ P A] [IsNoetherianRing R₀]
    {k : ℕ} (ψ : MvPolynomial (Fin k) A →ₐ[A] B) (hψ : Function.Surjective ψ)
    (tk : Finset (MvPolynomial (Fin k) A))
    (htk : Ideal.span (↑tk : Set (MvPolynomial (Fin k) A)) = RingHom.ker ψ)
    (g₀ : tk → MvPolynomial (Fin k) R₀) (hg₀ : ∀ g, MvPolynomial.map (algebraMap R₀ A) (g₀ g) = g) :
    (RingHom.ker (algebraMap P A)).FG := by
  classical
  let J₀ : Ideal (MvPolynomial (Fin k) R₀) := Ideal.span (Set.range g₀)
  have hJ : J₀.map (MvPolynomial.map (algebraMap R₀ A)) = RingHom.ker ψ := by
    rw [← htk]; exact map_span_range_lift tk g₀ hg₀
  have : Algebra.FinitePresentation R₀ (MvPolynomial (Fin k) R₀ ⧸ J₀) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span (Set.finite_range g₀))
  exact ker_fg_of_model P A B hπ R₀ (MvPolynomial (Fin k) R₀ ⧸ J₀) (modelEquiv J₀ ψ hψ hJ)

theorem ker_fg_of_surjective (P : Type*) (A : Type*) (B : Type*)
    [CommRing P] [CommRing A] [CommRing B]
    [Algebra P A] [Algebra A B] [Algebra P B] [IsScalarTower P A B]
    (hπ : Function.Surjective (algebraMap P A))
    [Module.FaithfullyFlat A B] [Algebra.FinitePresentation A B] [Algebra.FinitePresentation P B] :
    (RingHom.ker (algebraMap P A)).FG := by
  classical
  obtain ⟨k, ψ, hψ, hkerψ⟩ := (‹Algebra.FinitePresentation A B›).out
  obtain ⟨tk, htk⟩ := hkerψ
  have htk' : Ideal.span (↑tk : Set (MvPolynomial (Fin k) A)) = RingHom.ker ψ := htk
  choose gl hgl using fun g : tk ↦
    MvPolynomial.map_surjective (algebraMap P A) hπ (g : MvPolynomial (Fin k) A)
  let c : Finset P := Finset.univ.biUnion fun g : tk => (gl g).coeffs
  let R₀ : Subalgebra ℤ P := Algebra.adjoin ℤ (↑c : Set P)
  have : Algebra.FiniteType ℤ R₀ := ⟨(Subalgebra.fg_top R₀).mpr (Subalgebra.fg_adjoin_finset c)⟩
  have : IsNoetherianRing R₀ := Algebra.FiniteType.isNoetherianRing ℤ R₀
  have hcoef : ∀ g : tk, ((gl g).coeffs : Set P) ⊆ Set.range (algebraMap R₀ P) := by
    intro g a ha
    refine ⟨⟨a, Algebra.subset_adjoin ?_⟩, rfl⟩
    simp only [c, Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true,
      Set.mem_iUnion, Finset.mem_coe]
    exact ⟨g, ha⟩
  choose g₀ hg₀ using fun g : tk =>
    (MvPolynomial.mem_range_map_iff_coeffs_subset).mpr (hcoef g)
  have hg₀A : ∀ g : tk, MvPolynomial.map (algebraMap R₀ A) (g₀ g) = g := fun g ↦ by
    rw [IsScalarTower.algebraMap_eq R₀ P A, ← MvPolynomial.map_map, hg₀, hgl]
  exact ker_fg_of_lifts P A B hπ R₀ ψ hψ tk htk' g₀ hg₀A

theorem main (R : Type u) (A : Type v) (B : Type w) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Module.FaithfullyFlat A B] [Algebra.FinitePresentation A B] [Algebra.FinitePresentation R B] :
    Algebra.FinitePresentation R A := by
  classical
  have hft : Algebra.FiniteType R A :=
    Algebra.FiniteType.of_faithfullyFlat_of_finitePresentation R A B
  obtain ⟨n, π, hπ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 hft
  let algPA : Algebra (MvPolynomial (Fin n) R) A := π.toRingHom.toAlgebra
  have : IsScalarTower R (MvPolynomial (Fin n) R) A :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (π.commutes r).symm
  let algPB : Algebra (MvPolynomial (Fin n) R) B := ((algebraMap A B).comp π.toRingHom).toAlgebra
  have : IsScalarTower (MvPolynomial (Fin n) R) A B := IsScalarTower.of_algebraMap_eq fun p ↦
    show algebraMap (MvPolynomial (Fin n) R) B p =
      algebraMap A B (algebraMap (MvPolynomial (Fin n) R) A p) from rfl
  have : IsScalarTower R (MvPolynomial (Fin n) R) B := IsScalarTower.of_algebraMap_eq fun r ↦ by
    change algebraMap R B r = algebraMap A B (π (algebraMap R (MvPolynomial (Fin n) R) r))
    rw [π.commutes, ← IsScalarTower.algebraMap_apply]
  have : Algebra.FinitePresentation (MvPolynomial (Fin n) R) B :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R (MvPolynomial (Fin n) R) B
  have hπ' : Function.Surjective (Algebra.ofId (MvPolynomial (Fin n) R) A) := hπ
  have hI : (RingHom.ker (Algebra.ofId (MvPolynomial (Fin n) R) A)).FG :=
    ker_fg_of_surjective (MvPolynomial (Fin n) R) A B hπ
  have : Algebra.FinitePresentation (MvPolynomial (Fin n) R)
      (MvPolynomial (Fin n) R ⧸ RingHom.ker (Algebra.ofId (MvPolynomial (Fin n) R) A)) :=
    Algebra.FinitePresentation.quotient hI
  have : Algebra.FinitePresentation (MvPolynomial (Fin n) R) A :=
    Algebra.FinitePresentation.equiv (Ideal.quotientKerAlgEquivOfSurjective hπ')
  exact Algebra.FinitePresentation.trans (R := R) (A := MvPolynomial (Fin n) R) (B := A)

end Assembly

end FaithfullyFlatFinitePresentation

end

theorem Algebra.FinitePresentation.of_faithfullyFlat_of_finitePresentation
    (R : Type u) (A : Type v) (B : Type w) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Module.FaithfullyFlat A B] [Algebra.FinitePresentation A B] [Algebra.FinitePresentation R B] :
    Algebra.FinitePresentation R A :=
  FaithfullyFlatFinitePresentation.main R A B
