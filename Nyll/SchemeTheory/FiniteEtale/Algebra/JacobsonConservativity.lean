/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.JacobsonIntegral
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Finite étale isomorphisms detected modulo a Jacobson ideal

Reduction modulo an ideal in the Jacobson radical reflects isomorphisms of
finite étale algebras. Nakayama first gives surjectivity. The kernel is then a
finitely generated idempotent ideal in the Jacobson radical, so it vanishes.
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Algebra.FiniteEtale

/-- A map of finite étale algebras that becomes bijective after reduction by a
Jacobson ideal was already bijective. -/
theorem bijective_of_baseChange_quotient
    {R : Type u} {A : Type v} {B : Type w}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [Module.Finite R A] [Algebra.Etale R A]
    [Module.Finite R B] [Algebra.Etale R B]
    (I : Ideal R) (hI : I ≤ Ideal.jacobson ⊥) (f : A →ₐ[R] B)
    (hf : Function.Bijective
      (Algebra.TensorProduct.map (.id (R ⧸ I) (R ⧸ I)) f)) :
    Function.Bijective f := by
  let JA : Ideal A := I.map (algebraMap R A)
  let JB : Ideal B := I.map (algebraMap R B)
  let eA := Algebra.TensorProduct.quotIdealMapEquivQuotTensor A I
  let eB := Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I
  have hquot (b : B) : ∃ a : A, Ideal.Quotient.mk JB (f a) = Ideal.Quotient.mk JB b := by
    obtain ⟨t, ht⟩ := hf.surjective ((1 : R ⧸ I) ⊗ₜ[R] b)
    obtain ⟨a, rfl⟩ := Algebra.TensorProduct.includeRight_surjective
      (R := R) (S := R ⧸ I) A Ideal.Quotient.mk_surjective t
    refine ⟨a, eB.injective ?_⟩
    change (1 : R ⧸ I) ⊗ₜ[R] f a = (1 : R ⧸ I) ⊗ₜ[R] b
    exact ht
  have hsurj : Function.Surjective f := by
    change Function.Surjective f.toLinearMap
    apply LinearMap.range_eq_top.mp
    apply top_unique
    apply Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hI
    intro b _
    obtain ⟨a, ha⟩ := hquot b
    have hdiff : b - f a ∈ I • (⊤ : Submodule R B) := by
      rw [Ideal.smul_top_eq_map]
      exact Ideal.Quotient.eq.mp ha.symm
    have hmem : f a + (b - f a) ∈
        LinearMap.range f.toLinearMap ⊔ I • (⊤ : Submodule R B) :=
      Submodule.add_mem_sup (show f a ∈ LinearMap.range f.toLinearMap from ⟨a, rfl⟩) hdiff
    simpa only [add_sub_cancel] using hmem
  have hkerle : RingHom.ker f.toRingHom ≤ JA := by
    intro a ha
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply eA.injective
    change (1 : R ⧸ I) ⊗ₜ[R] a = eA 0
    rw [map_zero]
    apply hf.injective
    change (1 : R ⧸ I) ⊗ₜ[R] f a =
      Algebra.TensorProduct.map (.id (R ⧸ I) (R ⧸ I)) f 0
    rw [show f a = 0 from ha, TensorProduct.tmul_zero, map_zero]
  have hkerjac : RingHom.ker f.toRingHom ≤ Ideal.jacobson ⊥ :=
    hkerle.trans (Ideal.map_le_jacobson_bot_of_isIntegral hI)
  let : Algebra A B := f.toAlgebra
  let : IsScalarTower R A B := .of_algebraMap_eq' f.comp_algebraMap.symm
  have hfe : Algebra.FormallyEtale A B :=
    Algebra.FormallyEtale.of_restrictScalars (R := R)
  have hkeridem : IsIdempotentElem (RingHom.ker f.toRingHom) :=
    (Algebra.FormallyEtale.iff_of_surjective (R := A) (S := B)
      (show Function.Surjective (algebraMap A B) from hsurj)).mp hfe
  have hkerbot : RingHom.ker f.toRingHom = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot
      (RingHom.ker f.toRingHom) (RingHom.ker f.toRingHom)
      (Algebra.FinitePresentation.ker_fG_of_surjective f hsurj)
      (by rw [Ideal.smul_eq_mul]; exact hkeridem.ge) hkerjac
  exact ⟨(RingHom.injective_iff_ker_eq_bot f.toRingHom).mpr hkerbot, hsurj⟩

end Algebra.FiniteEtale
