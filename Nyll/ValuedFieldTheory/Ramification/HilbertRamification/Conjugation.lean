/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.ValuationSubring

/-!
# Hilbert ramification theory: conjugating valuation subrings

This file records the functorial conjugation law for chosen valuations: inside
a fixed Galois extension, conjugating the chosen
valuation subring conjugates the decomposition group.  The inertia and
ramification parts require the residue/principal-unit transport and are handled
separately.
-/

namespace RamificationTheory

noncomputable section

universe u v

namespace HilbertRamification
namespace ValuationSubring

open scoped Pointwise

variable (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]

/-- Conjugating a valuation subring by an automorphism gives an isomorphic
valuation subring.  This is the ring-level form of the conjugation law. -/
def valuationSubringConjRingEquiv
    (A : _root_.ValuationSubring L) (τ : L ≃ₐ[K] L) :
    (A : Type v) ≃+* ((τ • A : _root_.ValuationSubring L) : Type v) where
  toFun a :=
    ⟨τ a,
      _root_.ValuationSubring.smul_mem_pointwise_smul
        τ (a : L) A a.property⟩
  invFun b :=
    ⟨τ⁻¹ b,
      (_root_.ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem
        (g := τ) (S := A) (x := (b : L))).mp b.property⟩
  left_inv a := by
    ext
    simp
  right_inv b := by
    ext
    simp
  map_mul' a b := by
    ext
    simp
  map_add' a b := by
    ext
    simp

/-- The conjugation law:
conjugation transports valuation-ring units. -/
def unitGroupConjEquiv
    (A : _root_.ValuationSubring L) (τ : L ≃ₐ[K] L) :
    A.unitGroup ≃* (τ • A).unitGroup :=
  A.unitGroupMulEquiv.trans
    ((Units.mapEquiv
      (valuationSubringConjRingEquiv (K := K) A τ).toMulEquiv).trans
      ((τ • A).unitGroupMulEquiv.symm))

/-- States the theorem `unitGroupConjEquiv_coe`. -/
@[simp] theorem unitGroupConjEquiv_coe
    (A : _root_.ValuationSubring L) (τ : L ≃ₐ[K] L)
    (u : A.unitGroup) :
    (unitGroupConjEquiv (K := K) A τ u : Lˣ) =
      Units.mapEquiv τ.toMulEquiv (u : Lˣ) := by
  ext
  simp [unitGroupConjEquiv,
    valuationSubringConjRingEquiv]

/-- The conjugation law:
conjugation by an automorphism sends the decomposition group of `A` into the
decomposition group of the conjugate valuation subring `τ • A`. -/
def decompositionGroupConj
    (A : _root_.ValuationSubring L) (τ : L ≃ₐ[K] L) :
    decompositionGroup K A →* decompositionGroup K (τ • A) where
  toFun σ :=
    ⟨τ * (σ : L ≃ₐ[K] L) * τ⁻¹, by
      change (τ * (σ : L ≃ₐ[K] L) * τ⁻¹) • (τ • A) = τ • A
      rw [mul_assoc, mul_smul, mul_smul, inv_smul_smul, σ.property]⟩
  map_one' := by
    ext x
    simp
  map_mul' σ ρ := by
    ext x
    simp [mul_assoc]

/-- States the theorem `decompositionGroupConj_apply`. -/
@[simp] theorem decompositionGroupConj_apply
    (A : _root_.ValuationSubring L) (τ : L ≃ₐ[K] L)
    (σ : decompositionGroup K A) :
    decompositionGroupConj (K := K) A τ σ =
      ⟨τ * (σ : L ≃ₐ[K] L) * τ⁻¹, by
        change (τ * (σ : L ≃ₐ[K] L) * τ⁻¹) • (τ • A) = τ • A
        rw [mul_assoc, mul_smul, mul_smul, inv_smul_smul, σ.property]⟩ :=
  rfl

/-- The inverse conjugation map for decomposition groups. -/
def decompositionGroupConjInv
    (A : _root_.ValuationSubring L) (τ : L ≃ₐ[K] L) :
    decompositionGroup K (τ • A) →* decompositionGroup K A where
  toFun σ :=
    ⟨τ⁻¹ * (σ : L ≃ₐ[K] L) * τ, by
      change (τ⁻¹ * (σ : L ≃ₐ[K] L) * τ) • A = A
      rw [mul_assoc, mul_smul, mul_smul]
      have hσ : (σ : L ≃ₐ[K] L) • (τ • A) = τ • A := σ.property
      rw [hσ, inv_smul_smul]⟩
  map_one' := by
    ext x
    simp
  map_mul' σ ρ := by
    ext x
    simp [mul_assoc]

/-- The conjugation law:
the decomposition groups of conjugate valuation subrings are canonically
isomorphic by conjugation. -/
def decompositionGroupConjEquiv
    (A : _root_.ValuationSubring L) (τ : L ≃ₐ[K] L) :
    decompositionGroup K A ≃* decompositionGroup K (τ • A) where
  toFun := decompositionGroupConj (K := K) A τ
  invFun := decompositionGroupConjInv (K := K) A τ
  left_inv σ := by
    ext x
    simp [decompositionGroupConj,
      decompositionGroupConjInv, mul_assoc]
  right_inv σ := by
    ext x
    simp [decompositionGroupConj,
      decompositionGroupConjInv, mul_assoc]
  map_mul' σ ρ := by
    ext x
    simp [decompositionGroupConj, mul_assoc]

/-- States the theorem `decompositionGroupConjEquiv_apply`. -/
@[simp] theorem decompositionGroupConjEquiv_apply
    (A : _root_.ValuationSubring L) (τ : L ≃ₐ[K] L)
    (σ : decompositionGroup K A) :
    decompositionGroupConjEquiv (K := K) A τ σ =
      decompositionGroupConj (K := K) A τ σ :=
  rfl

end ValuationSubring
end HilbertRamification

end
end RamificationTheory
