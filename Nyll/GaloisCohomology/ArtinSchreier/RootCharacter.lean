/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.IsSepClosed
import Nyll.GaloisCohomology.Topology.AlgebraicGaloisOrbits
import Mathlib.Topology.Instances.ZMod
import Mathlib.Tactic.LinearCombination

/-!
# Continuous Artin–Schreier characters from roots

The Frobenius-fixed elements are exactly the prime field. Thus the difference
between a root and its Galois translate gives a continuous cyclic character.
-/

namespace ArtinSchreierTheory
open Polynomial
variable (p : ℕ) [Fact p.Prime] (Ω : Type*) [Field Ω] [CharP Ω p]

/-- The fixed elements of the prime Frobenius come from the prime field. -/
theorem exists_zmod_of_pow_eq {x : Ω} (hx : x ^ p = x) :
    ∃ z : ZMod p, (ZMod.castHom (dvd_refl p) Ω) z = x := by
  let f : (ZMod p)[X] := X ^ p - X
  have hr : f.roots = Finset.univ.val := by
    simpa only [ZMod.card] using FiniteField.roots_X_pow_card_sub_X (K := ZMod p)
  have hsplit : f.Splits := Polynomial.splits_iff_card_roots.mpr (by
    rw [hr]
    change Fintype.card (ZMod p) = f.natDegree
    rw [ZMod.card]
    exact (FiniteField.X_pow_card_sub_X_natDegree_eq (ZMod p) (Fact.out : p.Prime).one_lt).symm)
  apply hsplit.mem_range_of_isRoot
    (FiniteField.X_pow_card_sub_X_ne_zero (ZMod p) (Fact.out : p.Prime).one_lt)
  simp only [f, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    hx, sub_self]

/-- Every Artin–Schreier equation has a root in a separably closed field. -/
theorem exists_root [IsSepClosed Ω] (a : Ω) : ∃ β : Ω, β ^ p - β = a := by
  obtain ⟨β, hβ⟩ := IsSepClosed.exists_root_C_mul_X_pow_add_C_mul_X_add_C
    (1 : Ω) (-1) (-a) (CharP.cast_eq_zero Ω p) (Fact.out : p.Prime).two_le
    (neg_ne_zero.mpr one_ne_zero)
  refine ⟨β, ?_⟩
  simpa only [one_mul, neg_one_mul, ← sub_eq_add_neg, sub_eq_zero] using hβ

variable {K : Type*} [Field K] [Algebra K Ω]

private theorem rootDifference_pow_eq (a : K) (β : Ω)
    (hβ : β ^ p - β = algebraMap K Ω a) (σ : Gal(Ω/K)) :
    (σ β - β) ^ p = σ β - β := by
  rw [sub_pow_char]
  have hσ := congrArg σ hβ
  rw [map_sub, map_pow, σ.commutes] at hσ
  linear_combination hσ - hβ

/-- The prime-field coordinate of the difference between a root and its Galois translate. -/
noncomputable def rootCharacterValue (a : K) (β : Ω)
    (hβ : β ^ p - β = algebraMap K Ω a) (σ : Gal(Ω/K)) : ZMod p :=
  (exists_zmod_of_pow_eq p Ω (rootDifference_pow_eq p Ω a β hβ σ)).choose

theorem rootCharacterValue_cast (a : K) (β : Ω)
    (hβ : β ^ p - β = algebraMap K Ω a) (σ : Gal(Ω/K)) :
    (ZMod.castHom (dvd_refl p) Ω) (rootCharacterValue p Ω a β hβ σ) = σ β - β :=
  (exists_zmod_of_pow_eq p Ω (rootDifference_pow_eq p Ω a β hβ σ)).choose_spec

variable [Algebra.IsIntegral K Ω]

/-- The continuous cyclic character defined by a root of an Artin–Schreier equation. -/
noncomputable def rootCharacter (a : K) (β : Ω)
    (hβ : β ^ p - β = algebraMap K Ω a) :
    Gal(Ω/K) →ₜ* Multiplicative (ZMod p) where
  toFun σ := Multiplicative.ofAdd (rootCharacterValue p Ω a β hβ σ)
  map_one' := by
    change rootCharacterValue p Ω a β hβ 1 = 0
    apply (ZMod.castHom (dvd_refl p) Ω).injective
    rw [rootCharacterValue_cast, map_zero]
    exact sub_self β
  map_mul' σ τ := by
    change rootCharacterValue p Ω a β hβ (σ * τ) =
      rootCharacterValue p Ω a β hβ σ + rootCharacterValue p Ω a β hβ τ
    apply (ZMod.castHom (dvd_refl p) Ω).injective
    rw [map_add, rootCharacterValue_cast, rootCharacterValue_cast, rootCharacterValue_cast]
    have hfix : σ (τ β - β) = τ β - β := by
      rw [← rootCharacterValue_cast p Ω a β hβ τ]
      simp only [ZMod.castHom_apply, ZMod.cast_eq_val, map_natCast]
    change σ (τ β) - β = (σ β - β) + (τ β - β)
    rw [map_sub] at hfix
    linear_combination hfix
  continuous_toFun := by
    apply IsLocallyConstant.continuous
    apply (IsLocallyConstant.iff_exists_open _).mpr
    intro σ
    obtain ⟨U, hU, hσ, hconst⟩ :=
      (GaloisCohomology.isLocallyConstant_galois_apply (K := K) β).exists_open σ
    refine ⟨U, hU, hσ, ?_⟩
    intro τ hτ
    apply congrArg Multiplicative.ofAdd
    apply (ZMod.castHom (dvd_refl p) Ω).injective
    rw [rootCharacterValue_cast, rootCharacterValue_cast, hconst τ hτ]

theorem rootCharacter_cast (a : K) (β : Ω)
    (hβ : β ^ p - β = algebraMap K Ω a) (σ : Gal(Ω/K)) :
    (ZMod.castHom (dvd_refl p) Ω) ((rootCharacter p Ω a β hβ σ).toAdd) = σ β - β :=
  rootCharacterValue_cast p Ω a β hβ σ

/-- The Artin–Schreier character is independent of the chosen root. -/
theorem rootCharacter_eq (a : K) (β γ : Ω)
    (hβ : β ^ p - β = algebraMap K Ω a)
    (hγ : γ ^ p - γ = algebraMap K Ω a) :
    rootCharacter p Ω a β hβ = rootCharacter p Ω a γ hγ := by
  have hdiff : (β - γ) ^ p = β - γ := by
    rw [sub_pow_char]
    linear_combination hβ - hγ
  obtain ⟨z, hz⟩ := exists_zmod_of_pow_eq p Ω hdiff
  apply ContinuousMonoidHom.ext
  intro σ
  change (rootCharacter p Ω a β hβ σ).toAdd = (rootCharacter p Ω a γ hγ σ).toAdd
  apply (ZMod.castHom (dvd_refl p) Ω).injective
  rw [rootCharacter_cast, rootCharacter_cast]
  have hfix : σ (β - γ) = β - γ := by
    rw [← hz]
    simp only [ZMod.castHom_apply, ZMod.cast_eq_val, map_natCast]
  rw [map_sub] at hfix
  linear_combination hfix

end ArtinSchreierTheory
