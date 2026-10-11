/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.ArtinSchreier.RootCharacter
import Nyll.GaloisCohomology.FieldTheory.ContinuousAdditiveHilbert90
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Artin–Schreier classes and all continuous cyclic characters

Additive Hilbert 90 realizes every character by a root. Changing the field
element by an Artin–Schreier coboundary leaves its character unchanged.
-/

namespace ArtinSchreierTheory
section Surjectivity
variable (p : ℕ) [Fact p.Prime] {K Ω : Type*} [Field K] [Field Ω]
  [CharP Ω p] [Algebra K Ω] [IsGalois K Ω]

/-- Every continuous cyclic character is the difference character of a root. -/
theorem exists_rootCharacter_eq (χ : Gal(Ω/K) →ₜ* Multiplicative (ZMod p)) :
    ∃ (a : K) (β : Ω) (hβ : β ^ p - β = algebraMap K Ω a),
      rootCharacter p Ω a β hβ = χ := by
  let c : Gal(Ω/K) → Ω := fun σ => (ZMod.castHom (dvd_refl p) Ω) (χ σ).toAdd
  have hc : ∀ σ τ : Gal(Ω/K), c (σ * τ) = σ (c τ) + c σ := by
    intro σ τ
    have hfix : σ (c τ) = c τ := by
      simp only [c, ZMod.castHom_apply, ZMod.cast_eq_val, map_natCast]
    rw [hfix]
    change (ZMod.castHom (dvd_refl p) Ω) (χ (σ * τ)).toAdd = _
    rw [map_mul]
    change (ZMod.castHom (dvd_refl p) Ω) ((χ σ).toAdd + (χ τ).toAdd) = _
    rw [map_add, add_comm]
  have hlc : IsLocallyConstant c :=
    ((IsLocallyConstant.iff_continuous χ).mpr χ.continuous).comp
      (fun z : Multiplicative (ZMod p) => (ZMod.castHom (dvd_refl p) Ω) z.toAdd)
  obtain ⟨β, hβ⟩ := GaloisCohomology.additiveHilbert90_of_isLocallyConstant c hc hlc
  have hfixed : ∀ σ : Gal(Ω/K), σ (β ^ p - β) = β ^ p - β := by
    intro σ
    have hσ : σ β = c σ + β := (sub_eq_iff_eq_add).mp (hβ σ)
    have hpow : c σ ^ p = c σ := by
      change ((ZMod.castHom (dvd_refl p) Ω) (χ σ).toAdd) ^ p = _
      rw [← map_pow, ZMod.pow_card]
    rw [map_sub, map_pow, hσ, add_pow_char, hpow]
    ring
  obtain ⟨a, ha⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (β ^ p - β)).mpr hfixed
  refine ⟨a, β, ha.symm, ?_⟩
  apply ContinuousMonoidHom.ext
  intro σ
  change (rootCharacter p Ω a β ha.symm σ).toAdd = (χ σ).toAdd
  apply (ZMod.castHom (dvd_refl p) Ω).injective
  exact (rootCharacter_cast p Ω a β ha.symm σ).trans (hβ σ)
end Surjectivity

section Classes
variable (p : ℕ) [Fact p.Prime] {K Ω : Type*} [Field K] [Field Ω]
  [CharP K p] [CharP Ω p] [Algebra K Ω] [Algebra.IsIntegral K Ω]

/-- Equal additive Artin–Schreier classes give equal continuous characters. -/
theorem rootCharacter_eq_of_class_eq (a b : K) (β γ : Ω)
    (hβ : β ^ p - β = algebraMap K Ω a)
    (hγ : γ ^ p - γ = algebraMap K Ω b)
    (hab : (a : K ⧸ ((frobenius K p).toAddMonoidHom - AddMonoidHom.id K).range) =
      (b : K ⧸ ((frobenius K p).toAddMonoidHom - AddMonoidHom.id K).range)) :
    rootCharacter p Ω a β hβ = rootCharacter p Ω b γ hγ := by
  obtain ⟨x, hx⟩ := QuotientAddGroup.eq.mp hab
  change x ^ p - x = -a + b at hx
  have hxmap := congrArg (algebraMap K Ω) hx
  rw [map_sub, map_pow, map_add, map_neg] at hxmap
  have hβ' : (β + algebraMap K Ω x) ^ p - (β + algebraMap K Ω x) =
      algebraMap K Ω b := by
    rw [add_pow_char]
    linear_combination hβ + hxmap
  apply Eq.trans ?_ (rootCharacter_eq p Ω b (β + algebraMap K Ω x) γ hβ' hγ)
  apply ContinuousMonoidHom.ext
  intro σ
  change (rootCharacter p Ω a β hβ σ).toAdd =
    (rootCharacter p Ω b (β + algebraMap K Ω x) hβ' σ).toAdd
  apply (ZMod.castHom (dvd_refl p) Ω).injective
  rw [rootCharacter_cast, rootCharacter_cast, map_add, σ.commutes]
  ring
end Classes
end ArtinSchreierTheory
