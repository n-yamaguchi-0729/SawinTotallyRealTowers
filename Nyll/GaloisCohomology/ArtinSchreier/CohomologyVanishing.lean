/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.FieldTheory.AdditiveH2Finite
import Nyll.GaloisCohomology.Topology.GaloisFiniteStageFunctions
import Nyll.GaloisCohomology.ArtinSchreier.RootCharacter
import Mathlib.Topology.Instances.ZMod
import Mathlib.Tactic.LinearCombination

/-!
# Continuous Artin–Schreier two-cocycles

Trace averaging and the Artin–Schreier exact sequence give explicit locally
constant primitives for two-cocycles with values in the prime field.
-/

namespace ArtinSchreierTheory
universe u v
variable {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
variable (p : ℕ) [Fact p.Prime] [CharP Ω p]

/-- A prime-field two-cocycle has a locally constant primitive with values in
the separable Galois extension. -/
theorem exists_additive_primitive_of_zmod_two_cocycle
    (z : Gal(Ω/K) → Gal(Ω/K) → ZMod p)
    (hz : ∀ σ τ υ : Gal(Ω/K),
      z σ (τ * υ) + z τ υ = z (σ * τ) υ + z σ τ)
    (hlc : IsLocallyConstant (fun x : Gal(Ω/K) × Gal(Ω/K) => z x.1 x.2)) :
    ∃ b : Gal(Ω/K) → Ω, IsLocallyConstant b ∧
      ∀ σ τ : Gal(Ω/K), σ (b τ) - b (σ * τ) + b σ =
        (ZMod.castHom (dvd_refl p) Ω) (z σ τ) := by
  classical
  obtain ⟨E, zE, hvalue⟩ := GaloisCohomology.exists_finiteGalois_factor_continuous_pair
    (fun x : Gal(Ω/K) × Gal(Ω/K) => z x.1 x.2) hlc.continuous
  let r : Gal(Ω/K) →* Gal(E/K) := AlgEquiv.restrictNormalHom E
  have hr : Function.Surjective r := AlgEquiv.restrictNormalHom_surjective Ω
  have hzE (σ τ υ : Gal(E/K)) :
      zE σ (τ * υ) + zE τ υ = zE (σ * τ) υ + zE σ τ := by
    obtain ⟨σ', rfl⟩ := hr σ
    obtain ⟨τ', rfl⟩ := hr τ
    obtain ⟨υ', rfl⟩ := hr υ
    rw [← map_mul, ← map_mul]
    exact (congrArg₂ (· + ·) (hvalue σ' (τ' * υ')) (hvalue τ' υ')).trans
      ((hz σ' τ' υ').trans
        (congrArg₂ (· + ·) (hvalue (σ' * τ') υ') (hvalue σ' τ')).symm)
  let φE : ZMod p →+* E := ZMod.castHom (dvd_refl p) E
  have hfix (σ : Gal(E/K)) (x : ZMod p) : σ (φE x) = φE x := by
    simp only [φE, ZMod.castHom_apply, ZMod.cast_eq_val, map_natCast]
  have hcE (σ τ υ : Gal(E/K)) :
      φE (zE σ (τ * υ)) + σ (φE (zE τ υ)) =
        φE (zE (σ * τ) υ) + φE (zE σ τ) := by
    rw [hfix, ← map_add, ← map_add, hzE]
  obtain ⟨bE, hbE⟩ := GaloisCohomology.additiveH2_finite
    (fun σ τ : Gal(E/K) => φE (zE σ τ)) hcE
  let b : Gal(Ω/K) → Ω := fun σ => (bE (r σ) : Ω)
  have hrlc : IsLocallyConstant r :=
    (IsLocallyConstant.iff_continuous r).mpr
      (InfiniteGalois.restrictNormalHom_continuous E.toIntermediateField)
  refine ⟨b, hrlc.comp (fun τ : Gal(E/K) => (bE τ : Ω)), ?_⟩
  intro σ τ
  have hφ (x : ZMod p) :
      ((φE x : E) : Ω) = (ZMod.castHom (dvd_refl p) Ω) x := by
    obtain ⟨a, rfl⟩ := ZMod.intCast_surjective x
    rw [map_intCast, map_intCast]
    rfl
  have h := congrArg (fun x : E => (x : Ω)) (hbE (r σ) (r τ))
  change ((r σ) (bE (r τ)) : Ω) - (bE (r σ * r τ) : Ω) +
    (bE (r σ) : Ω) = ((φE (zE (r σ) (r τ)) : E) : Ω) at h
  rw [AlgEquiv.restrictNormalHom_apply, ← map_mul, hφ, hvalue] at h
  exact h

variable [IsSepClosed Ω]

/-- Every continuous prime-field two-cocycle of an absolute Galois group in
characteristic `p` is a coboundary. -/
theorem exists_zmod_primitive_of_two_cocycle
    (z : Gal(Ω/K) → Gal(Ω/K) → ZMod p)
    (hz : ∀ σ τ υ : Gal(Ω/K),
      z σ (τ * υ) + z τ υ = z (σ * τ) υ + z σ τ)
    (hlc : IsLocallyConstant (fun x : Gal(Ω/K) × Gal(Ω/K) => z x.1 x.2)) :
    ∃ d : Gal(Ω/K) → ZMod p, IsLocallyConstant d ∧
      ∀ σ τ : Gal(Ω/K), d τ - d (σ * τ) + d σ = z σ τ := by
  classical
  obtain ⟨b, hblc, hb⟩ := exists_additive_primitive_of_zmod_two_cocycle p z hz hlc
  let φ : ZMod p →+* Ω := ZMod.castHom (dvd_refl p) Ω
  let AS : Ω →+ Ω := (frobenius Ω p).toAddMonoidHom - AddMonoidHom.id Ω
  have hAS (x : Ω) : AS x = x ^ p - x := rfl
  have hcomm (σ : Gal(Ω/K)) (x : Ω) : AS (σ x) = σ (AS x) := by
    rw [hAS, hAS, map_sub, map_pow]
  have hφ (x : ZMod p) : AS (φ x) = 0 := by
    rw [hAS, ← map_pow]
    have hx : x ^ p = x := by
      simpa only [ZMod.card] using (FiniteField.pow_card x)
    rw [hx, sub_self]
  have hc (σ τ : Gal(Ω/K)) : AS (b (σ * τ)) = σ (AS (b τ)) + AS (b σ) := by
    have h := congrArg AS (hb σ τ)
    change AS (σ (b τ) - b (σ * τ) + b σ) = AS (φ (z σ τ)) at h
    rw [map_add, map_sub, hcomm, hφ] at h
    linear_combination -h
  obtain ⟨a, ha⟩ := GaloisCohomology.additiveHilbert90_of_isLocallyConstant
    (fun σ => AS (b σ)) hc (hblc.comp AS)
  obtain ⟨β, hβ⟩ := exists_root p Ω a
  have hASβ : AS β = a := hβ
  let D : Gal(Ω/K) → Ω := fun σ => b σ - (σ β - β)
  have hD (σ : Gal(Ω/K)) : AS (D σ) = 0 := by
    change AS (b σ - (σ β - β)) = 0
    rw [map_sub, map_sub, hcomm, hASβ, ← ha, sub_self]
  have hDpow (σ : Gal(Ω/K)) : D σ ^ p = D σ :=
    sub_eq_zero.mp (hD σ)
  choose d hd using fun σ => exists_zmod_of_pow_eq p Ω (hDpow σ)
  have hDlc : IsLocallyConstant D :=
    (hblc.prodMk ((GaloisCohomology.isLocallyConstant_galois_apply (K := K) β).comp
      (fun x : Ω => x - β))).comp (fun x : Ω × Ω => x.1 - x.2)
  have hdlc : IsLocallyConstant d := by
    rw [IsLocallyConstant.iff_eventually_eq] at hDlc ⊢
    intro σ
    filter_upwards [hDlc σ] with τ hτ
    apply φ.injective
    exact (hd τ).trans (hτ.trans (hd σ).symm)
  refine ⟨d, hdlc, ?_⟩
  intro σ τ
  have hfix : σ (D τ) = D τ := by
    rw [← hd τ]
    simp only [ZMod.castHom_apply, ZMod.cast_eq_val, map_natCast]
  have hδ : σ (D τ) - D (σ * τ) + D σ = φ (z σ τ) := by
    dsimp only [D]
    rw [map_sub, map_sub]
    change σ (b τ) - (σ (τ β) - σ β) -
      (b (σ * τ) - (σ (τ β) - β)) + (b σ - (σ β - β)) = φ (z σ τ)
    linear_combination hb σ τ
  apply φ.injective
  change φ (d τ - d (σ * τ) + d σ) = φ (z σ τ)
  rw [map_add, map_sub, hd, hd, hd]
  rw [hfix] at hδ
  exact hδ

end ArtinSchreierTheory
