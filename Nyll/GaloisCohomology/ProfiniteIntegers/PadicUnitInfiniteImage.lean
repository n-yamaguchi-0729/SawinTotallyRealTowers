/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.ProfiniteIntegers.PadicInverseLimit
import Nyll.ProCGroups.Abelian.PrimeQuotients
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Data.Nat.Totient

/-!
# Cyclic quotients detected by infinite p-adic unit characters

If every finite reduction had order prime to p, each reduction would have
exponent dividing p - 1. Separation by reductions would then place the entire
image in the finite group of (p - 1)-st roots of unity.
-/

namespace PadicInt
variable {p : ℕ} [Fact p.Prime]

/-- Continuous reduction of p-adic units at a positive finite level. -/
noncomputable def unitsReduction (n : ℕ) :
    (PadicInt p)ˣ →ₜ* (ZMod (p ^ (n + 1)))ˣ :=
  ⟨Units.map (toZModPow (n + 1)).toMonoidHom,
    (continuous_toZModPow (n + 1)).units_map _⟩

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- An infinite unit image has a finite reduction whose order is divisible by p. -/
theorem exists_prime_dvd_card_reduction_range
    (χ : G →ₜ* (PadicInt p)ˣ) (hinf : Set.Infinite (Set.range χ)) :
    ∃ n : ℕ, p ∣ Nat.card ((unitsReduction n).comp χ).toMonoidHom.range := by
  classical
  by_contra! h
  have (n : ℕ) : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  let ρ (n : ℕ) := (unitsReduction n).comp χ
  have hcard (n : ℕ) : Nat.card (ρ n).toMonoidHom.range ∣ p - 1 := by
    have hd : Nat.card (ρ n).toMonoidHom.range ∣ p ^ n * (p - 1) := by
      have hsub := Subgroup.card_subgroup_dvd_card (ρ n).toMonoidHom.range
      simpa only [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
        Nat.totient_prime_pow_succ (Fact.out : p.Prime)] using hsub
    exact ((Fact.out : p.Prime).coprime_pow_of_not_dvd (h n)).dvd_of_dvd_mul_left hd
  have hpow (n : ℕ) (g : G) : ρ n g ^ (p - 1) = 1 := by
    let x : (ρ n).toMonoidHom.range := ⟨ρ n g, ⟨g, rfl⟩⟩
    obtain ⟨k, hk⟩ := hcard n
    have hx : x ^ (p - 1) = 1 := by
      rw [hk, pow_mul, pow_card_eq_one', one_pow]
    exact congrArg Subtype.val hx
  have hχpow (g : G) : χ g ^ (p - 1) = 1 := by
    apply Units.ext
    apply ext_of_toZModPow.mp
    intro n
    cases n with
    | zero =>
      have : Subsingleton (ZMod (p ^ 0)) := by rw [pow_zero]; infer_instance
      exact Subsingleton.elim _ _
    | succ n =>
      have heq := congrArg Units.val (hpow n g)
      change (toZModPow (n + 1) (χ g : PadicInt p)) ^ (p - 1) = 1 at heq
      simpa only [Units.val_pow_eq_pow_val, Units.val_one, map_pow, map_one] using heq
  have : NeZero (p - 1) := ⟨Nat.ne_of_gt (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt)⟩
  have hfinite : Set.Finite (rootsOfUnity (p - 1) (PadicInt p) : Set (PadicInt p)ˣ) :=
    Set.finite_coe_iff.mp (inferInstanceAs (Finite (rootsOfUnity (p - 1) (PadicInt p))))
  apply hinf
  apply hfinite.subset
  rintro _ ⟨g, rfl⟩
  exact hχpow g

/-- An infinite p-adic unit image yields an actual continuous cyclic quotient of order p. -/
theorem exists_surjective_prime_character_of_infinite_unit_image
    (χ : G →ₜ* (PadicInt p)ˣ) (hinf : Set.Infinite (Set.range χ)) :
    ∃ ψ : G →ₜ* Multiplicative (ZMod p), Function.Surjective ψ := by
  obtain ⟨n, hn⟩ := exists_prime_dvd_card_reduction_range χ hinf
  have : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  let ρ : G →ₜ* (ZMod (p ^ (n + 1)))ˣ := (unitsReduction n).comp χ
  obtain ⟨φ, hφ⟩ := ProCGroups.Abelian.exists_surjective_prime_character_finite hn
  let ρrange : G →ₜ* ρ.toMonoidHom.range :=
    { toMonoidHom := ρ.toMonoidHom.rangeRestrict
      continuous_toFun := ρ.continuous.subtype_mk (fun g => ⟨g, rfl⟩) }
  let φcont : ρ.toMonoidHom.range →ₜ* Multiplicative (ZMod p) :=
    ⟨φ, continuous_of_discreteTopology⟩
  exact ⟨φcont.comp ρrange, hφ.comp ρ.toMonoidHom.rangeRestrict_surjective⟩

end PadicInt
