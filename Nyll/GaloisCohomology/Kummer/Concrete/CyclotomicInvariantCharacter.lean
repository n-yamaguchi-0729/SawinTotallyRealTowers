/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Kummer.Concrete.AbsoluteKummerNaturality
import Nyll.GaloisCohomology.Kummer.Concrete.AbsoluteRootPowerAction
import Mathlib.GroupTheory.OrderOfElement

/-!
# Cyclotomic eigenclasses give invariant Kummer characters

When an automorphism acts by the same power on a unit's power class and on
the roots of unity, Kummer naturality cancels these two actions. Coprimality
of the exponent makes the power map injective on the character values.
-/

namespace ClassFieldTower.Martinet.Shafarevich

open KummerTheory

variable (K : Type*) [Field K] [CharZero K]

/-- A power eigenclass whose exponent matches the actual cyclotomic action
gives a Kummer character fixed by Galois conjugation. -/
theorem absoluteKummerContinuousNthRootsCharacterEquiv_conjugation_invariant_of_power_action
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (τ : K ≃+* K) (u : Kˣ) (a : ℕ) (ha : a.Coprime (n : ℕ))
    (hu : ((Units.map τ.toMonoidHom u : Kˣ) :
        Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range) =
      (u : Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range) ^ a)
    (hτ : ∀ ζ : K, ζ ^ (n : ℕ) = 1 → τ ζ = ζ ^ a)
    (σ : Gal(AlgebraicClosure K/K)) :
    absoluteKummerContinuousNthRootsCharacterEquiv K n hmu
        (u : Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range)
        (absoluteGaloisConjugate τ σ) =
      absoluteKummerContinuousNthRootsCharacterEquiv K n hmu
        (u : Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range) σ := by
  let κ := absoluteKummerContinuousNthRootsCharacterEquiv K n hmu
  let c := κ (u : Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range)
  let x : DiscreteNthRootsSubgroup (AlgebraicClosure K) (n : ℕ) :=
    c (absoluteGaloisConjugate τ σ)
  let y : DiscreteNthRootsSubgroup (AlgebraicClosure K) (n : ℕ) := c σ
  have hy : (y : (AlgebraicClosure K)ˣ) ^ (n : ℕ) = 1 := y.property
  have hroots :
      Units.map (IsAlgClosure.equivOfEquiv (AlgebraicClosure K)
        (AlgebraicClosure K) τ).toMonoidHom (y : (AlgebraicClosure K)ˣ) =
      (y : (AlgebraicClosure K)ˣ) ^ a :=
    absoluteGaloisLift_nthRoot_eq_pow K n hmu τ a hτ y
  have hpowers : (x : (AlgebraicClosure K)ˣ) ^ a =
      (y : (AlgebraicClosure K)ˣ) ^ a := by
    have hnatural :=
      absoluteKummerContinuousNthRootsCharacterEquiv_naturality K n hmu τ u σ
    rw [hu, map_pow] at hnatural
    have heval := ContinuousMonoidHom.pow_apply c a
      (absoluteGaloisConjugate τ σ)
    have hevalUnits := congrArg
      (fun z : DiscreteNthRootsSubgroup (AlgebraicClosure K) (n : ℕ) =>
        (z : (AlgebraicClosure K)ˣ)) heval
    rw [hevalUnits] at hnatural
    change (x : (AlgebraicClosure K)ˣ) ^ a =
      Units.map (IsAlgClosure.equivOfEquiv (AlgebraicClosure K)
        (AlgebraicClosure K) τ).toMonoidHom (y : (AlgebraicClosure K)ˣ) at hnatural
    exact hnatural.trans hroots
  have hquotient_a :
      ((x : (AlgebraicClosure K)ˣ) / (y : (AlgebraicClosure K)ˣ)) ^ a = 1 := by
    rw [div_pow, hpowers, div_self']
  have hquotient_n :
      ((x : (AlgebraicClosure K)ˣ) / (y : (AlgebraicClosure K)ˣ)) ^ (n : ℕ) = 1 := by
    rw [div_pow, x.property, hy, div_self']
  have hquotient : (x : (AlgebraicClosure K)ˣ) / (y : (AlgebraicClosure K)ˣ) = 1 :=
    orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes ha
      (orderOf_dvd_of_pow_eq_one hquotient_a)
      (orderOf_dvd_of_pow_eq_one hquotient_n))
  change x = y
  apply Subtype.ext
  exact div_eq_one.mp hquotient

end ClassFieldTower.Martinet.Shafarevich
