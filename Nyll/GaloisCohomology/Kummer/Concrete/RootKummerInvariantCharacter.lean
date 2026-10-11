/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Kummer.Concrete.CyclotomicInvariantCharacter
import Nyll.GaloisCohomology.Kummer.Concrete.RootOfUnityPowerAction
import Nyll.GaloisCohomology.Kummer.Concrete.AbsoluteContinuousCharacterAction
import Nyll.GaloisCohomology.Kummer.Concrete.AbsoluteKummerH1
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Instances.ZMod

/-!
# Roots give invariant Kummer characters

An automorphism has the same actual power action on a root and on the
Kummer coefficient roots. Their cyclotomic actions cancel. The resulting
constant-coefficient Kummer character is fixed by the true left action.
-/

namespace ClassFieldTower.Martinet.Shafarevich

open KummerTheory

variable (K : Type*) [Field K] [CharZero K]

/-- A unit which is an n-th root of unity has an invariant Kummer character
under every field automorphism. -/
theorem absoluteKummerContinuousNthRootsCharacterEquiv_conjugation_invariant_of_root
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (u : Kˣ) (hu : (u : K) ^ (n : ℕ) = 1) (τ : K ≃+* K)
    (σ : Gal(AlgebraicClosure K/K)) :
    absoluteKummerContinuousNthRootsCharacterEquiv K n hmu
        (u : Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range)
        (absoluteGaloisConjugate τ σ) =
      absoluteKummerContinuousNthRootsCharacterEquiv K n hmu
        (u : Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range) σ := by
  obtain ⟨a, _ha, hcop, hroots⟩ := exists_bounded_coprime_power_action_on_roots K n hmu τ
  have hunit : Units.map τ.toMonoidHom u = u ^ a := by
    apply Units.ext
    exact hroots (u : K) hu
  apply absoluteKummerContinuousNthRootsCharacterEquiv_conjugation_invariant_of_power_action
    K n hmu τ u a hcop ?_ hroots σ
  rw [hunit]
  exact map_pow (QuotientGroup.mk' (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range) u a

/-- The root's constant-coefficient Kummer character is fixed by the
inverse-conjugation left action, with the original Kummer coordinate. -/
theorem absoluteContinuousCharacterAction_kummer_root
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (u : Kˣ) (hu : (u : K) ^ (n : ℕ) = 1) (τ : K ≃+* K) :
    absoluteContinuousCharacterAction (K := K) (A := Multiplicative (ZMod (n : ℕ))) τ
        (absoluteKummerContinuousZModCharacterEquiv K n hmu
          (u : Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range)) =
      absoluteKummerContinuousZModCharacterEquiv K n hmu
        (u : Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range) := by
  apply ContinuousMonoidHom.ext
  intro σ
  change discreteNthRootsContinuousMulEquivMultiplicativeZMod K n hmu
      (absoluteKummerContinuousNthRootsCharacterEquiv K n hmu
        (u : Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range)
        (absoluteGaloisConjugate τ.symm σ)) =
    discreteNthRootsContinuousMulEquivMultiplicativeZMod K n hmu
      (absoluteKummerContinuousNthRootsCharacterEquiv K n hmu
        (u : Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range) σ)
  exact congrArg (discreteNthRootsContinuousMulEquivMultiplicativeZMod K n hmu)
    (absoluteKummerContinuousNthRootsCharacterEquiv_conjugation_invariant_of_root
      K n hmu u hu τ.symm σ)

end ClassFieldTower.Martinet.Shafarevich
