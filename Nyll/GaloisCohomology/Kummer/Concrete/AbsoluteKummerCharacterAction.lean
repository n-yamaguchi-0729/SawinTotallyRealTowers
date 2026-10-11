/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Kummer.Concrete.AbsoluteKummerNaturality
import Nyll.GaloisCohomology.Kummer.Concrete.AbsoluteKummerH1
import Nyll.GaloisCohomology.Kummer.Concrete.AbsoluteContinuousCharacterAction
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Instances.ZMod

/-!
# Exact Kummer differences under the character action

When a field automorphism fixes the roots of unity, inverse-conjugation
pullback sends a Kummer character to the character of the transformed unit.
The fixed coordinate identification with cyclic coefficients preserves this
formula and the nontrivial difference supplied by an eigenunit.
-/

namespace ClassFieldTower.Martinet.Shafarevich

open KummerTheory

variable (K : Type*) [Field K] [CharZero K]

/-- The actual left character action agrees with the action on Kummer
classes when the coefficient roots are fixed. -/
theorem absoluteKummerContinuousNthRootsCharacterEquiv_action_of_fixes_roots
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (τ : K ≃+* K) (hτ : ∀ ξ : K, ξ ^ (n : ℕ) = 1 → τ ξ = ξ) (u : Kˣ) :
    absoluteContinuousCharacterAction
        (K := K) (A := DiscreteNthRootsSubgroup (AlgebraicClosure K) (n : ℕ)) τ
        (absoluteKummerContinuousNthRootsCharacterEquiv K n hmu
          (u : Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range)) =
      absoluteKummerContinuousNthRootsCharacterEquiv K n hmu
        ((Units.map τ.toMonoidHom u : Kˣ) :
          Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range) := by
  have hinv : ∀ ξ : K, ξ ^ (n : ℕ) = 1 → τ.symm ξ = ξ := by
    intro ξ hξ
    apply τ.injective
    rw [τ.apply_symm_apply, hτ ξ hξ]
  have hunit : Units.map τ.symm.toMonoidHom (Units.map τ.toMonoidHom u) = u := by
    apply Units.ext
    exact τ.symm_apply_apply (u : K)
  apply ContinuousMonoidHom.ext
  intro σ
  change absoluteKummerContinuousNthRootsCharacterEquiv K n hmu
      (u : Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range)
      (absoluteGaloisConjugate τ.symm σ) =
    absoluteKummerContinuousNthRootsCharacterEquiv K n hmu
      ((Units.map τ.toMonoidHom u : Kˣ) :
        Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range) σ
  have hnatural := absoluteKummerContinuousNthRootsCharacterEquiv_naturality_of_fixes_roots
    K n hmu τ.symm hinv (Units.map τ.toMonoidHom u) σ
  rw [hunit] at hnatural
  exact hnatural

/-- The same fixed cyclic-coordinate identification preserves the exact
Kummer action formula. -/
theorem absoluteKummerContinuousZModCharacterEquiv_action_of_fixes_roots
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (τ : K ≃+* K) (hτ : ∀ ξ : K, ξ ^ (n : ℕ) = 1 → τ ξ = ξ) (u : Kˣ) :
    absoluteContinuousCharacterAction (K := K) (A := Multiplicative (ZMod (n : ℕ))) τ
        (absoluteKummerContinuousZModCharacterEquiv K n hmu
          (u : Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range) :
          Gal(AlgebraicClosure K/K) →ₜ* Multiplicative (ZMod (n : ℕ))) =
      absoluteKummerContinuousZModCharacterEquiv K n hmu
        ((Units.map τ.toMonoidHom u : Kˣ) :
          Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range) := by
  let e : DiscreteNthRootsSubgroup (AlgebraicClosure K) (n : ℕ) ≃ₜ*
      Multiplicative (ZMod (n : ℕ)) :=
    discreteNthRootsContinuousMulEquivMultiplicativeZMod K n hmu
  have hroot := absoluteKummerContinuousNthRootsCharacterEquiv_action_of_fixes_roots
    K n hmu τ hτ u
  apply ContinuousMonoidHom.ext
  intro σ
  have hvalue := DFunLike.congr_fun hroot σ
  change absoluteKummerContinuousNthRootsCharacterEquiv K n hmu
      (u : Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range)
      (absoluteGaloisConjugate τ.symm σ) =
    absoluteKummerContinuousNthRootsCharacterEquiv K n hmu
      ((Units.map τ.toMonoidHom u : Kˣ) :
        Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range) σ at hvalue
  change e (absoluteKummerContinuousNthRootsCharacterEquiv K n hmu
      (u : Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range)
      (absoluteGaloisConjugate τ.symm σ)) =
    e (absoluteKummerContinuousNthRootsCharacterEquiv K n hmu
      ((Units.map τ.toMonoidHom u : Kˣ) :
        Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range) σ)
  exact congrArg e hvalue

/-- An eigenunit retains its exact nontrivial Kummer-character difference,
in the cyclic coordinates used by continuous H¹. -/
theorem absoluteKummerContinuousZModCharacterEquiv_action_div_ne_one_of_eigenunit
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (τ : K ≃+* K) (hτ : ∀ ξ : K, ξ ^ (n : ℕ) = 1 → τ ξ = ξ)
    (α ζ : Kˣ) (hα : Units.map τ.toMonoidHom α = ζ * α)
    (hζ : (ζ : Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range) ≠ 1) :
    let κ : (Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range) ≃*
        (Gal(AlgebraicClosure K/K) →ₜ* Multiplicative (ZMod (n : ℕ))) :=
      absoluteKummerContinuousZModCharacterEquiv K n hmu
    absoluteContinuousCharacterAction (K := K) (A := Multiplicative (ZMod (n : ℕ))) τ
        (κ (α : Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range)) /
      κ (α : Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range) =
        κ (ζ : Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range) ∧
      κ (ζ : Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range) ≠ 1 := by
  intro κ
  have haction :
      absoluteContinuousCharacterAction (K := K) (A := Multiplicative (ZMod (n : ℕ))) τ
          (κ (α : Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range)) =
        κ ((Units.map τ.toMonoidHom α : Kˣ) :
          Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range) :=
    absoluteKummerContinuousZModCharacterEquiv_action_of_fixes_roots K n hmu τ hτ α
  constructor
  · rw [haction, hα, QuotientGroup.mk_mul, κ.map_mul, mul_div_cancel_right]
  · intro h
    apply hζ
    apply κ.injective
    simpa only [_root_.map_one] using h

end ClassFieldTower.Martinet.Shafarevich
