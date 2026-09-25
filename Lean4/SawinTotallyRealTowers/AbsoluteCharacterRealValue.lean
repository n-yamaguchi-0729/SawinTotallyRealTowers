/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.NegativeThreeCharacter
import SawinTotallyRealTowers.AbsoluteRealKernelField
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FinitePlaceH2Localization
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FinitePlaceUnramifiedH1
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.Tactic.FinCases
import Mathlib.Topology.Algebra.ContinuousMonoidHom

set_option autoImplicit false

/-!
# Prescribing the real value of an absolute quadratic character

Multiplication by the actual character of negative three switches the real
value and leaves inertia at every finite place other than three unchanged.
This constructs a character with any specified real value, starting with
an arbitrary continuous quadratic character and imposing no arithmetic
condition on that input.
-/

open scoped NumberField
open NumberField IsDedekindDomain

namespace ClassFieldTower.Sawin

open ClassFieldTower.Martinet.Shafarevich

private theorem quadratic_mul_eq_of_ne
    (a b c : Multiplicative (ZMod 2)) (hab : a ≠ b) (hc : c ≠ 1) :
    a * c = b := by
  have habAdd : a.toAdd ≠ b.toAdd := fun h ↦ hab (Multiplicative.toAdd.injective h)
  have hcAdd : c.toAdd ≠ 0 := fun h ↦ hc (Multiplicative.toAdd.injective h)
  apply Multiplicative.toAdd.injective
  change a.toAdd + c.toAdd = b.toAdd
  generalize ha : a.toAdd = x at habAdd ⊢
  generalize hb : b.toAdd = y at habAdd ⊢
  generalize hc' : c.toAdd = z at hcAdd ⊢
  fin_cases x <;> fin_cases y <;> fin_cases z
  · exact False.elim (habAdd rfl)
  · exact False.elim (habAdd rfl)
  · exact False.elim (hcAdd rfl)
  · change (0 : ZMod 2) + 1 = 1
    decide +kernel
  · exact False.elim (hcAdd rfl)
  · change (1 : ZMod 2) + 1 = 0
    decide +kernel
  · exact False.elim (habAdd rfl)
  · exact False.elim (habAdd rfl)

/-- Prescribe the value at the unique real place by either keeping the
input character or multiplying it by the character of negative three. -/
noncomputable def absoluteCharacterWithRealValue
    (γ : Field.absoluteGaloisGroup ℚ →ₜ* Multiplicative (ZMod 2))
    (ε : Multiplicative (ZMod 2)) :
    Field.absoluteGaloisGroup ℚ →ₜ* Multiplicative (ZMod 2) :=
  if γ (absoluteInfinitePlaceArtinNegOne ℚ Rat.infinitePlace) = ε then γ
  else γ * negativeThreeCharacter

/-- The constructed character has the specified value on every real
Artin value of negative one over the rationals. -/
theorem absoluteCharacterWithRealValue_infinite
    (γ : Field.absoluteGaloisGroup ℚ →ₜ* Multiplicative (ZMod 2))
    (ε : Multiplicative (ZMod 2)) (v : InfinitePlace ℚ) :
    absoluteCharacterWithRealValue γ ε (absoluteInfinitePlaceArtinNegOne ℚ v) = ε := by
  rw [Subsingleton.elim v Rat.infinitePlace]
  by_cases h : γ (absoluteInfinitePlaceArtinNegOne ℚ Rat.infinitePlace) = ε
  · rw [absoluteCharacterWithRealValue, ite_eq_left h]
    exact h
  · rw [absoluteCharacterWithRealValue, ite_eq_right h, ContinuousMonoidHom.mul_apply]
    exact quadratic_mul_eq_of_ne
      (γ (absoluteInfinitePlaceArtinNegOne ℚ Rat.infinitePlace)) ε
      (negativeThreeCharacter (absoluteInfinitePlaceArtinNegOne ℚ Rat.infinitePlace)) h
      (negativeThreeCharacter_infinite Rat.infinitePlace)

/-- Prescribing the real value preserves the original character on
absolute inertia away from three, including at the prime two. -/
theorem absoluteCharacterWithRealValue_inertia
    (γ : Field.absoluteGaloisGroup ℚ →ₜ* Multiplicative (ZMod 2))
    (ε : Multiplicative (ZMod 2)) (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : v ≠ (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm
      (⟨3, Nat.prime_three⟩ : Nat.Primes))
    (σ : finitePlaceAbsoluteInertiaSubgroup ℚ v) :
    absoluteCharacterWithRealValue γ ε
        (finitePlaceAbsoluteDecompositionInclusion ℚ v
          (finitePlaceAbsoluteInertiaInclusion ℚ v σ)) =
      γ (finitePlaceAbsoluteDecompositionInclusion ℚ v
        (finitePlaceAbsoluteInertiaInclusion ℚ v σ)) := by
  by_cases h : γ (absoluteInfinitePlaceArtinNegOne ℚ Rat.infinitePlace) = ε
  · rw [absoluteCharacterWithRealValue, ite_eq_left h]
  · rw [absoluteCharacterWithRealValue, ite_eq_right h, ContinuousMonoidHom.mul_apply,
      negativeThreeCharacter_inertia v hv σ, mul_one]

end ClassFieldTower.Sawin
