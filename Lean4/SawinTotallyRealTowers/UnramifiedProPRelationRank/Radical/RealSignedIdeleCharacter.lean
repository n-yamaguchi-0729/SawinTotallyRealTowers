/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.IdeleIntegralCharacterRadical
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.IdealPowerRadical
import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.Core
import ClassFieldTheory.AlgebraicNumberTheory.Idele.IdealMap
import ClassFieldTheory.AlgebraicNumberTheory.Idele.NormApproximation.InfinitePlaces
import ClassFieldTheory.AlgebraicNumberTheory.Idele.SinglePlace
import ClassFieldTheory.AlgebraicNumberTheory.RayClass.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Prod
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Instances.ZMod

set_option autoImplicit false

/-!
# Real-sign-trivial quadratic idele characters

Positive real units and all complex units have square roots. A quadratic
character killing the real sign generators therefore kills every infinite
idele. Finite integral-unit triviality then kills integral ideles and the
principal ideles of the ideal-square radical, by the actual ideal map.
-/

open NumberField IsDedekindDomain
open scoped NumberField BigOperators Classical

namespace ClassFieldTower.Martinet.Shafarevich

variable (F : Type) [Field F] [NumberField F]

private theorem ideleCharacter_two_positive_eq_one
    (chi : IdeleGroup F →* Multiplicative (ZMod 2))
    (v : InfinitePlace F) (a : v.Completionˣ)
    (ha : a ∈ RayClass.infinitePositiveSubgroup v) :
    chi (IdeleGroup.infinitePlaceIdele v a) = 1 := by
  obtain ⟨b, hb⟩ := exists_infinitePositiveSubgroup_nthRoot v 2 (by decide) a ha
  rw [← hb, map_pow, map_pow]
  exact multiplicativeZMod_pow_eq_one (2 : ℕ+) _

/-- Killing the real sign generator kills the whole corresponding local factor;
at a complex place the square-root construction requires no sign condition. -/
theorem ideleCharacter_two_infinitePlace_eq_one
    (chi : IdeleGroup F →* Multiplicative (ZMod 2))
    (v : InfinitePlace F)
    (hsign : v.IsReal → chi (IdeleGroup.infinitePlaceIdele v (-1)) = 1)
    (a : v.Completionˣ) : chi (IdeleGroup.infinitePlaceIdele v a) = 1 := by
  by_cases hv : v.IsReal
  · let e : v.Completion →+* ℝ :=
      InfinitePlace.Completion.extensionEmbeddingOfIsReal hv
    have hne : e (a : v.Completion) ≠ 0 :=
      fun h ↦ a.ne_zero (e.injective (h.trans (map_zero e).symm))
    by_cases hpos : 0 < e (a : v.Completion)
    · apply ideleCharacter_two_positive_eq_one F chi v a
      rw [RayClass.mem_infinitePositiveSubgroup_iff]
      intro hv'
      exact hpos
    · have hneg : e (a : v.Completion) < 0 :=
        lt_of_le_of_ne (le_of_not_gt hpos) hne
      have hpositive : -a ∈ RayClass.infinitePositiveSubgroup v := by
        rw [RayClass.mem_infinitePositiveSubgroup_iff]
        intro hv'
        change 0 < e (↑(-a) : v.Completion)
        simpa only [Units.val_neg, map_neg, neg_pos] using hneg
      have ha : a = (-1 : v.Completionˣ) * -a := by
        rw [neg_one_mul, neg_neg]
      rw [ha, map_mul, map_mul, hsign hv,
        ideleCharacter_two_positive_eq_one F chi v (-a) hpositive, one_mul]
  · apply ideleCharacter_two_positive_eq_one F chi v a
    rw [RayClass.mem_infinitePositiveSubgroup_iff]
    exact fun hreal ↦ (hv hreal).elim

/-- A quadratic idele character trivial on all real signs kills every infinite idele. -/
theorem ideleCharacter_two_infinite_eq_one
    (chi : IdeleGroup F →ₜ* Multiplicative (ZMod 2))
    (hsign : ∀ v : InfinitePlace F, v.IsReal →
      chi (IdeleGroup.infinitePlaceIdele v (-1)) = 1)
    (a : InfiniteIdeleGroup F) : chi (a, 1) = 1 := by
  let e : InfiniteIdeleGroup F ≃ₜ* (∀ v : InfinitePlace F, v.Completionˣ) :=
    ContinuousMulEquiv.piUnits
  let f : (∀ v : InfinitePlace F, v.Completionˣ) →* IdeleGroup F :=
    e.symm.toMonoidHom.prod (1 : (∀ v : InfinitePlace F, v.Completionˣ) →*
      FiniteIdeleGroup F)
  have hfa : f (e a) = (a, 1) := by
    apply Prod.ext
    · exact e.symm_apply_apply a
    · rfl
  rw [← hfa, ← Finset.univ_prod_mulSingle (e a), map_prod, map_prod]
  apply Finset.prod_eq_one
  intro v hv
  change chi (IdeleGroup.infinitePlaceIdele v (e a v)) = 1
  exact ideleCharacter_two_infinitePlace_eq_one F chi.toMonoidHom v (hsign v) (e a v)

/-- Real-sign and finite integral-unit triviality kill the full integral idele subgroup. -/
theorem ideleCharacter_two_integral_eq_one
    (chi : IdeleGroup F →ₜ* Multiplicative (ZMod 2))
    (hsign : ∀ v : InfinitePlace F, v.IsReal →
      chi (IdeleGroup.infinitePlaceIdele v (-1)) = 1)
    (hfinite : ∀ (v : HeightOneSpectrum (𝓞 F)) (a : (v.adicCompletion F)ˣ),
      a ∈ (v.adicCompletionIntegers F).units → chi (IdeleGroup.finitePlaceIdele v a) = 1)
    (a : IdeleGroup F) (ha : a ∈ IdeleGroup.integralAtFinitePlaces (K := F)) :
    chi a = 1 := by
  let u : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletionIntegers F).units :=
    fun v ↦ ⟨a.2 v, ha v⟩
  have hfin := ideleCharacter_integralFinite_eq_one F (2 : ℕ+) chi hfinite u
  have hsplit : a = (a.1, 1) * integralFiniteIdeleContinuousHom F u := by
    apply Prod.ext
    · exact (mul_one _).symm
    · exact (one_mul _).symm
  rw [hsplit, map_mul, ideleCharacter_two_infinite_eq_one F chi hsign a.1, one_mul]
  exact hfin

/-- The actual fractional-ideal map then kills principal ideles of ideal-square
radical elements, with no oddness assumption. -/
theorem ideleCharacter_two_principal_radical_eq_one_of_integral_local
    (chi : IdeleGroup F →ₜ* Multiplicative (ZMod 2))
    (hsign : ∀ v : InfinitePlace F, v.IsReal →
      chi (IdeleGroup.infinitePlaceIdele v (-1)) = 1)
    (hfinite : ∀ (v : HeightOneSpectrum (𝓞 F)) (a : (v.adicCompletion F)ˣ),
      a ∈ (v.adicCompletionIntegers F).units → chi (IdeleGroup.finitePlaceIdele v a) = 1)
    (a : (idealNthPowerRadicalKummerSubgroup F (2 : ℕ+)).1) :
    chi (IdeleGroup.principalIdele F a.1) = 1 := by
  obtain ⟨b, hb⟩ := IdeleGroup.fractionalIdeal_surjective (K := F)
    (idealNthRoot F (2 : ℕ+) a)
  have hroot := idealNthRoot_pow F (2 : ℕ+) a
  have hint : IdeleGroup.principalIdele F a.1 / b ^ 2 ∈
      IdeleGroup.integralAtFinitePlaces (K := F) := by
    rw [← IdeleGroup.fractionalIdeal_ker, MonoidHom.mem_ker, map_div, map_pow,
      IdeleGroup.fractionalIdeal_principalIdele, hb]
    exact div_eq_one.mpr hroot.symm
  have h := ideleCharacter_two_integral_eq_one F chi hsign hfinite _ hint
  have hpow : chi b ^ (2 : ℕ) = 1 := multiplicativeZMod_pow_eq_one (2 : ℕ+) (chi b)
  rw [map_div, map_pow, hpow, div_one] at h
  exact h

end ClassFieldTower.Martinet.Shafarevich
