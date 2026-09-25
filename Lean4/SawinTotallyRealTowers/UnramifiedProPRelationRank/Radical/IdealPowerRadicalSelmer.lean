/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.IdealPowerRadical
import Mathlib.RingTheory.DedekindDomain.SelmerGroup

set_option autoImplicit false
/-!
# The empty-support Selmer interpretation of the ideal-power radical

This file identifies the ideal-power condition on a principal fractional
ideal with the empty-support Selmer condition on its Kummer class.
-/

open scoped NumberField nonZeroDivisors WithZero
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open KummerTheory

variable (K : Type*) [Field K] [NumberField K]

private theorem count_toPrincipalIdeal_eq_neg_valuationOfNeZero
    (a : Kˣ) (v : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K v
        ((toPrincipalIdeal (𝓞 K) K a : FractionalIdealGroup K) :
          FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      -(v.valuationOfNeZero a).toAdd := by
  rw [IdeleGroup.count_toPrincipalIdeal]
  have h := congrArg WithZero.log (v.valuationOfNeZero_eq a)
  congr 1
  calc
    WithZero.log (v.valuation K (a : K)) =
        WithZero.log
          ((v.valuationOfNeZero a : Multiplicative ℤ) : ℤᵐ⁰) := h.symm
    _ = (v.valuationOfNeZero a).toAdd := by
      change WithZero.log
        (WithZero.exp (v.valuationOfNeZero a).toAdd) = _
      exact WithZero.log_exp _

private theorem valuationOfNeZeroMod_mk_eq_one_iff
    (n : ℕ+) (a : Kˣ) (v : HeightOneSpectrum (𝓞 K)) :
    v.valuationOfNeZeroMod (n : ℕ)
        (QuotientGroup.mk'
          (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range a) = 1 ↔
      (n : ℤ) ∣ (v.valuationOfNeZero a).toAdd := by
  erw [HeightOneSpectrum.valuationOfNeZeroMod, MonoidHom.comp_apply,
    QuotientGroup.map_mk' (G := Kˣ)
      (N := MonoidHom.range (powMonoidHom (n : ℕ)))]
  change
    ((v.valuationOfNeZero a).toAdd : ZMod (n : ℕ)) = 0 ↔ _
  exact ZMod.intCast_zmod_eq_zero_iff_dvd _ _

/-- A field unit lies in the ideal-power radical exactly when all finite
valuations are divisible by the exponent. -/
theorem mem_idealNthPowerRadicalKummerSubgroup_iff_valuation
    (n : ℕ+) (a : Kˣ) :
    a ∈ (idealNthPowerRadicalKummerSubgroup K n).1 ↔
      ∀ v : HeightOneSpectrum (𝓞 K),
        (n : ℤ) ∣ (v.valuationOfNeZero a).toAdd := by
  constructor
  · rintro ⟨I, hI⟩ v
    rw [powMonoidHom_apply] at hI
    have hcount :
        (n : ℤ) * FractionalIdeal.count K v
            (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
          -(v.valuationOfNeZero a).toAdd := by
      calc
        _ = FractionalIdeal.count K v
            ((I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^
              (n : ℕ)) := by
                rw [FractionalIdeal.count_pow]
        _ = FractionalIdeal.count K v
            ((toPrincipalIdeal (𝓞 K) K a : FractionalIdealGroup K) :
              FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
                rw [← Units.val_pow_eq_pow_val, hI]
        _ = _ := count_toPrincipalIdeal_eq_neg_valuationOfNeZero K a v
    have hneg : (n : ℤ) ∣ -(v.valuationOfNeZero a).toAdd :=
      ⟨_, hcount.symm⟩
    simpa using hneg
  · intro h
    let c := FractionalIdealGroup.countVector
      (toPrincipalIdeal (𝓞 K) K a)
    let d := c.mapRange (fun z : ℤ ↦ z / (n : ℤ)) (by simp)
    refine ⟨FractionalIdealGroup.factorization
      (K := K) (Multiplicative.ofAdd d), ?_⟩
    apply FractionalIdealGroup.ext_count
    intro v
    rw [powMonoidHom_apply, Units.val_pow_eq_pow_val,
      FractionalIdeal.count_pow,
      FractionalIdealGroup.count_factorization]
    change (n : ℤ) * (c v / (n : ℤ)) =
      FractionalIdeal.count K v
        ((toPrincipalIdeal (𝓞 K) K a : FractionalIdealGroup K) :
          FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
    have hc : (n : ℤ) ∣ c v := by
      rw [FractionalIdealGroup.countVector_apply,
        count_toPrincipalIdeal_eq_neg_valuationOfNeZero K]
      simpa using h v
    exact Int.mul_ediv_cancel' hc

/-- The empty-support Selmer group, with all finite valuations constrained. -/
abbrev EmptySupportSelmerGroup (n : ℕ+) :=
  IsDedekindDomain.selmerGroup
    (R := 𝓞 K) (K := K)
    (S := (∅ : Set (HeightOneSpectrum (𝓞 K)))) (n := (n : ℕ))

private noncomputable def idealRadicalRepresentativeToEmptySelmer
    (n : ℕ+) :
    (idealNthPowerRadicalKummerSubgroup K n).1 →*
      EmptySupportSelmerGroup K n where
  toFun a := ⟨QuotientGroup.mk'
      (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range a.1, by
    intro v _
    exact (valuationOfNeZeroMod_mk_eq_one_iff K n a.1 v).2
      ((mem_idealNthPowerRadicalKummerSubgroup_iff_valuation
        K n a.1).1 a.property v)⟩
  map_one' := by
    apply Subtype.ext
    exact map_one _
  map_mul' a b := by
    apply Subtype.ext
    exact map_mul
      (QuotientGroup.mk'
        (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range) a.1 b.1

private theorem restrictedNthPowers_le_ker_representativeToEmptySelmer
    (n : ℕ+) :
    restrictedNthPowersSubgroup n
        (idealNthPowerRadicalKummerSubgroup K n) ≤
      MonoidHom.ker (idealRadicalRepresentativeToEmptySelmer K n) := by
  intro a ha
  rw [MonoidHom.mem_ker]
  obtain ⟨b, hb⟩ :=
    (mem_restrictedNthPowersSubgroup_iff n
      (idealNthPowerRadicalKummerSubgroup K n)).mp ha
  apply Subtype.ext
  apply (QuotientGroup.eq_one_iff _).2
  exact ⟨b, by simpa only [powMonoidHom_apply] using hb⟩

/-- The canonical comparison from the ideal-power radical quotient to the
empty-support Selmer group. -/
noncomputable def idealNthPowerRadicalQuotientToEmptySelmer
    (n : ℕ+) :
    IdealNthPowerRadicalQuotient K n →*
      EmptySupportSelmerGroup K n :=
  restrictedRadicalQuotientLift n
    (idealNthPowerRadicalKummerSubgroup K n)
    (idealRadicalRepresentativeToEmptySelmer K n)
    (restrictedNthPowers_le_ker_representativeToEmptySelmer K n)

@[simp]
theorem idealNthPowerRadicalQuotientToEmptySelmer_mk
    (n : ℕ+)
    (a : (idealNthPowerRadicalKummerSubgroup K n).1) :
    idealNthPowerRadicalQuotientToEmptySelmer K n
        (restrictedRadicalQuotientMk n
          (idealNthPowerRadicalKummerSubgroup K n) a) =
      idealRadicalRepresentativeToEmptySelmer K n a :=
  restrictedRadicalQuotientLift_mk n
    (idealNthPowerRadicalKummerSubgroup K n)
    (idealRadicalRepresentativeToEmptySelmer K n)
    (restrictedNthPowers_le_ker_representativeToEmptySelmer K n) a

theorem idealNthPowerRadicalQuotientToEmptySelmer_injective
    (n : ℕ+) :
    Function.Injective
      (idealNthPowerRadicalQuotientToEmptySelmer K n) := by
  intro q r hqr
  obtain ⟨a, rfl⟩ := restrictedRadicalQuotientMk_surjective n
    (idealNthPowerRadicalKummerSubgroup K n) q
  obtain ⟨b, rfl⟩ := restrictedRadicalQuotientMk_surjective n
    (idealNthPowerRadicalKummerSubgroup K n) r
  apply (restrictedRadicalQuotientMk_eq_iff n
    (idealNthPowerRadicalKummerSubgroup K n) a b).2
  apply (mem_restrictedNthPowersSubgroup_iff n
    (idealNthPowerRadicalKummerSubgroup K n)).2
  have hquot :
      QuotientGroup.mk'
          (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range a.1 =
        QuotientGroup.mk'
          (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range b.1 :=
    congrArg Subtype.val hqr
  obtain ⟨c, hc⟩ := (QuotientGroup.eq_iff_div_mem.mp hquot)
  refine ⟨c, ?_⟩
  change c ^ (n : ℕ) = a.1 / b.1
  simpa only [powMonoidHom_apply] using hc

theorem idealNthPowerRadicalQuotientToEmptySelmer_surjective
    (n : ℕ+) :
    Function.Surjective
      (idealNthPowerRadicalQuotientToEmptySelmer K n) := by
  intro x
  obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective
    (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range x.1
  have hval : ∀ v : HeightOneSpectrum (𝓞 K),
      (n : ℤ) ∣ (v.valuationOfNeZero a).toAdd := by
    intro v
    apply (valuationOfNeZeroMod_mk_eq_one_iff K n a v).1
    rw [ha]
    exact x.property v (Set.notMem_empty v)
  let aRad : (idealNthPowerRadicalKummerSubgroup K n).1 :=
    ⟨a, (mem_idealNthPowerRadicalKummerSubgroup_iff_valuation K n a).2 hval⟩
  refine ⟨restrictedRadicalQuotientMk n
    (idealNthPowerRadicalKummerSubgroup K n) aRad, ?_⟩
  apply Subtype.ext
  exact ha

/-- The ideal-power radical quotient is canonically the empty-support
Selmer group. -/
noncomputable def idealNthPowerRadicalQuotientEquivEmptySelmer
    (n : ℕ+) :
    IdealNthPowerRadicalQuotient K n ≃*
      EmptySupportSelmerGroup K n :=
  MulEquiv.ofBijective
    (idealNthPowerRadicalQuotientToEmptySelmer K n)
    ⟨idealNthPowerRadicalQuotientToEmptySelmer_injective K n,
      idealNthPowerRadicalQuotientToEmptySelmer_surjective K n⟩

end ClassFieldTower.Martinet.Shafarevich
