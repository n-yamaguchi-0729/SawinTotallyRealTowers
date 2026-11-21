/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.ClassGroup.Basic

/-! # Principal fractional ideals, prime counts, and the class quotient -/

@[expose] public section

open IsDedekindDomain
open scoped WithZero

noncomputable section

universe u v

variable {R : Type u} {F : Type v} [CommRing R] [IsDedekindDomain R]
  [Field F] [Algebra R F] [IsFractionRing R F]

/-- The exponent of a prime in a principal fractional ideal is the additive
form of the corresponding normalized finite-place valuation. -/
theorem FractionalIdeal.count_toPrincipalIdeal (x : Fˣ)
    (v : HeightOneSpectrum R) :
    FractionalIdeal.count F v
        ((toPrincipalIdeal R F x : (FractionalIdeal (nonZeroDivisors R) F)ˣ) :
          FractionalIdeal (nonZeroDivisors R) F) =
      -WithZero.log (v.valuation F (x : F)) := by
  obtain ⟨⟨n, d, hd⟩, hnd⟩ :=
    IsLocalization.surj (nonZeroDivisors R) (x : F)
  let d' : nonZeroDivisors R := ⟨d, hd⟩
  have hx :
      (x : F) = IsLocalization.mk' F n d' :=
    IsLocalization.eq_mk'_iff_mul_eq.mpr hnd
  have hn : n ≠ 0 := by
    intro hn
    have : (x : F) = 0 := by
      rw [hx, hn, IsFractionRing.mk'_eq_div, map_zero, zero_div]
    exact x.ne_zero this
  have hspan :
      (toPrincipalIdeal R F x :
          FractionalIdeal (nonZeroDivisors R) F) =
        FractionalIdeal.spanSingleton (nonZeroDivisors R)
            ((algebraMap R F) d)⁻¹ *
          (Ideal.span {n} :
            FractionalIdeal (nonZeroDivisors R) F) := by
    rw [coe_toPrincipalIdeal, hx,
      FractionalIdeal.coeIdeal_span_singleton,
      ← map_mul (FractionalIdeal.spanSingleton (nonZeroDivisors R)),
      IsFractionRing.mk'_eq_div, div_eq_mul_inv, mul_comm]
  rw [FractionalIdeal.count_well_defined F v
      (Units.ne_zero (toPrincipalIdeal R F x)) hspan,
    hx, v.valuation_of_mk']
  rw [v.intValuation_if_neg hn,
    v.intValuation_if_neg (nonZeroDivisors.coe_ne_zero d')]
  simp only [d', ← WithZero.exp_sub, WithZero.log_exp, sub_eq_add_neg,
    neg_add_rev, neg_neg, add_comm]

/-- A fractional ideal has trivial class precisely when it is a principal ideal. -/
theorem ClassGroup.mk_eq_one_iff_mem_principal
    (I : (FractionalIdeal (nonZeroDivisors R) F)ˣ) :
    ClassGroup.mk F I = 1 ↔
      I ∈ (toPrincipalIdeal R F).range := by
  rw [← (ClassGroup.equiv F).injective.eq_iff, ClassGroup.equiv_mk]
  simp only [FractionalIdeal.canonicalEquiv_self, RingEquiv.coe_mulEquiv_refl, map_one]
  change (QuotientGroup.mk' (toPrincipalIdeal R F).range I = 1) ↔
    I ∈ (toPrincipalIdeal R F).range
  exact QuotientGroup.eq_one_iff (N := (toPrincipalIdeal R F).range) I
