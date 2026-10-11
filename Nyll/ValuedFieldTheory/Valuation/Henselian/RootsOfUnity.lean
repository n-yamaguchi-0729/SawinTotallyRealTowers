/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic

/-!
# Roots of unity in valuation rings

Reduction on roots of unity of order invertible in the residue field is
injective and, for a Henselian valuation ring, surjective. Roots of nonzero
order in the field also belong to the valuation ring.
-/

namespace ValuationSubring

variable {K : Type*} [Field K] (A : ValuationSubring K)

/-- Reduction is injective on roots with order invertible in the residue field. -/
theorem rootsOfUnityReduction_injective
    (n : ℕ) [NeZero (n : IsLocalRing.ResidueField A)] :
    Function.Injective (restrictRootsOfUnity (IsLocalRing.residue A) n) := by
  intro x y hxy
  have hres : IsLocalRing.residue A ((x : Aˣ) : A) =
      IsLocalRing.residue A ((y : Aˣ) : A) :=
    congrArg (fun z : rootsOfUnity n (IsLocalRing.ResidueField A) =>
      ((z : (IsLocalRing.ResidueField A)ˣ) : IsLocalRing.ResidueField A)) hxy
  have hdiff : ¬ IsUnit (((x : Aˣ) : A) - ((y : Aˣ) : A)) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_sub, hres, sub_self]
    exact not_not_intro rfl
  have hn : IsUnit (n : A) :=
    (IsLocalRing.residue_ne_zero_iff_isUnit (n : A)).mp
      (by simpa only [map_natCast] using NeZero.ne (n : IsLocalRing.ResidueField A))
  have hder : IsUnit (((Polynomial.X ^ n - 1 : Polynomial A).derivative).eval
      ((x : Aˣ) : A)) := by
    simpa only [Polynomial.derivative_sub, Polynomial.derivative_X_pow,
      Polynomial.derivative_one, sub_zero, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X] using hn.mul ((x : Aˣ).isUnit.pow (n-1))
  have heq := IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub
    ((mem_rootsOfUnity_iff_isRoot n (x : Aˣ)).mp x.property)
    ((mem_rootsOfUnity_iff_isRoot n (y : Aˣ)).mp y.property) hdiff hder
  exact rootsOfUnity.coe_injective heq

/-- Hensel's lemma lifts every prime-to-residue-characteristic root of unity. -/
theorem rootsOfUnityReduction_surjective
    [HenselianRing A (IsLocalRing.maximalIdeal A)]
    (n : ℕ) [NeZero (n : IsLocalRing.ResidueField A)] :
    Function.Surjective (restrictRootsOfUnity (IsLocalRing.residue A) n) := by
  have : NeZero n := .of_neZero_natCast (IsLocalRing.ResidueField A)
  intro y
  obtain ⟨a₀, ha₀⟩ := IsLocalRing.residue_surjective
    ((y : (IsLocalRing.ResidueField A)ˣ) : IsLocalRing.ResidueField A)
  let f : Polynomial A := Polynomial.X ^ n - 1
  have hroot : f.eval a₀ ∈ IsLocalRing.maximalIdeal A := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change IsLocalRing.residue A (f.eval a₀) = 0
    simp only [f, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_one, map_sub, map_pow, map_one, ha₀, sub_eq_zero]
    exact (mem_rootsOfUnity' n (y : (IsLocalRing.ResidueField A)ˣ)).mp y.property
  have hsimple : IsUnit
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) (f.derivative.eval a₀)) := by
    change IsUnit (IsLocalRing.residue A (f.derivative.eval a₀))
    apply isUnit_iff_ne_zero.mpr
    simp only [f, Polynomial.derivative_sub, Polynomial.derivative_X_pow,
      Polynomial.derivative_one, sub_zero, Polynomial.eval_mul,
      Polynomial.eval_natCast, Polynomial.eval_pow, Polynomial.eval_X, map_mul,
      map_natCast, map_pow, ha₀]
    exact mul_ne_zero (NeZero.ne (n : IsLocalRing.ResidueField A))
      (pow_ne_zero (n-1) (y : (IsLocalRing.ResidueField A)ˣ).ne_zero)
  obtain ⟨a, haroot, ha⟩ := HenselianRing.is_henselian f
    (Polynomial.monic_X_pow_sub_C 1 (NeZero.ne n)) a₀ hroot hsimple
  have hapow : a ^ n = 1 := by
    simpa only [f, Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_one, sub_eq_zero] using haroot
  refine ⟨rootsOfUnity.mkOfPowEq a hapow, ?_⟩
  apply rootsOfUnity.coe_injective
  have hared : IsLocalRing.residue A (a - a₀) = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).mpr ha
  rw [map_sub, ha₀, sub_eq_zero] at hared
  exact hared

/-- All field roots of nonzero order belong to a valuation ring. -/
theorem rootsOfUnity_toField_bijective (n : ℕ) [NeZero n] :
    Function.Bijective (restrictRootsOfUnity (algebraMap A K) n) := by
  constructor
  · intro x y hxy
    apply rootsOfUnity.coe_injective
    apply Subtype.ext
    exact congrArg (fun z : rootsOfUnity n K => ((z : Kˣ) : K)) hxy
  · intro ζ
    have hpow : ((ζ : Kˣ) : K) ^ n = 1 :=
      (mem_rootsOfUnity' n (ζ : Kˣ)).mp ζ.property
    have hvalpow : A.valuation ((ζ : Kˣ) : K) ^ n = 1 := by
      rw [← map_pow, hpow, map_one]
    have hval : A.valuation ((ζ : Kˣ) : K) = 1 :=
      (pow_eq_one_iff_of_nonneg zero_le (NeZero.ne n)).mp hvalpow
    let a : A := ⟨((ζ : Kˣ) : K), by
      exact (A.valuation_le_one_iff _).mp hval.le⟩
    have hapow : a ^ n = 1 := Subtype.ext hpow
    refine ⟨rootsOfUnity.mkOfPowEq a hapow, ?_⟩
    apply rootsOfUnity.coe_injective
    rfl

end ValuationSubring
