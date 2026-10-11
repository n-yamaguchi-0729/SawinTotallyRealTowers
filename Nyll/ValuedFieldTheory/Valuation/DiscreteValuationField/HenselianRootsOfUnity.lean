/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.HenselLemma
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic

/-!
# Reduction of roots of unity over a Henselian DVF

If the root order is nonzero in the residue field, Hensel lifting and
uniqueness make reduction bijective on roots of unity. No completeness or
finiteness assumption on the residue field is needed.
-/

namespace ValuationTheory.DiscreteValuationField.HenselianDVF

universe u v

variable {K : Type u} [Field K] (F : HenselianDVF.{u, v} K)

/-- Reduction on the actual group of roots of unity in the valuation ring. -/
noncomputable def rootsOfUnityReduction (n : ℕ) :
    rootsOfUnity n F.valuationSubring →* rootsOfUnity n F.residueField :=
  restrictRootsOfUnity F.residueMap n

@[simp] theorem rootsOfUnityReduction_apply (n : ℕ)
    (ζ : rootsOfUnity n F.valuationSubring) :
    ((rootsOfUnityReduction F n ζ : F.residueFieldˣ) : F.residueField) =
      F.residueMap ((ζ : F.valuationSubringˣ) : F.valuationSubring) := rfl

private theorem rootPolynomial_derivative_isUnit
    (n : ℕ) [NeZero (n : F.residueField)] (a : F.valuationSubringˣ) :
    IsUnit (((Polynomial.X ^ n - 1 : Polynomial F.valuationSubring).derivative).eval
      (a : F.valuationSubring)) := by
  have hn : IsUnit (n : F.valuationSubring) :=
    (F.toDVF.residue_ne_zero_iff_isUnit (n : F.valuationSubring)).mp
      (by simpa only [map_natCast] using (NeZero.ne (n : F.residueField)))
  simpa only [Polynomial.derivative_sub, Polynomial.derivative_X_pow,
    Polynomial.derivative_one, sub_zero, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X] using hn.mul (a.isUnit.pow (n - 1))

/-- Reduction is injective when the root order is nonzero in the residue field. -/
theorem rootsOfUnityReduction_injective (n : ℕ) [NeZero (n : F.residueField)] :
    Function.Injective (rootsOfUnityReduction F n) := by
  intro x y hxy
  have hres : F.residueMap ((y : F.valuationSubringˣ) : F.valuationSubring) =
      F.residueMap ((x : F.valuationSubringˣ) : F.valuationSubring) :=
    congrArg (fun z : rootsOfUnity n F.residueField =>
      ((z : F.residueFieldˣ) : F.residueField)) hxy.symm
  have heq := F.eq_of_isRoot_of_isRoot_of_residue_eq_of_derivative_isUnit
    ((mem_rootsOfUnity_iff_isRoot n (x : F.valuationSubringˣ)).mp x.property)
    ((mem_rootsOfUnity_iff_isRoot n (y : F.valuationSubringˣ)).mp y.property)
    hres (rootPolynomial_derivative_isUnit F n (x : F.valuationSubringˣ))
  exact rootsOfUnity.coe_injective heq.symm

/-- Each residual root of unity lifts to an actual root in the valuation ring. -/
theorem rootsOfUnityReduction_surjective (n : ℕ) [NeZero (n : F.residueField)] :
    Function.Surjective (rootsOfUnityReduction F n) := by
  have : NeZero n := .of_neZero_natCast F.residueField
  intro y
  let f : Polynomial F.valuationSubring := Polynomial.X ^ n - 1
  have hf : f.Monic := Polynomial.monic_X_pow_sub_C 1 (NeZero.ne n)
  have hroot : (f.map F.residueMap).eval ((y : F.residueFieldˣ) : F.residueField) = 0 := by
    simpa only [f, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_one, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_one, sub_eq_zero] using
      (mem_rootsOfUnity' n (y : F.residueFieldˣ)).mp y.property
  have hsimple : ((f.map F.residueMap).derivative).eval
      ((y : F.residueFieldˣ) : F.residueField) ≠ 0 := by
    simpa only [f, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_one, Polynomial.derivative_sub, Polynomial.derivative_X_pow,
      Polynomial.derivative_one, sub_zero, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X] using
      mul_ne_zero (NeZero.ne (n : F.residueField))
        (pow_ne_zero (n - 1) (y : F.residueFieldˣ).ne_zero)
  obtain ⟨a, _q, haroot, hares, _⟩ :=
    F.exists_monic_linear_factor_lift_of_reduced_simple_root
      f hf ((y : F.residueFieldˣ) : F.residueField) hroot hsimple
  have hapow : a ^ n = 1 := by
    simpa only [f, Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_one, sub_eq_zero] using haroot
  refine ⟨rootsOfUnity.mkOfPowEq a hapow, ?_⟩
  apply rootsOfUnity.coe_injective
  exact hares

/-- Reduction is a bijection on roots whose order is invertible in the residue field. -/
theorem rootsOfUnityReduction_bijective (n : ℕ) [NeZero (n : F.residueField)] :
    Function.Bijective (rootsOfUnityReduction F n) :=
  ⟨rootsOfUnityReduction_injective F n, rootsOfUnityReduction_surjective F n⟩

/-- The multiplicative equivalence obtained from actual root reduction. -/
noncomputable def rootsOfUnityReductionEquiv (n : ℕ) [NeZero (n : F.residueField)] :
    rootsOfUnity n F.valuationSubring ≃* rootsOfUnity n F.residueField :=
  MulEquiv.ofBijective (rootsOfUnityReduction F n) (rootsOfUnityReduction_bijective F n)

@[simp] theorem rootsOfUnityReductionEquiv_apply (n : ℕ) [NeZero (n : F.residueField)]
    (ζ : rootsOfUnity n F.valuationSubring) :
    rootsOfUnityReductionEquiv F n ζ = rootsOfUnityReduction F n ζ := rfl

private theorem rootsOfUnity_toField_bijective (D : DVF.{u, v} K)
    (n : ℕ) [NeZero n] :
    Function.Bijective (restrictRootsOfUnity (algebraMap D.valuationSubring K) n) := by
  constructor
  · intro x y hxy
    apply rootsOfUnity.coe_injective
    apply Subtype.ext
    exact congrArg (fun z : rootsOfUnity n K => ((z : Kˣ) : K)) hxy
  · intro ζ
    have hpow : ((ζ : Kˣ) : K) ^ n = 1 :=
      (mem_rootsOfUnity' n (ζ : Kˣ)).mp ζ.property
    have hvalpow : D.valuation ((ζ : Kˣ) : K) ^ n = 1 := by
      rw [← map_pow, hpow, map_one]
    have hval : D.valuation ((ζ : Kˣ) : K) = 1 :=
      (pow_eq_one_iff_of_nonneg zero_le (NeZero.ne n)).mp hvalpow
    let a : D.valuationSubring := ⟨((ζ : Kˣ) : K), hval.le⟩
    have hapow : a ^ n = 1 := by
      apply Subtype.ext
      exact hpow
    refine ⟨rootsOfUnity.mkOfPowEq a hapow, ?_⟩
    apply rootsOfUnity.coe_injective
    rfl

private noncomputable def rootsOfUnityFieldEquiv (D : DVF.{u, v} K)
    (n : ℕ) [NeZero n] : rootsOfUnity n D.valuationSubring ≃* rootsOfUnity n K :=
  MulEquiv.ofBijective (restrictRootsOfUnity (algebraMap D.valuationSubring K) n)
    (rootsOfUnity_toField_bijective D n)

/-- Reduction identifies the actual field roots with the residue-field roots.
Every field root is first regarded as a valuation-ring unit. -/
noncomputable def fieldRootsOfUnityReductionEquiv
    (n : ℕ) [NeZero (n : F.residueField)] :
    rootsOfUnity n K ≃* rootsOfUnity n F.residueField :=
  let : NeZero n := .of_neZero_natCast F.residueField
  (rootsOfUnityFieldEquiv F.toDVF n).symm.trans (rootsOfUnityReductionEquiv F n)

/-- The field-root equivalence is the actual residue map on integral roots. -/
@[simp] theorem fieldRootsOfUnityReductionEquiv_toField
    (n : ℕ) [NeZero (n : F.residueField)] (ζ : rootsOfUnity n F.valuationSubring) :
    fieldRootsOfUnityReductionEquiv F n
        (restrictRootsOfUnity (algebraMap F.valuationSubring K) n ζ) =
      rootsOfUnityReduction F n ζ := by
  have : NeZero n := .of_neZero_natCast F.residueField
  change rootsOfUnityReductionEquiv F n
    ((rootsOfUnityFieldEquiv F.toDVF n).symm ((rootsOfUnityFieldEquiv F.toDVF n) ζ)) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

end ValuationTheory.DiscreteValuationField.HenselianDVF
