/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.Henselian.SimpleRootFactorization
import Nyll.ValuedFieldTheory.Valuation.Henselian.Core
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Simple roots of nonmonic polynomials over Henselian valuation rings

A simple residual root gives a coprime linear factor. Primitive factor
lifting produces an actual factor of degree one. Its leading coefficient
reduces to one, so it is a unit and its linear root belongs to the valuation ring.
-/

namespace DiscreteValuationField

open ValuationTheory.DiscreteValuationField

variable {K : Type*} [Field K] (V : ValuationSubring K)
  [HenselianRing V (IsLocalRing.maximalIdeal V)]

/-- A simple residual root lifts for an arbitrary polynomial over a Henselian
valuation ring. No monicity or completeness assumption is needed. -/
theorem exists_root_of_henselianRing_of_simpleRoot_mod
    (f : Polynomial V) (a₀ : V)
    (hroot : f.eval a₀ ∈ IsLocalRing.maximalIdeal V)
    (hsimple : IsUnit
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal V) (f.derivative.eval a₀))) :
    ∃ a : V, f.IsRoot a ∧ a - a₀ ∈ IsLocalRing.maximalIdeal V := by
  let fbar : Polynomial (IsLocalRing.ResidueField V) :=
    f.map (IsLocalRing.residue V)
  let abar : IsLocalRing.ResidueField V := IsLocalRing.residue V a₀
  let lbar : Polynomial (IsLocalRing.ResidueField V) :=
    Polynomial.X - Polynomial.C abar
  let qbar : Polynomial (IsLocalRing.ResidueField V) := fbar /ₘ lbar
  have hderivative : IsUnit (fbar.derivative.eval abar) :=
    derivative_isUnit_map_quotient_mk_of_simpleRoot_mod hsimple
  have hfbar : fbar ≠ 0 := by
    intro hzero
    rw [hzero, Polynomial.derivative_zero, Polynomial.eval_zero] at hderivative
    exact not_isUnit_zero hderivative
  have hresidual : fbar = lbar * qbar :=
    (residual_X_sub_C_mul_divByMonic_eq_map_of_eval_mem hroot).symm
  have hcoprime : IsCoprime lbar qbar :=
    isCoprime_residual_X_sub_C_divByMonic_of_simpleRoot_mod hsimple
  obtain ⟨G, H, hGdegree, _, hfactor, hGmap, _⟩ :=
    henselFactorization_of_henselianRing V hfbar hresidual hcoprime
  have hGdegreeOne : G.natDegree = 1 := by
    rw [hGdegree]
    exact Polynomial.natDegree_X_sub_C abar
  have hGcoeffOne : IsLocalRing.residue V (G.coeff 1) = 1 := by
    have hcoeff := congrArg (fun p : Polynomial (IsLocalRing.ResidueField V) =>
      p.coeff 1) hGmap
    simpa only [lbar, Polynomial.coeff_map, Polynomial.coeff_sub,
      Polynomial.coeff_X_one, Polynomial.coeff_C_succ, sub_zero] using hcoeff
  have hGunit : IsUnit (G.coeff 1) :=
    isUnit_of_map_unit (IsLocalRing.residue V) (G.coeff 1)
      (hGcoeffOne.symm ▸ isUnit_one)
  obtain ⟨u, hu⟩ := hGunit
  let a : V := -(↑u⁻¹ * G.coeff 0)
  have hGa : G.eval a = 0 := by
    rw [Polynomial.eq_X_add_C_of_natDegree_le_one hGdegreeOne.le,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_C, ← hu]
    dsimp only [a]
    rw [mul_neg, ← mul_assoc, u.mul_inv, one_mul, neg_add_cancel]
  have haRoot : f.IsRoot a := by
    rw [hfactor, Polynomial.IsRoot, Polynomial.eval_mul, hGa, zero_mul]
  have hmapRoot :
      (G.map (IsLocalRing.residue V)).eval (IsLocalRing.residue V a) = 0 := by
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, hGa, map_zero]
  have haresidue : IsLocalRing.residue V a = abar := by
    rw [hGmap] at hmapRoot
    simpa only [lbar, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C, sub_eq_zero] using hmapRoot
  refine ⟨a, haRoot, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  change IsLocalRing.residue V (a - a₀) = 0
  rw [map_sub, haresidue, sub_self]

end DiscreteValuationField
