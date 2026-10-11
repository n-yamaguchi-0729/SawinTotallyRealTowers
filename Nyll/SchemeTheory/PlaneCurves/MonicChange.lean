/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.NoetherNormalization.LinearChange
import Nyll.SchemeTheory.PlaneCurves.MonicProjection
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# Monic linear representatives of plane curves

This file connects the linear normalization developed for Fried--Jarden,
Proposition 6.2.1, with the monic projection model.  Over an infinite field,
an invertible linear change of the two affine coordinates makes the leading
coefficient in the projection variable a unit.  Multiplication by that unit's
inverse then gives a monic equation defining the same principal ideal.
-/

noncomputable section

namespace FieldArithmetic
namespace Chapter06
namespace PlaneCurveMonicNormalization

open MvPolynomial Polynomial
open AffinePlaneCurve MonicPlaneCurveProjection

universe u

variable {K : Type u} [Field K]

/--
Conjugate the triangular change from `LinearNormalization` by the exchange of
the two plane coordinates.  In the `asPolynomialY` presentation this is
exactly `linearChangeFirst`.
-/
def linearChangeY (c : Fin 1 → K) :
    BivariatePolynomial K ≃ₐ[K] BivariatePolynomial K :=
  (MvPolynomial.renameEquiv K coordinateSwap).trans
    ((linearChangeFirstEquiv c).trans
      (MvPolynomial.renameEquiv K coordinateSwap).symm)

theorem rename_linearChangeY
    (c : Fin 1 → K) (f : BivariatePolynomial K) :
    MvPolynomial.rename coordinateSwap (linearChangeY c f) =
      linearChangeFirst c (MvPolynomial.rename coordinateSwap f) := by
  simp [linearChangeY, linearChangeFirstEquiv]

theorem yPolynomial_linearChangeY
    (c : Fin 1 → K) (f : BivariatePolynomial K) :
    yPolynomial (linearChangeY c f) =
      MvPolynomial.finSuccEquiv K 1
        (linearChangeFirst c (MvPolynomial.rename coordinateSwap f)) := by
  rw [yPolynomial, asPolynomialY_apply, rename_linearChangeY]

/--
Over an infinite field, an invertible linear change makes the leading
coefficient of the `Y`-polynomial a unit of `K[X]`.
-/
theorem exists_linearChangeY_leadingCoeff_isUnit
    [Infinite K] {f : BivariatePolynomial K} (hf : f ≠ 0) :
    ∃ c : Fin 1 → K,
      IsUnit (yPolynomial (linearChangeY c f)).leadingCoeff := by
  have hrename :
      MvPolynomial.rename coordinateSwap f ≠ 0 := by
    exact
      (MvPolynomial.renameEquiv K coordinateSwap).injective.ne hf
  obtain ⟨c, hc⟩ :=
    exists_linearChangeFirst_leadingCoeff_isUnit hrename
  exact ⟨c, by simpa [yPolynomial_linearChangeY] using hc⟩

theorem totalDegree_linearChangeFirst_le
    {n : ℕ} (c : Fin n → K)
    (f : MvPolynomial (Fin (n + 1)) K) :
    (linearChangeFirst c f).totalDegree ≤ f.totalDegree := by
  have hsum :
      (∑ i ∈ Finset.range (f.totalDegree + 1),
          homogeneousComponent i f) = f := by
    simpa using (sum_homogeneousComponent (φ := f))
  calc
    (linearChangeFirst c f).totalDegree =
        (linearChangeFirst c
          (∑ i ∈ Finset.range (f.totalDegree + 1),
            homogeneousComponent i f)).totalDegree := by
      rw [hsum]
    _ =
        (∑ i ∈ Finset.range (f.totalDegree + 1),
          linearChangeFirst c (homogeneousComponent i f)).totalDegree := by
      rw [map_sum]
    _ ≤ f.totalDegree := by
      apply totalDegree_finsetSum_le
      intro i hi
      exact
        (linearChangeFirst_isHomogeneous c
          (homogeneousComponent_isHomogeneous i f)).totalDegree_le.trans
          (Nat.le_of_lt_succ (Finset.mem_range.mp hi))

theorem totalDegree_linearChangeFirst
    {n : ℕ} (c : Fin n → K)
    (f : MvPolynomial (Fin (n + 1)) K) :
    (linearChangeFirst c f).totalDegree = f.totalDegree := by
  apply le_antisymm
  · exact totalDegree_linearChangeFirst_le c f
  · have h :=
      totalDegree_linearChangeFirst_le (-c) (linearChangeFirst c f)
    have hinv :
        linearChangeFirst (-c) (linearChangeFirst c f) = f := by
      have hcomp := congrArg
        (fun φ :
          MvPolynomial (Fin (n + 1)) K →ₐ[K]
            MvPolynomial (Fin (n + 1)) K => φ f)
        (linearChangeFirst_comp_neg (-c))
      simpa using hcomp
    rw [hinv] at h
    exact h

theorem totalDegree_linearChangeY
    (c : Fin 1 → K) (f : BivariatePolynomial K) :
    (linearChangeY c f).totalDegree = f.totalDegree := by
  calc
    (linearChangeY c f).totalDegree =
        (MvPolynomial.rename coordinateSwap
          (linearChangeY c f)).totalDegree :=
      (MvPolynomial.totalDegree_renameEquiv coordinateSwap _).symm
    _ =
        (linearChangeFirst c
          (MvPolynomial.rename coordinateSwap f)).totalDegree := by
      rw [rename_linearChangeY]
    _ = (MvPolynomial.rename coordinateSwap f).totalDegree :=
      totalDegree_linearChangeFirst c _
    _ = f.totalDegree :=
      MvPolynomial.totalDegree_renameEquiv coordinateSwap f

/--
Multiply a polynomial by the inverse of its unit leading coefficient.
-/
def normalizeLeadingUnit
    (p : Polynomial (ProjectionBase K)) (h : IsUnit p.leadingCoeff) :
    Polynomial (ProjectionBase K) :=
  Polynomial.C (↑(h.unit⁻¹) : ProjectionBase K) * p

theorem normalizeLeadingUnit_monic
    (p : Polynomial (ProjectionBase K)) (h : IsUnit p.leadingCoeff) :
    (normalizeLeadingUnit p h).Monic := by
  rw [Polynomial.Monic, normalizeLeadingUnit,
    Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
  change
    (↑(h.unit⁻¹) : ProjectionBase K) * p.leadingCoeff = 1
  exact Units.inv_mul h.unit

theorem normalizeLeadingUnit_associated
    (p : Polynomial (ProjectionBase K)) (h : IsUnit p.leadingCoeff) :
    Associated (normalizeLeadingUnit p h) p := by
  apply associated_unit_mul_left
  exact (h.unit⁻¹).isUnit.map Polynomial.C

/--
The monic plane equation obtained from a chosen linear change whose leading
coefficient is a unit.
-/
def monicRepresentative
    (f : BivariatePolynomial K) (c : Fin 1 → K)
    (h : IsUnit (yPolynomial (linearChangeY c f)).leadingCoeff) :
    BivariatePolynomial K :=
  (asPolynomialY (K := K)).symm
    (normalizeLeadingUnit (yPolynomial (linearChangeY c f)) h)

@[simp]
theorem yPolynomial_monicRepresentative
    (f : BivariatePolynomial K) (c : Fin 1 → K)
    (h : IsUnit (yPolynomial (linearChangeY c f)).leadingCoeff) :
    yPolynomial (monicRepresentative f c h) =
      normalizeLeadingUnit (yPolynomial (linearChangeY c f)) h := by
  exact (asPolynomialY (K := K)).apply_symm_apply _

theorem monicRepresentative_monic
    (f : BivariatePolynomial K) (c : Fin 1 → K)
    (h : IsUnit (yPolynomial (linearChangeY c f)).leadingCoeff) :
    (yPolynomial (monicRepresentative f c h)).Monic := by
  rw [yPolynomial_monicRepresentative]
  exact normalizeLeadingUnit_monic _ h

theorem monicRepresentative_associated
    (f : BivariatePolynomial K) (c : Fin 1 → K)
    (h : IsUnit (yPolynomial (linearChangeY c f)).leadingCoeff) :
    Associated (monicRepresentative f c h) (linearChangeY c f) := by
  have hback :
      (asPolynomialY (K := K)).symm
          (yPolynomial (linearChangeY c f)) =
        linearChangeY c f := by
    exact (asPolynomialY (K := K)).symm_apply_apply _
  have ha :=
    Associated.map (asPolynomialY (K := K)).symm
      (normalizeLeadingUnit_associated
        (yPolynomial (linearChangeY c f)) h)
  rw [hback] at ha
  exact ha

theorem equationIdeal_monicRepresentative
    (f : BivariatePolynomial K) (c : Fin 1 → K)
    (h : IsUnit (yPolynomial (linearChangeY c f)).leadingCoeff) :
    equationIdeal (monicRepresentative f c h) =
      equationIdeal (linearChangeY c f) := by
  exact
    Ideal.span_singleton_eq_span_singleton.mpr
      (monicRepresentative_associated f c h)

theorem map_equationIdeal_linearChangeY
    (f : BivariatePolynomial K) (c : Fin 1 → K) :
    (equationIdeal f).map (linearChangeY c).toRingEquiv.toRingHom =
      equationIdeal (linearChangeY c f) := by
  rw [equationIdeal, Ideal.map_span]
  simp
  rfl

/-- The invertible linear change descends to the two coordinate rings. -/
def coordinateRingEquivLinearChangeY
    (f : BivariatePolynomial K) (c : Fin 1 → K) :
    CoordinateRing f ≃ₐ[K] CoordinateRing (linearChangeY c f) :=
  Ideal.quotientEquivAlg
    (equationIdeal f)
    (equationIdeal (linearChangeY c f))
    (linearChangeY c)
    (map_equationIdeal_linearChangeY f c).symm

/--
The original plane equation and its monic representative have isomorphic
coordinate rings.
-/
def coordinateRingEquivMonicRepresentative
    (f : BivariatePolynomial K) (c : Fin 1 → K)
    (h : IsUnit (yPolynomial (linearChangeY c f)).leadingCoeff) :
    CoordinateRing f ≃ₐ[K] CoordinateRing (monicRepresentative f c h) :=
  (coordinateRingEquivLinearChangeY f c).trans
    (Ideal.quotientEquivAlgOfEq K
      (equationIdeal_monicRepresentative f c h).symm)

theorem totalDegree_monicRepresentative
    {f : BivariatePolynomial K} (hf : f ≠ 0)
    (c : Fin 1 → K)
    (h : IsUnit (yPolynomial (linearChangeY c f)).leadingCoeff) :
    (monicRepresentative f c h).totalDegree = f.totalDegree := by
  have ht : linearChangeY c f ≠ 0 :=
    (linearChangeY c).injective.ne hf
  have ha := monicRepresentative_associated f c h
  have hg : monicRepresentative f c h ≠ 0 :=
    ha.ne_zero_iff.mpr ht
  calc
    (monicRepresentative f c h).totalDegree =
        (linearChangeY c f).totalDegree := by
      apply le_antisymm
      · exact
          MvPolynomial.totalDegree_le_of_dvd_of_isDomain
            ha.dvd ht
      · exact
          MvPolynomial.totalDegree_le_of_dvd_of_isDomain
            ha.dvd' hg
    _ = f.totalDegree := totalDegree_linearChangeY c f

theorem monicRepresentative_irreducible
    {f : BivariatePolynomial K} (hf : Irreducible f)
    (c : Fin 1 → K)
    (h : IsUnit (yPolynomial (linearChangeY c f)).leadingCoeff) :
    Irreducible (monicRepresentative f c h) := by
  exact
    (monicRepresentative_associated f c h).symm.irreducible
      (hf.map (linearChangeY c).toMulEquiv)

/--
The induced equivalence of plane-curve function fields.
-/
def functionFieldEquivMonicRepresentative
    {f : BivariatePolynomial K} (_hf : Irreducible f)
    (c : Fin 1 → K)
    (h : IsUnit (yPolynomial (linearChangeY c f)).leadingCoeff) :
    FractionRing (CoordinateRing f) ≃ₐ[K]
      FractionRing (CoordinateRing (monicRepresentative f c h)) := by
  letI : IsDomain (CoordinateRing f) :=
    coordinateRing_isDomain _hf
  letI : IsDomain (CoordinateRing (monicRepresentative f c h)) :=
    coordinateRing_isDomain
      (monicRepresentative_irreducible _hf c h)
  exact
    IsFractionRing.algEquivOfAlgEquiv
      (coordinateRingEquivMonicRepresentative f c h)

/--
Existence of an irreducible monic representative after an invertible linear
change, over an infinite field.
-/
theorem exists_irreducible_monicRepresentative
    [Infinite K] {f : BivariatePolynomial K} (hf : Irreducible f) :
    ∃ c : Fin 1 → K,
      ∃ h : IsUnit (yPolynomial (linearChangeY c f)).leadingCoeff,
        Irreducible (monicRepresentative f c h) ∧
          (yPolynomial (monicRepresentative f c h)).Monic ∧
            (monicRepresentative f c h).totalDegree =
              f.totalDegree := by
  obtain ⟨c, h⟩ :=
    exists_linearChangeY_leadingCoeff_isUnit hf.ne_zero
  exact
    ⟨c, h, monicRepresentative_irreducible hf c h,
      monicRepresentative_monic f c h,
      totalDegree_monicRepresentative hf.ne_zero c h⟩

end PlaneCurveMonicNormalization
end Chapter06
end FieldArithmetic
