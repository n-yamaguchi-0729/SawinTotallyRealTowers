/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.PlaneCurves.NormalPoint
import Nyll.SchemeTheory.PlaneCurves.PartialDerivatives

/-!
# Normal points on affine plane curves are simple

This file proves the difficult implication in Fried--Jarden, Lemma 6.2.3:
a normal rational point of an irreducible affine plane curve has a nonzero
partial derivative.

The proof follows the valuation-theoretic argument.  The normal point local
ring is a DVR, so its two translated coordinates are comparable for
divisibility.  After clearing the localization denominator, differentiating
the resulting polynomial identity at the point contradicts the fact that the
denominator lies outside the point ideal.
-/

noncomputable section

namespace FieldArithmetic
namespace Chapter06
namespace AffinePlaneCurve

open MvPolynomial

universe u

variable {K : Type u} [Field K]

private theorem not_coordinateX_dvd_coordinateY_of_partialAt_eq_zero
    {f : BivariatePolynomial K} (hf : Irreducible f)
    (p : RationalPoint f) (hpartial : partialAt p 1 = 0) :
    letI : IsDomain (CoordinateRing f) := coordinateRing_isDomain hf
    letI : (pointIdeal p).IsPrime := (pointIdeal_isMaximal p).isPrime
    ¬ algebraMap (CoordinateRing f) (PointLocalRing p)
          (coordinate f 0 -
            algebraMap K (CoordinateRing f) (p.coords 0)) ∣
        algebraMap (CoordinateRing f) (PointLocalRing p)
          (coordinate f 1 -
            algebraMap K (CoordinateRing f) (p.coords 1)) := by
  let : IsDomain (CoordinateRing f) := coordinateRing_isDomain hf
  let : (pointIdeal p).IsPrime := (pointIdeal_isMaximal p).isPrime
  let xA : CoordinateRing f :=
    coordinate f 0 - algebraMap K (CoordinateRing f) (p.coords 0)
  let yA : CoordinateRing f :=
    coordinate f 1 - algebraMap K (CoordinateRing f) (p.coords 1)
  let xP : BivariatePolynomial K :=
    MvPolynomial.X 0 - MvPolynomial.C (p.coords 0)
  let yP : BivariatePolynomial K :=
    MvPolynomial.X 1 - MvPolynomial.C (p.coords 1)
  intro hdiv
  obtain ⟨q, hq⟩ := hdiv
  obtain ⟨⟨h, s⟩, hs⟩ :=
    IsLocalization.surj (pointIdeal p).primeCompl q
  have hlocal :
      algebraMap (CoordinateRing f) (PointLocalRing p)
          (yA * (s : CoordinateRing f)) =
        algebraMap (CoordinateRing f) (PointLocalRing p) (xA * h) := by
    simp only [map_mul]
    rw [hq, mul_assoc, hs]
  have hcoordinate :
      yA * (s : CoordinateRing f) = xA * h :=
    IsLocalization.injective
      (S := PointLocalRing p)
      (pointIdeal p).primeCompl_le_nonZeroDivisors hlocal
  obtain ⟨S, hS⟩ :=
    Ideal.Quotient.mk_surjective
      (I := equationIdeal f) (s : CoordinateRing f)
  obtain ⟨H, hH⟩ :=
    Ideal.Quotient.mk_surjective (I := equationIdeal f) h
  have hquotient :
      Ideal.Quotient.mk (equationIdeal f) (yP * S - xP * H) = 0 := by
    simp only [map_sub, map_mul]
    rw [hS, hH]
    change yA * (s : CoordinateRing f) - xA * h = 0
    rw [hcoordinate, sub_self]
  have hmem :
      yP * S - xP * H ∈ equationIdeal f :=
    Ideal.Quotient.eq_zero_iff_mem.mp hquotient
  have hfdvd : f ∣ yP * S - xP * H := by
    apply Ideal.mem_span_singleton.mp
    simpa [equationIdeal] using hmem
  obtain ⟨G, hG⟩ := hfdvd
  have hderiv :=
    congrArg
      (fun z : BivariatePolynomial K =>
        polynomialEval p (MvPolynomial.pderiv 1 z))
      hG
  have hfzero : polynomialEval p f = 0 := by
    simpa [polynomialEval] using p.isZero
  have hpartial' :
      polynomialEval p (MvPolynomial.pderiv 1 f) = 0 := by
    simpa [partialAt] using hpartial
  have hSzero : polynomialEval p S = 0 := by
    simpa [xP, yP, MvPolynomial.pderiv_mul, hpartial',
      hfzero] using hderiv
  have hsPoint : (s : CoordinateRing f) ∈ pointIdeal p := by
    change pointEval p (s : CoordinateRing f) = 0
    rw [← hS]
    simpa [polynomialEval] using hSzero
  exact s.property hsPoint

private theorem not_coordinateY_dvd_coordinateX_of_partialAt_eq_zero
    {f : BivariatePolynomial K} (hf : Irreducible f)
    (p : RationalPoint f) (hpartial : partialAt p 0 = 0) :
    letI : IsDomain (CoordinateRing f) := coordinateRing_isDomain hf
    letI : (pointIdeal p).IsPrime := (pointIdeal_isMaximal p).isPrime
    ¬ algebraMap (CoordinateRing f) (PointLocalRing p)
          (coordinate f 1 -
            algebraMap K (CoordinateRing f) (p.coords 1)) ∣
        algebraMap (CoordinateRing f) (PointLocalRing p)
          (coordinate f 0 -
            algebraMap K (CoordinateRing f) (p.coords 0)) := by
  let : IsDomain (CoordinateRing f) := coordinateRing_isDomain hf
  let : (pointIdeal p).IsPrime := (pointIdeal_isMaximal p).isPrime
  let xA : CoordinateRing f :=
    coordinate f 0 - algebraMap K (CoordinateRing f) (p.coords 0)
  let yA : CoordinateRing f :=
    coordinate f 1 - algebraMap K (CoordinateRing f) (p.coords 1)
  let xP : BivariatePolynomial K :=
    MvPolynomial.X 0 - MvPolynomial.C (p.coords 0)
  let yP : BivariatePolynomial K :=
    MvPolynomial.X 1 - MvPolynomial.C (p.coords 1)
  intro hdiv
  obtain ⟨q, hq⟩ := hdiv
  obtain ⟨⟨h, s⟩, hs⟩ :=
    IsLocalization.surj (pointIdeal p).primeCompl q
  have hlocal :
      algebraMap (CoordinateRing f) (PointLocalRing p)
          (xA * (s : CoordinateRing f)) =
        algebraMap (CoordinateRing f) (PointLocalRing p) (yA * h) := by
    simp only [map_mul]
    rw [hq, mul_assoc, hs]
  have hcoordinate :
      xA * (s : CoordinateRing f) = yA * h :=
    IsLocalization.injective
      (S := PointLocalRing p)
      (pointIdeal p).primeCompl_le_nonZeroDivisors hlocal
  obtain ⟨S, hS⟩ :=
    Ideal.Quotient.mk_surjective
      (I := equationIdeal f) (s : CoordinateRing f)
  obtain ⟨H, hH⟩ :=
    Ideal.Quotient.mk_surjective (I := equationIdeal f) h
  have hquotient :
      Ideal.Quotient.mk (equationIdeal f) (xP * S - yP * H) = 0 := by
    simp only [map_sub, map_mul]
    rw [hS, hH]
    change xA * (s : CoordinateRing f) - yA * h = 0
    rw [hcoordinate, sub_self]
  have hmem :
      xP * S - yP * H ∈ equationIdeal f :=
    Ideal.Quotient.eq_zero_iff_mem.mp hquotient
  have hfdvd : f ∣ xP * S - yP * H := by
    apply Ideal.mem_span_singleton.mp
    simpa [equationIdeal] using hmem
  obtain ⟨G, hG⟩ := hfdvd
  have hderiv :=
    congrArg
      (fun z : BivariatePolynomial K =>
        polynomialEval p (MvPolynomial.pderiv 0 z))
      hG
  have hfzero : polynomialEval p f = 0 := by
    simpa [polynomialEval] using p.isZero
  have hpartial' :
      polynomialEval p (MvPolynomial.pderiv 0 f) = 0 := by
    simpa [partialAt] using hpartial
  have hSzero : polynomialEval p S = 0 := by
    simpa [xP, yP, MvPolynomial.pderiv_mul, hpartial',
      hfzero] using hderiv
  have hsPoint : (s : CoordinateRing f) ∈ pointIdeal p := by
    change pointEval p (s : CoordinateRing f) = 0
    rw [← hS]
    simpa [polynomialEval] using hSzero
  exact s.property hsPoint

/--
Fried--Jarden 6.2.3, normal-to-simple direction: a normal rational point of
an irreducible affine plane curve has a nonzero partial derivative.
-/
theorem isSimple_of_isNormalAt
    {f : BivariatePolynomial K} (hf : Irreducible f)
    (p : RationalPoint f) (hnormal : IsNormalAt p) :
    IsSimple p := by
  let : IsDomain (CoordinateRing f) := coordinateRing_isDomain hf
  let : (pointIdeal p).IsMaximal := pointIdeal_isMaximal p
  let : (pointIdeal p).IsPrime := (pointIdeal_isMaximal p).isPrime
  have hnormal' : IsIntegrallyClosed (PointLocalRing p) := by
    simpa [IsNormalAt] using hnormal
  let : IsDiscreteValuationRing (PointLocalRing p) :=
    pointLocalRing_isDiscreteValuationRing_of_isIntegrallyClosed
      hf p hnormal'
  let x :
      PointLocalRing p :=
    algebraMap (CoordinateRing f) (PointLocalRing p)
      (coordinate f 0 -
        algebraMap K (CoordinateRing f) (p.coords 0))
  let y :
      PointLocalRing p :=
    algebraMap (CoordinateRing f) (PointLocalRing p)
      (coordinate f 1 -
        algebraMap K (CoordinateRing f) (p.coords 1))
  by_contra hnonsimple
  have hpartial : ∀ i : Fin 2, partialAt p i = 0 := by
    intro i
    by_contra hi
    exact hnonsimple ⟨i, hi⟩
  rcases
      le_total
        (IsDiscreteValuationRing.addVal (PointLocalRing p) x)
        (IsDiscreteValuationRing.addVal (PointLocalRing p) y) with
    hxy | hyx
  · exact
      not_coordinateX_dvd_coordinateY_of_partialAt_eq_zero
        hf p (hpartial 1)
          (IsDiscreteValuationRing.addVal_le_iff_dvd.mp hxy)
  · exact
      not_coordinateY_dvd_coordinateX_of_partialAt_eq_zero
        hf p (hpartial 0)
          (IsDiscreteValuationRing.addVal_le_iff_dvd.mp hyx)

end AffinePlaneCurve
end Chapter06
end FieldArithmetic
