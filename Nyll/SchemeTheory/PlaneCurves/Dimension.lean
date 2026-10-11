/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.PlaneCurves.CoordinateRing
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

/-!
# Dimension of an irreducible affine plane curve

This file derives the one-dimensionality needed in Fried--Jarden, Section 6.2,
directly from an irreducible bivariate equation.  The proof uses the
correspondence between primes of a quotient and primes above its kernel,
Krull's principal ideal theorem, and the Krull dimension of a polynomial ring
in two variables over a field.
-/

noncomputable section

namespace FieldArithmetic
namespace Chapter06
namespace AffinePlaneCurve

universe u

variable {K : Type u} [Field K]

/-- A polynomial ring in two variables over a field has Krull dimension two. -/
theorem bivariatePolynomial_ringKrullDim :
    ringKrullDim (BivariatePolynomial K) = 2 := by
  change ringKrullDim (MvPolynomial (Fin 2) K) = 2
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing,
    ringKrullDim_eq_zero_of_field]
  simp

/--
The prime principal ideal of an irreducible plane equation has height one.
-/
theorem equationIdeal_height_eq_one
    {f : BivariatePolynomial K} (hf : Irreducible f) :
    (equationIdeal f).height = 1 := by
  rw [equationIdeal]
  exact
    Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_iff_ne_zero.mpr hf.ne_zero)
      hf.not_isUnit

/-- A translated coordinate variable over a field is irreducible. -/
theorem coordinate_sub_irreducible
    (i : Fin 2) (a : K) :
    Irreducible
      (MvPolynomial.X i - MvPolynomial.C a :
        BivariatePolynomial K) := by
  simpa [sub_eq_add_neg] using
    MvPolynomial.irreducible_mul_X_add
      (1 : BivariatePolynomial K) (-MvPolynomial.C a) i
      one_ne_zero (by simp) (by simp) isRelPrime_one_left

/--
The maximal ideal defined by a rational point of an irreducible affine plane
curve is nonzero.

If it were zero, the polynomial evaluation kernel would equal `(f)`.  Thus
`f` would divide both translated coordinate variables.  Irreducibility would
make those two variables associated, which is contradicted by evaluating one
of them at zero and the other at one.
-/
theorem pointIdeal_ne_bot
    {f : BivariatePolynomial K} (hf : Irreducible f)
    (p : RationalPoint f) :
    pointIdeal p ≠ ⊥ := by
  intro hpoint
  let π : BivariatePolynomial K →+* CoordinateRing f :=
    Ideal.Quotient.mk (equationIdeal f)
  have hmap :
      (RingHom.ker (polynomialEval p).toRingHom).map π = ⊥ := by
    rw [← pointIdeal_eq_map_polynomialEval_ker p, hpoint]
  have hevalKernel_eq :
      RingHom.ker (polynomialEval p).toRingHom =
        equationIdeal f := by
    apply le_antisymm
    · rw [← Ideal.mk_ker (I := equationIdeal f)]
      exact (Ideal.map_eq_bot_iff_le_ker π).mp hmap
    · exact equationIdeal_le_polynomialEval_ker p
  let xSub : BivariatePolynomial K :=
    MvPolynomial.X 0 - MvPolynomial.C (p.coords 0)
  let ySub : BivariatePolynomial K :=
    MvPolynomial.X 1 - MvPolynomial.C (p.coords 1)
  have hx_ker :
      xSub ∈ RingHom.ker (polynomialEval p).toRingHom := by
    rw [RingHom.mem_ker]
    simp [xSub, polynomialEval]
  have hy_ker :
      ySub ∈ RingHom.ker (polynomialEval p).toRingHom := by
    rw [RingHom.mem_ker]
    simp [ySub, polynomialEval]
  have hx_equation : xSub ∈ equationIdeal f :=
    hevalKernel_eq ▸ hx_ker
  have hy_equation : ySub ∈ equationIdeal f :=
    hevalKernel_eq ▸ hy_ker
  have hfx : f ∣ xSub := by
    apply Ideal.mem_span_singleton.mp
    simpa [equationIdeal] using hx_equation
  have hfy : f ∣ ySub := by
    apply Ideal.mem_span_singleton.mp
    simpa [equationIdeal] using hy_equation
  have hfassoc_x : Associated f xSub :=
    hf.associated_of_dvd
      (by simpa [xSub] using
        coordinate_sub_irreducible (K := K) 0 (p.coords 0))
      hfx
  have hfassoc_y : Associated f ySub :=
    hf.associated_of_dvd
      (by simpa [ySub] using
        coordinate_sub_irreducible (K := K) 1 (p.coords 1))
      hfy
  have hxy : Associated xSub ySub :=
    hfassoc_x.symm.trans hfassoc_y
  let q : Fin 2 → K :=
    ![p.coords 0, p.coords 1 + 1]
  have hxy_at_q :=
    hxy.map (MvPolynomial.aeval q).toMonoidHom
  simp [xSub, ySub, q] at hxy_at_q

/--
The coordinate ring of an irreducible affine plane equation has dimension at
most one.  No dimension hypothesis is supplied: it is derived from the
height-one equation ideal inside the dimension-two polynomial ring.
-/
theorem coordinateRing_dimensionLEOne
    {f : BivariatePolynomial K} (hf : Irreducible f) :
    Ring.DimensionLEOne (CoordinateRing f) := by
  let : (equationIdeal f).IsPrime := equationIdeal_isPrime hf
  let π : BivariatePolynomial K →+* CoordinateRing f :=
    Ideal.Quotient.mk (equationIdeal f)
  refine ⟨?_⟩
  intro p hp hprime
  let : p.IsPrime := hprime
  let P : Ideal (BivariatePolynomial K) := p.comap π
  let : P.IsPrime := Ideal.comap_isPrime π p
  have hkernel :
      equationIdeal f =
        (⊥ : Ideal (CoordinateRing f)).comap π := by
    rw [← RingHom.ker_eq_comap_bot]
    exact (Ideal.mk_ker (I := equationIdeal f)).symm
  have hequation_lt_P : equationIdeal f < P := by
    rw [hkernel]
    exact
      (Ideal.orderEmbeddingOfSurjective π
        Ideal.Quotient.mk_surjective).strictMono
        (bot_lt_iff_ne_bot.mpr hp)
  have hequation_height_lt_P :
      (equationIdeal f).height < P.height :=
    Ideal.height_strict_mono_of_isPrime hequation_lt_P
  have htwo_le_P : (2 : ℕ∞) ≤ P.height := by
    apply ENat.natCast_add_one_le_iff.mpr
    simpa [equationIdeal_height_eq_one hf] using hequation_height_lt_P
  refine ⟨⟨hprime.ne_top, ?_⟩⟩
  intro J hpJ
  by_contra hJ
  let Q : Ideal (BivariatePolynomial K) := J.comap π
  have hP_lt_Q : P < Q :=
    (Ideal.orderEmbeddingOfSurjective π
      Ideal.Quotient.mk_surjective).strictMono hpJ
  have hP_height_lt_Q : P.height < Q.height :=
    Ideal.height_strict_mono_of_isPrime hP_lt_Q
  have hP_height_ne_top : P.height ≠ ⊤ :=
    P.height_ne_top (Ideal.IsPrime.ne_top inferInstance)
  have hP_add_one_le_Q : P.height + 1 ≤ Q.height :=
    (ENat.add_one_le_iff hP_height_ne_top).mpr hP_height_lt_Q
  have hthree_le_Q : (3 : ℕ∞) ≤ Q.height := by
    calc
      (3 : ℕ∞) = 2 + 1 := by norm_num
      _ ≤ P.height + 1 := by
        simpa [add_comm] using add_le_add_right htwo_le_P 1
      _ ≤ Q.height := hP_add_one_le_Q
  have hQ_ne_top : Q ≠ ⊤ := Ideal.comap_ne_top π hJ
  have hQ_le_dimension :=
    Ideal.height_le_ringKrullDim_of_ne_top hQ_ne_top
  rw [bivariatePolynomial_ringKrullDim (K := K)] at hQ_le_dimension
  have hQ_le_two : Q.height ≤ (2 : ℕ∞) := by
    change
      (Q.height : WithBot ℕ∞) ≤
        ((2 : ℕ∞) : WithBot ℕ∞) at hQ_le_dimension
    exact WithBot.coe_le_coe.mp hQ_le_dimension
  have : (3 : ℕ∞) ≤ 2 := hthree_le_Q.trans hQ_le_two
  norm_num at this

/--
Krull dimension at most one is preserved when the coordinate ring is
localized at a prime ideal.
-/
theorem atPrime_dimensionLEOne
    {f : BivariatePolynomial K} (hf : Irreducible f)
    (p : Ideal (CoordinateRing f)) [p.IsPrime] :
    Ring.DimensionLEOne (Localization.AtPrime p) := by
  let : IsDomain (CoordinateRing f) := coordinateRing_isDomain hf
  let : Ring.DimensionLEOne (CoordinateRing f) :=
    coordinateRing_dimensionLEOne hf
  exact
    Ring.DimensionLEOne.localization
      (Localization.AtPrime p) p.primeCompl_le_nonZeroDivisors

/--
Every nonzero prime of a local ring of the irreducible curve is its maximal
ideal.
-/
theorem atPrime_nonzero_prime_eq_maximalIdeal
    {f : BivariatePolynomial K} (hf : Irreducible f)
    {p : Ideal (CoordinateRing f)} [p.IsPrime]
    (P : Ideal (Localization.AtPrime p))
    (hP : P ≠ ⊥) (hPprime : P.IsPrime) :
    P = IsLocalRing.maximalIdeal (Localization.AtPrime p) := by
  let : IsDomain (CoordinateRing f) := coordinateRing_isDomain hf
  let : Ring.DimensionLEOne (Localization.AtPrime p) :=
    atPrime_dimensionLEOne hf p
  let : P.IsPrime := hPprime
  have hPmaximal : P.IsMaximal :=
    @Ring.DimensionLEOne.maximalOfPrime
      (Localization.AtPrime p) inferInstance
      (atPrime_dimensionLEOne hf p) P hP hPprime
  exact IsLocalRing.eq_maximalIdeal hPmaximal

/--
At a nonzero prime of the curve there is exactly one nonzero prime in the
local ring.
-/
theorem atPrime_existsUnique_nonzero_prime
    {f : BivariatePolynomial K} (hf : Irreducible f)
    {p : Ideal (CoordinateRing f)} [p.IsPrime] (hp : p ≠ ⊥) :
    ∃! P : Ideal (Localization.AtPrime p), P ≠ ⊥ ∧ P.IsPrime := by
  let : IsDomain (CoordinateRing f) := coordinateRing_isDomain hf
  have hnotField :
      ¬ IsField (Localization.AtPrime p) :=
    IsLocalization.AtPrime.not_isField
      (CoordinateRing f) hp (Localization.AtPrime p)
  have hmaximal_ne_bot :
      IsLocalRing.maximalIdeal (Localization.AtPrime p) ≠ ⊥ := by
    intro hmaximal
    exact hnotField
      (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hmaximal)
  refine
    ⟨IsLocalRing.maximalIdeal (Localization.AtPrime p),
      ⟨hmaximal_ne_bot,
        (IsLocalRing.maximalIdeal.isMaximal
          (Localization.AtPrime p)).isPrime⟩, ?_⟩
  intro P hP
  exact atPrime_nonzero_prime_eq_maximalIdeal hf P hP.1 hP.2

/--
An integrally closed local ring at a nonzero maximal ideal of an irreducible
affine plane curve is a discrete valuation ring.
-/
theorem atPrime_isDiscreteValuationRing_of_isIntegrallyClosed
    {f : BivariatePolynomial K} (hf : Irreducible f)
    {m : Ideal (CoordinateRing f)} [m.IsMaximal] (hm : m ≠ ⊥) :
    letI : m.IsPrime := (inferInstance : m.IsMaximal).isPrime
    letI : IsDomain (CoordinateRing f) := coordinateRing_isDomain hf
    letI : IsDomain (Localization.AtPrime m) :=
      IsLocalization.isDomain_of_atPrime (Localization.AtPrime m) m
    IsIntegrallyClosed (Localization.AtPrime m) →
      IsDiscreteValuationRing (Localization.AtPrime m) := by
  intro hnormal
  let : IsDomain (CoordinateRing f) := coordinateRing_isDomain hf
  let : m.IsPrime := (inferInstance : m.IsMaximal).isPrime
  let : IsDomain (Localization.AtPrime m) :=
    IsLocalization.isDomain_of_atPrime (Localization.AtPrime m) m
  let : IsNoetherianRing (CoordinateRing f) := inferInstance
  let : IsNoetherianRing (Localization.AtPrime m) :=
    IsLocalization.isNoetherianRing m.primeCompl
      (Localization.AtPrime m) inferInstance
  let : IsLocalRing (Localization.AtPrime m) :=
    IsLocalization.AtPrime.isLocalRing (Localization.AtPrime m) m
  have hnotField :
      ¬ IsField (Localization.AtPrime m) :=
    IsLocalization.AtPrime.not_isField
      (CoordinateRing f) hm (Localization.AtPrime m)
  apply
    ((IsDiscreteValuationRing.TFAE
      (Localization.AtPrime m) hnotField).out 4 1).mp
  exact
    ⟨hnormal, atPrime_existsUnique_nonzero_prime hf hm⟩

/--
The preceding DVR criterion specialized to the local ring of a rational
point.
-/
theorem pointLocalRing_isDiscreteValuationRing_of_isIntegrallyClosed
    {f : BivariatePolynomial K} (hf : Irreducible f)
    (p : RationalPoint f) :
    letI : (pointIdeal p).IsPrime := (pointIdeal_isMaximal p).isPrime
    letI : IsDomain (CoordinateRing f) := coordinateRing_isDomain hf
    letI : IsDomain (Localization.AtPrime (pointIdeal p)) :=
      IsLocalization.isDomain_of_atPrime
        (Localization.AtPrime (pointIdeal p)) (pointIdeal p)
    IsIntegrallyClosed (Localization.AtPrime (pointIdeal p)) →
      IsDiscreteValuationRing
        (Localization.AtPrime (pointIdeal p)) := by
  intro hnormal
  let : (pointIdeal p).IsMaximal := pointIdeal_isMaximal p
  let : (pointIdeal p).IsPrime := (pointIdeal_isMaximal p).isPrime
  exact
    atPrime_isDiscreteValuationRing_of_isIntegrallyClosed
      hf (pointIdeal_ne_bot hf p) hnormal

end AffinePlaneCurve
end Chapter06
end FieldArithmetic
