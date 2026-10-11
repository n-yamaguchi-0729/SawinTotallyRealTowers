/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.PlaneCurves.MonicProjection
import Nyll.SchemeTheory.FunctionFields.PrimeDivisors.Counting
import Nyll.SchemeTheory.FunctionFields.PrimeDivisors.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# Prime divisors centered at a rational point

This file supplies the monic-projection form of Fried--Jarden, Lemma 6.2.2(b).
-/

noncomputable section

namespace FieldArithmetic
namespace Chapter06
namespace CenteredPrimeDivisorBound

open AffinePlaneCurve MonicPlaneCurveProjection

universe u

variable {K : Type u} [Field K]

/-- The one-variable multivariate projection base is the usual polynomial
ring. -/
def projectionBaseEquivPolynomial :
    ProjectionBase K ≃ₐ[K] Polynomial K :=
  (MvPolynomial.finSuccEquiv K 0).trans
    (Polynomial.mapAlgEquiv
      (MvPolynomial.isEmptyAlgEquiv K (Fin 0)))

/-- In particular, the projection base is a principal ideal domain. -/
theorem projectionBase_isPrincipalIdealRing :
    IsPrincipalIdealRing (ProjectionBase K) :=
  IsPrincipalIdealRing.of_surjective
    (projectionBaseEquivPolynomial (K := K)).symm.toRingEquiv.toRingHom
    (projectionBaseEquivPolynomial (K := K)).symm.surjective

/-- The projection algebra structure is compatible with the constant
`K`-algebra structures. -/
theorem projectionAlgebra_algebraMap_apply
    (f : BivariatePolynomial K) (x : K) :
    @algebraMap (ProjectionBase K) (CoordinateRing f) _ _
        (projectionAlgebra f)
        (algebraMap K (ProjectionBase K) x) =
      algebraMap K (CoordinateRing f) x := by
  change
    (coordinateRingEquivProjectionModel f).symm
        (algebraMap (ProjectionBase K) (ProjectionModel f)
          (algebraMap K (ProjectionBase K) x)) =
      algebraMap K (CoordinateRing f) x
  rw [← IsScalarTower.algebraMap_apply K (ProjectionBase K)
    (ProjectionModel f)]
  exact (coordinateRingEquivProjectionModel f).symm.commutes x

/-- The inclusion of the affine coordinate ring in its fraction field. -/
abbrev coordinateRingMap
    {f : BivariatePolynomial K} [IsDomain (CoordinateRing f)] :
    CoordinateRing f →ₐ[K] FractionRing (CoordinateRing f) :=
  IsScalarTower.toAlgHom K (CoordinateRing f)
    (FractionRing (CoordinateRing f))

/--
A prime divisor finite on the affine coordinate ring and centered at the
rational point `p`.  These are exactly the objects counted in the
monic-projection form of Fried--Jarden 6.2.2(b).
-/
structure CenteredPrimeDivisor
    {f : BivariatePolynomial K} [IsDomain (CoordinateRing f)]
    (p : RationalPoint f) where
  /-- The underlying prime divisor of the fraction field of the coordinate ring. -/
  divisor :
    FunctionFieldPrimeDivisor K (FractionRing (CoordinateRing f))
  /-- The divisor is finite along the coordinate-ring inclusion. -/
  finite :
    divisor.FiniteAlong (coordinateRingMap (K := K) (f := f))
  /-- The center of the divisor is the ideal of the rational point p. -/
  center_eq :
    divisor.centerAlong (coordinateRingMap (K := K) (f := f)) finite =
      pointIdeal p

namespace CenteredPrimeDivisor

variable {f : BivariatePolynomial K} [IsDomain (CoordinateRing f)]
  {p : RationalPoint f}

@[ext]
theorem ext {v w : CenteredPrimeDivisor (K := K) p}
    (h : v.divisor = w.divisor) :
    v = w := by
  rcases v with ⟨v, hv, hvcenter⟩
  rcases w with ⟨w, hw, hwcenter⟩
  change v = w at h
  subst w
  rfl

end CenteredPrimeDivisor

/-- The prime of `K[X]` below a rational point of the affine curve. -/
def projectionPointIdeal
    {f : BivariatePolynomial K} (p : RationalPoint f) :
    Ideal (ProjectionBase K) :=
  (pointIdeal p).comap
    (@algebraMap (ProjectionBase K) (CoordinateRing f) _ _
      (projectionAlgebra f))

theorem projectionPointIdeal_isPrime
    {f : BivariatePolynomial K} (p : RationalPoint f) :
    (projectionPointIdeal (K := K) p).IsPrime := by
  let : (pointIdeal p).IsPrime := (pointIdeal_isMaximal p).isPrime
  exact Ideal.IsPrime.comap _

/--
Rank comparison for an integral-closure model, with the ambient
torsion-freeness supplied by an explicit algebra-map injection.

Keeping this comparison in its own declaration prevents the final rank
calculation from reopening the full projection and normalization instance
environment.
-/
private theorem integralClosure_finrank_eq_of_algebraMap_injective
    (A K₀ L C : Type*) [CommRing A] [IsDomain A]
    [Field K₀] [Field L] [CommRing C]
    [Algebra A K₀] [IsFractionRing A K₀]
    [Algebra K₀ L] [Algebra A L] [IsScalarTower A K₀ L]
    [Algebra C L] [IsIntegralClosure C A L]
    [Algebra A C] [IsScalarTower A C L]
    [FiniteDimensional K₀ L] [Algebra.IsSeparable K₀ L]
    [IsPrincipalIdealRing A]
    (hL : Function.Injective (algebraMap A L)) :
    Module.finrank A C = Module.finrank K₀ L := by
  let : Module.IsTorsionFree A L :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hL
  exact IsIntegralClosure.rank A K₀ L C

/--
For a monic projection whose function-field extension over `K(X)` is
separable, at most `totalDegree f` prime divisors are finite on the affine
coordinate ring and centered at a prescribed rational point.

The separability input is precisely the hypothesis used to make the integral
closure of `K[X]` finite and Dedekind.  In particular, it is structural input
for the normalization, not an assumed comparison or counting statement.
-/
theorem card_centeredPrimeDivisor_le_totalDegree
    {f : BivariatePolynomial K} (hirr : Irreducible f)
    (hmonic : (yPolynomial f).Monic) (p : RationalPoint f) :
    letI : IsDomain (CoordinateRing f) :=
      coordinateRing_isDomain hirr
    letI : Algebra (ProjectionFunctionField K)
        (FractionRing (CoordinateRing f)) :=
      functionFieldAlgebra f hirr hmonic
    Algebra.IsSeparable (ProjectionFunctionField K)
        (FractionRing (CoordinateRing f)) →
      Nat.card (CenteredPrimeDivisor (K := K) p) ≤
        MvPolynomial.totalDegree f := by
  let : IsDomain (CoordinateRing f) :=
    coordinateRing_isDomain hirr
  let : Algebra (ProjectionBase K) (CoordinateRing f) :=
    projectionAlgebra f
  let : Algebra (ProjectionBase K)
      (FractionRing (CoordinateRing f)) :=
    inferInstance
  let : IsScalarTower (ProjectionBase K) (CoordinateRing f)
      (FractionRing (CoordinateRing f)) :=
    inferInstance
  have hProjectionFraction_injective :
      Function.Injective
        (algebraMap (ProjectionBase K)
          (FractionRing (CoordinateRing f))) := by
    rw [IsScalarTower.algebraMap_eq
      (ProjectionBase K) (CoordinateRing f)
      (FractionRing (CoordinateRing f))]
    exact
      (IsFractionRing.injective (CoordinateRing f)
          (FractionRing (CoordinateRing f))).comp
        (projectionAlgebra_injective hirr hmonic)
  let : IsScalarTower K (ProjectionBase K)
      (FractionRing (CoordinateRing f)) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply K (CoordinateRing f)
          (FractionRing (CoordinateRing f)),
        IsScalarTower.algebraMap_apply (ProjectionBase K)
          (CoordinateRing f) (FractionRing (CoordinateRing f)),
        projectionAlgebra_algebraMap_apply f x]
  let : Algebra (ProjectionFunctionField K)
      (FractionRing (CoordinateRing f)) :=
    functionFieldAlgebra f hirr hmonic
  let : IsScalarTower (ProjectionBase K) (ProjectionFunctionField K)
      (FractionRing (CoordinateRing f)) :=
    IsScalarTower.of_algebraMap_eq fun x ↦
      (IsFractionRing.lift_algebraMap
        hProjectionFraction_injective x).symm
  intro hseparable
  let : Algebra.IsSeparable (ProjectionFunctionField K)
      (FractionRing (CoordinateRing f)) :=
    hseparable
  let : Module.Finite (ProjectionFunctionField K)
      (FractionRing (CoordinateRing f)) :=
    functionField_finiteDimensional f hirr hmonic
  let : IsPrincipalIdealRing (ProjectionBase K) :=
    projectionBase_isPrincipalIdealRing (K := K)
  let S :=
    (integralClosure (ProjectionBase K)
      (FractionRing (CoordinateRing f))).restrictScalars K
  let baseToS : ProjectionBase K →+* S :=
    { toFun := fun r =>
        ⟨algebraMap (ProjectionBase K)
            (FractionRing (CoordinateRing f)) r,
          isIntegral_algebraMap⟩
      map_zero' := Subtype.ext (map_zero _)
      map_one' := Subtype.ext (map_one _)
      map_add' := fun _ _ => Subtype.ext (map_add _ _ _)
      map_mul' := fun _ _ => Subtype.ext (map_mul _ _ _) }
  let : Algebra (ProjectionBase K) S :=
    baseToS.toAlgebra
  let : IsScalarTower (ProjectionBase K) S
      (FractionRing (CoordinateRing f)) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower K S (FractionRing (CoordinateRing f)) :=
    IsScalarTower.subalgebra' K
      (FractionRing (CoordinateRing f))
      (FractionRing (CoordinateRing f)) S
  let : IsIntegralClosure S (ProjectionBase K)
      (FractionRing (CoordinateRing f)) :=
    { algebraMap_injective := fun _ _ h => Subtype.ext h
      isIntegral_iff := by
        intro x
        constructor
        · intro hx
          exact ⟨⟨x, hx⟩, rfl⟩
        · rintro ⟨x, rfl⟩
          exact x.property }
  let : Module.Finite (ProjectionBase K) S :=
    IsIntegralClosure.finite
      (ProjectionBase K) (ProjectionFunctionField K)
      (FractionRing (CoordinateRing f)) S
  let : IsDedekindDomain S :=
    IsIntegralClosure.isDedekindDomain
      (ProjectionBase K) (ProjectionFunctionField K)
      (FractionRing (CoordinateRing f)) S
  let : IsFractionRing S (FractionRing (CoordinateRing f)) :=
    IsIntegralClosure.isFractionRing_of_finite_extension
      (ProjectionBase K) (ProjectionFunctionField K)
      (FractionRing (CoordinateRing f)) S
  let hTorsionFreeS : Module.IsTorsionFree (ProjectionBase K) S :=
    FunctionFieldPrimeDivisor.integralClosure_isTorsionFree_of_algebraMap_injective
      (A := ProjectionBase K) (B := S)
      hProjectionFraction_injective
  let hFlat : Module.Flat (ProjectionBase K) S := by
    let : Module.IsTorsionFree (ProjectionBase K) S :=
      hTorsionFreeS
    infer_instance
  let : Module.Flat (ProjectionBase K) S := hFlat
  let : (projectionPointIdeal (K := K) p).IsPrime :=
    projectionPointIdeal_isPrime p
  let toFiniteDivisorOver :
      CenteredPrimeDivisor (K := K) p →
        PrimeDivisorCounting.FiniteDivisorOver
          (K := K) (S := S)
          (F := FractionRing (CoordinateRing f))
          (projectionPointIdeal (K := K) p) :=
    fun v => by
      let ιS :=
        IsScalarTower.toAlgHom K S
          (FractionRing (CoordinateRing f))
      have hfiniteBase :
          v.divisor.FiniteAlong
            (IsScalarTower.toAlgHom K (ProjectionBase K)
              (FractionRing (CoordinateRing f))) := by
        intro r
        change
          algebraMap (ProjectionBase K)
              (FractionRing (CoordinateRing f)) r ∈
            v.divisor.valuationSubring
        rw [IsScalarTower.algebraMap_apply
          (ProjectionBase K) (CoordinateRing f)
          (FractionRing (CoordinateRing f))]
        exact v.finite (algebraMap (ProjectionBase K)
          (CoordinateRing f) r)
      have hfiniteS : v.divisor.FiniteAlong ιS := by
        exact v.divisor.finiteAlong_integralClosure
          (A := ProjectionBase K) (B := S) hfiniteBase
      refine
        { divisor := v.divisor
          finite := hfiniteS
          center_liesOver := ?_ }
      ext r
      change
        algebraMap (ProjectionBase K) (CoordinateRing f) r ∈
            pointIdeal p ↔
          algebraMap (ProjectionBase K) S r ∈
            v.divisor.centerAlong ιS hfiniteS
      rw [← v.center_eq]
      rw [v.divisor.mem_centerAlong_iff_mem_nonunits,
        v.divisor.mem_centerAlong_iff_mem_nonunits]
      change
        algebraMap (CoordinateRing f)
              (FractionRing (CoordinateRing f))
              (algebraMap (ProjectionBase K) (CoordinateRing f) r) ∈
            v.divisor.valuationSubring.nonunits ↔
          algebraMap S (FractionRing (CoordinateRing f))
              (algebraMap (ProjectionBase K) S r) ∈
            v.divisor.valuationSubring.nonunits
      rw [← IsScalarTower.algebraMap_apply
          (ProjectionBase K) (CoordinateRing f)
          (FractionRing (CoordinateRing f)),
        ← IsScalarTower.algebraMap_apply
          (ProjectionBase K) S
          (FractionRing (CoordinateRing f))]
  have toFiniteDivisorOver_injective :
      Function.Injective toFiniteDivisorOver := by
    intro v w h
    apply CenteredPrimeDivisor.ext
    exact congrArg
      PrimeDivisorCounting.FiniteDivisorOver.divisor h
  let toPrimeOver :
      CenteredPrimeDivisor (K := K) p →
        (projectionPointIdeal (K := K) p).primesOver S :=
    fun v ↦
      PrimeDivisorCounting.FiniteDivisorOver.centerMap
        (toFiniteDivisorOver v)
  have toPrimeOver_injective : Function.Injective toPrimeOver :=
    PrimeDivisorCounting.FiniteDivisorOver.centerMap_injective.comp
      toFiniteDivisorOver_injective
  let : Finite
      ((projectionPointIdeal (K := K) p).primesOver S) :=
    Algebra.QuasiFinite.finite_primesOver
      (R := ProjectionBase K) (S := S)
      (projectionPointIdeal (K := K) p)
  calc
    Nat.card (CenteredPrimeDivisor (K := K) p) ≤
        Nat.card ((projectionPointIdeal (K := K) p).primesOver S) :=
      Nat.card_le_card_of_injective
        toPrimeOver toPrimeOver_injective
    _ ≤ Module.finrank (ProjectionBase K) S :=
      PrimeCounting.card_primesOver_le_finrank
        (projectionPointIdeal (K := K) p)
    _ = Module.finrank (ProjectionFunctionField K)
          (FractionRing (CoordinateRing f)) :=
      integralClosure_finrank_eq_of_algebraMap_injective
        (ProjectionBase K) (ProjectionFunctionField K)
        (FractionRing (CoordinateRing f)) S
        hProjectionFraction_injective
    _ ≤ MvPolynomial.totalDegree f :=
      functionField_finrank_le_totalDegree f hirr hmonic

end CenteredPrimeDivisorBound
end Chapter06
end FieldArithmetic
