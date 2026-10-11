/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.FunctionFields.PrimeDivisors.Basic
import Nyll.SchemeTheory.PlaneCurves.Dimension
import Nyll.SchemeTheory.PlaneCurves.Geometric
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

/-!
# The prime divisor centered at a normal rational point

For an irreducible affine plane curve and a rational point at which the local
ring is normal, the point local ring is a discrete valuation ring.  This file
realizes that local ring as its canonical valuation subring in the fraction
field of the coordinate ring, proves that its residue field has degree one
over the constant field, and characterizes it by its center.
-/

noncomputable section

namespace FieldArithmetic
namespace Chapter06
namespace AffinePlaneCurve

open IsLocalRing

universe u

variable {K : Type u} [Field K]

/-- The local ring of an affine plane curve at a rational point. -/
abbrev PointLocalRing
    {f : BivariatePolynomial K} (p : RationalPoint f) :=
  letI : (pointIdeal p).IsPrime := (pointIdeal_isMaximal p).isPrime
  Localization.AtPrime (pointIdeal p)

/-- A point is normal when its local ring is integrally closed. -/
def IsNormalAt
    {f : BivariatePolynomial K} (p : RationalPoint f) : Prop :=
  IsIntegrallyClosed (PointLocalRing p)

/-- The function field of the irreducible affine coordinate ring. -/
abbrev CoordinateFunctionField (f : BivariatePolynomial K) :=
  FractionRing (CoordinateRing f)

/-- The coordinate ring embedded in its function field. -/
noncomputable def coordinateFunctionFieldMap
    {f : BivariatePolynomial K} [IsDomain (CoordinateRing f)] :
    CoordinateRing f →ₐ[K] CoordinateFunctionField f :=
  IsScalarTower.toAlgHom K (CoordinateRing f) (CoordinateFunctionField f)

/--
The canonical valuation subring obtained from the DVR at a normal rational
point.
-/
noncomputable def normalPointValuationSubring
    {f : BivariatePolynomial K} [IsDomain (CoordinateRing f)]
    (hf : Irreducible f)
    (p : RationalPoint f) (hnormal : IsNormalAt p) :
    ValuationSubring (CoordinateFunctionField f) := by
  letI : (pointIdeal p).IsMaximal := pointIdeal_isMaximal p
  letI : (pointIdeal p).IsPrime := (pointIdeal_isMaximal p).isPrime
  have hnormal' : IsIntegrallyClosed (PointLocalRing p) := by
    simpa [IsNormalAt] using hnormal
  letI : IsDiscreteValuationRing (PointLocalRing p) :=
    pointLocalRing_isDiscreteValuationRing_of_isIntegrallyClosed
      hf p hnormal'
  exact
    ((IsDiscreteValuationRing.maximalIdeal (PointLocalRing p)).valuation
      (CoordinateFunctionField f)).valuationSubring

/-- The normal-point valuation subring is itself a DVR. -/
theorem normalPointValuationSubring_isDiscreteValuationRing
    {f : BivariatePolynomial K} [IsDomain (CoordinateRing f)]
    (hf : Irreducible f)
    (p : RationalPoint f) (hnormal : IsNormalAt p) :
    IsDiscreteValuationRing
      (normalPointValuationSubring hf p hnormal) := by
  let : (pointIdeal p).IsMaximal := pointIdeal_isMaximal p
  let : (pointIdeal p).IsPrime := (pointIdeal_isMaximal p).isPrime
  have hnormal' : IsIntegrallyClosed (PointLocalRing p) := by
    simpa [IsNormalAt] using hnormal
  let : IsDiscreteValuationRing (PointLocalRing p) :=
    pointLocalRing_isDiscreteValuationRing_of_isIntegrallyClosed
      hf p hnormal'
  let e :=
    IsDiscreteValuationRing.equivValuationSubring
      (A := PointLocalRing p) (K := CoordinateFunctionField f)
  change
    IsDiscreteValuationRing
      ((IsDiscreteValuationRing.maximalIdeal (PointLocalRing p)).valuation
        (CoordinateFunctionField f)).valuationSubring
  exact
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e

/--
The discrete `K`-valuation of the coordinate function field determined by a
normal rational point.
-/
noncomputable def normalPointDiscreteKValuation
    {f : BivariatePolynomial K} [IsDomain (CoordinateRing f)]
    (hf : Irreducible f)
    (p : RationalPoint f) (hnormal : IsNormalAt p) :
    DiscreteKValuation K (CoordinateFunctionField f) where
  valuationSubring := normalPointValuationSubring hf p hnormal
  isDiscreteValuationRing :=
    normalPointValuationSubring_isDiscreteValuationRing hf p hnormal
  algebraMap_mem := by
    intro x
    let : (pointIdeal p).IsMaximal := pointIdeal_isMaximal p
    let : (pointIdeal p).IsPrime := (pointIdeal_isMaximal p).isPrime
    have hnormal' : IsIntegrallyClosed (PointLocalRing p) := by
      simpa [IsNormalAt] using hnormal
    let : IsDiscreteValuationRing (PointLocalRing p) :=
      pointLocalRing_isDiscreteValuationRing_of_isIntegrallyClosed
        hf p hnormal'
    change
      (IsDiscreteValuationRing.maximalIdeal (PointLocalRing p)).valuation
          (CoordinateFunctionField f)
          (algebraMap K (CoordinateFunctionField f) x) ≤ 1
    have hconstant :
        algebraMap K (CoordinateFunctionField f) x =
          algebraMap (PointLocalRing p) (CoordinateFunctionField f)
            (algebraMap K (PointLocalRing p) x) := by
      rw [IsScalarTower.algebraMap_apply
        K (CoordinateRing f) (CoordinateFunctionField f)]
      rw [IsScalarTower.algebraMap_apply
        K (CoordinateRing f) (PointLocalRing p)]
      rw [IsScalarTower.algebraMap_apply
        (CoordinateRing f) (PointLocalRing p)
          (CoordinateFunctionField f)]
    rw [hconstant]
    exact
      (IsDiscreteValuationRing.maximalIdeal
        (PointLocalRing p)).valuation_le_one
          (K := CoordinateFunctionField f)
          (algebraMap K (PointLocalRing p) x)

/--
The local ring is canonically isomorphic, as a `K`-algebra, to the valuation
subring just constructed.
-/
noncomputable def normalPointLocalRingEquiv
    {f : BivariatePolynomial K} [IsDomain (CoordinateRing f)]
    (hf : Irreducible f)
    (p : RationalPoint f) (hnormal : IsNormalAt p) :
    PointLocalRing p ≃ₐ[K]
      (normalPointDiscreteKValuation hf p hnormal).valuationSubring := by
  letI : (pointIdeal p).IsMaximal := pointIdeal_isMaximal p
  letI : (pointIdeal p).IsPrime := (pointIdeal_isMaximal p).isPrime
  have hnormal' : IsIntegrallyClosed (PointLocalRing p) := by
    simpa [IsNormalAt] using hnormal
  letI : IsDiscreteValuationRing (PointLocalRing p) :=
    pointLocalRing_isDiscreteValuationRing_of_isIntegrallyClosed
      hf p hnormal'
  let e :=
    IsDiscreteValuationRing.equivValuationSubring
      (A := PointLocalRing p) (K := CoordinateFunctionField f)
  refine
    { e with
      commutes' := ?_ }
  intro x
  apply Subtype.ext
  change
    algebraMap (PointLocalRing p) (CoordinateFunctionField f)
        (algebraMap K (PointLocalRing p) x) =
      algebraMap K (CoordinateFunctionField f) x
  rw [IsScalarTower.algebraMap_apply
    K (CoordinateRing f) (CoordinateFunctionField f)]
  rw [IsScalarTower.algebraMap_apply
    K (CoordinateRing f) (PointLocalRing p)]
  rw [IsScalarTower.algebraMap_apply
    (CoordinateRing f) (PointLocalRing p)
      (CoordinateFunctionField f)]

/--
The residue field of the canonical valuation ring is canonically the constant
field at a rational point.
-/
noncomputable def normalPointResidueEquiv
    {f : BivariatePolynomial K} [IsDomain (CoordinateRing f)]
    (hf : Irreducible f)
    (p : RationalPoint f) (hnormal : IsNormalAt p) :
    K ≃ₐ[K]
      (normalPointDiscreteKValuation hf p hnormal).ResidueField := by
  letI : (pointIdeal p).IsMaximal := pointIdeal_isMaximal p
  letI : (pointIdeal p).IsPrime := (pointIdeal_isMaximal p).isPrime
  let quotientToLocalResidue :
      (CoordinateRing f ⧸ pointIdeal p) ≃ₐ[K]
        (pointIdeal p).ResidueField :=
    AlgEquiv.ofBijective
      (IsScalarTower.toAlgHom K
        (CoordinateRing f ⧸ pointIdeal p)
        (pointIdeal p).ResidueField)
      (pointIdeal p).bijective_algebraMap_quotient_residueField
  let pointToLocalResidue :
      K ≃ₐ[K] (pointIdeal p).ResidueField :=
    (pointResidueEquiv p).symm.trans quotientToLocalResidue
  exact
    pointToLocalResidue.trans
      (IsLocalRing.ResidueField.mapAlgEquiv
        (normalPointLocalRingEquiv hf p hnormal))

/-- The canonical normal-point valuation has finite residue degree. -/
theorem normalPoint_hasFiniteResidueDegree
    {f : BivariatePolynomial K} [IsDomain (CoordinateRing f)]
    (hf : Irreducible f)
    (p : RationalPoint f) (hnormal : IsNormalAt p) :
    HasFiniteResidueDegree K (CoordinateFunctionField f)
      (normalPointDiscreteKValuation hf p hnormal) := by
  let e := normalPointResidueEquiv hf p hnormal
  apply Module.Finite.of_surjective (Algebra.linearMap K _)
  intro y
  refine ⟨e.symm y, ?_⟩
  change
    algebraMap K
        (normalPointDiscreteKValuation hf p hnormal).ResidueField
        (e.symm y) =
      y
  rw [← e.commutes]
  simp

/--
The genuine function-field prime divisor associated to a normal rational
point.
-/
noncomputable def normalPointPrimeDivisor
    {f : BivariatePolynomial K} [IsDomain (CoordinateRing f)]
    (hf : Irreducible f)
    (p : RationalPoint f) (hnormal : IsNormalAt p) :
    FunctionFieldPrimeDivisor K (CoordinateFunctionField f) where
  toDiscreteKValuation :=
    normalPointDiscreteKValuation hf p hnormal
  residueFinite :=
    normalPoint_hasFiniteResidueDegree hf p hnormal

/-- A rational normal point gives a prime divisor of residue degree one. -/
theorem normalPointPrimeDivisor_degree
    {f : BivariatePolynomial K} [IsDomain (CoordinateRing f)]
    (hf : Irreducible f)
    (p : RationalPoint f) (hnormal : IsNormalAt p) :
    (normalPointPrimeDivisor hf p hnormal).degree = 1 := by
  rw [FunctionFieldPrimeDivisor.degree]
  change
    Module.finrank K
      (normalPointDiscreteKValuation hf p hnormal).ResidueField = 1
  rw [← (normalPointResidueEquiv hf p hnormal).toLinearEquiv.finrank_eq,
    Module.finrank_self]

/--
Every element of the affine coordinate ring is finite at the prime divisor
defined by the normal point.
-/
theorem normalPointPrimeDivisor_finiteAlong
    {f : BivariatePolynomial K} [IsDomain (CoordinateRing f)]
    (hf : Irreducible f)
    (p : RationalPoint f) (hnormal : IsNormalAt p) :
    (normalPointPrimeDivisor hf p hnormal).FiniteAlong
      (coordinateFunctionFieldMap (K := K) (f := f)) := by
  intro a
  let : (pointIdeal p).IsMaximal := pointIdeal_isMaximal p
  let : (pointIdeal p).IsPrime := (pointIdeal_isMaximal p).isPrime
  have hnormal' : IsIntegrallyClosed (PointLocalRing p) := by
    simpa [IsNormalAt] using hnormal
  let : IsDiscreteValuationRing (PointLocalRing p) :=
    pointLocalRing_isDiscreteValuationRing_of_isIntegrallyClosed
      hf p hnormal'
  change
    (IsDiscreteValuationRing.maximalIdeal (PointLocalRing p)).valuation
        (CoordinateFunctionField f)
        (algebraMap (CoordinateRing f) (CoordinateFunctionField f) a) ≤ 1
  rw [IsScalarTower.algebraMap_apply
    (CoordinateRing f) (PointLocalRing p)
      (CoordinateFunctionField f)]
  exact
    (IsDiscreteValuationRing.maximalIdeal
      (PointLocalRing p)).valuation_le_one
        (K := CoordinateFunctionField f)
        (algebraMap (CoordinateRing f) (PointLocalRing p) a)

/--
The center of the normal-point prime divisor on the affine coordinate model
is exactly the maximal ideal of the given rational point.
-/
theorem normalPointPrimeDivisor_centerAlong
    {f : BivariatePolynomial K} [IsDomain (CoordinateRing f)]
    (hf : Irreducible f)
    (p : RationalPoint f) (hnormal : IsNormalAt p) :
    (normalPointPrimeDivisor hf p hnormal).centerAlong
        (coordinateFunctionFieldMap (K := K) (f := f))
        (normalPointPrimeDivisor_finiteAlong hf p hnormal) =
      pointIdeal p := by
  let : (pointIdeal p).IsMaximal := pointIdeal_isMaximal p
  let : (pointIdeal p).IsPrime := (pointIdeal_isMaximal p).isPrime
  let v := normalPointPrimeDivisor hf p hnormal
  let ι := coordinateFunctionFieldMap (K := K) (f := f)
  let hfinite : v.FiniteAlong ι :=
    normalPointPrimeDivisor_finiteAlong hf p hnormal
  let e := normalPointLocalRingEquiv hf p hnormal
  change v.centerAlong ι hfinite = pointIdeal p
  apply Ideal.ext
  intro a
  rw [v.mem_centerAlong_iff]
  have helement :
      v.finiteAlongRingHom ι hfinite a =
        e (algebraMap (CoordinateRing f) (PointLocalRing p) a) := by
    apply Subtype.ext
    change
      algebraMap (CoordinateRing f) (CoordinateFunctionField f) a =
        algebraMap (PointLocalRing p) (CoordinateFunctionField f)
          (algebraMap (CoordinateRing f) (PointLocalRing p) a)
    rw [IsScalarTower.algebraMap_apply
      (CoordinateRing f) (PointLocalRing p)
        (CoordinateFunctionField f)]
  rw [helement]
  change
    e (algebraMap (CoordinateRing f) (PointLocalRing p) a) ∈
        maximalIdeal
          (normalPointDiscreteKValuation hf p hnormal).valuationSubring ↔
      a ∈ pointIdeal p
  rw [IsLocalRing.mem_maximalIdeal,
    map_mem_nonunits_iff e, ← IsLocalRing.mem_maximalIdeal]
  exact
    IsLocalization.AtPrime.to_map_mem_maximal_iff
      (PointLocalRing p) (pointIdeal p) a

/--
Any prime divisor finite on the coordinate model and centered at the same
normal point has the canonical valuation subring.

The proof extends the coordinate-model map to the point localization.  This
places the canonical valuation ring inside the competing one; dimension one
and properness then force equality of valuation subrings.
-/
theorem normalPointValuationSubring_unique
    {f : BivariatePolynomial K} [IsDomain (CoordinateRing f)]
    (hf : Irreducible f)
    (p : RationalPoint f) (hnormal : IsNormalAt p)
    (w : FunctionFieldPrimeDivisor K (CoordinateFunctionField f))
    (hw : w.FiniteAlong
      (coordinateFunctionFieldMap (K := K) (f := f)))
    (hcenter :
      w.centerAlong
          (coordinateFunctionFieldMap (K := K) (f := f)) hw =
        pointIdeal p) :
    (normalPointPrimeDivisor hf p hnormal).valuationSubring =
      w.valuationSubring := by
  let : (pointIdeal p).IsMaximal := pointIdeal_isMaximal p
  let : (pointIdeal p).IsPrime := (pointIdeal_isMaximal p).isPrime
  let ι := coordinateFunctionFieldMap (K := K) (f := f)
  let gR : CoordinateRing f →+* w.valuationSubring :=
    w.finiteAlongRingHom ι hw
  have hdenominator :
      ∀ s : (pointIdeal p).primeCompl, IsUnit (gR s) := by
    intro s
    apply IsLocalRing.notMem_maximalIdeal.mp
    intro hs
    have hscenter : (s : CoordinateRing f) ∈
        w.centerAlong ι hw := by
      change
        w.finiteAlongRingHom ι hw (s : CoordinateRing f) ∈
          maximalIdeal w.valuationSubring
      exact hs
    have hsPoint : (s : CoordinateRing f) ∈ pointIdeal p := by
      exact (le_of_eq hcenter) hscenter
    exact s.property hsPoint
  let gO : PointLocalRing p →+* w.valuationSubring :=
    IsLocalization.lift hdenominator
  let wInclusion : w.valuationSubring →+* CoordinateFunctionField f :=
    w.valuationSubring.toSubring.subtype
  have hgO :
      wInclusion.comp gO =
        algebraMap (PointLocalRing p) (CoordinateFunctionField f) := by
    apply IsLocalization.ringHom_ext (pointIdeal p).primeCompl
    apply RingHom.ext
    intro a
    change
      ((gO
          (algebraMap (CoordinateRing f) (PointLocalRing p) a) :
            w.valuationSubring) : CoordinateFunctionField f) =
        algebraMap (PointLocalRing p) (CoordinateFunctionField f)
          (algebraMap (CoordinateRing f) (PointLocalRing p) a)
    rw [IsLocalization.lift_eq hdenominator]
    change
      algebraMap (CoordinateRing f) (CoordinateFunctionField f) a =
        algebraMap (PointLocalRing p) (CoordinateFunctionField f)
          (algebraMap (CoordinateRing f) (PointLocalRing p) a)
    rw [IsScalarTower.algebraMap_apply
      (CoordinateRing f) (PointLocalRing p)
        (CoordinateFunctionField f)]
  have hle :
      (normalPointPrimeDivisor hf p hnormal).valuationSubring ≤
        w.valuationSubring := by
    intro z hz
    change
      z ∈ (normalPointDiscreteKValuation hf p hnormal).valuationSubring at hz
    let e := normalPointLocalRingEquiv hf p hnormal
    let o : PointLocalRing p := e.symm ⟨z, hz⟩
    have he :
        algebraMap (PointLocalRing p) (CoordinateFunctionField f) o = z := by
      have he' :=
        congrArg
          (fun y :
            (normalPointDiscreteKValuation hf p hnormal).valuationSubring =>
              (y : CoordinateFunctionField f))
          (e.apply_symm_apply ⟨z, hz⟩)
      change
        algebraMap (PointLocalRing p) (CoordinateFunctionField f) o = z at he'
      exact he'
    have hgo :
        ((gO o : w.valuationSubring) : CoordinateFunctionField f) = z := by
      calc
        ((gO o : w.valuationSubring) : CoordinateFunctionField f) =
            algebraMap (PointLocalRing p) (CoordinateFunctionField f) o :=
          RingHom.congr_fun hgO o
        _ = z := he
    rw [← hgo]
    exact (gO o).property
  change
    (normalPointDiscreteKValuation hf p hnormal).valuationSubring =
      w.valuationSubring
  exact
    ValuationSubring.eq_of_le_of_ne_top
      (A :=
        (normalPointDiscreteKValuation hf p hnormal).valuationSubring)
      hle w.valuationSubring_ne_top

/--
The canonical normal-point divisor is the unique function-field prime divisor
which is finite on the affine coordinate model and has center `pointIdeal p`.
-/
theorem normalPointPrimeDivisor_unique
    {f : BivariatePolynomial K} [IsDomain (CoordinateRing f)]
    (hf : Irreducible f)
    (p : RationalPoint f) (hnormal : IsNormalAt p)
    (w : FunctionFieldPrimeDivisor K (CoordinateFunctionField f))
    (hw : w.FiniteAlong
      (coordinateFunctionFieldMap (K := K) (f := f)))
    (hcenter :
      w.centerAlong
          (coordinateFunctionFieldMap (K := K) (f := f)) hw =
        pointIdeal p) :
    w = normalPointPrimeDivisor hf p hnormal := by
  have hvaluation :=
    (normalPointValuationSubring_unique
      hf p hnormal w hw hcenter).symm
  cases w with
  | mk wDiscrete wFinite =>
      cases wDiscrete with
      | mk W wDvr wConstants =>
          change W =
            (normalPointPrimeDivisor hf p hnormal).valuationSubring at hvaluation
          subst W
          rfl

/--
Fried--Jarden 6.2.2(a), normal rational-point form: there is a unique prime
divisor finite on the affine coordinate ring and centered at the point, and
its residue degree is one.

The only hypotheses are irreducibility of the curve equation and normality of
the point local ring.  The coordinate-ring domain, the DVR, and residue
finiteness are all constructed above.
-/
theorem proposition_6_2_2_a
    {f : BivariatePolynomial K} (hf : Irreducible f)
    (p : RationalPoint f) (hnormal : IsNormalAt p) :
    letI : IsDomain (CoordinateRing f) := coordinateRing_isDomain hf
    ∃! w : FunctionFieldPrimeDivisor K (CoordinateFunctionField f),
      ∃ hw : w.FiniteAlong
          (coordinateFunctionFieldMap (K := K) (f := f)),
        w.centerAlong
            (coordinateFunctionFieldMap (K := K) (f := f)) hw =
            pointIdeal p ∧
          w.degree = 1 := by
  let : IsDomain (CoordinateRing f) := coordinateRing_isDomain hf
  let v := normalPointPrimeDivisor hf p hnormal
  let hv : v.FiniteAlong
      (coordinateFunctionFieldMap (K := K) (f := f)) :=
    normalPointPrimeDivisor_finiteAlong hf p hnormal
  refine ⟨v, ?_, ?_⟩
  · exact
      ⟨hv,
        normalPointPrimeDivisor_centerAlong hf p hnormal,
        normalPointPrimeDivisor_degree hf p hnormal⟩
  · intro w hwitness
    obtain ⟨hw, hcenter, _⟩ := hwitness
    exact
      normalPointPrimeDivisor_unique
        hf p hnormal w hw hcenter

/--
The absolutely irreducible form of `proposition_6_2_2_a`.  Absolute
irreducibility supplies the irreducibility used in the construction rather
than adding a separate coordinate-ring hypothesis.
-/
theorem proposition_6_2_2_a_of_isAbsolutelyIrreducible
    {f : BivariatePolynomial K} (hf : IsAbsolutelyIrreducible f)
    (p : RationalPoint f) (hnormal : IsNormalAt p) :
    let hirreducible : Irreducible f := hf.irreducible
    letI : IsDomain (CoordinateRing f) :=
      coordinateRing_isDomain hirreducible
    ∃! w : FunctionFieldPrimeDivisor K (CoordinateFunctionField f),
      ∃ hw : w.FiniteAlong
          (coordinateFunctionFieldMap (K := K) (f := f)),
        w.centerAlong
            (coordinateFunctionFieldMap (K := K) (f := f)) hw =
            pointIdeal p ∧
          w.degree = 1 := by
  exact proposition_6_2_2_a hf.irreducible p hnormal

end AffinePlaneCurve
end Chapter06
end FieldArithmetic
