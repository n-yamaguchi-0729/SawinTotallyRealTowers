/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.PlaneCurves.CoordinateRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Algebraic.Integral

/-!
# Monic projections of affine plane curves

This file isolates the finite-degree input used in Fried--Jarden, Lemma
6.2.2(b),(d).  If the equation of a plane curve is monic in `Y`, its
coordinate ring is a finite free algebra over the polynomial ring in `X`.
After passing to fraction fields, the same rank is the degree in `Y`, hence
is bounded by the total degree of the equation.
-/

noncomputable section

namespace FieldArithmetic
namespace Chapter06
namespace MonicPlaneCurveProjection

open MvPolynomial Polynomial
open AffinePlaneCurve

universe u

variable {K : Type u} [Field K]

/-- The coefficient ring `K[X]`, represented as the one-variable
multivariate polynomial ring used by `MvPolynomial.finSuccEquiv`. -/
abbrev ProjectionBase (K : Type u) [Field K] :=
  MvPolynomial (Fin 1) K

/-- The rational function field `K(X)`. -/
abbrev ProjectionFunctionField (K : Type u) [Field K] :=
  FractionRing (ProjectionBase K)

/-- Exchange the two affine coordinates. -/
def coordinateSwap : Fin 2 ≃ Fin 2 :=
  Equiv.swap (0 : Fin 2) (1 : Fin 2)

/--
View a bivariate polynomial as a polynomial in the original `Y` variable
with coefficients in `K[X]`.
-/
def asPolynomialY :
    BivariatePolynomial K ≃ₐ[K] Polynomial (ProjectionBase K) :=
  (MvPolynomial.renameEquiv K coordinateSwap).trans
    (MvPolynomial.finSuccEquiv K 1)

/-- A bivariate equation, viewed as a polynomial in `Y` over `K[X]`. -/
def yPolynomial (f : BivariatePolynomial K) :
    Polynomial (ProjectionBase K) :=
  asPolynomialY f

/-- The degree of a bivariate equation in `Y`. -/
def degreeY (f : BivariatePolynomial K) : ℕ :=
  (yPolynomial f).natDegree

@[simp]
theorem asPolynomialY_apply (f : BivariatePolynomial K) :
    asPolynomialY f =
      MvPolynomial.finSuccEquiv K 1
        (MvPolynomial.rename coordinateSwap f) :=
  rfl

@[simp]
theorem asPolynomialY_X :
    asPolynomialY (K := K) (MvPolynomial.X (R := K) (0 : Fin 2)) =
      Polynomial.C (MvPolynomial.X (R := K) (0 : Fin 1)) := by
  rw [asPolynomialY_apply, MvPolynomial.rename_X]
  rw [show coordinateSwap (0 : Fin 2) = 1 by decide]
  change
    MvPolynomial.finSuccEquiv K 1 (MvPolynomial.X (R := K) (1 : Fin 2)) =
      Polynomial.C (MvPolynomial.X (R := K) (0 : Fin 1))
  exact
    MvPolynomial.finSuccEquiv_X_succ
      (R := K) (n := 1) (j := (0 : Fin 1))

@[simp]
theorem asPolynomialY_Y :
    asPolynomialY (K := K) (MvPolynomial.X (R := K) (1 : Fin 2)) =
      (Polynomial.X : Polynomial (ProjectionBase K)) := by
  rw [asPolynomialY_apply, MvPolynomial.rename_X]
  rw [show coordinateSwap (1 : Fin 2) = 0 by decide]
  change
    MvPolynomial.finSuccEquiv K 1 (MvPolynomial.X (R := K) (0 : Fin 2)) =
      Polynomial.X
  exact MvPolynomial.finSuccEquiv_X_zero (R := K) (n := 1)

/-- Degree in `Y` is bounded by total degree. -/
theorem degreeY_le_totalDegree (f : BivariatePolynomial K) :
    degreeY f ≤ MvPolynomial.totalDegree f := by
  rw [degreeY, yPolynomial, asPolynomialY_apply,
    MvPolynomial.natDegree_finSuccEquiv]
  exact
    (MvPolynomial.degreeOf_le_totalDegree
      (MvPolynomial.rename coordinateSwap f) 0).trans_eq
      (MvPolynomial.totalDegree_renameEquiv coordinateSwap f)

/-- Irreducibility is preserved by viewing the equation as a polynomial in
`Y`. -/
theorem yPolynomial_irreducible
    {f : BivariatePolynomial K} (hf : Irreducible f) :
    Irreducible (yPolynomial f) := by
  exact hf.map (asPolynomialY (K := K)).toMulEquiv

/-- An irreducible monic equation has positive degree in `Y`. -/
theorem degreeY_pos
    {f : BivariatePolynomial K} (hirr : Irreducible f)
    (hmonic : (yPolynomial f).Monic) :
    0 < degreeY f := by
  rw [Nat.pos_iff_ne_zero, degreeY]
  intro hzero
  have hone : yPolynomial f = 1 :=
    hmonic.natDegree_eq_zero.mp hzero
  exact (yPolynomial_irreducible hirr).not_isUnit
    (hone.symm ▸ isUnit_one)

/-- The polynomial-quotient model attached to the `Y`-projection. -/
abbrev ProjectionModel (f : BivariatePolynomial K) :=
  Polynomial (ProjectionBase K) ⧸ Ideal.span ({yPolynomial f} : Set _)

theorem mapped_equationIdeal (f : BivariatePolynomial K) :
    (equationIdeal f).map
      (asPolynomialY (K := K)).toRingEquiv.toRingHom =
      Ideal.span ({yPolynomial f} : Set _) := by
  rw [equationIdeal, Ideal.map_span]
  simp [yPolynomial]

/-- The coordinate ring and the polynomial quotient are canonically
equivalent as `K`-algebras. -/
def coordinateRingEquivProjectionModel (f : BivariatePolynomial K) :
    CoordinateRing f ≃ₐ[K] ProjectionModel f :=
  Ideal.quotientEquivAlg
    (equationIdeal f)
    (Ideal.span ({yPolynomial f} : Set _))
    (asPolynomialY (K := K))
    (mapped_equationIdeal f).symm

/--
The `K[X]`-algebra structure on the coordinate ring induced by projection
to the `X`-axis.
-/
@[reducible]
def projectionAlgebra (f : BivariatePolynomial K) :
    Algebra (ProjectionBase K) (CoordinateRing f) :=
  ((coordinateRingEquivProjectionModel f).symm.toRingHom.comp
    (algebraMap (ProjectionBase K) (ProjectionModel f))).toAlgebra

local instance projectionAlgebraInstance (f : BivariatePolynomial K) :
    Algebra (ProjectionBase K) (CoordinateRing f) :=
  projectionAlgebra f

/-- The polynomial-quotient equivalence, now over the projection base. -/
def coordinateRingEquivProjection (f : BivariatePolynomial K) :
    @AlgEquiv (ProjectionBase K) (CoordinateRing f) (ProjectionModel f)
      _ _ _ (projectionAlgebra f) _ := by
  letI : Algebra (ProjectionBase K) (CoordinateRing f) :=
    projectionAlgebra f
  exact
    { (coordinateRingEquivProjectionModel f).toRingEquiv with
      commutes' := fun a => by
        simp [RingHom.algebraMap_toAlgebra] }

/-- The monic quotient power basis, transported to the coordinate ring. -/
def coordinateRingPowerBasis
    (f : BivariatePolynomial K) (hf : (yPolynomial f).Monic) :
    @PowerBasis (ProjectionBase K) (CoordinateRing f)
      _ _ (projectionAlgebra f) := by
  letI : Algebra (ProjectionBase K) (CoordinateRing f) :=
    projectionAlgebra f
  exact
    PowerBasis.map
      (AdjoinRoot.powerBasis' hf)
      (coordinateRingEquivProjection f).symm

@[simp]
theorem coordinateRingPowerBasis_dim
    (f : BivariatePolynomial K) (hf : (yPolynomial f).Monic) :
    (coordinateRingPowerBasis f hf).dim = degreeY f := by
  rfl

/-- A monic plane-curve coordinate ring is finite free over `K[X]`. -/
theorem coordinateRing_moduleFinite
    (f : BivariatePolynomial K) (hf : (yPolynomial f).Monic) :
    @Module.Finite (ProjectionBase K) (CoordinateRing f)
      _ _ (projectionAlgebra f).toModule := by
  let : Algebra (ProjectionBase K) (CoordinateRing f) :=
    projectionAlgebra f
  exact (coordinateRingPowerBasis f hf).finite

/-- A monic plane-curve coordinate ring is free over `K[X]`. -/
theorem coordinateRing_moduleFree
    (f : BivariatePolynomial K) (hf : (yPolynomial f).Monic) :
    @Module.Free (ProjectionBase K) (CoordinateRing f)
      _ _ (projectionAlgebra f).toModule := by
  let : Algebra (ProjectionBase K) (CoordinateRing f) :=
    projectionAlgebra f
  exact Module.Free.of_basis (coordinateRingPowerBasis f hf).basis

/-- The module rank of a monic plane-curve coordinate ring is its
degree in `Y`. -/
theorem coordinateRing_finrank
    (f : BivariatePolynomial K) (hf : (yPolynomial f).Monic) :
    @Module.finrank (ProjectionBase K) (CoordinateRing f)
      _ _ (projectionAlgebra f).toModule =
      degreeY f := by
  let : Algebra (ProjectionBase K) (CoordinateRing f) :=
    projectionAlgebra f
  exact (coordinateRingPowerBasis f hf).finrank

/-- Module-finiteness supplies integrality of the coordinate ring over
`K[X]`. -/
theorem coordinateRing_isIntegral
    (f : BivariatePolynomial K) (hf : (yPolynomial f).Monic) :
    @Algebra.IsIntegral (ProjectionBase K) (CoordinateRing f)
      _ _ (projectionAlgebra f) := by
  let : Algebra (ProjectionBase K) (CoordinateRing f) :=
    projectionAlgebra f
  let : Module.Finite (ProjectionBase K) (CoordinateRing f) :=
    coordinateRing_moduleFinite f hf
  infer_instance

/-- The projection map `K[X] → K[X,Y]/(f)` is injective when the transformed
equation is irreducible and monic. -/
theorem projectionAlgebra_injective
    {f : BivariatePolynomial K} (hirr : Irreducible f)
    (hmonic : (yPolynomial f).Monic) :
    Function.Injective
      (@algebraMap (ProjectionBase K) (CoordinateRing f)
        _ _ (projectionAlgebra f)) := by
  let : Algebra (ProjectionBase K) (CoordinateRing f) :=
    projectionAlgebra f
  have hdegree : (yPolynomial f).degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hmonic.ne_zero]
    exact_mod_cast (degreeY_pos hirr hmonic).ne'
  intro a b hab
  apply AdjoinRoot.of.injective_of_degree_ne_zero hdegree
  rw [← AdjoinRoot.algebraMap_eq]
  exact
    ((coordinateRingEquivProjection f).commutes a).symm.trans <|
      (congrArg (coordinateRingEquivProjection f) hab).trans <|
        (coordinateRingEquivProjection f).commutes b

/--
The field extension `K(X) → Frac(K[X,Y]/(f))` induced by the monic
projection.  Irreducibility supplies the domain structure, while monicity
supplies injectivity of the map from `K[X]`.
-/
@[reducible]
def functionFieldAlgebra
    (f : BivariatePolynomial K) (hirr : Irreducible f)
    (hmonic : (yPolynomial f).Monic) :
    Algebra (ProjectionFunctionField K) (FractionRing (CoordinateRing f)) := by
  letI : IsDomain (CoordinateRing f) :=
    coordinateRing_isDomain hirr
  letI : FaithfulSMul (ProjectionBase K) (CoordinateRing f) :=
    (faithfulSMul_iff_algebraMap_injective
      (ProjectionBase K) (CoordinateRing f)).mpr
      (projectionAlgebra_injective hirr hmonic)
  exact
    FractionRing.liftAlgebra
      (ProjectionBase K) (FractionRing (CoordinateRing f))

/-- The function field is finite-dimensional over `K(X)`. -/
theorem functionField_finiteDimensional
    (f : BivariatePolynomial K) (hirr : Irreducible f)
    (hmonic : (yPolynomial f).Monic) :
    @Module.Finite (ProjectionFunctionField K)
      (FractionRing (CoordinateRing f)) _ _
      (functionFieldAlgebra f hirr hmonic).toModule := by
  let : IsDomain (CoordinateRing f) :=
    coordinateRing_isDomain hirr
  let : FaithfulSMul (ProjectionBase K) (CoordinateRing f) :=
    (faithfulSMul_iff_algebraMap_injective
      (ProjectionBase K) (CoordinateRing f)).mpr
      (projectionAlgebra_injective hirr hmonic)
  let : Module.Finite (ProjectionBase K) (CoordinateRing f) :=
    coordinateRing_moduleFinite f hmonic
  let : Algebra (ProjectionFunctionField K)
      (FractionRing (CoordinateRing f)) :=
    functionFieldAlgebra f hirr hmonic
  let : IsScalarTower (ProjectionBase K) (ProjectionFunctionField K)
      (FractionRing (CoordinateRing f)) :=
    FractionRing.isScalarTower_liftAlgebra
      (ProjectionBase K) (FractionRing (CoordinateRing f))
  apply Module.finite_of_finrank_pos
  rw [IsFractionRing.finrank_eq
    (ProjectionBase K) (ProjectionFunctionField K)
    (CoordinateRing f) (FractionRing (CoordinateRing f))]
  rw [coordinateRing_finrank f hmonic]
  exact degreeY_pos hirr hmonic

/-- Passing to fraction fields preserves the power-basis rank. -/
theorem functionField_finrank
    (f : BivariatePolynomial K) (hirr : Irreducible f)
    (hmonic : (yPolynomial f).Monic) :
    @Module.finrank (ProjectionFunctionField K)
      (FractionRing (CoordinateRing f)) _ _
      (functionFieldAlgebra f hirr hmonic).toModule =
      degreeY f := by
  let : IsDomain (CoordinateRing f) :=
    coordinateRing_isDomain hirr
  let : FaithfulSMul (ProjectionBase K) (CoordinateRing f) :=
    (faithfulSMul_iff_algebraMap_injective
      (ProjectionBase K) (CoordinateRing f)).mpr
      (projectionAlgebra_injective hirr hmonic)
  let : Module.Finite (ProjectionBase K) (CoordinateRing f) :=
    coordinateRing_moduleFinite f hmonic
  let : Algebra (ProjectionFunctionField K)
      (FractionRing (CoordinateRing f)) :=
    functionFieldAlgebra f hirr hmonic
  let : IsScalarTower (ProjectionBase K) (ProjectionFunctionField K)
      (FractionRing (CoordinateRing f)) :=
    FractionRing.isScalarTower_liftAlgebra
      (ProjectionBase K) (FractionRing (CoordinateRing f))
  rw [IsFractionRing.finrank_eq
    (ProjectionBase K) (ProjectionFunctionField K)
    (CoordinateRing f) (FractionRing (CoordinateRing f))]
  exact coordinateRing_finrank f hmonic

/-- The function-field degree is bounded by the total degree of the plane
equation. -/
theorem functionField_finrank_le_totalDegree
    (f : BivariatePolynomial K) (hirr : Irreducible f)
    (hmonic : (yPolynomial f).Monic) :
    @Module.finrank (ProjectionFunctionField K)
      (FractionRing (CoordinateRing f)) _ _
      (functionFieldAlgebra f hirr hmonic).toModule ≤
      MvPolynomial.totalDegree f := by
  rw [functionField_finrank f hirr hmonic]
  exact degreeY_le_totalDegree f

end MonicPlaneCurveProjection
end Chapter06
end FieldArithmetic
