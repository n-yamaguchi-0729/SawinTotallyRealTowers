/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.PlaneCurves.CoordinateRing
import Nyll.SchemeTheory.FunctionFields.PrimeDivisors.Basic
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

/-!
# Degree-one prime divisors have rational centers

This file formalizes Fried--Jarden, Lemma 6.2.2(c), for an arbitrary map from
an affine plane-curve coordinate ring into a function field.  Finiteness at a
prime divisor gives a residue map on the coordinate ring.  When the residue
degree is one, every residue class is the image of a unique constant, so the
residues of the two coordinates define a `K`-rational point whose point ideal
is the center.
-/

noncomputable section

namespace FieldArithmetic
namespace Chapter06
namespace FunctionFieldPrimeDivisor

open AffinePlaneCurve IsLocalRing

universe u v

variable {K : Type u} {F : Type v}
  [Field K] [Field F] [Algebra K F]

/--
Fried--Jarden, Lemma 6.2.2(c): a degree-one prime divisor which is finite
along a plane-curve model map has a `K`-rational center.
-/
theorem exists_rationalPoint_centerAlong_eq_pointIdeal_of_degree_one
    {f : BivariatePolynomial K}
    (ι : CoordinateRing f →ₐ[K] F)
    (v : FunctionFieldPrimeDivisor K F)
    (hfinite : v.FiniteAlong ι)
    (hdegree : v.degree = 1) :
    ∃ p : RationalPoint f,
      v.centerAlong ι hfinite = pointIdeal p := by
  let residueAlong :
      CoordinateRing f →ₐ[K] v.ResidueField :=
    (IsScalarTower.toAlgHom
      K v.valuationSubring v.ResidueField).comp
      (v.finiteAlongAlgHom ι hfinite)
  have hresidue_bijective :
      Function.Bijective (algebraMap K v.ResidueField) := by
    apply Algebra.finrank_eq_one_iff_bijective_algebraMap.mp
    simpa [degree] using hdegree
  let residueEquiv : K ≃ v.ResidueField :=
    Equiv.ofBijective (algebraMap K v.ResidueField)
      hresidue_bijective
  let coords : Fin 2 → K :=
    fun i =>
      residueEquiv.symm (residueAlong (coordinate f i))
  have algebraMap_coords (i : Fin 2) :
      algebraMap K v.ResidueField (coords i) =
        residueAlong (coordinate f i) := by
    change
      residueEquiv
          (residueEquiv.symm
            (residueAlong (coordinate f i))) =
        residueAlong (coordinate f i)
    exact residueEquiv.apply_symm_apply _
  let quotientMap :
      BivariatePolynomial K →ₐ[K] CoordinateRing f :=
    Ideal.Quotient.mkₐ K (equationIdeal f)
  have evaluation_residue_eq :
      MvPolynomial.aeval
          (fun i => algebraMap K v.ResidueField (coords i)) =
        residueAlong.comp quotientMap := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [MvPolynomial.aeval_X, AlgHom.comp_apply]
    change
      algebraMap K v.ResidueField (coords i) =
        residueAlong (coordinate f i)
    exact algebraMap_coords i
  have equation_evaluation_residue_eq_zero :
      MvPolynomial.aeval
          (fun i => algebraMap K v.ResidueField (coords i)) f =
        0 := by
    rw [evaluation_residue_eq]
    change
      residueAlong
          (Ideal.Quotient.mk (equationIdeal f) f) =
        0
    rw [quotient_mk_equation]
    exact map_zero residueAlong
  have equation_evaluation_eq_zero :
      MvPolynomial.aeval coords f = 0 := by
    apply hresidue_bijective.1
    rw [map_zero]
    calc
      algebraMap K v.ResidueField
          (MvPolynomial.aeval coords f) =
          MvPolynomial.aeval
            (fun i => algebraMap K v.ResidueField (coords i)) f := by
        exact
          MvPolynomial.comp_aeval_apply
            (f := coords) (Algebra.ofId K v.ResidueField) f
      _ = 0 := equation_evaluation_residue_eq_zero
  let p : RationalPoint f :=
    ⟨coords, equation_evaluation_eq_zero⟩
  let constantsToResidue : K →ₐ[K] v.ResidueField :=
    Algebra.ofId K v.ResidueField
  have residueAlong_eq_pointEval :
      residueAlong = constantsToResidue.comp (pointEval p) := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply]
    simpa [coordinate, p, constantsToResidue] using
      (algebraMap_coords i).symm
  refine ⟨p, ?_⟩
  ext a
  rw [v.mem_centerAlong_iff_residue_eq_zero ι hfinite,
    mem_pointIdeal_iff]
  change residueAlong a = 0 ↔ pointEval p a = 0
  rw [residueAlong_eq_pointEval]
  change
    algebraMap K v.ResidueField (pointEval p a) = 0 ↔
      pointEval p a = 0
  constructor
  · intro h
    apply hresidue_bijective.1
    simpa using h
  · rintro h
    simp [h]

end FunctionFieldPrimeDivisor
end Chapter06
end FieldArithmetic
