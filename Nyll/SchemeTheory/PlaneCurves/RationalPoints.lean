/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.PlaneCurves.CoordinateRing

/-!
# Rational points from coordinate-ring morphisms

Every `K`-algebra map from an affine plane-curve coordinate ring to `K`
comes from a unique rational point.  Consequently, coordinate-ring
equivalences transport rational points and their maximal ideals.
-/

noncomputable section

namespace FieldArithmetic
namespace Chapter06
namespace AffinePlaneCurve

universe u

variable {K : Type u} [Field K]

/-- Recover a rational point from a `K`-algebra map of its coordinate ring. -/
def RationalPoint.ofAlgHom
    {f : BivariatePolynomial K}
    (φ : CoordinateRing f →ₐ[K] K) :
    RationalPoint f where
  coords i := φ (coordinate f i)
  isZero := by
    have hcomp :
        MvPolynomial.aeval (fun i => φ (coordinate f i)) =
          φ.comp (Ideal.Quotient.mkₐ K (equationIdeal f)) := by
      apply MvPolynomial.algHom_ext
      intro i
      simp [coordinate]
    rw [hcomp]
    have hfzero :
        Ideal.Quotient.mk (equationIdeal f) f = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span (Set.mem_singleton f)
    change φ (Ideal.Quotient.mk (equationIdeal f) f) = 0
    rw [hfzero, map_zero]

@[simp]
theorem RationalPoint.ofAlgHom_coords
    {f : BivariatePolynomial K}
    (φ : CoordinateRing f →ₐ[K] K) (i : Fin 2) :
    (RationalPoint.ofAlgHom φ).coords i = φ (coordinate f i) :=
  rfl

/-- Evaluation at the recovered point is the original algebra map. -/
@[simp]
theorem pointEval_ofAlgHom
    {f : BivariatePolynomial K}
    (φ : CoordinateRing f →ₐ[K] K) :
    pointEval (RationalPoint.ofAlgHom φ) = φ := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  simp [pointEval_mk, coordinate]

/-- Transport a rational point contravariantly along a coordinate-ring equivalence. -/
def RationalPoint.mapCoordinateRingEquiv
    {f g : BivariatePolynomial K}
    (e : CoordinateRing f ≃ₐ[K] CoordinateRing g)
    (p : RationalPoint f) :
    RationalPoint g :=
  RationalPoint.ofAlgHom
    ((pointEval p).comp e.symm.toAlgHom)

@[simp]
theorem pointEval_mapCoordinateRingEquiv
    {f g : BivariatePolynomial K}
    (e : CoordinateRing f ≃ₐ[K] CoordinateRing g)
    (p : RationalPoint f) :
    pointEval (p.mapCoordinateRingEquiv e) =
      (pointEval p).comp e.symm.toAlgHom := by
  exact pointEval_ofAlgHom _

/-- The point ideal is carried to the point ideal of the transported point. -/
theorem map_pointIdeal_mapCoordinateRingEquiv
    {f g : BivariatePolynomial K}
    (e : CoordinateRing f ≃ₐ[K] CoordinateRing g)
    (p : RationalPoint f) :
    (pointIdeal p).map e.toRingEquiv.toRingHom =
      pointIdeal (p.mapCoordinateRingEquiv e) := by
  ext x
  constructor
  · intro hx
    have hx' :
        e.symm x ∈
          ((pointIdeal p).map e.toRingEquiv.toRingHom).comap
            e.toRingEquiv.toRingHom := by
      change e (e.symm x) ∈
        (pointIdeal p).map e.toRingEquiv.toRingHom
      simpa using hx
    rw [Ideal.comap_map_of_bijective
      e.toRingEquiv.toRingHom e.bijective] at hx'
    rw [mem_pointIdeal_iff,
      pointEval_mapCoordinateRingEquiv]
    exact hx'
  · intro hx
    rw [mem_pointIdeal_iff,
      pointEval_mapCoordinateRingEquiv] at hx
    have hx' : e.symm x ∈ pointIdeal p := by
      rw [mem_pointIdeal_iff]
      exact hx
    have hmap :=
      Ideal.mem_map_of_mem e.toRingEquiv.toRingHom hx'
    simpa using hmap

end AffinePlaneCurve
end Chapter06
end FieldArithmetic
