/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.FunctionFields.PrimeDivisors.Centered
import Nyll.SchemeTheory.PlaneCurves.MonicChange
import Nyll.SchemeTheory.FunctionFields.PrimeDivisors.Transport
import Nyll.SchemeTheory.PlaneCurves.RationalPoints

/-!
# Transport of centered prime divisors

Coordinate-ring equivalences transport rational points and centered prime
divisors.  Applied to the monic representative of a plane equation, this
removes the literal monicity assumption from the separable-projection form of
Fried--Jarden, Lemma 6.2.2(b).
-/

noncomputable section

namespace FieldArithmetic
namespace Chapter06

open AffinePlaneCurve
open MonicPlaneCurveProjection PlaneCurveMonicNormalization
open CenteredPrimeDivisorBound

universe u

variable {K : Type u} [Field K]

namespace FunctionFieldPrimeDivisor

theorem centerAlong_comap_comp
    {F A B : Type*} [Field F] [CommRing A] [CommRing B]
    [Algebra K F] [Algebra K A] [Algebra K B]
    (v : FunctionFieldPrimeDivisor K F)
    (j : B →ₐ[K] F) (hj : v.FiniteAlong j)
    (e : A →ₐ[K] B) :
    (v.centerAlong j hj).comap e.toRingHom =
      v.centerAlong (j.comp e) (fun a => hj (e a)) := by
  rfl

/--
The center along a model map depends only on the underlying map into the
function field, not on the proof that the map lands in the valuation ring.
-/
theorem centerAlong_congr
    {F A : Type*} [Field F] [CommRing A]
    [Algebra K F] [Algebra K A]
    (v : FunctionFieldPrimeDivisor K F)
    {ι κ : A →ₐ[K] F}
    (hι : v.FiniteAlong ι) (hκ : v.FiniteAlong κ)
    (h : ∀ a, ι a = κ a) :
    v.centerAlong ι hι = v.centerAlong κ hκ := by
  ext a
  rw [v.mem_centerAlong_iff_mem_nonunits,
    v.mem_centerAlong_iff_mem_nonunits, h a]

end FunctionFieldPrimeDivisor

namespace AffinePlaneCurve

@[ext]
theorem RationalPoint.ext
    {f : BivariatePolynomial K} {p q : RationalPoint f}
    (h : p.coords = q.coords) :
    p = q := by
  cases p
  cases q
  cases h
  rfl

@[simp]
theorem RationalPoint.mapCoordinateRingEquiv_symm
    {f g : BivariatePolynomial K}
    (e : CoordinateRing f ≃ₐ[K] CoordinateRing g)
    (p : RationalPoint f) :
    (p.mapCoordinateRingEquiv e).mapCoordinateRingEquiv e.symm = p := by
  apply RationalPoint.ext
  funext i
  change
    ((pointEval (p.mapCoordinateRingEquiv e)).comp e.toAlgHom)
        (coordinate f i) =
      p.coords i
  rw [pointEval_mapCoordinateRingEquiv]
  simp [coordinate]

end AffinePlaneCurve

namespace CenteredPrimeDivisorBound

/-- The fraction-field equivalence induced by a coordinate-ring equivalence. -/
def coordinateFunctionFieldEquiv
    {f g : BivariatePolynomial K}
    [IsDomain (CoordinateRing f)] [IsDomain (CoordinateRing g)]
    (e : CoordinateRing f ≃ₐ[K] CoordinateRing g) :
    FractionRing (CoordinateRing f) ≃ₐ[K]
      FractionRing (CoordinateRing g) :=
  IsFractionRing.algEquivOfAlgEquiv e

@[simp]
theorem coordinateFunctionFieldEquiv_algebraMap
    {f g : BivariatePolynomial K}
    [IsDomain (CoordinateRing f)] [IsDomain (CoordinateRing g)]
    (e : CoordinateRing f ≃ₐ[K] CoordinateRing g)
    (x : CoordinateRing f) :
    coordinateFunctionFieldEquiv e
        (algebraMap (CoordinateRing f)
          (FractionRing (CoordinateRing f)) x) =
      algebraMap (CoordinateRing g)
        (FractionRing (CoordinateRing g)) (e x) :=
  IsFractionRing.algEquivOfAlgEquiv_algebraMap e x

/--
Transport a divisor centered at `p` to the corresponding point under a
coordinate-ring equivalence.
-/
def CenteredPrimeDivisor.mapCoordinateRingEquiv
    {f g : BivariatePolynomial K}
    [IsDomain (CoordinateRing f)] [IsDomain (CoordinateRing g)]
    (e : CoordinateRing f ≃ₐ[K] CoordinateRing g)
    (p : RationalPoint f)
    (v : CenteredPrimeDivisor (K := K) p) :
    CenteredPrimeDivisor (K := K)
      (p.mapCoordinateRingEquiv e) := by
  let ef := coordinateFunctionFieldEquiv e
  let ιf := coordinateRingMap (K := K) (f := f)
  let ιg := coordinateRingMap (K := K) (f := g)
  have hfinite :
      (v.divisor.map ef).FiniteAlong ιg := by
    intro x
    have hx :=
      FunctionFieldPrimeDivisor.finiteAlong_map
        ef v.divisor ιf v.finite (e.symm x)
    change
      ef (algebraMap (CoordinateRing f)
        (FractionRing (CoordinateRing f)) (e.symm x)) ∈
        (v.divisor.map ef).valuationSubring at hx
    change
      algebraMap (CoordinateRing g)
          (FractionRing (CoordinateRing g)) x ∈
        (v.divisor.map ef).valuationSubring
    simpa [ef] using hx
  refine
    { divisor := v.divisor.map ef
      finite := hfinite
      center_eq := ?_ }
  apply
    Ideal.comap_injective_of_surjective
      e.toRingEquiv.toRingHom e.surjective
  have hmaps :
      ιg.comp e.toAlgHom = ef.toAlgHom.comp ιf := by
    apply AlgHom.ext
    intro x
    exact (coordinateFunctionFieldEquiv_algebraMap e x).symm
  calc
    ((v.divisor.map ef).centerAlong ιg hfinite).comap
        e.toRingEquiv.toRingHom =
        (v.divisor.map ef).centerAlong
          (ιg.comp e.toAlgHom)
          (fun x => hfinite (e x)) :=
      v.divisor.map ef |>.centerAlong_comap_comp ιg hfinite e.toAlgHom
    _ =
        (v.divisor.map ef).centerAlong
          (ef.toAlgHom.comp ιf)
          (FunctionFieldPrimeDivisor.finiteAlong_map
            ef v.divisor ιf v.finite) := by
      apply FunctionFieldPrimeDivisor.centerAlong_congr
      intro x
      exact AlgHom.congr_fun hmaps x
    _ = v.divisor.centerAlong ιf v.finite :=
      FunctionFieldPrimeDivisor.centerAlong_map
        ef v.divisor ιf v.finite
    _ = pointIdeal p := v.center_eq
    _ =
        (pointIdeal (p.mapCoordinateRingEquiv e)).comap
          e.toRingEquiv.toRingHom := by
      rw [← AffinePlaneCurve.map_pointIdeal_mapCoordinateRingEquiv e p]
      exact
        (Ideal.comap_map_of_bijective
          e.toRingEquiv.toRingHom e.bijective).symm

@[simp]
theorem CenteredPrimeDivisor.divisor_mapCoordinateRingEquiv
    {f g : BivariatePolynomial K}
    [IsDomain (CoordinateRing f)] [IsDomain (CoordinateRing g)]
    (e : CoordinateRing f ≃ₐ[K] CoordinateRing g)
    (p : RationalPoint f)
    (v : CenteredPrimeDivisor (K := K) p) :
    (v.mapCoordinateRingEquiv e p).divisor =
      v.divisor.map (coordinateFunctionFieldEquiv e) :=
  rfl

@[simp]
theorem CenteredPrimeDivisor.divisor_cast
    {f : BivariatePolynomial K} [IsDomain (CoordinateRing f)]
    {p q : RationalPoint f} (h : p = q)
    (v : CenteredPrimeDivisor (K := K) p) :
    ((h ▸ v) : CenteredPrimeDivisor (K := K) q).divisor =
      v.divisor := by
  cases h
  rfl

theorem CenteredPrimeDivisor.mapCoordinateRingEquiv_injective
    {f g : BivariatePolynomial K}
    [IsDomain (CoordinateRing f)] [IsDomain (CoordinateRing g)]
    (e : CoordinateRing f ≃ₐ[K] CoordinateRing g)
    (p : RationalPoint f) :
    Function.Injective
      (CenteredPrimeDivisor.mapCoordinateRingEquiv
        (K := K) e p) := by
  intro v w hvw
  apply CenteredPrimeDivisor.ext
  apply
    (FunctionFieldPrimeDivisor.equivOfAlgEquiv
      (coordinateFunctionFieldEquiv e)).injective
  exact congrArg CenteredPrimeDivisor.divisor hvw

theorem CenteredPrimeDivisor.mapCoordinateRingEquiv_surjective
    {f g : BivariatePolynomial K}
    [IsDomain (CoordinateRing f)] [IsDomain (CoordinateRing g)]
    (e : CoordinateRing f ≃ₐ[K] CoordinateRing g)
    (p : RationalPoint f) :
    Function.Surjective
      (CenteredPrimeDivisor.mapCoordinateRingEquiv
        (K := K) e p) := by
  intro w
  let vback :=
    w.mapCoordinateRingEquiv e.symm
      (p.mapCoordinateRingEquiv e)
  have hp :
      (p.mapCoordinateRingEquiv e).mapCoordinateRingEquiv e.symm = p :=
    AffinePlaneCurve.RationalPoint.mapCoordinateRingEquiv_symm e p
  let v : CenteredPrimeDivisor (K := K) p :=
    hp ▸ vback
  refine ⟨v, ?_⟩
  apply CenteredPrimeDivisor.ext
  simp only [CenteredPrimeDivisor.divisor_mapCoordinateRingEquiv]
  simpa [v, vback, coordinateFunctionFieldEquiv] using
    (FunctionFieldPrimeDivisor.map_symm_map
      (coordinateFunctionFieldEquiv e).symm w.divisor)

/-- Centered prime divisors are invariant under coordinate-ring equivalence. -/
def CenteredPrimeDivisor.equivCoordinateRingEquiv
    {f g : BivariatePolynomial K}
    [IsDomain (CoordinateRing f)] [IsDomain (CoordinateRing g)]
    (e : CoordinateRing f ≃ₐ[K] CoordinateRing g)
    (p : RationalPoint f) :
    CenteredPrimeDivisor (K := K) p ≃
      CenteredPrimeDivisor (K := K)
        (p.mapCoordinateRingEquiv e) :=
  Equiv.ofBijective
    (CenteredPrimeDivisor.mapCoordinateRingEquiv
      (K := K) e p)
    ⟨CenteredPrimeDivisor.mapCoordinateRingEquiv_injective
        (K := K) e p,
      CenteredPrimeDivisor.mapCoordinateRingEquiv_surjective
        (K := K) e p⟩

/--
The projection attached to a chosen monic representative is separable.

This packages the local domain and algebra structures used by
`card_centeredPrimeDivisor_le_totalDegree_of_monicRepresentative`.
-/
def MonicRepresentativeProjectionSeparable
    {f : BivariatePolynomial K} (hirr : Irreducible f)
    (c : Fin 1 → K)
    (h : IsUnit
      (yPolynomial (linearChangeY c f)).leadingCoeff) : Prop := by
  let g := monicRepresentative f c h
  let hg : Irreducible g :=
    monicRepresentative_irreducible hirr c h
  let hmonic : (yPolynomial g).Monic :=
    monicRepresentative_monic f c h
  letI : IsDomain (CoordinateRing g) :=
    coordinateRing_isDomain hg
  letI : Algebra (ProjectionFunctionField K)
      (FractionRing (CoordinateRing g)) :=
    functionFieldAlgebra g hg hmonic
  exact
    Algebra.IsSeparable (ProjectionFunctionField K)
      (FractionRing (CoordinateRing g))

/--
After an invertible linear coordinate change and unit rescaling, the
separable-projection bound for a monic equation bounds the centered prime
divisors of the original plane curve.

Thus literal monicity is a choice of coordinates rather than a hypothesis on
the original equation.
-/
theorem card_centeredPrimeDivisor_le_totalDegree_of_monicRepresentative
    {f : BivariatePolynomial K} (hirr : Irreducible f)
    (c : Fin 1 → K)
    (h : IsUnit
      (yPolynomial (linearChangeY c f)).leadingCoeff)
    (p : RationalPoint f)
    (hseparable :
      MonicRepresentativeProjectionSeparable hirr c h) :
    letI : IsDomain (CoordinateRing f) :=
      coordinateRing_isDomain hirr
    Nat.card (CenteredPrimeDivisor (K := K) p) ≤
      MvPolynomial.totalDegree f := by
  let : IsDomain (CoordinateRing f) :=
    coordinateRing_isDomain hirr
  let g := monicRepresentative f c h
  have hg : Irreducible g :=
    monicRepresentative_irreducible hirr c h
  have hmonic : (yPolynomial g).Monic :=
    monicRepresentative_monic f c h
  let : IsDomain (CoordinateRing g) :=
    coordinateRing_isDomain hg
  let : Algebra (ProjectionFunctionField K)
      (FractionRing (CoordinateRing g)) :=
    functionFieldAlgebra g hg hmonic
  have hseparable' :
      Algebra.IsSeparable (ProjectionFunctionField K)
        (FractionRing (CoordinateRing g)) := by
    simpa [MonicRepresentativeProjectionSeparable, g] using
      hseparable
  let e : CoordinateRing f ≃ₐ[K] CoordinateRing g :=
    coordinateRingEquivMonicRepresentative f c h
  calc
    Nat.card (CenteredPrimeDivisor (K := K) p) =
        Nat.card
          (CenteredPrimeDivisor (K := K)
            (p.mapCoordinateRingEquiv e)) :=
      Nat.card_congr
        (CenteredPrimeDivisor.equivCoordinateRingEquiv
          (K := K) e p)
    _ ≤ MvPolynomial.totalDegree g :=
      card_centeredPrimeDivisor_le_totalDegree
        hg hmonic (p.mapCoordinateRingEquiv e) hseparable'
    _ = MvPolynomial.totalDegree f :=
      totalDegree_monicRepresentative hirr.ne_zero c h

end CenteredPrimeDivisorBound

end Chapter06
end FieldArithmetic
