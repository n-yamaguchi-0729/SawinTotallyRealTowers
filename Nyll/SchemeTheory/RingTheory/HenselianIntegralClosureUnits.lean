/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.HenselianIntegralDomainLocal
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Units of integral elements over a Henselian base

The integral closure of a Henselian local ring in a field is local. Inside
a normal local ring with that fraction field, the integral closure embeds
by the native integral-element constructor. Its map is local because its
maximal-ideal contraction lies over the maximal ideal of the base.
Consequently a base-linear field automorphism preserves whether an integral
element is a unit in the specified normal local ring.
-/

noncomputable section

namespace SchemeTheory

universe u v w

section Lift

variable (R : Type u) (T : Type v) (L : Type w)
  [CommRing R] [CommRing T] [IsIntegrallyClosed T]
  [Field L] [Algebra R T] [Algebra T L] [IsFractionRing T L]
  [Algebra R L] [IsScalarTower R T L]

private def integralClosureToNormalRing : integralClosure R L →+* T where
  toFun c := IsIntegralClosure.mk' T (c : L) (c.property.tower_top (A := T))
  map_one' := IsIntegralClosure.mk'_one (R := T) T
  map_zero' := IsIntegralClosure.mk'_zero (R := T) T
  map_add' c d := IsIntegralClosure.mk'_add T (c : L) (d : L)
    (c.property.tower_top (A := T)) (d.property.tower_top (A := T))
  map_mul' c d := IsIntegralClosure.mk'_mul T (c : L) (d : L)
    (c.property.tower_top (A := T)) (d.property.tower_top (A := T))

private theorem integralClosureToNormalRing_evaluation (c : integralClosure R L) :
    algebraMap T L (integralClosureToNormalRing R T L c) = (c : L) :=
  IsIntegralClosure.algebraMap_mk' T (c : L) (c.property.tower_top (A := T))

private theorem integralClosureToNormalRing_comp :
    (integralClosureToNormalRing R T L).comp (algebraMap R (integralClosure R L)) =
      algebraMap R T := by
  apply RingHom.ext
  intro r
  apply IsFractionRing.injective T L
  exact (integralClosureToNormalRing_evaluation R T L
    (algebraMap R (integralClosure R L) r)).trans
      (IsScalarTower.algebraMap_apply R T L r)

end Lift

section Local

variable (R : Type u) (T : Type v) (L : Type w)
  [CommRing R] [HenselianLocalRing R]
  [CommRing T] [IsIntegrallyClosed T] [IsLocalRing T]
  [Field L] [Algebra R T] [Algebra T L] [IsFractionRing T L]
  [Algebra R L] [IsScalarTower R T L] [IsLocalHom (algebraMap R T)]

private theorem integralClosureToNormalRing_isLocalHom :
    IsLocalHom (integralClosureToNormalRing R T L) := by
  let C := integralClosure R L
  have : IsLocalRing C := isLocalRing_of_integral_domain_henselian R C
  let k : C →+* T := integralClosureToNormalRing R T L
  let P : Ideal C := (IsLocalRing.maximalIdeal T).comap k
  have : P.IsPrime := Ideal.comap_isPrime k (IsLocalRing.maximalIdeal T)
  have hPbase : P.comap (algebraMap R C) = IsLocalRing.maximalIdeal R :=
    (Ideal.comap_comap (I := IsLocalRing.maximalIdeal T) (algebraMap R C) k).trans
      ((congrArg (fun f : R →+* T => (IsLocalRing.maximalIdeal T).comap f)
        (integralClosureToNormalRing_comp R T L)).trans
          (IsLocalRing.maximalIdeal_comap (algebraMap R T)))
  have hPmax : P.IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (algebraMap R C)
      (algebraMap_isIntegral_iff.mpr inferInstance) P (by
        rw [hPbase]
        infer_instance)
  have hP : P = IsLocalRing.maximalIdeal C := IsLocalRing.eq_maximalIdeal hPmax
  exact ((IsLocalRing.local_hom_TFAE k).out 5 1).mp hP

/-- A base-linear automorphism of the fraction field preserves unit status
for elements integral over the Henselian local base, in the given normal
local overring. Both elements and their equality in the field are actual
input elements; no extension of the automorphism to the overring is assumed. -/
theorem isUnit_iff_of_henselian_integral_conjugate
    (e : L ≃ₐ[R] L) (t t' : T)
    (ht : IsIntegral R (algebraMap T L t))
    (he : algebraMap T L t' = e (algebraMap T L t)) :
    IsUnit t' ↔ IsUnit t := by
  let C := integralClosure R L
  let k : C →+* T := integralClosureToNormalRing R T L
  have : IsLocalHom k := integralClosureToNormalRing_isLocalHom R T L
  let c : C := ⟨algebraMap T L t, ht⟩
  let eC : C ≃ₐ[R] C := e.mapIntegralClosure
  have : IsLocalHom eC.toRingHom :=
    isLocalHom_of_leftInverse eC.symm.toRingHom (fun x => eC.symm_apply_apply x)
  have hc : k c = t :=
    (IsFractionRing.injective T L) (integralClosureToNormalRing_evaluation R T L c)
  have hc' : k (eC c) = t' := by
    apply IsFractionRing.injective T L
    exact (integralClosureToNormalRing_evaluation R T L (eC c)).trans he.symm
  have hunit : IsUnit (k (eC c)) ↔ IsUnit (k c) :=
    (isUnit_map_iff k (eC c)).trans
      ((isUnit_map_iff eC.toRingHom c).trans (isUnit_map_iff k c).symm)
  simpa only [hc, hc'] using hunit

end Local

end SchemeTheory
