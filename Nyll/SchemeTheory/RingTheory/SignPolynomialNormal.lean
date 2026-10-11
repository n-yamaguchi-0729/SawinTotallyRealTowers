/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.SignPolynomialFinite
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.Algebra.Subalgebra.Tower

/-! # Normality and the integral closure for the sign quotient

Normality descends because a polynomial quotient of two invariant polynomials
is itself invariant. The polynomial ring is the integral closure of the
quadratic subalgebra in its own fraction field, using its original inclusion.
-/

noncomputable section

namespace SchemeTheory.SignPolynomial

open MvPolynomial

/-- The canonical inclusion of fraction rings, using only ring-hom data. -/
private noncomputable def subringFractionLift
    {B : Type*} [CommRing B] [IsDomain B] (S : Subring B) :
    FractionRing S →+* FractionRing B :=
  IsFractionRing.lift (g := (algebraMap B (FractionRing B)).comp S.subtype)
    ((IsFractionRing.injective B (FractionRing B)).comp Subtype.val_injective)

/-- The fraction inclusion extends the original subtype inclusion. -/
private theorem subringFractionLift_algebraMap
    {B : Type*} [CommRing B] [IsDomain B] (S : Subring B) (a : S) :
    subringFractionLift S (algebraMap S (FractionRing S) a) =
      algebraMap B (FractionRing B) (a : B) := by
  exact IsFractionRing.lift_algebraMap
    (g := (algebraMap B (FractionRing B)).comp S.subtype)
    ((IsFractionRing.injective B (FractionRing B)).comp Subtype.val_injective) a

/-- Transport integrality through the literal commuting square of ring maps. -/
private theorem subringFractionLift_isIntegral
    {B : Type*} [CommRing B] [IsDomain B] (S : Subring B)
    (x : FractionRing S) (hx : IsIntegral S x) :
    IsIntegral B (subringFractionLift S x) := by
  apply IsIntegral.map_of_comp_eq S.subtype (subringFractionLift S) ?_ hx
  apply RingHom.ext
  intro a
  exact (subringFractionLift_algebraMap S a).symm

/-- Choose a fraction presentation with its denominator nonzero in the base ring. -/
private theorem fractionRing_exists_div_ne_zero
    (R : Type*) [CommRing R] [IsDomain R] (x : FractionRing R) :
    ∃ a d : R, d ≠ 0 ∧
      algebraMap R (FractionRing R) a / algebraMap R (FractionRing R) d = x := by
  obtain ⟨a, d, hd, hx⟩ := IsFractionRing.div_surjective R x
  exact ⟨a, d, nonZeroDivisors.ne_zero hd, hx⟩

/-- A fraction whose image is a polynomial already comes from the subring
when that subring is closed under quotients in the ambient ring. -/
private theorem subringFractionLift_preimage
    {B : Type*} [CommRing B] [IsDomain B] (S : Subring B)
    (hdiv : ∀ (b : B) (a : S), a ≠ 0 → b * (a : B) ∈ S → b ∈ S)
    (x : FractionRing S) (b : B)
    (hb : algebraMap B (FractionRing B) b = subringFractionLift S x) :
    ∃ a : S, algebraMap S (FractionRing S) a = x := by
  obtain ⟨a, d, hd0, rfl⟩ := fractionRing_exists_div_ne_zero S x
  have hdB : (d : B) ≠ 0 := by
    intro h
    exact hd0 (Subtype.ext h)
  have hdL : algebraMap B (FractionRing B) (d : B) ≠ 0 := by
    intro h
    apply hdB
    apply IsFractionRing.injective B (FractionRing B)
    exact h.trans (map_zero (algebraMap B (FractionRing B))).symm
  have hb' : algebraMap B (FractionRing B) b =
      algebraMap B (FractionRing B) (a : B) /
        algebraMap B (FractionRing B) (d : B) := by
    simpa only [map_div₀, subringFractionLift_algebraMap] using hb
  have hmul : b * (d : B) = (a : B) := by
    apply IsFractionRing.injective B (FractionRing B)
    rw [map_mul]
    exact (eq_div_iff hdL).mp hb'
  have hbS : b ∈ S := hdiv b d hd0 (hmul.symm ▸ a.property)
  refine ⟨⟨b, hbS⟩, (subringFractionLift S).injective ?_⟩
  rw [subringFractionLift_algebraMap]
  exact hb

private theorem subring_isIntegrallyClosed_of_mul_mem
    {B : Type*} [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
    (S : Subring B)
    (hdiv : ∀ (b : B) (a : S), a ≠ 0 → b * (a : B) ∈ S → b ∈ S) :
    IsIntegrallyClosed S := by
  apply (isIntegrallyClosed_iff (FractionRing S)).mpr
  intro x hx
  obtain ⟨b, hb⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral
    (subringFractionLift_isIntegral S x hx)
  exact subringFractionLift_preimage S hdiv x b hb

variable (k : Type*) [Field k] (n : ℕ)

/-- A polynomial quotient with invariant nonzero denominator is invariant. -/
theorem mem_quadratic_of_mul_mem (htwo : (2 : k) ≠ 0)
    (p : MvPolynomial (Fin n) k) (a : quadraticSubalgebra k n)
    (ha : a ≠ 0) (hpa : p * (a : MvPolynomial (Fin n) k) ∈ quadraticSubalgebra k n) :
    p ∈ quadraticSubalgebra k n := by
  have ha0 : (a : MvPolynomial (Fin n) k) ≠ 0 := by
    intro h
    exact ha (Subtype.ext h)
  have hfixed_a : simultaneousNeg k n (a : MvPolynomial (Fin n) k) = a := by
    apply (mem_fixedSubalgebra_iff k n (a : MvPolynomial (Fin n) k)).mp
    rw [fixedSubalgebra_eq_quadraticSubalgebra k n htwo]
    exact a.property
  have hfixed_pa : simultaneousNeg k n (p * (a : MvPolynomial (Fin n) k)) =
      p * (a : MvPolynomial (Fin n) k) := by
    apply (mem_fixedSubalgebra_iff k n (p * (a : MvPolynomial (Fin n) k))).mp
    rw [fixedSubalgebra_eq_quadraticSubalgebra k n htwo]
    exact hpa
  rw [map_mul, hfixed_a] at hfixed_pa
  rw [← fixedSubalgebra_eq_quadraticSubalgebra k n htwo,
    mem_fixedSubalgebra_iff]
  exact mul_right_cancel₀ ha0 hfixed_pa

/-- The quadratic invariant subalgebra is a normal domain. -/
theorem quadratic_isIntegrallyClosed (htwo : (2 : k) ≠ 0) :
    IsIntegrallyClosed (quadraticSubalgebra k n) := by
  exact subring_isIntegrallyClosed_of_mul_mem (quadraticSubalgebra k n).toSubring
    (mem_quadratic_of_mul_mem k n htwo)

/-- The original polynomial ring is the integral closure in its fraction field. -/
theorem polynomial_isIntegralClosure_quadratic (htwo : (2 : k) ≠ 0) :
    IsIntegralClosure (MvPolynomial (Fin n) k) (quadraticSubalgebra k n)
      (FractionRing (MvPolynomial (Fin n) k)) := by
  have hintegral :
      Algebra.IsIntegral (quadraticSubalgebra k n) (MvPolynomial (Fin n) k) :=
    polynomial_isIntegral_quadratic k n htwo
  exact IsIntegralClosure.of_isIntegrallyClosed
    (MvPolynomial (Fin n) k) (quadraticSubalgebra k n)
    (FractionRing (MvPolynomial (Fin n) k))

end SchemeTheory.SignPolynomial
