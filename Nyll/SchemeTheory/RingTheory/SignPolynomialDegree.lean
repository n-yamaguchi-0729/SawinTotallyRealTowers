/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.SignPolynomialFinite
import Mathlib.RingTheory.IsGaloisGroup.Defs
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.RingTheory.Localization.FractionRing

/-! # Degree two of the actual simultaneous sign quotient

A nonempty set of variables makes the sign action faithful. The existing
finite-group invariant-field theorem then gives ring rank two, and the
canonical fraction-field extension has the same degree. No algebraic closure
or characteristic-zero hypothesis is imposed.
-/

noncomputable section

namespace SchemeTheory.SignPolynomial

open MvPolynomial

/-- The fraction-ring map induced by the original injective algebra map.
The map, rather than a newly reconstructed scalar tower, owns the field extension. -/
noncomputable def fractionRingInclusion
    (A B : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Algebra A B] [FaithfulSMul A B] : FractionRing A →+* FractionRing B :=
  IsFractionRing.lift (K := FractionRing A) (g := algebraMap A (FractionRing B))
    (FaithfulSMul.algebraMap_injective A (FractionRing B))

/-- The constructed fraction-ring map extends the original inclusion. -/
theorem fractionRingInclusion_algebraMap
    (A B : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Algebra A B] [FaithfulSMul A B] (a : A) :
    fractionRingInclusion A B (algebraMap A (FractionRing A) a) =
      algebraMap A (FractionRing B) a := by
  exact IsFractionRing.lift_algebraMap (K := FractionRing A)
    (g := algebraMap A (FractionRing B))
    (FaithfulSMul.algebraMap_injective A (FractionRing B)) a

private theorem fractionRingInclusion_isScalarTower
    (A B : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Algebra A B] [FaithfulSMul A B] :
    let _fractionAlgebra : Algebra (FractionRing A) (FractionRing B) :=
      (fractionRingInclusion A B).toAlgebra
    IsScalarTower A (FractionRing A) (FractionRing B) := by
  intro _fractionAlgebra
  exact FractionRing.isScalarTower_liftAlgebra A (FractionRing B)

/-- Rank compatibility for the actual fraction-ring inclusion, proved in a
ring-only scope before the polynomial coefficient field is introduced. -/
theorem fractionRingInclusion_finrank
    (A B : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Algebra A B] [FaithfulSMul A B] :
    let _fractionAlgebra : Algebra (FractionRing A) (FractionRing B) :=
      (fractionRingInclusion A B).toAlgebra
    Module.finrank (FractionRing A) (FractionRing B) = Module.finrank A B := by
  intro _fractionAlgebra
  have hscalar : IsScalarTower A (FractionRing A) (FractionRing B) :=
    fractionRingInclusion_isScalarTower A B
  exact IsFractionRing.finrank_eq A (FractionRing A) B (FractionRing B)

variable (k : Type*) [Field k] (n : ℕ)

/-- A variable is moved by the sign involution in characteristic different from two. -/
theorem simultaneousNeg_X_ne (htwo : (2 : k) ≠ 0) (i : Fin n) :
    simultaneousNeg k n (X i) ≠ (X i : MvPolynomial (Fin n) k) := by
  intro h
  have hcoeff : (-1 : k) = 1 := by
    have hc := congrArg (fun p : MvPolynomial (Fin n) k =>
      p.coeff (Finsupp.single i 1)) h
    simpa only [simultaneousNeg_X, MvPolynomial.coeff_neg, MvPolynomial.coeff_X_same] using hc
  apply htwo
  calc
    (2 : k) = 1 + 1 := (one_add_one_eq_two : (1 : k) + 1 = 2).symm
    _ = -1 + 1 := congrArg (fun a : k => a + 1) hcoeff.symm
    _ = 0 := neg_add_cancel 1

/-- The actual sign action is faithful as soon as one variable exists. -/
theorem signAction_faithful (htwo : (2 : k) ≠ 0) (hn : 0 < n) :
    let _action : MulSemiringAction ℤˣ (MvPolynomial (Fin n) k) := signAction k n
    let _smul : SMul ℤˣ (MvPolynomial (Fin n) k) := _action.toSMul
    FaithfulSMul ℤˣ (MvPolynomial (Fin n) k) := by
  intro _action _smul
  constructor
  intro ε δ h
  let i : Fin n := ⟨0, hn⟩
  have hone : _action.smul (1 : ℤˣ) (X i) = X i := _action.one_smul (X i)
  have hneg : _action.smul (-1 : ℤˣ) (X i) = simultaneousNeg k n (X i) :=
    signAction_neg_one k n (X i)
  rcases Int.units_eq_one_or ε with rfl | rfl
  · rcases Int.units_eq_one_or δ with rfl | rfl
    · rfl
    · have hi : _action.smul (1 : ℤˣ) (X i) = _action.smul (-1 : ℤˣ) (X i) := h (X i)
      exact (simultaneousNeg_X_ne k n htwo i
        (hneg.symm.trans (hi.symm.trans hone))).elim
  · rcases Int.units_eq_one_or δ with rfl | rfl
    · have hi : _action.smul (-1 : ℤˣ) (X i) = _action.smul (1 : ℤˣ) (X i) := h (X i)
      exact (simultaneousNeg_X_ne k n htwo i
        (hneg.symm.trans (hi.trans hone))).elim
    · rfl

/-- Multiplication by an invariant polynomial commutes with sign change. -/
theorem signAction_smulCommClass (htwo : (2 : k) ≠ 0) :
    let _action : MulSemiringAction ℤˣ (MvPolynomial (Fin n) k) := signAction k n
    let _smul : SMul ℤˣ (MvPolynomial (Fin n) k) := _action.toSMul
    SMulCommClass ℤˣ (quadraticSubalgebra k n) (MvPolynomial (Fin n) k) := by
  intro _action _smul
  constructor
  intro ε a p
  rw [Algebra.smul_def, Algebra.smul_def, smul_mul']
  have ha : _action.smul ε (a : MvPolynomial (Fin n) k) = a :=
    (forall_signAction_iff_mem_quadraticSubalgebra k n htwo a).mpr a.property ε
  rw [Subalgebra.algebraMap_apply]
  exact congrArg (fun q : MvPolynomial (Fin n) k => q * _action.smul ε p) ha

/-- The order-two group is the Galois group of the literal ring extension B/A. -/
theorem quadratic_isGaloisGroup (htwo : (2 : k) ≠ 0) (hn : 0 < n) :
    let _action : MulSemiringAction ℤˣ (MvPolynomial (Fin n) k) := signAction k n
    IsGaloisGroup ℤˣ (quadraticSubalgebra k n) (MvPolynomial (Fin n) k) := by
  intro _action
  let _smul : SMul ℤˣ (MvPolynomial (Fin n) k) := _action.toSMul
  exact ⟨signAction_faithful k n htwo hn, signAction_smulCommClass k n htwo,
    quadratic_isInvariant k n htwo⟩

/-- The polynomial ring has rank two over the quadratic invariant subalgebra. -/
theorem polynomial_finrank_quadratic (htwo : (2 : k) ≠ 0) (hn : 0 < n) :
    Module.finrank (quadraticSubalgebra k n) (MvPolynomial (Fin n) k) = 2 := by
  let _action : MulSemiringAction ℤˣ (MvPolynomial (Fin n) k) := signAction k n
  let _smul : SMul ℤˣ (MvPolynomial (Fin n) k) := _action.toSMul
  have hG : IsGaloisGroup ℤˣ (quadraticSubalgebra k n) (MvPolynomial (Fin n) k) :=
    quadratic_isGaloisGroup k n htwo hn
  rw [← IsGaloisGroup.card_eq_finrank' ℤˣ (quadraticSubalgebra k n)
    (MvPolynomial (Fin n) k), Nat.card_eq_fintype_card, Fintype.card_units_int]

/-- The actual fraction-field extension, induced from the original inclusion, has degree two. -/
theorem fractionRing_finrank_quadratic (htwo : (2 : k) ≠ 0) (hn : 0 < n) :
    let _fractionAlgebra : Algebra (FractionRing (quadraticSubalgebra k n))
        (FractionRing (MvPolynomial (Fin n) k)) :=
      (fractionRingInclusion (quadraticSubalgebra k n)
        (MvPolynomial (Fin n) k)).toAlgebra
    Module.finrank (FractionRing (quadraticSubalgebra k n))
      (FractionRing (MvPolynomial (Fin n) k)) = 2 := by
  intro _fractionAlgebra
  rw [fractionRingInclusion_finrank (quadraticSubalgebra k n) (MvPolynomial (Fin n) k)]
  exact polynomial_finrank_quadratic k n htwo hn

end SchemeTheory.SignPolynomial
