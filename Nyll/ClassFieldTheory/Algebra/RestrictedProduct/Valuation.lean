/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Group.Submonoid.Units
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Data.Finsupp.Basic
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Mathlib.Topology.Algebra.Valued.ValuedField

/-!
# Valuation vectors of restricted products

Normalized discrete orders send the restricted product of multiplicative valued
fields to the free abelian group on the index set. The kernel consists of the
families integral and invertible at every index. When the valuations are
surjective, choosing an element of each prescribed order constructs a preimage
of every finitely supported vector.

This is the common valuation-vector construction for finite number-field ideles
and all-place function-field ideles.
-/

open scoped RestrictedProduct WithZero

noncomputable section

namespace RestrictedProduct.DiscreteValuation

section Local

variable (F : Type*) [Field F] [Valued F ℤᵐ⁰]

/-- Normalized additive order, expressed as a homomorphism to multiplicative integers. -/
def localOrder : Fˣ →* Multiplicative ℤ :=
  MonoidHom.mk'
    (fun x => Multiplicative.ofAdd (-WithZero.log (Valued.v (x : F))))
    (fun x y => by
      apply Multiplicative.ext
      change -WithZero.log (Valued.v ((x * y : Fˣ) : F)) =
        -WithZero.log (Valued.v (x : F)) + -WithZero.log (Valued.v (y : F))
      rw [Units.val_mul, map_mul,
        WithZero.log_mul
          ((Valuation.ne_zero_iff (Valued.v : Valuation F ℤᵐ⁰)).mpr (Units.ne_zero x))
          ((Valuation.ne_zero_iff (Valued.v : Valuation F ℤᵐ⁰)).mpr (Units.ne_zero y)), neg_add])

@[simp]
theorem localOrder_apply (x : Fˣ) :
    (localOrder F x).toAdd = -WithZero.log (Valued.v (x : F)) :=
  rfl

/-- A field unit is an integral unit precisely when its valuation is one. -/
theorem mem_localUnits_iff (x : Fˣ) :
    x ∈ (Valued.v : Valuation F ℤᵐ⁰).valuationSubring.units ↔
      Valued.v (x : F) = 1 := by
  change (Valued.v (x : F) ≤ 1 ∧ Valued.v ((x⁻¹ : Fˣ) : F) ≤ 1) ↔
    Valued.v (x : F) = 1
  rw [Units.val_inv_eq_inv_val, map_inv₀,
    inv_le_one₀ (zero_lt_iff.mpr
      ((Valuation.ne_zero_iff (Valued.v : Valuation F ℤᵐ⁰)).mpr (Units.ne_zero x)))]
  exact le_antisymm_iff.symm

@[simp]
theorem localOrder_eq_zero_iff (x : Fˣ) :
    (localOrder F x).toAdd = 0 ↔
      x ∈ (Valued.v : Valuation F ℤᵐ⁰).valuationSubring.units := by
  rw [localOrder_apply, neg_eq_zero, mem_localUnits_iff]
  constructor
  · intro h
    calc
      Valued.v (x : F) = WithZero.exp (WithZero.log (Valued.v (x : F))) :=
        (WithZero.exp_log
          ((Valuation.ne_zero_iff (Valued.v : Valuation F ℤᵐ⁰)).mpr (Units.ne_zero x))).symm
      _ = 1 := by rw [h, WithZero.exp_zero]
  · intro h
    rw [h, WithZero.log_one]

/-- An actual field unit with a prescribed normalized order. -/
def chosenLocalOrderSection
    (hval : Function.Surjective (Valued.v : Valuation F ℤᵐ⁰)) (n : ℤ) : Fˣ :=
  let x := Classical.choose (hval (WithZero.exp (-n)))
  Units.mk0 x (by
    intro hx
    have h := Classical.choose_spec (hval (WithZero.exp (-n)))
    change Valued.v x = WithZero.exp (-n) at h
    rw [hx, map_zero] at h
    exact WithZero.exp_ne_zero h.symm)

@[simp]
theorem localOrder_chosenLocalOrderSection
    (hval : Function.Surjective (Valued.v : Valuation F ℤᵐ⁰)) (n : ℤ) :
    (localOrder F (chosenLocalOrderSection F hval n)).toAdd = n := by
  rw [localOrder_apply]
  change -WithZero.log (Valued.v (Classical.choose (hval (WithZero.exp (-n))))) = n
  rw [Classical.choose_spec (hval (WithZero.exp (-n))), WithZero.log_exp, neg_neg]

end Local

section Family

variable {ι : Type*} (F : ι → Type*) [∀ i, Field (F i)] [∀ i, Valued (F i) ℤᵐ⁰]

/-- The restricted product relative to the integral-unit subgroups. -/
abbrev UnitProduct :=
  Πʳ i, [(F i)ˣ, (Valued.v : Valuation (F i) ℤᵐ⁰).valuationSubring.units]

/-- There are only finitely many nonintegral-unit components. -/
theorem finite_nonLocalUnits (a : UnitProduct F) :
    {i | a i ∉ (Valued.v : Valuation (F i) ℤᵐ⁰).valuationSubring.units}.Finite :=
  Filter.eventually_cofinite.mp a.2

/-- The finitely supported family of the local normalized orders. -/
def valuationVectorAdd (a : UnitProduct F) : ι →₀ ℤ :=
  Finsupp.onFinset (finite_nonLocalUnits F a).toFinset
    (fun i => (localOrder (F i) (a i)).toAdd) (fun i hi => by
      rw [Set.Finite.mem_toFinset]
      intro hmem
      exact hi ((localOrder_eq_zero_iff (F i) (a i)).2 hmem))

@[simp]
theorem valuationVectorAdd_apply (a : UnitProduct F) (i : ι) :
    valuationVectorAdd F a i = (localOrder (F i) (a i)).toAdd :=
  rfl

/-- The normalized valuation-vector homomorphism. -/
def valuationVector : UnitProduct F →* Multiplicative (ι →₀ ℤ) :=
  MonoidHom.mk' (fun a => Multiplicative.ofAdd (valuationVectorAdd F a))
    (fun a b => by
      apply Multiplicative.ext
      apply Finsupp.ext
      intro i
      exact congrArg Multiplicative.toAdd (map_mul (localOrder (F i)) (a i) (b i)))

@[simp]
theorem valuationVector_apply (a : UnitProduct F) (i : ι) :
    (valuationVector F a).toAdd i = (localOrder (F i) (a i)).toAdd :=
  rfl

/-- A valuation vector is zero exactly when all components are integral units. -/
theorem valuationVector_eq_one_iff (a : UnitProduct F) :
    valuationVector F a = 1 ↔
      ∀ i, a i ∈ (Valued.v : Valuation (F i) ℤᵐ⁰).valuationSubring.units := by
  constructor
  · intro h i
    apply (localOrder_eq_zero_iff (F i) (a i)).1
    rw [← valuationVector_apply F a i, h]
    rfl
  · intro h
    apply Multiplicative.ext
    apply Finsupp.ext
    intro i
    exact (localOrder_eq_zero_iff (F i) (a i)).2 (h i)

/-- Families that are integral units at every index. -/
def integralSubgroup : Subgroup (UnitProduct F) where
  carrier := {a | ∀ i, a i ∈ (Valued.v : Valuation (F i) ℤᵐ⁰).valuationSubring.units}
  one_mem' i := (Valued.v : Valuation (F i) ℤᵐ⁰).valuationSubring.units.one_mem
  mul_mem' ha hb i := Subgroup.mul_mem _ (ha i) (hb i)
  inv_mem' ha i := Subgroup.inv_mem _ (ha i)

theorem valuationVector_ker : (valuationVector F).ker = integralSubgroup F := by
  apply Subgroup.ext
  intro a
  exact valuationVector_eq_one_iff F a

/-- Construct a restricted family with a prescribed valuation vector. -/
def valuationVectorSection
    (hval : ∀ i, Function.Surjective (Valued.v : Valuation (F i) ℤᵐ⁰))
    (e : ι →₀ ℤ) : UnitProduct F :=
  ⟨fun i => chosenLocalOrderSection (F i) (hval i) (e i), by
    filter_upwards [e.support.eventually_cofinite_notMem] with i hi
    apply (localOrder_eq_zero_iff (F i) _).1
    rw [localOrder_chosenLocalOrderSection, Finsupp.notMem_support_iff.mp hi]⟩

@[simp]
theorem valuationVector_valuationVectorSection
    (hval : ∀ i, Function.Surjective (Valued.v : Valuation (F i) ℤᵐ⁰))
    (e : ι →₀ ℤ) :
    valuationVector F (valuationVectorSection F hval e) = Multiplicative.ofAdd e := by
  apply Multiplicative.ext
  apply Finsupp.ext
  intro i
  exact localOrder_chosenLocalOrderSection (F i) (hval i) (e i)

/-- Surjective local valuations give a surjective valuation-vector map. -/
theorem valuationVector_surjective
    (hval : ∀ i, Function.Surjective (Valued.v : Valuation (F i) ℤᵐ⁰)) :
    Function.Surjective (valuationVector F) := by
  intro e
  exact ⟨valuationVectorSection F hval e.toAdd,
    valuationVector_valuationVectorSection F hval e.toAdd⟩

end Family

end RestrictedProduct.DiscreteValuation
