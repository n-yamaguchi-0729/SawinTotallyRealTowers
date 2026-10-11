/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Prime divisors of function fields

This file introduces the model-independent form of a prime divisor used in
Fried--Jarden, Chapter 6.  The underlying discrete `K`-valuation of `F` is
represented by a valuation subring of `F` which

* is a discrete valuation ring, and
* contains the image of the constant field `K`.

The discrete-valuation-ring condition forces the valuation subring to be
proper, so nontriviality is derived rather than stored as redundant data.
An FJ prime divisor additionally has residue field finite over `K`; this
condition is part of `FunctionFieldPrimeDivisor`, so its degree is a genuine
positive finite extension degree.

For a `K`-subalgebra `A` of `F`, being finite at the prime divisor means that
every element of `A` belongs to the valuation subring.  In that case the center
on `A` is the contraction of the valuation ring's maximal ideal.  This center
is prime; no maximality assertion is made without additional finiteness or
integrality hypotheses on the model.
-/

noncomputable section

namespace FieldArithmetic
namespace Chapter06

open IsLocalRing

universe u v w

variable (K : Type u) (F : Type v) [Field K] [Field F] [Algebra K F]

/--
A model-independent discrete `K`-valuation of `F`.

The valuation subring property says that its fraction field is the ambient
field `F`.  Discreteness is recorded by the DVR instance, while
`algebraMap_mem` says that the valuation is trivial on the constant field in
the valuation-ring sense.
-/
structure DiscreteKValuation where
  /-- The valuation subring of the ambient function field. -/
  valuationSubring : ValuationSubring F
  /-- The valuation subring is a discrete valuation ring. -/
  isDiscreteValuationRing :
    IsDiscreteValuationRing valuationSubring
  /-- Every constant lies in the valuation subring. -/
  algebraMap_mem : ∀ x : K, algebraMap K F x ∈ valuationSubring

namespace DiscreteKValuation

variable {K F}

instance (v : DiscreteKValuation K F) :
    IsDiscreteValuationRing v.valuationSubring :=
  v.isDiscreteValuationRing

/-- The constant-field embedding into the valuation ring. -/
def constantRingHom (v : DiscreteKValuation K F) :
    K →+* v.valuationSubring where
  toFun x := ⟨algebraMap K F x, v.algebraMap_mem x⟩
  map_zero' := Subtype.ext (map_zero (algebraMap K F))
  map_one' := Subtype.ext (map_one (algebraMap K F))
  map_add' x y := Subtype.ext (map_add (algebraMap K F) x y)
  map_mul' x y := Subtype.ext (map_mul (algebraMap K F) x y)

instance (v : DiscreteKValuation K F) :
    Algebra K v.valuationSubring :=
  v.constantRingHom.toAlgebra

@[simp]
theorem coe_algebraMap
    (v : DiscreteKValuation K F) (x : K) :
    ((algebraMap K v.valuationSubring x : v.valuationSubring) : F) =
      algebraMap K F x := by
  rfl

instance (v : DiscreteKValuation K F) :
    IsScalarTower K v.valuationSubring F :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/--
The valuation subring of a prime divisor is proper.  This follows from its DVR
structure and is therefore not an extra field of `FunctionFieldPrimeDivisor`.
-/
theorem valuationSubring_ne_top
    (v : DiscreteKValuation K F) :
    v.valuationSubring ≠ ⊤ := by
  intro h
  apply IsDiscreteValuationRing.not_isField v.valuationSubring
  rw [h]
  exact Field.toIsField _

/-- The residue field of a prime divisor. -/
abbrev ResidueField (v : DiscreteKValuation K F) :=
  IsLocalRing.ResidueField v.valuationSubring

/-- The constants embed into the residue field of a discrete `K`-valuation. -/
theorem residueField_algebraMap_injective
    (v : DiscreteKValuation K F) :
    Function.Injective (algebraMap K v.ResidueField) :=
  (algebraMap K v.ResidueField).injective

end DiscreteKValuation

/--
The residue-finiteness condition which distinguishes FJ prime divisors from
arbitrary discrete `K`-valuations.
-/
def HasFiniteResidueDegree (v : DiscreteKValuation K F) : Prop :=
  Module.Finite K v.ResidueField

/--
A prime divisor of `F / K` in the sense of Fried--Jarden: a nontrivial
discrete `K`-valuation whose residue field is finite over `K`.
-/
structure FunctionFieldPrimeDivisor extends DiscreteKValuation K F where
  /-- The residue field of the underlying discrete valuation is finite over K. -/
  residueFinite : HasFiniteResidueDegree K F toDiscreteKValuation

namespace FunctionFieldPrimeDivisor

variable {K F}

/-- The residue field of a prime divisor. -/
abbrev ResidueField (v : FunctionFieldPrimeDivisor K F) :=
  v.toDiscreteKValuation.ResidueField

/-- The residue field is finite-dimensional over the constant field. -/
instance (v : FunctionFieldPrimeDivisor K F) :
    FiniteDimensional K v.ResidueField :=
  v.residueFinite

/--
The degree of a prime divisor is the finite vector-space dimension of its
residue field over the constant field.
-/
def degree (v : FunctionFieldPrimeDivisor K F) : ℕ :=
  Module.finrank K v.ResidueField

/-- The residue degree of a prime divisor is positive. -/
theorem one_le_degree (v : FunctionFieldPrimeDivisor K F) :
    1 ≤ v.degree := by
  rw [degree, Nat.succ_le_iff]
  exact Module.finrank_pos

/-- The constants embed into the residue field of a prime divisor. -/
theorem residueField_algebraMap_injective
    (v : FunctionFieldPrimeDivisor K F) :
    Function.Injective (algebraMap K v.ResidueField) :=
  (algebraMap K v.ResidueField).injective

/-- The valuation subring of a prime divisor is proper. -/
theorem valuationSubring_ne_top
    (v : FunctionFieldPrimeDivisor K F) :
    v.valuationSubring ≠ ⊤ :=
  v.toDiscreteKValuation.valuationSubring_ne_top

/--
The prime divisor is finite along a model map `ι : A →ₐ[K] F` when the image
of every element of `A` belongs to its valuation ring.

No injectivity condition is needed: this formulation applies directly to
coordinate-ring maps into a function field.
-/
def FiniteAlong
    {A : Type w} [CommRing A] [Algebra K A]
    (v : FunctionFieldPrimeDivisor K F) (ι : A →ₐ[K] F) : Prop :=
  ∀ a : A, ι a ∈ v.valuationSubring

/-- A model map factored through the valuation ring at a finite prime divisor. -/
def finiteAlongRingHom
    {A : Type w} [CommRing A] [Algebra K A]
    (v : FunctionFieldPrimeDivisor K F) (ι : A →ₐ[K] F)
    (h : v.FiniteAlong ι) :
    A →+* v.valuationSubring where
  toFun a := ⟨ι a, h a⟩
  map_zero' := Subtype.ext (by simp)
  map_one' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)

/-- The finite-along factorization respects the `K`-algebra structures. -/
def finiteAlongAlgHom
    {A : Type w} [CommRing A] [Algebra K A]
    (v : FunctionFieldPrimeDivisor K F) (ι : A →ₐ[K] F)
    (h : v.FiniteAlong ι) :
    A →ₐ[K] v.valuationSubring :=
  { v.finiteAlongRingHom ι h with
    commutes' := fun x => Subtype.ext (by
      change ι (algebraMap K A x) = algebraMap K F x
      exact ι.commutes x) }

/--
The center along a model map is the contraction of the valuation ring's
maximal ideal.
-/
def centerAlong
    {A : Type w} [CommRing A] [Algebra K A]
    (v : FunctionFieldPrimeDivisor K F) (ι : A →ₐ[K] F)
    (h : v.FiniteAlong ι) : Ideal A :=
  (maximalIdeal v.valuationSubring).comap
    (v.finiteAlongRingHom ι h)

@[simp]
theorem mem_centerAlong_iff
    {A : Type w} [CommRing A] [Algebra K A]
    (v : FunctionFieldPrimeDivisor K F) (ι : A →ₐ[K] F)
    (h : v.FiniteAlong ι) (a : A) :
    a ∈ v.centerAlong ι h ↔
      v.finiteAlongRingHom ι h a ∈ maximalIdeal v.valuationSubring :=
  Iff.rfl

/-- Ambient-field characterization of membership in a center along a map. -/
theorem mem_centerAlong_iff_mem_nonunits
    {A : Type w} [CommRing A] [Algebra K A]
    (v : FunctionFieldPrimeDivisor K F) (ι : A →ₐ[K] F)
    (h : v.FiniteAlong ι) (a : A) :
    a ∈ v.centerAlong ι h ↔ ι a ∈ v.valuationSubring.nonunits := by
  change
    v.finiteAlongRingHom ι h a ∈ maximalIdeal v.valuationSubring ↔
      ι a ∈ v.valuationSubring.nonunits
  exact v.valuationSubring.coe_mem_nonunits_iff.symm

/-- A model element is in the center along `ι` exactly when its residue is zero. -/
theorem mem_centerAlong_iff_residue_eq_zero
    {A : Type w} [CommRing A] [Algebra K A]
    (v : FunctionFieldPrimeDivisor K F) (ι : A →ₐ[K] F)
    (h : v.FiniteAlong ι) (a : A) :
    a ∈ v.centerAlong ι h ↔
      residue v.valuationSubring (v.finiteAlongRingHom ι h a) = 0 := by
  rw [mem_centerAlong_iff, residue_eq_zero_iff]

/-- The center along any finite model map is a prime ideal. -/
theorem centerAlong_isPrime
    {A : Type w} [CommRing A] [Algebra K A]
    (v : FunctionFieldPrimeDivisor K F) (ι : A →ₐ[K] F)
    (h : v.FiniteAlong ι) :
    (v.centerAlong ι h).IsPrime := by
  let : (maximalIdeal v.valuationSubring).IsPrime :=
    (maximalIdeal.isMaximal v.valuationSubring).isPrime
  exact Ideal.IsPrime.comap _

/--
The prime divisor is finite on a `K`-model `A` when every function in `A` is
contained in its valuation ring.  This is `FiniteAlong` for the inclusion
`A.val : A →ₐ[K] F`.
-/
def FiniteOn
    (v : FunctionFieldPrimeDivisor K F) (A : Subalgebra K F) : Prop :=
  v.FiniteAlong A.val

@[simp]
theorem finiteOn_iff_finiteAlong_val
    (v : FunctionFieldPrimeDivisor K F) (A : Subalgebra K F) :
    v.FiniteOn A ↔ v.FiniteAlong A.val :=
  Iff.rfl

theorem finiteOn_iff_toSubring_le
    (v : FunctionFieldPrimeDivisor K F) (A : Subalgebra K F) :
    v.FiniteOn A ↔ A.toSubring ≤ v.valuationSubring.toSubring := by
  constructor
  · intro h x hx
    exact h ⟨x, hx⟩
  · intro h x
    exact h x.property

/-- Inclusion of a model into the valuation ring at a finite prime divisor. -/
def finiteOnRingHom
    (v : FunctionFieldPrimeDivisor K F) (A : Subalgebra K F)
    (h : v.FiniteOn A) :
    A →+* v.valuationSubring :=
  v.finiteAlongRingHom A.val h

/-- The finite-on inclusion respects the `K`-algebra structures. -/
def finiteOnAlgHom
    (v : FunctionFieldPrimeDivisor K F) (A : Subalgebra K F)
    (h : v.FiniteOn A) :
  A →ₐ[K] v.valuationSubring :=
  v.finiteAlongAlgHom A.val h

theorem finiteOnRingHom_injective
    (v : FunctionFieldPrimeDivisor K F) (A : Subalgebra K F)
    (h : v.FiniteOn A) :
    Function.Injective (v.finiteOnRingHom A h) := by
  intro x y hxy
  apply Subtype.ext
  exact congrArg (fun z : v.valuationSubring => (z : F)) hxy

/--
The center of a prime divisor on a model is the contraction of the maximal
ideal of its valuation ring.
-/
def center
    (v : FunctionFieldPrimeDivisor K F) (A : Subalgebra K F)
    (h : v.FiniteOn A) : Ideal A :=
  v.centerAlong A.val h

@[simp]
theorem mem_center_iff
    (v : FunctionFieldPrimeDivisor K F) (A : Subalgebra K F)
    (h : v.FiniteOn A) (x : A) :
    x ∈ v.center A h ↔
      v.finiteOnRingHom A h x ∈ maximalIdeal v.valuationSubring :=
  Iff.rfl

/--
Ambient-field characterization of the center: a model element is centered at
`v` exactly when it is a nonunit of the valuation ring.
-/
theorem mem_center_iff_mem_nonunits
    (v : FunctionFieldPrimeDivisor K F) (A : Subalgebra K F)
    (h : v.FiniteOn A) (x : A) :
    x ∈ v.center A h ↔ (x : F) ∈ v.valuationSubring.nonunits := by
  exact v.mem_centerAlong_iff_mem_nonunits A.val h x

/-- A model element is in the center exactly when its residue is zero. -/
theorem mem_center_iff_residue_eq_zero
    (v : FunctionFieldPrimeDivisor K F) (A : Subalgebra K F)
    (h : v.FiniteOn A) (x : A) :
    x ∈ v.center A h ↔
      residue v.valuationSubring (v.finiteOnRingHom A h x) = 0 := by
  exact v.mem_centerAlong_iff_residue_eq_zero A.val h x

/-- The center of a finite prime divisor on a model is a prime ideal. -/
theorem center_isPrime
    (v : FunctionFieldPrimeDivisor K F) (A : Subalgebra K F)
    (h : v.FiniteOn A) :
    (v.center A h).IsPrime := by
  exact v.centerAlong_isPrime A.val h

end FunctionFieldPrimeDivisor
end Chapter06
end FieldArithmetic
