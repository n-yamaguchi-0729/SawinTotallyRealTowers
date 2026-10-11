/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.FunctionFields.PrimeDivisors.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Extending finiteness to an integral-closure model

A valuation ring is integrally closed in its fraction field.  Consequently,
if a prime divisor is finite on a model `A`, it is finite on the integral
closure of `A` in the ambient field.  This is the bridge from an affine
coordinate model to the Dedekind normalization used in the prime counts of
Fried--Jarden, Lemma 6.2.2.
-/

noncomputable section

namespace FieldArithmetic
namespace Chapter06
namespace FunctionFieldPrimeDivisor

universe u v

variable {K : Type u} {F : Type v}
  [Field K] [Field F] [Algebra K F]

/--
The integral closure in `F` of a `K`-subalgebra `A`, regarded again as a
`K`-subalgebra of `F`.
-/
def integralClosureModel (A : Subalgebra K F) : Subalgebra K F :=
  (integralClosure A F).restrictScalars K

@[simp]
theorem integralClosureModel_coe
    (A : Subalgebra K F) (x : integralClosureModel A) :
    ((x : integralClosureModel A) : F) = x :=
  rfl

/--
Finiteness on a model extends to its integral closure in the ambient field.

No finiteness assumption on the normalization is needed: every element is
integral over `A`, and the valuation ring is integrally closed.
-/
theorem finiteOn_integralClosureModel
    (v : FunctionFieldPrimeDivisor K F) (A : Subalgebra K F)
    (hfinite : v.FiniteOn A) :
    v.FiniteOn (integralClosureModel A) := by
  intro x
  let : Algebra A v.valuationSubring :=
    (v.finiteOnAlgHom A hfinite).toRingHom.toAlgebra
  let : IsScalarTower A v.valuationSubring F :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hxIntegral :
      IsIntegral v.valuationSubring (x : F) :=
    x.property.tower_top
  obtain ⟨y, hy⟩ :=
    IsIntegrallyClosed.isIntegral_iff.mp hxIntegral
  have hy' : ((y : v.valuationSubring) : F) = x := hy
  change (x : F) ∈ v.valuationSubring
  rw [← hy']
  exact y.property

/--
Finiteness along an algebra model extends to any realization of its integral
closure in the ambient field.

The algebra structures on the source and the integral-closure model are
explicit inputs.  Only the valuation-subring algebra needed by the
integrality argument is installed locally, so downstream proofs do not have
to reconstruct that instance tower.
-/
theorem finiteAlong_integralClosure
    {A B : Type*} [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] [Algebra A B]
    [Algebra A F] [Algebra B F]
    [IsScalarTower K A F] [IsScalarTower K B F]
    [IsScalarTower A B F] [IsIntegralClosure B A F]
    (v : FunctionFieldPrimeDivisor K F)
    (hfinite : v.FiniteAlong (IsScalarTower.toAlgHom K A F)) :
    v.FiniteAlong (IsScalarTower.toAlgHom K B F) := by
  intro x
  let gA : A →+* v.valuationSubring :=
    v.finiteAlongRingHom (IsScalarTower.toAlgHom K A F) hfinite
  let : Algebra A v.valuationSubring := gA.toAlgebra
  let : IsScalarTower A v.valuationSubring F :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hxIntegral :
      IsIntegral v.valuationSubring (algebraMap B F x) :=
    ((IsIntegralClosure.isIntegral_iff (R := A) (A := B)).mpr
      ⟨x, rfl⟩).tower_top
  obtain ⟨y, hy⟩ :=
    IsIntegrallyClosed.isIntegral_iff.mp hxIntegral
  change algebraMap B F x ∈ v.valuationSubring
  rw [← hy]
  exact y.property

/--
An integral-closure model is torsion-free over the base as soon as the base
embeds in the ambient field.  Supplying the injectivity proof explicitly
avoids asking typeclass synthesis to rediscover a `FaithfulSMul` path through
the surrounding algebra tower.
-/
theorem integralClosure_isTorsionFree_of_algebraMap_injective
    {A B : Type*} [CommRing A] [IsDomain A] [CommRing B]
    [Algebra A B] [Algebra A F] [Algebra B F]
    [IsScalarTower A B F] [IsIntegralClosure B A F]
    (hF : Function.Injective (algebraMap A F)) :
    Module.IsTorsionFree A B := by
  let : Module.IsTorsionFree A F :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hF
  exact IsIntegralClosure.isTorsionFree A F

/-- Finiteness descends along an inclusion of models. -/
theorem finiteOn_of_le
    (v : FunctionFieldPrimeDivisor K F)
    {A B : Subalgebra K F} (hAB : A ≤ B)
    (hfinite : v.FiniteOn B) :
    v.FiniteOn A :=
  fun x => hfinite ⟨x, hAB x.property⟩

/--
Centers are compatible with contraction along an inclusion of models.
-/
theorem center_comap_of_le
    (v : FunctionFieldPrimeDivisor K F)
    {A B : Subalgebra K F} (hAB : A ≤ B)
    (hfinite : v.FiniteOn B) :
    (v.center B hfinite).comap
        (Subalgebra.inclusion hAB).toRingHom =
      v.center A (v.finiteOn_of_le hAB hfinite) := by
  ext x
  rw [Ideal.mem_comap, v.mem_center_iff_mem_nonunits,
    v.mem_center_iff_mem_nonunits]
  rfl

/-- The original model is contained in its integral closure model. -/
theorem le_integralClosureModel (A : Subalgebra K F) :
    A ≤ integralClosureModel A := by
  intro x hx
  change IsIntegral A x
  have h :
      IsIntegral A (algebraMap A F ⟨x, hx⟩) :=
    isIntegral_algebraMap
  simpa using h

/--
The center on the integral closure contracts to the original center.
-/
theorem center_integralClosureModel_comap
    (v : FunctionFieldPrimeDivisor K F) (A : Subalgebra K F)
    (hfinite : v.FiniteOn A) :
    (v.center (integralClosureModel A)
        (v.finiteOn_integralClosureModel A hfinite)).comap
        (Subalgebra.inclusion (le_integralClosureModel A)).toRingHom =
      v.center A hfinite := by
  exact v.center_comap_of_le
    (le_integralClosureModel A)
    (v.finiteOn_integralClosureModel A hfinite)

end FunctionFieldPrimeDivisor
end Chapter06
end FieldArithmetic
