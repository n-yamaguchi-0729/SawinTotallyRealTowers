/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Components
public import Nyll.ClassFieldTheory.Algebra.RestrictedProduct.Valuation
public import Nyll.ClassFieldTheory.Algebra.FractionalIdealFactorization
public import Mathlib.RingTheory.ClassGroup.Basic

/-!
# Ideal maps on the standard adele-unit carriers

Local orders and fractional-ideal factorization supply the maps directly on
finite adele units and standard ideles. The generic Dedekind-domain parameters
are retained throughout.
-/

@[expose] public section

open NumberField IsDedekindDomain
open scoped RestrictedProduct

noncomputable section

universe u v

variable {R : Type u} {K : Type v} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

namespace IsDedekindDomain.FiniteAdeleRing

/-- The normalized finite valuation vector of a finite adele unit. -/
def valuationVector : (FiniteAdeleRing R K)ˣ →*
    Multiplicative (HeightOneSpectrum R →₀ ℤ) :=
  (RestrictedProduct.DiscreteValuation.valuationVector
    (fun v : HeightOneSpectrum R => v.adicCompletion K)).comp
    (unitComponentsEquiv (R := R) (K := K)).toMonoidHom

/-- The vector is evaluated by the normalized local order. -/
theorem valuationVector_apply (a : (FiniteAdeleRing R K)ˣ) (v : HeightOneSpectrum R) :
    (valuationVector a).toAdd v =
      (RestrictedProduct.DiscreteValuation.localOrder (v.adicCompletion K)
        (unitComponent v a)).toAdd :=
  RestrictedProduct.DiscreteValuation.valuationVector_apply
    (fun w : HeightOneSpectrum R => w.adicCompletion K) (unitComponentsEquiv a) v

/-- Every finitely supported valuation vector occurs on the standard carrier. -/
theorem valuationVector_surjective :
    Function.Surjective (valuationVector (R := R) (K := K)) :=
  (RestrictedProduct.DiscreteValuation.valuationVector_surjective
    (fun v : HeightOneSpectrum R => v.adicCompletion K)
    (fun v => HeightOneSpectrum.valuedAdicCompletion_surjective K v)).comp
    unitComponentsEquiv.surjective

/-- The nonzero fractional ideal attached to a finite adele unit. -/
def fractionalIdeal : (FiniteAdeleRing R K)ˣ →*
    (FractionalIdeal (nonZeroDivisors R) K)ˣ :=
  let e := ClassFieldTheory.FractionalIdealFactorization.factorizationEquiv (R := R) (F := K)
  e.toMonoidHom.comp (valuationVector (R := R) (K := K))

/-- Every nonzero fractional ideal is represented by a finite adele unit. -/
theorem fractionalIdeal_surjective :
    Function.Surjective (fractionalIdeal (R := R) (K := K)) :=
  let e := ClassFieldTheory.FractionalIdealFactorization.factorizationEquiv (R := R) (F := K)
  e.surjective.comp valuationVector_surjective

/-- Finite adele units integral and invertible at every finite place. -/
def integralUnitSubgroup : Subgroup (FiniteAdeleRing R K)ˣ :=
  (RestrictedProduct.DiscreteValuation.integralSubgroup
    (fun v : HeightOneSpectrum R => v.adicCompletion K)).comap unitComponentsEquiv.toMonoidHom

/-- Membership is the componentwise local-unit condition. -/
theorem mem_integralUnitSubgroup_iff (a : (FiniteAdeleRing R K)ˣ) :
    a ∈ integralUnitSubgroup ↔
      ∀ v : HeightOneSpectrum R, unitComponent v a ∈ (v.adicCompletionIntegers K).units :=
  Iff.rfl

/-- The valuation vector vanishes precisely on the everywhere integral units. -/
theorem valuationVector_eq_one_iff (a : (FiniteAdeleRing R K)ˣ) :
    valuationVector a = 1 ↔ a ∈ integralUnitSubgroup := by
  rw [mem_integralUnitSubgroup_iff]
  exact RestrictedProduct.DiscreteValuation.valuationVector_eq_one_iff
    (fun v : HeightOneSpectrum R => v.adicCompletion K) (unitComponentsEquiv a)

/-- The kernel of the fractional-ideal map is the intrinsic integral subgroup. -/
theorem fractionalIdeal_ker :
    (fractionalIdeal (R := R) (K := K)).ker = integralUnitSubgroup := by
  ext a
  change ClassFieldTheory.FractionalIdealFactorization.factorizationEquiv
      (valuationVector a) = 1 ↔ a ∈ integralUnitSubgroup
  constructor
  · intro h
    apply (valuationVector_eq_one_iff a).mp
    apply (ClassFieldTheory.FractionalIdealFactorization.factorizationEquiv
      (R := R) (F := K)).injective
    simpa only [map_one] using h
  · intro h
    rw [(valuationVector_eq_one_iff a).mpr h, map_one]

end IsDedekindDomain.FiniteAdeleRing

namespace NumberField.IdeleGroup

/-- The fractional ideal of a standard idele depends only on its finite part. -/
def fractionalIdeal : IdeleGroup R K →* (FractionalIdeal (nonZeroDivisors R) K)ˣ :=
  (FiniteAdeleRing.fractionalIdeal (R := R) (K := K)).comp finitePart

/-- Every fractional ideal is represented by a standard idele. -/
theorem fractionalIdeal_surjective :
    Function.Surjective (fractionalIdeal (R := R) (K := K)) := by
  intro I
  obtain ⟨a, rfl⟩ := FiniteAdeleRing.fractionalIdeal_surjective (K := K) I
  exact ⟨MulEquiv.prodUnits.symm (1, a), rfl⟩

/-- Standard ideles integral at every finite place. -/
def integralAtFinitePlaces : Subgroup (IdeleGroup R K) :=
  FiniteAdeleRing.integralUnitSubgroup.comap finitePart

/-- Integral ideles are precisely the kernel of the standard fractional-ideal map. -/
theorem fractionalIdeal_ker :
    (fractionalIdeal (R := R) (K := K)).ker = integralAtFinitePlaces := by
  ext a
  change FiniteAdeleRing.fractionalIdeal (finitePart a) = 1 ↔
    finitePart a ∈ FiniteAdeleRing.integralUnitSubgroup
  rw [← MonoidHom.mem_ker, FiniteAdeleRing.fractionalIdeal_ker]

/-- The ordinary ideal class of a standard idele. -/
def idealClass : IdeleGroup R K →* ClassGroup R :=
  (ClassGroup.mk K).comp (fractionalIdeal (R := R) (K := K))

/-- Every ideal class is represented by a standard idele. -/
theorem idealClass_surjective : Function.Surjective (idealClass (R := R) (K := K)) := by
  intro c
  induction c using ClassGroup.induction (R := R) K with
  | h I =>
      obtain ⟨a, ha⟩ := fractionalIdeal_surjective (K := K) I
      exact ⟨a, by simp only [idealClass, MonoidHom.comp_apply, ha]⟩

end NumberField.IdeleGroup
