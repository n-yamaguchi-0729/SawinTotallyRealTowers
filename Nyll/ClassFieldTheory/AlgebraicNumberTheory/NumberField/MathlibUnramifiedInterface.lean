/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.NumberField.FiniteUnramifiedTower
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.NumberField.EverywhereUnramifiedTower
public import Nyll.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsEverywhereUnramified
public import Nyll.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsUnramifiedAtFinitePlaces

/-!
# Finite-place unramifiedness comparison

Finite unramifiedness uses the same integer-ring predicate in internal and public
class-field statements. The comparison here is invariance under actual field
equivalences, including the independent condition at infinite places.
-/



@[expose] public section

universe u v w

open scoped NumberField
open NumberField IsDedekindDomain

namespace ClassFieldTheory

/-- A number-field equivalence over `K` restricts to an equivalence of
integer rings over the integer ring of `K`. -/
noncomputable def ringOfIntegersEquivOfAlgEquiv
    (K : Type u) (L : Type v) (E : Type w)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [Field E] [NumberField E] [Algebra K E]
    (e : L ≃ₐ[K] E) : 𝓞 L ≃ₐ[𝓞 K] 𝓞 E := by
  let eℤ : L ≃ₐ[ℤ] E := e.restrictScalars ℤ
  let e𝓞 : 𝓞 L ≃ₐ[ℤ] 𝓞 E := eℤ.mapIntegralClosure
  exact AlgEquiv.ofRingEquiv (f := e𝓞.toRingEquiv) (fun x => by
    apply Subtype.ext
    change e (algebraMap (𝓞 K) L x) = algebraMap (𝓞 K) E x
    rw [IsScalarTower.algebraMap_apply (𝓞 K) K L x,
      IsScalarTower.algebraMap_apply (𝓞 K) K E x]
    exact e.commutes (algebraMap (𝓞 K) K x))

/-- Finite-place unramifiedness is invariant under a number-field
equivalence over the base. -/
theorem isUnramifiedAtFinitePlaces_iff_of_algEquiv
    (K : Type u) (L : Type v) (E : Type w)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [Field E] [NumberField E] [Algebra K E]
    (e : L ≃ₐ[K] E) :
    ClassFieldTheory.IsUnramifiedAtFinitePlaces K L ↔
      ClassFieldTheory.IsUnramifiedAtFinitePlaces K E := by
  exact Algebra.FormallyUnramified.iff_of_equiv
    (ringOfIntegersEquivOfAlgEquiv K L E e)

/-- Unramifiedness at infinite places is also invariant under a
number-field equivalence over the base. -/
theorem isUnramifiedAtInfinitePlaces_iff_of_algEquiv
    (K : Type u) (L : Type v) (E : Type w)
    [Field K]
    [Field L] [Algebra K L]
    [Field E] [Algebra K E]
    (e : L ≃ₐ[K] E) :
    IsUnramifiedAtInfinitePlaces K L ↔
      IsUnramifiedAtInfinitePlaces K E := by
  constructor
  · intro h
    refine ⟨fun w => ?_⟩
    have hw := (h.isUnramified (w.comap (e : L →+* E))).comap_algHom
      e.symm.toAlgHom
    have hcomp :
        (e : L →+* E).comp (e.symm.toAlgHom : E →+* L) = RingHom.id E := by
      ext x
      exact e.apply_symm_apply x
    simpa only [← InfinitePlace.comap_comp, hcomp,
      InfinitePlace.comap_id] using hw
  · intro h
    refine ⟨fun w => ?_⟩
    have hw := (h.isUnramified (w.comap (e.symm : E →+* L))).comap_algHom
      e.toAlgHom
    have hcomp :
        (e.symm : E →+* L).comp (e.toAlgHom : L →+* E) = RingHom.id L := by
      ext x
      exact e.symm_apply_apply x
    simpa only [← InfinitePlace.comap_comp, hcomp,
      InfinitePlace.comap_id] using hw

/-- Everywhere-unramifiedness is invariant under a number-field
equivalence over the base. -/
theorem isEverywhereUnramified_iff_of_algEquiv
    (K : Type u) (L : Type v) (E : Type w)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [Field E] [NumberField E] [Algebra K E]
    (e : L ≃ₐ[K] E) :
    ClassFieldTheory.IsEverywhereUnramified K L ↔
      ClassFieldTheory.IsEverywhereUnramified K E := by
  exact and_congr
    (isUnramifiedAtFinitePlaces_iff_of_algEquiv K L E e)
    (isUnramifiedAtInfinitePlaces_iff_of_algEquiv K L E e)

end ClassFieldTheory
