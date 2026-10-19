/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Order.Filter.Cofinite
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Adele.RestrictedProduct
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Topology
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Approximation

/-!
# Ideles supported at one place

Local-to-global diagrams use the canonical embedding of a local multiplicative
group into the idele group. This file constructs
that embedding at finite places and the corresponding one-component
relative idele.
-/



open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section

namespace IdeleGroup

variable {K : Type*} [Field K] [NumberField K]

open scoped Classical in
/-- The dependent archimedean value which is `x` at `v` and `1`
elsewhere. -/
private def infinitePlaceValue
    (v : InfinitePlace K)
    (x : v.Completionˣ) :
    (w : InfinitePlace K) → w.Completionˣ :=
  Pi.mulSingle
    (M := fun u : InfinitePlace K ↦ u.Completionˣ)
    v x

omit [NumberField K] in
@[simp]
private theorem infinitePlaceValue_same
    (v : InfinitePlace K)
    (x : v.Completionˣ) :
    infinitePlaceValue v x v = x := by
  classical
  exact Pi.mulSingle_eq_same
    (M := fun u : InfinitePlace K ↦ u.Completionˣ) v x

omit [NumberField K] in
@[simp]
private theorem infinitePlaceValue_of_ne
    (v w : InfinitePlace K)
    (x : v.Completionˣ)
    (h : w ≠ v) :
    infinitePlaceValue v x w = 1 := by
  classical
  exact Pi.mulSingle_eq_of_ne
    (M := fun u : InfinitePlace K ↦ u.Completionˣ) h x

/-- The idele whose `v`-component is prescribed and whose other
components are `1`, for an archimedean place `v`. -/
def infinitePlaceIdele
    (v : InfinitePlace K) :
    v.Completionˣ →* IdeleGroup K where
  toFun x :=
    (ContinuousMulEquiv.piUnits.symm
      (infinitePlaceValue v x), 1)
  map_one' := by
    classical
    have hvalue : infinitePlaceValue v 1 = 1 :=
      Pi.mulSingle_one (M := fun w : InfinitePlace K => w.Completionˣ) v
    apply Prod.ext
    · change
        ContinuousMulEquiv.piUnits.symm
            (infinitePlaceValue v 1) = 1
      rw [hvalue, map_one]
    · rfl
  map_mul' x y := by
    classical
    have hvalue :
        infinitePlaceValue v (x * y) =
          infinitePlaceValue v x * infinitePlaceValue v y :=
      Pi.mulSingle_mul (f := fun w : InfinitePlace K => w.Completionˣ) v x y
    apply Prod.ext
    · change
        ContinuousMulEquiv.piUnits.symm
            (infinitePlaceValue v (x * y)) =
          ContinuousMulEquiv.piUnits.symm
              (infinitePlaceValue v x) *
            ContinuousMulEquiv.piUnits.symm
              (infinitePlaceValue v y)
      rw [hvalue, map_mul]
    · exact (one_mul 1).symm

/-- Inserting a unit at one archimedean place is continuous. -/
theorem continuous_infinitePlaceIdele
    (v : InfinitePlace K) :
    Continuous (infinitePlaceIdele v) := by
  classical
  change Continuous
    (fun x : v.Completionˣ ↦
      (ContinuousMulEquiv.piUnits.symm
        (infinitePlaceValue v x), 1))
  have hvalue :
      Continuous
        (fun x : v.Completionˣ ↦
          infinitePlaceValue v x) := by
    simpa only [infinitePlaceValue] using
      (continuous_mulSingle
        (A := fun u : InfinitePlace K ↦ u.Completionˣ) v)
  exact
    (ContinuousMulEquiv.piUnits.symm.continuous.comp
      hvalue).prodMk continuous_const

/-- The continuous homomorphism inserting a unit at one archimedean place. -/
def infinitePlaceIdeleContinuous
    (v : InfinitePlace K) :
    v.Completionˣ →ₜ* IdeleGroup K where
  __ := infinitePlaceIdele v
  continuous_toFun := continuous_infinitePlaceIdele v

@[simp]
theorem infinitePlaceIdeleContinuous_apply
    (v : InfinitePlace K) (x : v.Completionˣ) :
    infinitePlaceIdeleContinuous v x =
      infinitePlaceIdele v x :=
  rfl

/-- An archimedean one-place idele recovers its prescribed component
at the supporting place. -/
@[simp]
theorem infinitePlaceIdele_infiniteComponent_same
    (v : InfinitePlace K)
    (x : v.Completionˣ) :
    IdeleGroup.infiniteComponent v
        (infinitePlaceIdele v x) = x := by
  change
    ContinuousMulEquiv.piUnits
        (ContinuousMulEquiv.piUnits.symm
          (infinitePlaceValue v x)) v = x
  rw [ContinuousMulEquiv.piUnits.apply_symm_apply]
  exact infinitePlaceValue_same v x

/-- An archimedean one-place idele has component one at every other
archimedean place. -/
@[simp]
theorem infinitePlaceIdele_infiniteComponent_of_ne
    (v w : InfinitePlace K)
    (x : v.Completionˣ)
    (h : w ≠ v) :
    IdeleGroup.infiniteComponent w
        (infinitePlaceIdele v x) = 1 := by
  change
    ContinuousMulEquiv.piUnits
        (ContinuousMulEquiv.piUnits.symm
          (infinitePlaceValue v x)) w = 1
  rw [ContinuousMulEquiv.piUnits.apply_symm_apply]
  exact infinitePlaceValue_of_ne v w x h

/-- An archimedean one-place idele has component one at every finite
place. -/
@[simp]
theorem infinitePlaceIdele_finiteComponent
    (v : InfinitePlace K)
    (w : HeightOneSpectrum (𝓞 K))
    (x : v.Completionˣ) :
    IdeleGroup.finiteComponent w
        (infinitePlaceIdele v x) = 1 := by
  rfl

/-- Insert one archimedean-place element and then pass to the idele
class group. -/
def infinitePlaceIdeleClass
    (v : InfinitePlace K) :
    v.Completionˣ →* IdeleClassGroup K :=
  (QuotientGroup.mk'
    (IdeleGroup.principalSubgroup K)).comp
      (infinitePlaceIdele v)

open scoped Classical in
/-- The dependent local value which is `x` at `v` and `1` elsewhere. -/
private def finitePlaceValue
    (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ)
    (w : HeightOneSpectrum (𝓞 K)) :
    (w.adicCompletion K)ˣ :=
  Pi.mulSingle (M := fun u : HeightOneSpectrum (𝓞 K) => (u.adicCompletion K)ˣ) v x w

@[simp]
private theorem finitePlaceValue_same
    (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) :
    finitePlaceValue v x v = x := by
  classical
  exact Pi.mulSingle_eq_same
    (M := fun u : HeightOneSpectrum (𝓞 K) => (u.adicCompletion K)ˣ) v x

@[simp]
private theorem finitePlaceValue_of_ne
    (v w : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ)
    (h : w ≠ v) :
    finitePlaceValue v x w = 1 := by
  classical
  exact Pi.mulSingle_eq_of_ne
    (M := fun u : HeightOneSpectrum (𝓞 K) => (u.adicCompletion K)ˣ) h x

/-- The idele whose `v`-component is prescribed and whose other
components are `1`. -/
def finitePlaceIdele
    (v : HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletion K)ˣ →* IdeleGroup K where
  toFun x :=
    (1,
      ⟨finitePlaceValue v x, by
        have hAway :
            ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
              w ≠ v := Filter.eventually_cofinite_ne v
        filter_upwards [hAway] with w hw
        rw [finitePlaceValue_of_ne v w x hw]
        exact Subgroup.one_mem _⟩)
  map_one' := by
    classical
    apply Prod.ext
    · rfl
    · apply RestrictedProduct.ext
      intro w
      exact congrFun
        (Pi.mulSingle_one (M := fun u : HeightOneSpectrum (𝓞 K) => (u.adicCompletion K)ˣ) v) w
  map_mul' x y := by
    classical
    apply Prod.ext
    · exact (one_mul 1).symm
    · apply RestrictedProduct.ext
      intro w
      exact congrFun
        (Pi.mulSingle_mul (f := fun u : HeightOneSpectrum (𝓞 K) => (u.adicCompletion K)ˣ)
          v x y) w

/-- A finite-place idele recovers its prescribed component at the
supporting place. -/
@[simp]
theorem finitePlaceIdele_finiteComponent_same
    (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) :
    IdeleGroup.finiteComponent v
        (finitePlaceIdele v x) = x :=
  finitePlaceValue_same v x

/-- A finite-place idele has component one at every other finite place. -/
@[simp]
theorem finitePlaceIdele_finiteComponent_of_ne
    (v w : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ)
    (h : w ≠ v) :
    IdeleGroup.finiteComponent w
        (finitePlaceIdele v x) = 1 :=
  finitePlaceValue_of_ne v w x h

/-- A finite-place idele has component one at every infinite place. -/
@[simp]
theorem finitePlaceIdele_infiniteComponent
    (v : HeightOneSpectrum (𝓞 K))
    (w : InfinitePlace K)
    (x : (v.adicCompletion K)ˣ) :
    IdeleGroup.infiniteComponent w
        (finitePlaceIdele v x) = 1 := by
  rfl

/-- Insert one finite-place element and then pass to the idele class
group. -/
def finitePlaceIdeleClass
    (v : HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletion K)ˣ →* IdeleClassGroup K :=
  (QuotientGroup.mk'
    (IdeleGroup.principalSubgroup K)).comp
      (finitePlaceIdele v)

end IdeleGroup

namespace RelativeIdeleGroup

section Relative

variable
    {K : Type*} [Field K] [NumberField K]
    {L : Type*} [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

open scoped Classical in
/-- The dependent archimedean tensor value which is `z` at `v` and
`1` elsewhere. -/
private def relativeInfinitePlaceValue
    (v : InfinitePlace K)
    (z : (v.Completion ⊗[K] L)ˣ)
    (w : InfinitePlace K) :
    (w.Completion ⊗[K] L)ˣ :=
  if h : w = v then h.symm ▸ z else 1

omit [NumberField K] [NumberField L] [FiniteDimensional K L] in
@[simp]
private theorem relativeInfinitePlaceValue_same
    (v : InfinitePlace K)
    (z : (v.Completion ⊗[K] L)ˣ) :
    relativeInfinitePlaceValue (L := L) v z v = z := by
  simp [relativeInfinitePlaceValue]

omit [NumberField K] [NumberField L] [FiniteDimensional K L] in
@[simp]
private theorem relativeInfinitePlaceValue_of_ne
    (v w : InfinitePlace K)
    (z : (v.Completion ⊗[K] L)ˣ)
    (h : w ≠ v) :
    relativeInfinitePlaceValue (L := L) v z w = 1 := by
  simp [relativeInfinitePlaceValue, h]

/-- Restricted local tensor data supported at one archimedean place. -/
private noncomputable def relativeInfinitePlaceData
    (v : InfinitePlace K)
    (z : (v.Completion ⊗[K] L)ˣ) :
    RelativeLocalIdeleData (K := K) (L := L) where
  infinite w := relativeInfinitePlaceValue (L := L) v z w
  finite _ := 1
  eventually_integral i := by
    have hBase :=
      (relativeIdeleToLocalData
        (K := K) (L := L)
        (1 : RelativeIdeleGroup K L)).eventually_integral i
    filter_upwards [hBase] with w hw
    have hOne :
        (relativeIdeleToLocalData
          (K := K) (L := L)
          (1 : RelativeIdeleGroup K L)).finite w = 1 := by
      change
        RelativeIdeleGroup.finiteComponent
            (K := K) (L := L) w
            (1 : RelativeIdeleGroup K L) = 1
      exact map_one _
    rw [hOne] at hw
    exact hw
  eventually_inverse_integral i := by
    have hBase :=
      (relativeIdeleToLocalData
        (K := K) (L := L)
        (1 : RelativeIdeleGroup K L)).eventually_inverse_integral i
    filter_upwards [hBase] with w hw
    have hOne :
        (relativeIdeleToLocalData
          (K := K) (L := L)
          (1 : RelativeIdeleGroup K L)).finite w = 1 := by
      change
        RelativeIdeleGroup.finiteComponent
            (K := K) (L := L) w
            (1 : RelativeIdeleGroup K L) = 1
      exact map_one _
    rw [hOne] at hw
    exact hw

/-- A relative idele supported at the single archimedean place `v`. -/
def relativeInfinitePlaceIdele
    (v : InfinitePlace K)
    (z : (v.Completion ⊗[K] L)ˣ) :
    RelativeIdeleGroup K L :=
  relativeIdeleOfLocalData
    (K := K) (L := L)
    (relativeInfinitePlaceData (K := K) (L := L) v z)

omit [NumberField L] in
/-- A relative archimedean one-place idele recovers its prescribed
tensor component at the supporting place. -/
@[simp]
theorem relativeInfinitePlaceIdele_infiniteComponent_same
    (v : InfinitePlace K)
    (z : (v.Completion ⊗[K] L)ˣ) :
    RelativeIdeleGroup.infiniteComponent
        (K := K) (L := L) v
        (relativeInfinitePlaceIdele (K := K) (L := L) v z) =
      z := by
  rw [relativeInfinitePlaceIdele,
    relativeIdeleOfLocalData_infiniteComponent]
  exact relativeInfinitePlaceValue_same (L := L) v z

omit [NumberField L] in
/-- A relative archimedean one-place idele has component one at every
other archimedean place. -/
@[simp]
theorem relativeInfinitePlaceIdele_infiniteComponent_of_ne
    (v w : InfinitePlace K)
    (z : (v.Completion ⊗[K] L)ˣ)
    (h : w ≠ v) :
    RelativeIdeleGroup.infiniteComponent
        (K := K) (L := L) w
        (relativeInfinitePlaceIdele (K := K) (L := L) v z) =
      1 := by
  rw [relativeInfinitePlaceIdele,
    relativeIdeleOfLocalData_infiniteComponent]
  exact relativeInfinitePlaceValue_of_ne (L := L) v w z h

omit [NumberField L] in
/-- A relative archimedean one-place idele has component one at every
finite place. -/
@[simp]
theorem relativeInfinitePlaceIdele_finiteComponent
    (v : InfinitePlace K)
    (w : HeightOneSpectrum (𝓞 K))
    (z : (v.Completion ⊗[K] L)ˣ) :
    RelativeIdeleGroup.finiteComponent
        (K := K) (L := L) w
        (relativeInfinitePlaceIdele (K := K) (L := L) v z) =
      1 := by
  rw [relativeInfinitePlaceIdele,
    relativeIdeleOfLocalData_finiteComponent]
  rfl

open scoped Classical in
/-- The dependent local tensor value which is `z` at `v` and `1`
elsewhere. -/
private def relativeFinitePlaceValue
    (v : HeightOneSpectrum (𝓞 K))
    (z : (v.adicCompletion K ⊗[K] L)ˣ)
    (w : HeightOneSpectrum (𝓞 K)) :
    (w.adicCompletion K ⊗[K] L)ˣ :=
  if h : w = v then h.symm ▸ z else 1

omit [NumberField L] [FiniteDimensional K L] in
@[simp]
private theorem relativeFinitePlaceValue_same
    (v : HeightOneSpectrum (𝓞 K))
    (z : (v.adicCompletion K ⊗[K] L)ˣ) :
    relativeFinitePlaceValue (L := L) v z v = z := by
  simp [relativeFinitePlaceValue]

omit [NumberField L] [FiniteDimensional K L] in
@[simp]
private theorem relativeFinitePlaceValue_of_ne
    (v w : HeightOneSpectrum (𝓞 K))
    (z : (v.adicCompletion K ⊗[K] L)ˣ)
    (h : w ≠ v) :
    relativeFinitePlaceValue (L := L) v z w = 1 := by
  simp [relativeFinitePlaceValue, h]

/-- Restricted local data supported at one finite place. -/
private noncomputable def relativeFinitePlaceData
    (v : HeightOneSpectrum (𝓞 K))
    (z : (v.adicCompletion K ⊗[K] L)ˣ) :
    RelativeLocalIdeleData (K := K) (L := L) where
  infinite _ := 1
  finite w := relativeFinitePlaceValue (L := L) v z w
  eventually_integral i := by
    have hBase :=
      (relativeIdeleToLocalData
        (K := K) (L := L)
        (1 : RelativeIdeleGroup K L)).eventually_integral i
    have hAway :
        ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
          w ≠ v := Filter.eventually_cofinite_ne v
    filter_upwards [hBase, hAway] with w hw hne
    have hOne :
        (relativeIdeleToLocalData
          (K := K) (L := L)
          (1 : RelativeIdeleGroup K L)).finite w = 1 := by
      change
        RelativeIdeleGroup.finiteComponent
            (K := K) (L := L) w
            (1 : RelativeIdeleGroup K L) = 1
      exact map_one _
    rw [hOne] at hw
    simpa [relativeFinitePlaceValue_of_ne
      (L := L) v w z hne] using hw
  eventually_inverse_integral i := by
    have hBase :=
      (relativeIdeleToLocalData
        (K := K) (L := L)
        (1 : RelativeIdeleGroup K L)).eventually_inverse_integral i
    have hAway :
        ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
          w ≠ v := Filter.eventually_cofinite_ne v
    filter_upwards [hBase, hAway] with w hw hne
    have hOne :
        (relativeIdeleToLocalData
          (K := K) (L := L)
          (1 : RelativeIdeleGroup K L)).finite w = 1 := by
      change
        RelativeIdeleGroup.finiteComponent
            (K := K) (L := L) w
            (1 : RelativeIdeleGroup K L) = 1
      exact map_one _
    rw [hOne] at hw
    simpa [relativeFinitePlaceValue_of_ne
      (L := L) v w z hne] using hw

/-- A relative idele supported at the single finite place `v`. -/
def relativeFinitePlaceIdele
    (v : HeightOneSpectrum (𝓞 K))
    (z : (v.adicCompletion K ⊗[K] L)ˣ) :
    RelativeIdeleGroup K L :=
  relativeIdeleOfLocalData
    (K := K) (L := L)
    (relativeFinitePlaceData (K := K) (L := L) v z)

omit [NumberField L] in
/-- A relative finite-place idele recovers its prescribed tensor component
at the supporting place. -/
@[simp]
theorem relativeFinitePlaceIdele_finiteComponent_same
    (v : HeightOneSpectrum (𝓞 K))
    (z : (v.adicCompletion K ⊗[K] L)ˣ) :
    RelativeIdeleGroup.finiteComponent
        (K := K) (L := L) v
        (relativeFinitePlaceIdele (K := K) (L := L) v z) =
      z := by
  rw [relativeFinitePlaceIdele,
    relativeIdeleOfLocalData_finiteComponent]
  exact relativeFinitePlaceValue_same (L := L) v z

omit [NumberField L] in
/-- A relative finite-place idele has component one at every other finite
place. -/
@[simp]
theorem relativeFinitePlaceIdele_finiteComponent_of_ne
    (v w : HeightOneSpectrum (𝓞 K))
    (z : (v.adicCompletion K ⊗[K] L)ˣ)
    (h : w ≠ v) :
    RelativeIdeleGroup.finiteComponent
        (K := K) (L := L) w
        (relativeFinitePlaceIdele (K := K) (L := L) v z) =
      1 := by
  rw [relativeFinitePlaceIdele,
    relativeIdeleOfLocalData_finiteComponent]
  exact relativeFinitePlaceValue_of_ne (L := L) v w z h

omit [NumberField L] in
/-- A relative finite-place idele has component one at every infinite
place. -/
@[simp]
theorem relativeFinitePlaceIdele_infiniteComponent
    (v : HeightOneSpectrum (𝓞 K))
    (w : InfinitePlace K)
    (z : (v.adicCompletion K ⊗[K] L)ˣ) :
    RelativeIdeleGroup.infiniteComponent
        (K := K) (L := L) w
        (relativeFinitePlaceIdele (K := K) (L := L) v z) =
      1 := by
  rw [relativeFinitePlaceIdele,
    relativeIdeleOfLocalData_infiniteComponent]
  rfl

end Relative

end RelativeIdeleGroup
