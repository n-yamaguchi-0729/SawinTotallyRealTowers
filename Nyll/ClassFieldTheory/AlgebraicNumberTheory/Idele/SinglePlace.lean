/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Order.Filter.Cofinite
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Adele.RestrictedProduct
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Topology
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Approximation
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Basic
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Components
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalCore
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.LocalComponent

/-!
# Ideles supported at one place

Local-to-global diagrams use the canonical embedding of a local multiplicative
group into the idele group. This file constructs
that embedding at finite places and the corresponding one-component
relative idele.
-/



@[expose] public section

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section

namespace IdeleGroup

variable {K : Type*} [Field K] [NumberField K]

/-- The infinite one-place map into the standard idèle group. -/
abbrev infinitePlaceIdele (v : InfinitePlace K) : v.Completionˣ →* IdeleGroup K :=
  NumberField.IdeleGroup.ofCompletion (𝓞 K) K v

/-- Inserting a unit at one archimedean place is continuous. -/
theorem continuous_infinitePlaceIdele (v : InfinitePlace K) :
    Continuous (infinitePlaceIdele v) :=
  NumberField.IdeleGroup.continuous_ofCompletion v

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
        (infinitePlaceIdele v x) = x :=
  NumberField.IdeleGroup.infiniteComponent_ofCompletion_same v x

/-- An archimedean one-place idele has component one at every other
archimedean place. -/
@[simp]
theorem infinitePlaceIdele_infiniteComponent_of_ne
    (v w : InfinitePlace K)
    (x : v.Completionˣ)
    (h : w ≠ v) :
    IdeleGroup.infiniteComponent w
        (infinitePlaceIdele v x) = 1 :=
  NumberField.IdeleGroup.infiniteComponent_ofCompletion_of_ne v w x h

/-- An archimedean one-place idele has component one at every finite
place. -/
@[simp]
theorem infinitePlaceIdele_finiteComponent
    (v : InfinitePlace K)
    (w : HeightOneSpectrum (𝓞 K))
    (x : v.Completionˣ) :
    IdeleGroup.finiteComponent w
        (infinitePlaceIdele v x) = 1 :=
  NumberField.IdeleGroup.finiteComponent_ofCompletion v x w

/-- The finite coordinates of a pure archimedean idèle are trivial. -/
@[simp]
theorem finiteCoordinates_infinitePlaceIdele
    (v : InfinitePlace K) (x : v.Completionˣ) :
    finiteCoordinates (infinitePlaceIdele v x) = 1 := by
  apply RestrictedProduct.ext
  intro w
  exact infinitePlaceIdele_finiteComponent v w x

/-- Insert one archimedean-place element and then pass to the idele
class group. -/
abbrev infinitePlaceIdeleClass
    (v : InfinitePlace K) :
    v.Completionˣ →* IdeleClassGroup K :=
  NumberField.IdeleClassGroup.ofCompletion (𝓞 K) K v

@[simp]
theorem toStandardClass_infinitePlaceIdele
    (v : InfinitePlace K) (x : v.Completionˣ) :
    toStandardClass K (infinitePlaceIdele v x) = infinitePlaceIdeleClass v x := rfl

/-- The finite one-place map into the standard idèle group. -/
abbrev finitePlaceIdele (v : HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletion K)ˣ →* IdeleGroup K :=
  NumberField.IdeleGroup.ofAdicCompletion (𝓞 K) K v

/-- A finite-place idele recovers its prescribed component at the
supporting place. -/
@[simp]
theorem finitePlaceIdele_finiteComponent_same
    (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) :
    IdeleGroup.finiteComponent v
        (finitePlaceIdele v x) = x :=
  NumberField.IdeleGroup.finiteComponent_ofAdicCompletion_same v x

/-- A finite-place idele has component one at every other finite place. -/
@[simp]
theorem finitePlaceIdele_finiteComponent_of_ne
    (v w : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ)
    (h : w ≠ v) :
    IdeleGroup.finiteComponent w
        (finitePlaceIdele v x) = 1 :=
  NumberField.IdeleGroup.finiteComponent_ofAdicCompletion_of_ne v w x h

/-- A finite-place idele has component one at every infinite place. -/
@[simp]
theorem finitePlaceIdele_infiniteComponent
    (v : HeightOneSpectrum (𝓞 K))
    (w : InfinitePlace K)
    (x : (v.adicCompletion K)ˣ) :
    IdeleGroup.infiniteComponent w
        (finitePlaceIdele v x) = 1 :=
  NumberField.IdeleGroup.infiniteComponent_ofAdicCompletion v x w

/-- The archimedean part of a finite-place idèle is trivial. -/
@[simp]
theorem infinitePart_finitePlaceIdele
    (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    infinitePart (finitePlaceIdele v x) = 1 := by
  apply ContinuousMulEquiv.piUnits.injective
  funext w
  rw [map_one]
  exact finitePlaceIdele_infiniteComponent v w x

/-- Insert one finite-place element and then pass to the idele class
group. -/
abbrev finitePlaceIdeleClass
    (v : HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletion K)ˣ →* IdeleClassGroup K :=
  NumberField.IdeleClassGroup.ofAdicCompletion (𝓞 K) K v

@[simp]
theorem toStandardClass_finitePlaceIdele
    (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    toStandardClass K (finitePlaceIdele v x) = finitePlaceIdeleClass v x := rfl

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
def relativeInfinitePlaceValue
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
noncomputable def relativeInfinitePlaceData
    (v : InfinitePlace K) (z : (v.Completion ⊗[K] L)ˣ) :
    RelativeLocalIdeleData (K := K) (L := L) :=
  ⟨relativeInfinitePlaceValue (L := L) v z, 1⟩

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
def relativeFinitePlaceValue
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
theorem relativeFinitePlaceValue_of_ne
    (v w : HeightOneSpectrum (𝓞 K))
    (z : (v.adicCompletion K ⊗[K] L)ˣ)
    (h : w ≠ v) :
    relativeFinitePlaceValue (L := L) v z w = 1 := by
  simp [relativeFinitePlaceValue, h]

/-- Restricted local data supported at one finite place. -/
noncomputable def relativeFinitePlaceData
    (v : HeightOneSpectrum (𝓞 K)) (z : (v.adicCompletion K ⊗[K] L)ˣ) :
    RelativeLocalIdeleData (K := K) (L := L) :=
  ⟨1, ⟨relativeFinitePlaceValue (L := L) v z, by
    filter_upwards [Filter.eventually_cofinite_ne v] with w hw
    rw [relativeFinitePlaceValue_of_ne (L := L) v w z hw]
    exact one_mem _⟩⟩

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
