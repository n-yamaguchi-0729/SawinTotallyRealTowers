/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Completion.FinitePlaceModel
public import Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.Completion
public import Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.CompletionIntegers
public import Nyll.ValuedFieldTheory.Valuation.Completion.TensorProductDecomposition
public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Topology.Algebra.RestrictedProduct.Basic

/-!
# Intrinsic finite tensor factors

The completed tensor algebra decomposes into the product of the completions
above a finite place. Its component maps and integral subgroups are defined
here without global adelic coordinates or a Galois action. Basis-dependent
integral comparisons and action covariance use these same maps downstream.
-/

@[expose] public section

open scoped NumberField TensorProduct RestrictedProduct
open NumberField IsDedekindDomain
open AlgebraicNumberTheory.Valuations

noncomputable section

universe u v

variable {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

/-- The component of the concrete finite tensor factor in a completion
above `w`, obtained from the canonical local tensor equivalence. -/
noncomputable def finitePlaceLocalTensorDecompositionComponent
    (w : HeightOneSpectrum (𝓞 K))
    (wL : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K w) L)
    (x : w.adicCompletion K ⊗[K] L) :
    wL.1.Completion := by
  let vK :=
    NumberField.HeightOneSpectrum.adicAbv K w
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial w
  letI : ∀ u : AbsoluteValueExtension vK L,
      Algebra vK.Completion u.1.Completion :=
    fun u =>
      AbsoluteValue.completionAlgebra vK u.1 u.2
  exact
    completionTensorDecomposition_left
      (K := K) (L := L) vK hvK
      ((finitePlaceLocalTensorAlgEquiv
        (K := K) (L := L) w).symm x) wL

/-- Integrality in the actual product of completion valuation rings
on the local tensor-product side. -/
def RelativeLocalTensorDecompositionIntegralAt
    (w : HeightOneSpectrum (𝓞 K))
    (x : w.adicCompletion K ⊗[K] L) : Prop :=
  ∀ wL : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K w) L,
    finitePlaceLocalTensorDecompositionComponent
        (K := K) (L := L) w wL x ∈
      absoluteValueCompletionIntegers wL.1
        (absoluteValueExtension_isNonarchimedean
          (NumberField.HeightOneSpectrum.adicAbv K w)
          (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv
            K w) wL)

/-- A tensor unit is valuation-integral when every completion
component of it and of its inverse is in the corresponding valuation
ring. -/
def RelativeLocalTensorDecompositionIntegralUnitAt
    (w : HeightOneSpectrum (𝓞 K))
    (x : (w.adicCompletion K ⊗[K] L)ˣ) : Prop :=
  RelativeLocalTensorDecompositionIntegralAt
      (K := K) (L := L) w
      (x : w.adicCompletion K ⊗[K] L) ∧
    RelativeLocalTensorDecompositionIntegralAt
      (K := K) (L := L) w
      ((x⁻¹ : (w.adicCompletion K ⊗[K] L)ˣ) :
        w.adicCompletion K ⊗[K] L)

omit [NumberField L] in
/-- The local tensor-decomposition component of a pure tensor has the expected value. -/
@[simp]
theorem finitePlaceLocalTensorDecompositionComponent_tmul
    (w : HeightOneSpectrum (𝓞 K))
    (wL : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K w) L)
    (a : w.adicCompletion K) (b : L) :
    finitePlaceLocalTensorDecompositionComponent
        (K := K) (L := L) w wL (a ⊗ₜ[K] b) =
      AbsoluteValue.completionMap
          (NumberField.HeightOneSpectrum.adicAbv K w)
          wL.1 wL.2
          ((finitePlaceCompletionAlgEquiv w).symm a) *
        AbsoluteValue.toCompletion wL.1 b := by
  change
    completionTensorDecomposition_left
        (K := K) (L := L)
        (HeightOneSpectrum.adicAbv K w) (RayClass.adicAbv_isNontrivial w)
        (((finitePlaceCompletionAlgEquiv w).symm a) ⊗ₜ[K] b) wL = _
  exact completionTensorDecomposition_left_tmul_apply
    (HeightOneSpectrum.adicAbv K w) (RayClass.adicAbv_isNontrivial w)
    ((finitePlaceCompletionAlgEquiv w).symm a) b wL

/-- The projection of the finite local tensor algebra to one completion
factor in the canonical local tensor decomposition, as a ring homomorphism. -/
noncomputable def finitePlaceLocalTensorDecompositionComponentRingHom
    (w : HeightOneSpectrum (𝓞 K))
    (wL : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K w) L) :
    (w.adicCompletion K ⊗[K] L) →+* wL.1.Completion := by
  let vK := HeightOneSpectrum.adicAbv K w
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial w
  letI : ∀ u : AbsoluteValueExtension vK L,
      Algebra vK.Completion u.1.Completion :=
    fun u =>
      AbsoluteValue.completionAlgebra vK u.1 u.2
  exact
    (Pi.evalRingHom
      (fun u : AbsoluteValueExtension vK L =>
        u.1.Completion) wL).comp
      ((completionTensorDecomposition_left
        (K := K) (L := L) vK hvK).toRingEquiv.toRingHom.comp
        (finitePlaceLocalTensorAlgEquiv
          (K := K) (L := L) w).symm.toRingEquiv.toRingHom)

omit [NumberField L] in
/-- The ring-homomorphism packaging evaluates to the original
relative-tensor component map. -/
@[simp]
theorem finitePlaceLocalTensorDecompositionComponentRingHom_apply
    (w : HeightOneSpectrum (𝓞 K))
    (wL : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K w) L)
    (x : w.adicCompletion K ⊗[K] L) :
    finitePlaceLocalTensorDecompositionComponentRingHom
        (K := K) (L := L) w wL x =
      finitePlaceLocalTensorDecompositionComponent
        (K := K) (L := L) w wL x :=
  rfl

omit [NumberField L] in
/-- Every relative-tensor component map sends zero to zero. -/
@[simp]
theorem finitePlaceLocalTensorDecompositionComponent_zero
    (w : HeightOneSpectrum (𝓞 K))
    (wL : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K w) L) :
    finitePlaceLocalTensorDecompositionComponent
        (K := K) (L := L) w wL 0 = 0 := by
  simpa only [finitePlaceLocalTensorDecompositionComponentRingHom_apply] using
    (finitePlaceLocalTensorDecompositionComponentRingHom
      (K := K) (L := L) w wL).map_zero

omit [NumberField L] in
/-- Relative-tensor component maps preserve addition. -/
@[simp]
theorem finitePlaceLocalTensorDecompositionComponent_add
    (w : HeightOneSpectrum (𝓞 K))
    (wL : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K w) L)
    (x y : w.adicCompletion K ⊗[K] L) :
    finitePlaceLocalTensorDecompositionComponent
        (K := K) (L := L) w wL (x + y) =
      finitePlaceLocalTensorDecompositionComponent
          (K := K) (L := L) w wL x +
        finitePlaceLocalTensorDecompositionComponent
          (K := K) (L := L) w wL y := by
  simpa only [finitePlaceLocalTensorDecompositionComponentRingHom_apply] using
    (finitePlaceLocalTensorDecompositionComponentRingHom
      (K := K) (L := L) w wL).map_add x y

/-- The corresponding component homomorphism on units. -/
noncomputable def finitePlaceLocalTensorDecompositionUnitsComponent
    (w : HeightOneSpectrum (𝓞 K))
    (wL : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K w) L) :
    (w.adicCompletion K ⊗[K] L)ˣ →*
      wL.1.Completionˣ :=
  Units.map
    (finitePlaceLocalTensorDecompositionComponentRingHom
      (K := K) (L := L) w wL)

/-- The canonical local tensor decomposition on the complete group of units of the finite local
tensor algebra. -/
noncomputable def finitePlaceLocalTensorDecompositionUnitsEquiv
    (w : HeightOneSpectrum (𝓞 K)) :
    (w.adicCompletion K ⊗[K] L)ˣ ≃*
      ∀ wL : AbsoluteValueExtension
          (HeightOneSpectrum.adicAbv K w) L,
        wL.1.Completionˣ := by
  let vK := HeightOneSpectrum.adicAbv K w
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial w
  letI : ∀ u : AbsoluteValueExtension vK L,
      Algebra vK.Completion u.1.Completion :=
    fun u =>
      AbsoluteValue.completionAlgebra vK u.1 u.2
  exact
    (Units.mapEquiv
      (((finitePlaceLocalTensorAlgEquiv
            (K := K) (L := L) w).symm.toRingEquiv.trans
          (completionTensorDecomposition_left
            (K := K) (L := L) vK hvK).toRingEquiv).toMulEquiv)).trans
      MulEquiv.piUnits

omit [NumberField L] in
/-- The product equivalence on units evaluates componentwise through the
corresponding unit homomorphism. -/
@[simp]
theorem finitePlaceLocalTensorDecompositionUnitsEquiv_apply
    (w : HeightOneSpectrum (𝓞 K))
    (x : (w.adicCompletion K ⊗[K] L)ˣ)
    (wL : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K w) L) :
    finitePlaceLocalTensorDecompositionUnitsEquiv
        (K := K) (L := L) w x wL =
      finitePlaceLocalTensorDecompositionUnitsComponent
        (K := K) (L := L) w wL x :=
  rfl

omit [NumberField L] in
/-- Coercing a unit component to the completion agrees with applying the
underlying tensor component map. -/
@[simp]
theorem finitePlaceLocalTensorDecompositionUnitsComponent_coe
    (w : HeightOneSpectrum (𝓞 K))
    (wL : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K w) L)
    (x : (w.adicCompletion K ⊗[K] L)ˣ) :
    ((finitePlaceLocalTensorDecompositionUnitsComponent
        (K := K) (L := L) w wL x :
          wL.1.Completionˣ) :
        wL.1.Completion) =
      finitePlaceLocalTensorDecompositionComponent
        (K := K) (L := L) w wL
        (x : w.adicCompletion K ⊗[K] L) :=
  rfl

omit [NumberField L] in
/-- Integrality of a tensor unit is exactly membership of every
relative-tensor component in the unit subgroup of its valuation ring. -/
theorem relativeLocalTensorDecompositionIntegralUnitAt_iff
    (w : HeightOneSpectrum (𝓞 K))
    (x : (w.adicCompletion K ⊗[K] L)ˣ) :
    RelativeLocalTensorDecompositionIntegralUnitAt
        (K := K) (L := L) w x ↔
      ∀ wL : AbsoluteValueExtension
          (HeightOneSpectrum.adicAbv K w) L,
        finitePlaceLocalTensorDecompositionUnitsComponent
            (K := K) (L := L) w wL x ∈
          (absoluteValueCompletionIntegers wL.1
            (absoluteValueExtension_isNonarchimedean
              (HeightOneSpectrum.adicAbv K w)
              (HeightOneSpectrum.isNonarchimedean_adicAbv K w)
              wL)).units := by
  constructor
  · rintro ⟨hx, hxinv⟩ wL
    exact ⟨hx wL, by
      change
        finitePlaceLocalTensorDecompositionComponent
            (K := K) (L := L) w wL
            (↑(x⁻¹) :
              w.adicCompletion K ⊗[K] L) ∈
          absoluteValueCompletionIntegers wL.1
            (absoluteValueExtension_isNonarchimedean
              (HeightOneSpectrum.adicAbv K w)
              (HeightOneSpectrum.isNonarchimedean_adicAbv K w)
              wL)
      exact hxinv wL⟩
  · intro hx
    constructor
    · intro wL
      exact (hx wL).1
    · intro wL
      exact (hx wL).2

/-- The intrinsic integral subring of a finite local tensor algebra is the
inverse image of the valuation rings in all completion factors. -/
noncomputable def relativeLocalTensorDecompositionIntegralSubring
    (w : HeightOneSpectrum (𝓞 K)) :
    Subring (w.adicCompletion K ⊗[K] L) where
  carrier := {x | RelativeLocalTensorDecompositionIntegralAt (K := K) (L := L) w x}
  zero_mem' := by
    intro wL
    change finitePlaceLocalTensorDecompositionComponentRingHom
      (K := K) (L := L) w wL 0 ∈ _
    rw [map_zero]
    exact zero_mem _
  one_mem' := by
    intro wL
    change finitePlaceLocalTensorDecompositionComponentRingHom
      (K := K) (L := L) w wL 1 ∈ _
    rw [map_one]
    exact one_mem _
  add_mem' := by
    intro x y hx hy wL
    change finitePlaceLocalTensorDecompositionComponentRingHom
      (K := K) (L := L) w wL (x + y) ∈ _
    rw [map_add]
    exact add_mem (hx wL) (hy wL)
  neg_mem' := by
    intro x hx wL
    change finitePlaceLocalTensorDecompositionComponentRingHom
      (K := K) (L := L) w wL (-x) ∈ _
    rw [map_neg]
    exact neg_mem (hx wL)
  mul_mem' := by
    intro x y hx hy wL
    change finitePlaceLocalTensorDecompositionComponentRingHom
      (K := K) (L := L) w wL (x * y) ∈ _
    rw [map_mul]
    exact mul_mem (hx wL) (hy wL)

/-- The actual integral-unit subgroup is the unit subgroup of the same
intrinsic integral subring used in the relative restricted adele ring. -/
noncomputable def relativeLocalTensorDecompositionIntegralUnitSubgroup
    (w : HeightOneSpectrum (𝓞 K)) :
    Subgroup (w.adicCompletion K ⊗[K] L)ˣ :=
  (relativeLocalTensorDecompositionIntegralSubring (K := K) (L := L) w).units

/-- The product of the actual valuation-ring unit groups in all
completion factors above a finite base place. -/
abbrev FinitePlaceLocalTensorDecompositionIntegralUnitProduct
    (w : HeightOneSpectrum (𝓞 K)) :=
  Subgroup.pi Set.univ fun
      wL : AbsoluteValueExtension
        (HeightOneSpectrum.adicAbv K w) L =>
    (absoluteValueCompletionIntegers wL.1
      (absoluteValueExtension_isNonarchimedean
        (HeightOneSpectrum.adicAbv K w)
        (HeightOneSpectrum.isNonarchimedean_adicAbv K w)
        wL)).units

/-- A product subgroup is the product of its component subgroup types. -/
@[implicit_reducible]
noncomputable def
    finitePlaceLocalTensorDecompositionIntegralUnitProductEquivPi
    (w : HeightOneSpectrum (𝓞 K)) :
    FinitePlaceLocalTensorDecompositionIntegralUnitProduct
        (K := K) (L := L) w ≃*
      ∀ wL : AbsoluteValueExtension
          (HeightOneSpectrum.adicAbv K w) L,
        (absoluteValueCompletionIntegers wL.1
          (absoluteValueExtension_isNonarchimedean
            (HeightOneSpectrum.adicAbv K w)
            (HeightOneSpectrum.isNonarchimedean_adicAbv K w)
            wL)).units where
  toFun x wL :=
    ⟨x.1 wL, x.2 wL (Set.mem_univ wL)⟩
  invFun x :=
    ⟨fun wL => x wL, by
      intro wL hwL
      exact (x wL).2⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv x := by
    funext wL
    apply Subtype.ext
    rfl
  map_mul' x y := by
    funext wL
    apply Subtype.ext
    rfl

/-- Replace each valuation-ring unit subgroup by the intrinsic unit
group of the valuation ring. -/
noncomputable def
    finitePlaceLocalTensorDecompositionIntegralUnitProductEquivPiUnits
    (w : HeightOneSpectrum (𝓞 K)) :
    FinitePlaceLocalTensorDecompositionIntegralUnitProduct
        (K := K) (L := L) w ≃*
      ∀ wL : AbsoluteValueExtension
          (HeightOneSpectrum.adicAbv K w) L,
        (absoluteValueCompletionIntegers wL.1
          (absoluteValueExtension_isNonarchimedean
            (HeightOneSpectrum.adicAbv K w)
            (HeightOneSpectrum.isNonarchimedean_adicAbv K w)
            wL))ˣ :=
  (finitePlaceLocalTensorDecompositionIntegralUnitProductEquivPi
    (K := K) (L := L) w).trans
      (MulEquiv.piCongrRight fun wL =>
        (absoluteValueCompletionIntegers wL.1
          (absoluteValueExtension_isNonarchimedean
            (HeightOneSpectrum.adicAbv K w)
            (HeightOneSpectrum.isNonarchimedean_adicAbv K w)
            wL)).unitsEquivUnitsType)

omit [NumberField L] in
/-- Membership in the integral tensor-unit subgroup is exactly the
pointwise valuation-ring integrality condition. -/
@[simp]
theorem mem_relativeLocalTensorDecompositionIntegralUnitSubgroup_iff
    (w : HeightOneSpectrum (𝓞 K))
    (x : (w.adicCompletion K ⊗[K] L)ˣ) :
    x ∈ relativeLocalTensorDecompositionIntegralUnitSubgroup
        (K := K) (L := L) w ↔
      RelativeLocalTensorDecompositionIntegralUnitAt
        (K := K) (L := L) w x :=
  Iff.rfl

/-- The integral local tensor-unit subgroup is exactly the product of
the valuation-ring unit groups occurring in the canonical local tensor decomposition. -/
noncomputable def
    relativeLocalTensorDecompositionIntegralUnitSubgroupEquivProduct
    (w : HeightOneSpectrum (𝓞 K)) :
    relativeLocalTensorDecompositionIntegralUnitSubgroup
        (K := K) (L := L) w ≃*
      FinitePlaceLocalTensorDecompositionIntegralUnitProduct
        (K := K) (L := L) w where
  toFun x := ⟨finitePlaceLocalTensorDecompositionUnitsEquiv
      (K := K) (L := L) w x, by
    have hx := x.property
    rw [mem_relativeLocalTensorDecompositionIntegralUnitSubgroup_iff,
      relativeLocalTensorDecompositionIntegralUnitAt_iff] at hx
    rw [Subgroup.mem_pi]
    intro wL hwL
    simpa only [finitePlaceLocalTensorDecompositionUnitsEquiv_apply] using
      (hx wL)⟩
  invFun y := ⟨(finitePlaceLocalTensorDecompositionUnitsEquiv
      (K := K) (L := L) w).symm y, by
    rw [mem_relativeLocalTensorDecompositionIntegralUnitSubgroup_iff,
      relativeLocalTensorDecompositionIntegralUnitAt_iff]
    intro wL
    have hy :
        finitePlaceLocalTensorDecompositionUnitsEquiv
            (K := K) (L := L) w
            ((finitePlaceLocalTensorDecompositionUnitsEquiv
              (K := K) (L := L) w).symm y) wL ∈
          (absoluteValueCompletionIntegers wL.1
            (absoluteValueExtension_isNonarchimedean
              (HeightOneSpectrum.adicAbv K w)
              (HeightOneSpectrum.isNonarchimedean_adicAbv K w)
              wL)).units := by
      rw [(finitePlaceLocalTensorDecompositionUnitsEquiv
        (K := K) (L := L) w).apply_symm_apply]
      exact y.property wL (Set.mem_univ wL)
    simpa only [finitePlaceLocalTensorDecompositionUnitsEquiv_apply] using hy⟩
  left_inv x := by
    apply Subtype.ext
    exact
      (finitePlaceLocalTensorDecompositionUnitsEquiv
        (K := K) (L := L) w).symm_apply_apply x
  right_inv y := by
    apply Subtype.ext
    exact
      (finitePlaceLocalTensorDecompositionUnitsEquiv
        (K := K) (L := L) w).apply_symm_apply y
  map_mul' x y := by
    apply Subtype.ext
    exact
      (finitePlaceLocalTensorDecompositionUnitsEquiv
        (K := K) (L := L) w).map_mul x y

/-- Final local form: the integral tensor units are the product of the
intrinsic unit groups of all completion valuation rings above `w`. -/
noncomputable def
    relativeLocalTensorDecompositionIntegralUnitSubgroupEquivPiUnits
    (w : HeightOneSpectrum (𝓞 K)) :
    relativeLocalTensorDecompositionIntegralUnitSubgroup
        (K := K) (L := L) w ≃*
      ∀ wL : AbsoluteValueExtension
          (HeightOneSpectrum.adicAbv K w) L,
        (absoluteValueCompletionIntegers wL.1
          (absoluteValueExtension_isNonarchimedean
            (HeightOneSpectrum.adicAbv K w)
            (HeightOneSpectrum.isNonarchimedean_adicAbv K w)
            wL))ˣ :=
  (relativeLocalTensorDecompositionIntegralUnitSubgroupEquivProduct
    (K := K) (L := L) w).trans
      (finitePlaceLocalTensorDecompositionIntegralUnitProductEquivPiUnits
        (K := K) (L := L) w)

/-- Finite tensor-unit families integral at almost every place, with the
standard pointwise restricted-product group structure. -/
abbrev RelativeFiniteIdeleData :=
  Πʳ w : HeightOneSpectrum (𝓞 K),
    [(w.adicCompletion K ⊗[K] L)ˣ,
      relativeLocalTensorDecompositionIntegralUnitSubgroup (K := K) (L := L) w]

omit [NumberField L] in
/-- The finite components of the canonical restricted product. -/
abbrev RelativeFiniteIdeleData.finite
    (a : RelativeFiniteIdeleData (K := K) (L := L)) :
    ∀ w : HeightOneSpectrum (𝓞 K), (w.adicCompletion K ⊗[K] L)ˣ :=
  a

omit [NumberField L] in
/-- Finite restricted families are determined by their component values. -/
@[ext]
theorem RelativeFiniteIdeleData.ext
    {a b : RelativeFiniteIdeleData (K := K) (L := L)}
    (hfinite : a.finite = b.finite) : a = b :=
  Subtype.ext hfinite

omit [NumberField L] in
/-- Multiplication of finite restricted families is pointwise. -/
@[simp]
theorem RelativeFiniteIdeleData.finite_mul
    (a b : RelativeFiniteIdeleData (K := K) (L := L))
    (w : HeightOneSpectrum (𝓞 K)) :
    (a * b).finite w = a.finite w * b.finite w :=
  rfl
