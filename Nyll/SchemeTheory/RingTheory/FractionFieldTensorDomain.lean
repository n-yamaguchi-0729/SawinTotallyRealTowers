/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.Algebra.Rat

/-!
# Tensor domains after passage to a fraction field

A flat algebra over an arbitrary base embeds in its tensor product with a
faithful algebra. If that tensor product is a domain, localizing the original
algebra to its fraction field preserves this property. Over the integers this
also compares the integral and rational tensor products of fraction fields.
-/

open scoped TensorProduct

namespace Algebra.TensorProduct

/-- A domain tensor product remains a domain after localizing its flat left
factor to a fraction field. Injectivity of the right structure map ensures
that the denominators remain nonzero in the tensor product. -/
theorem isDomain_of_isFractionRing_left_of_flat
    {R B F K : Type*} [CommRing R] [CommRing B] [IsDomain B] [Algebra R B]
    [CommRing F] [Algebra R F] [Algebra B F] [IsScalarTower R B F]
    [IsFractionRing B F] [CommRing K] [Algebra R K]
    [Module.Flat R B] [IsDomain (B ⊗[R] K)]
    (hK : Function.Injective (algebraMap R K)) :
    IsDomain (F ⊗[R] K) := by
  let m : B ⊗[R] K →ₐ[R] F ⊗[R] K :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom R B F) (AlgHom.id R K)
  let : Algebra (B ⊗[R] K) (F ⊗[R] K) := m.toRingHom.toAlgebra
  have : IsScalarTower B (B ⊗[R] K) (F ⊗[R] K) := by
    apply IsScalarTower.of_algebraMap_eq'
    ext b
    change algebraMap B F b ⊗ₜ[R] (1 : K) = m (b ⊗ₜ[R] (1 : K))
    simp only [m, Algebra.TensorProduct.map_tmul, IsScalarTower.toAlgHom_apply,
      AlgHom.id_apply]
  have hmap : (algebraMap (B ⊗[R] K) (F ⊗[R] K)).comp
      Algebra.TensorProduct.includeRight.toRingHom =
      Algebra.TensorProduct.includeRight.toRingHom := by
    ext k
    change m ((1 : B) ⊗ₜ[R] k) = (1 : F) ⊗ₜ[R] k
    simp only [m, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
  let : IsLocalization
      (Algebra.algebraMapSubmonoid (B ⊗[R] K) (nonZeroDivisors B)) (F ⊗[R] K) :=
    IsLocalization.tensorProduct_tensorProduct R K (nonZeroDivisors B) F hmap
  have hinj : Function.Injective (algebraMap B (B ⊗[R] K)) :=
    Algebra.TensorProduct.includeLeft_injective (S := R) (A := B) hK
  apply IsLocalization.isDomain_of_le_nonZeroDivisors
    (R := B ⊗[R] K)
    (M := Algebra.algebraMapSubmonoid (B ⊗[R] K) (nonZeroDivisors B))
  rintro x ⟨b, hb, rfl⟩
  rw [mem_nonZeroDivisors_iff_ne_zero]
  intro hzero
  exact nonZeroDivisors.ne_zero hb (hinj (hzero.trans (map_zero _).symm))

/-- An integral tensor product over the integers controls the rational tensor
product after passage to the fraction field of a flat domain. -/
theorem isDomain_ratTensor_of_isFractionRing_intTensor
    {B F K : Type*} [CommRing B] [IsDomain B] [Module.Flat ℤ B]
    [Field F] [CharZero F] [Algebra B F] [IsFractionRing B F]
    [Field K] [CharZero K] [IsDomain (B ⊗[ℤ] K)] :
    IsDomain (F ⊗[ℚ] K) := by
  let : IsDomain (F ⊗[ℤ] K) :=
    isDomain_of_isFractionRing_left_of_flat
      (R := ℤ) (B := B) (F := F) (K := K) (Int.cast_injective (α := K))
  let e : F ⊗[ℚ] K ≃ₐ[ℚ] F ⊗[ℤ] K :=
    IsLocalization.algebraTensorEquiv (nonZeroDivisors ℤ) ℚ F K
  exact (MulEquiv.isDomain_iff e.toRingEquiv.toMulEquiv).mpr inferInstance

end Algebra.TensorProduct
