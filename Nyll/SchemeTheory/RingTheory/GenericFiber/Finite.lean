/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Generic fibre of a finite domain extension

For a finite extension of domains `C / R`, extending scalars from `R` to a
fraction field `K` identifies the generic fibre `K ⊗[R] C` with a fraction
field `E` of `C`, provided the two fraction-field embeddings are compatible.

The proof regards both sides as localizations of `C` at the image of the
non-zero elements of `R`.  Finiteness makes `C / R` algebraic, so every
non-zero denominator from `C` can be cleared by a non-zero element of `R`.
-/

noncomputable section

namespace EtaleFundamentalGroups

open scoped TensorProduct

universe uR uC uK uE

/-- The generic fibre of a finite extension of domains is its fraction field.

The equivalence is the natural product map induced by `K → E` and `C → E`.
In particular, it preserves the specified embeddings rather than merely
producing an abstract field equivalence. -/
def finiteGenericFiberAlgEquiv
    {R : Type uR} {C : Type uC} {K : Type uK} {E : Type uE}
    [CommRing R] [IsDomain R]
    [CommRing C] [IsDomain C] [Algebra R C] [Module.Finite R C]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field E] [Algebra C E] [IsFractionRing C E]
    [Algebra R E] [IsScalarTower R C E]
    [Algebra K E] [IsScalarTower R K E] :
    (K ⊗[R] C) ≃ₐ[K] E := by
  let M : Submonoid C :=
    Algebra.algebraMapSubmonoid C (nonZeroDivisors R)
  have hRE : Function.Injective (algebraMap R E) := by
    rw [IsScalarTower.algebraMap_eq R K E]
    exact (algebraMap K E).injective.comp
      (FaithfulSMul.algebraMap_injective R K)
  have hRC : Function.Injective (algebraMap R C) := by
    intro x y hxy
    apply hRE
    rw [IsScalarTower.algebraMap_apply R C E,
      IsScalarTower.algebraMap_apply R C E, hxy]
  letI : IsLocalization M E :=
    (isLocalization_iff M E).2 ⟨
      (by
        intro y
        obtain ⟨r, hr, hyr⟩ := y.property
        apply IsUnit.mk0
        intro hy
        apply (nonZeroDivisors.coe_ne_zero ⟨r, hr⟩)
        apply hRE
        rw [IsScalarTower.algebraMap_apply R C E, hyr]
        simpa using hy),
      (by
        intro z
        obtain ⟨a, b, hab⟩ :=
          IsLocalization.exists_mk'_eq (nonZeroDivisors C) z
        obtain ⟨c, d, hd, hden⟩ :=
          Algebra.IsAlgebraic.exists_smul_eq_mul R a
            (nonZeroDivisors.coe_ne_zero b)
        have hdC : algebraMap R C d ≠ 0 := by
          intro hdC
          exact hd (hRC (by simpa using hdC))
        let dC : nonZeroDivisors C :=
          ⟨algebraMap R C d, mem_nonZeroDivisors_iff_ne_zero.mpr hdC⟩
        let dM : M :=
          ⟨algebraMap R C d,
            Algebra.mem_algebraMapSubmonoid_of_mem
              ⟨d, mem_nonZeroDivisors_iff_ne_zero.mpr hd⟩⟩
        refine ⟨⟨c, dM⟩, ?_⟩
        rw [← hab]
        have hfrac : IsLocalization.mk' E a b =
            IsLocalization.mk' E c dC := by
          apply IsLocalization.mk'_eq_of_eq
          simpa only [dC, Algebra.smul_def] using hden.symm
        rw [hfrac]
        simpa only [dC, dM] using
          (IsLocalization.mk'_spec E c dC)),
      (by
        intro x y hxy
        refine ⟨1, ?_⟩
        have hxy' : x = y :=
          (FaithfulSMul.algebraMap_injective C E) hxy
        simp only [Submonoid.coe_one, one_mul, hxy'])⟩
  letI : Algebra C (K ⊗[R] C) :=
    Algebra.TensorProduct.rightAlgebra
  letI : IsLocalization M (K ⊗[R] C) :=
    IsLocalization.tensorRight (R := R) (S := C) (A := K)
      (nonZeroDivisors R)
  let f : (K ⊗[R] C) →ₐ[K] E :=
    (AlgHom.liftEquiv R K C E)
      (IsScalarTower.toAlgHom R C E)
  have hfC : f.toRingHom.comp (algebraMap C (K ⊗[R] C)) =
      algebraMap C E := by
    ext c
    change f (1 ⊗ₜ[R] c) = algebraMap C E c
    simp [f]
  exact AlgEquiv.ofBijective f
    (IsLocalization.bijective (M := M) f.toRingHom hfC)

/-- The generic-fibre equivalence is the natural product map on pure
tensors.  Keeping this computation theorem public avoids unfolding the
localization proof when a later component construction must track a
distinguished integral element. -/
@[simp]
theorem finiteGenericFiberAlgEquiv_tmul
    {R : Type uR} {C : Type uC} {K : Type uK} {E : Type uE}
    [CommRing R] [IsDomain R]
    [CommRing C] [IsDomain C] [Algebra R C] [Module.Finite R C]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field E] [Algebra C E] [IsFractionRing C E]
    [Algebra R E] [IsScalarTower R C E]
    [Algebra K E] [IsScalarTower R K E]
    (x : K) (c : C) :
    finiteGenericFiberAlgEquiv
        (R := R) (C := C) (K := K) (E := E) (x ⊗ₜ[R] c) =
      algebraMap K E x * algebraMap C E c := by
  simp [finiteGenericFiberAlgEquiv, Algebra.smul_def]

end EtaleFundamentalGroups

end
