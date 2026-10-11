/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Fraction fields from generic-fibre equivalences

An equivalence between the generic fibre `K ⊗[R] C` and a field `E`
canonically embeds `C` in `E`.  When `C` is a domain, this embedding makes
`E` a fraction field of `C`.
-/

noncomputable section

namespace EtaleFundamentalGroups

open scoped TensorProduct

universe uR uC uK uE

/-- The canonical map from the right-hand algebra into a field identified
with its generic fibre. -/
noncomputable def genericFiberRightAlgHom
    {R : Type uR} {C : Type uC} {K : Type uK} {E : Type uE}
    [CommRing R] [CommRing C] [Algebra R C]
    [Field K] [Algebra R K]
    [Field E] [Algebra K E] [Algebra R E] [IsScalarTower R K E]
    (e : (K ⊗[R] C) ≃ₐ[K] E) :
    C →ₐ[R] E :=
  (e.toAlgHom.restrictScalars R).comp Algebra.TensorProduct.includeRight

@[simp]
theorem genericFiberRightAlgHom_apply
    {R : Type uR} {C : Type uC} {K : Type uK} {E : Type uE}
    [CommRing R] [CommRing C] [Algebra R C]
    [Field K] [Algebra R K]
    [Field E] [Algebra K E] [Algebra R E] [IsScalarTower R K E]
    (e : (K ⊗[R] C) ≃ₐ[K] E) (c : C) :
    genericFiberRightAlgHom e c = e (1 ⊗ₜ[R] c) := by
  rfl

/-- A field identified with the generic fibre of a domain is a fraction
field of that domain, for the canonical right-factor embedding.

No finiteness assumption is needed: the existence of the field-valued
generic-fibre equivalence already forces the required localization to be a
field. -/
theorem isFractionRing_of_genericFiberAlgEquiv
    {R : Type uR} {C : Type uC} {K : Type uK} {E : Type uE}
    [CommRing R] [CommRing C] [IsDomain C] [Algebra R C]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field E] [Algebra K E] [Algebra R E] [IsScalarTower R K E]
    (e : (K ⊗[R] C) ≃ₐ[K] E) :
    letI : Algebra C E :=
      (genericFiberRightAlgHom e).toRingHom.toAlgebra
    IsFractionRing C E := by
  let M : Submonoid C :=
    Algebra.algebraMapSubmonoid C (nonZeroDivisors R)
  let T := K ⊗[R] C
  let f : C →ₐ[R] E := genericFiberRightAlgHom e
  let : Algebra C E := f.toRingHom.toAlgebra
  have hRE : Function.Injective (algebraMap R E) := by
    rw [IsScalarTower.algebraMap_eq R K E]
    exact (algebraMap K E).injective.comp
      (FaithfulSMul.algebraMap_injective R K)
  let : IsDomain R := hRE.isDomain _
  have hRC : Function.Injective (algebraMap R C) := by
    intro x y hxy
    apply hRE
    calc
      algebraMap R E x = f (algebraMap R C x) := (f.commutes x).symm
      _ = f (algebraMap R C y) := by rw [hxy]
      _ = algebraMap R E y := f.commutes y
  have hM : M ≤ nonZeroDivisors C := by
    rintro _ ⟨r, hr, rfl⟩
    have hr0 : r ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hr
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro h
    exact hr0 (hRC (by simpa using h))
  let : Algebra C T := Algebra.TensorProduct.rightAlgebra
  let : IsLocalization M T :=
    IsLocalization.tensorRight (R := R) (S := C) (A := K)
      (nonZeroDivisors R)
  let eC : T ≃ₐ[C] E :=
    { e with
      commutes' := fun c ↦ rfl }
  let : IsLocalization M E :=
    IsLocalization.isLocalization_of_algEquiv M eC
  let : FaithfulSMul C E :=
    (faithfulSMul_iff_algebraMap_injective C E).mpr
      (IsLocalization.injective E hM)
  apply IsFractionRing.of_field
  intro z
  obtain ⟨⟨x, s⟩, hz⟩ := IsLocalization.surj M z
  refine ⟨x, s, (eq_div_iff ?_).2 ?_⟩
  · exact (IsLocalization.map_units E s).ne_zero
  · simpa using hz

end EtaleFundamentalGroups

end
