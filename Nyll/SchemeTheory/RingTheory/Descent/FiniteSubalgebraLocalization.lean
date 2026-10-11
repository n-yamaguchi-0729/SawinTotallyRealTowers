/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Finite subalgebras realizing two localizations

For an integral algebra, finitely many numerators generate a finite subalgebra.
If two localizations are finite, the numerators of their module generators can
be chosen together. The resulting subalgebra has exactly the original two
localizations. This is the finite approximation used near a boundary point.
-/

noncomputable section

namespace SchemeTheory

open scoped TensorProduct

universe u v w w'

/-- Generators of a finite localized module can be chosen as images of a
finite set in the original module, by clearing their individual denominators. -/
theorem exists_finset_span_eq_top_of_isLocalizedModule
    {R : Type u} [CommRing R] (S : Submonoid R)
    (R' : Type v) [CommRing R'] [Algebra R R'] [IsLocalization S R']
    {M : Type w} [AddCommGroup M] [Module R M]
    {M' : Type w'} [AddCommGroup M'] [Module R M']
    [Module R' M'] [IsScalarTower R R' M']
    (f : M →ₗ[R] M') [IsLocalizedModule S f] [Module.Finite R' M'] :
    ∃ t : Finset M, Submodule.span R' (f '' (t : Set M)) = ⊤ := by
  classical
  obtain ⟨t, ht⟩ := Module.Finite.fg_top (R := R') (M := M')
  choose num hnum using fun z : t ↦ IsLocalizedModule.surj S f z.val
  let s : Finset M := t.attach.image fun z ↦ (num z).1
  refine ⟨s, top_unique ?_⟩
  rw [← ht]
  refine Submodule.span_le.mpr fun z hz ↦ ?_
  let q : t := ⟨z, hz⟩
  have hmem : f ((num q).1) ∈ Submodule.span R' (f '' (s : Set M)) := by
    apply Submodule.subset_span
    exact ⟨(num q).1, Finset.mem_image.mpr ⟨q, Finset.mem_attach _ _, rfl⟩, rfl⟩
  have hden : IsUnit (algebraMap R R' (num q).2) :=
    IsLocalization.map_units R' (num q).2
  apply (Submodule.smul_mem_iff_of_isUnit _ hden).mp
  rw [algebraMap_smul]
  exact (hnum q).symm ▸ hmem

section Subalgebra

variable {R : Type u} [CommRing R]
variable {B : Type v} [CommRing B] [Algebra R B]

/-- A subalgebra whose images span after a flat scalar extension realizes
that entire scalar extension. -/
theorem lTensor_subalgebra_bijective_of_span
    (A : Type w) [CommRing A] [Algebra R A] [Module.Flat R A]
    (C : Subalgebra R B)
    (hC : Submodule.span A ((fun b : B ↦ (1 : A) ⊗ₜ[R] b) '' (C : Set B)) = ⊤) :
    Function.Bijective (Algebra.TensorProduct.lTensor (S := A) A C.val) := by
  constructor
  · change Function.Injective (C.val.toLinearMap.lTensor A)
    exact Module.Flat.lTensor_preserves_injective_linearMap C.val.toLinearMap
      Subtype.val_injective
  · apply LinearMap.range_eq_top.mp
    apply top_unique
    rw [← hC]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨b, hb, rfl⟩
    exact ⟨(1 : A) ⊗ₜ[R] (⟨b, hb⟩ : C), rfl⟩

/-- An integral algebra with two finite localizations admits one finite
subalgebra realizing both localizations, through the actual inclusion maps. -/
theorem exists_finite_subalgebra_two_localizations
    [Algebra.IsIntegral R B]
    (S T : Submonoid R)
    (A : Type w) [CommRing A] [Algebra R A] [IsLocalization S A]
    (D : Type w') [CommRing D] [Algebra R D] [IsLocalization T D]
    [Module.Finite A (A ⊗[R] B)] [Module.Finite D (D ⊗[R] B)] :
    ∃ C : Subalgebra R B, Module.Finite R C ∧
      Function.Bijective (Algebra.TensorProduct.lTensor (S := A) A C.val) ∧
      Function.Bijective (Algebra.TensorProduct.lTensor (S := D) D C.val) := by
  classical
  obtain ⟨s, hs⟩ := exists_finset_span_eq_top_of_isLocalizedModule S A
    (TensorProduct.mk R A B 1)
  obtain ⟨t, ht⟩ := exists_finset_span_eq_top_of_isLocalizedModule T D
    (TensorProduct.mk R D B 1)
  let C : Subalgebra R B := Algebra.adjoin R ((s ∪ t : Finset B) : Set B)
  have hfinite : Module.Finite R C := Algebra.finite_adjoin_of_finite_of_isIntegral
    (s ∪ t).finite_toSet (fun b _ ↦ Algebra.IsIntegral.isIntegral b)
  refine ⟨C, hfinite, ?_, ?_⟩
  · let : Module.Flat R A := IsLocalization.flat A S
    apply lTensor_subalgebra_bijective_of_span A C
    apply top_unique
    rw [← hs]
    apply Submodule.span_mono
    rintro _ ⟨b, hb, rfl⟩
    exact ⟨b, Algebra.subset_adjoin (Finset.mem_union_left t hb), rfl⟩
  · let : Module.Flat R D := IsLocalization.flat D T
    apply lTensor_subalgebra_bijective_of_span D C
    apply top_unique
    rw [← ht]
    apply Submodule.span_mono
    rintro _ ⟨b, hb, rfl⟩
    exact ⟨b, Algebra.subset_adjoin (Finset.mem_union_right s hb), rfl⟩

end Subalgebra

end SchemeTheory
