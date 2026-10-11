/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Ideal.IdempotentFG
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Étale sections over a quotient base

An algebra map from an étale algebra to a quotient of the base factors
canonically through reduction by the extended ideal. The resulting map is
surjective and induces an open immersion on spectra. Thus it supplies an
actual finite open factor of the quotient fiber.
-/

@[expose] public section

open AlgebraicGeometry

universe u v

namespace AlgHom

/-- A surjective map between étale algebras induces an open immersion.
Its kernel is a finitely generated idempotent ideal. -/
theorem isOpenImmersion_SpecMap_of_surjective_of_etale
    {R : Type v} {A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra.Etale R A] [Algebra.Etale R B]
    (f : A →ₐ[R] B) (hf : Function.Surjective f) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom)) := by
  let : Algebra A B := f.toAlgebra
  let : IsScalarTower R A B := .of_algebraMap_eq' f.comp_algebraMap.symm
  have hfe : Algebra.FormallyEtale A B :=
    Algebra.FormallyEtale.of_restrictScalars (R := R)
  have hker : IsIdempotentElem (RingHom.ker f.toRingHom) :=
    (Algebra.FormallyEtale.iff_of_surjective (R := A) (S := B)
      (show Function.Surjective (algebraMap A B) from hf)).mp hfe
  exact (isOpenImmersion_SpecMap_iff_of_surjective
    (CommRingCat.ofHom f.toRingHom) hf).mpr
      ((Ideal.isIdempotentElem_iff_of_fg _
        (Algebra.FinitePresentation.ker_fG_of_surjective f hf)).mp hker)

section QuotientSection

variable {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B]
    (I : Ideal R) (σ : B →ₐ[R] R ⧸ I)

lemma extendedIdeal_le_ker_quotientSection :
    I.map (algebraMap R B) ≤ RingHom.ker σ.toRingHom := by
  rw [Ideal.map_le_iff_le_comap]
  intro r hr
  change σ (algebraMap R B r) = 0
  rw [σ.commutes]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hr

/-- The map over the quotient base induced by an algebra map to that quotient. -/
def quotientSection : B ⧸ I.map (algebraMap R B) →ₐ[R ⧸ I] R ⧸ I :=
  (Ideal.Quotient.liftₐ (I.map (algebraMap R B)) σ
    (extendedIdeal_le_ker_quotientSection I σ)).extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective

@[simp]
theorem quotientSection_mk (b : B) :
    quotientSection I σ (Ideal.Quotient.mk (I.map (algebraMap R B)) b) = σ b :=
  rfl

/-- A section to the quotient base is surjective because it fixes base scalars. -/
theorem quotientSection_surjective : Function.Surjective (quotientSection I σ) := by
  intro x
  exact ⟨algebraMap (R ⧸ I) (B ⧸ I.map (algebraMap R B)) x,
    (quotientSection I σ).commutes x⟩

end QuotientSection

/-- A section of an étale algebra over a quotient base defines an open immersion
into the quotient fiber. Its source is the base itself, hence is finite over it. -/
theorem isOpenImmersion_SpecMap_quotientSection
    {R B : Type u} [CommRing R] [CommRing B] [Algebra R B] [Algebra.Etale R B]
    (I : Ideal R) (σ : B →ₐ[R] R ⧸ I) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (quotientSection I σ).toRingHom)) := by
  let : Algebra.Etale (R ⧸ I) (B ⧸ I.map (algebraMap R B)) :=
    Algebra.Etale.of_equiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).symm
  exact (quotientSection I σ).isOpenImmersion_SpecMap_of_surjective_of_etale
    (quotientSection_surjective I σ)

end AlgHom
