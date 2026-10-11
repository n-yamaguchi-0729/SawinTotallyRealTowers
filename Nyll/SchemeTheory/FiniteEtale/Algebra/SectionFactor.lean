/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.FiniteEtale.Algebra.EtaleSection
public import Nyll.SchemeTheory.FiniteEtale.Algebra.IdempotentFactor
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Splitting off an étale section

An algebra section of a finite étale algebra cuts out an idempotent factor
isomorphic to the base. The complementary factor is an actual quotient by
the complementary idempotent, and remains finite étale. The product
isomorphism has the prescribed section as its first coordinate.
-/

@[expose] public noncomputable section

open AlgebraicGeometry

universe u

namespace Algebra.Etale

/-- A section splits a finite étale algebra as the base times an actual
finite étale complementary factor, with the specified first projection. -/
theorem exists_prod_of_section
    {R C : Type u} [CommRing R] [CommRing C] [Algebra R C]
    [Module.Finite R C] [Algebra.Etale R C] (σ : C →ₐ[R] R) :
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra R D),
      Module.Finite R D ∧ Algebra.Etale R D ∧
      ∃ E : C ≃ₐ[R] R × D, ∀ c : C, (E c).1 = σ c := by
  have hσ : Function.Surjective σ := fun r ↦
    ⟨algebraMap R C r, σ.commutes r⟩
  obtain ⟨e, he, hker⟩ :=
    (isOpenImmersion_SpecMap_iff_of_surjective (CommRingCat.ofHom σ.toRingHom) hσ).mp
      (σ.isOpenImmersion_SpecMap_of_surjective_of_etale hσ)
  let D := C ⧸ Ideal.span {1 - e}
  have hDfinite : Module.Finite R D :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ R (Ideal.span {1 - e})).toLinearMap
      Ideal.Quotient.mk_surjective
  have hDetale : Algebra.Etale R D :=
    Algebra.Etale.quotient_one_sub_of_isIdempotentElem e he
  have hsum : e + (1 - e) = 1 := by rw [add_comm, sub_add_cancel]
  have hmul : e * (1 - e) = 0 := by
    rw [mul_sub, mul_one, he.eq, sub_self]
  let E₁ : C ≃ₐ[R] (C ⧸ Ideal.span {e}) × D :=
    AlgEquiv.prodQuotientOfIsIdempotentElem (R := R) he he.one_sub hsum hmul
  let E₂ : (C ⧸ Ideal.span {e}) ≃ₐ[R] R :=
    (Ideal.quotientEquivAlgOfEq R hker.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective hσ)
  let E : C ≃ₐ[R] R × D := E₁.trans (AlgEquiv.prodCongr E₂ AlgEquiv.refl)
  refine ⟨D, inferInstance, inferInstance, hDfinite, hDetale, E, ?_⟩
  intro c
  change E₂ (Ideal.Quotient.mk (Ideal.span {e}) c) = σ c
  rfl

end Algebra.Etale
