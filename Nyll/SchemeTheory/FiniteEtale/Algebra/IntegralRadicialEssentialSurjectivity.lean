/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.FiniteEtale.AffineUniversalHomeomorphismModel
public import Nyll.SchemeTheory.FiniteEtale.Algebra.FiniteRadicialEssentialSurjectivity
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Finite étale models over affine universal homeomorphisms

The upper algebra first descends to an actual finite intermediate universal
homeomorphism. Finite radicial descent then constructs its model over the
original ring. The tensor-product associator supplies the comparison with
the original upper algebra.
-/

@[expose] public noncomputable section

open AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Algebra

/-- A finite étale algebra over any affine universal homeomorphism is the
scalar extension of a finite étale algebra over the original ring. -/
theorem Etale.exists_finite_model_of_universalHomeomorphism
    (R S A : Type u) [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra.IsIntegral R S] [Algebra S A]
    [Module.Finite S A] [Etale S A]
    [UniversallyInjective (Spec.map (CommRingCat.ofHom (algebraMap R S)))]
    [Surjective (Spec.map (CommRingCat.ofHom (algebraMap R S)))] :
    ∃ (I : Type u) (_ : CommRing I) (_ : Algebra R I),
      Module.Finite R I ∧ Etale R I ∧ Nonempty (S ⊗[R] I ≃ₐ[S] A) := by
  obtain ⟨S₀, A₀, hA₀, hS₀A₀, hfiniteS₀, hradicialS₀, hsurjectiveS₀,
      hfiniteA₀, hEtaleA₀, ⟨e⟩⟩ :=
    AlgebraicGeometry.FiniteEtale.exists_finite_subalgebra_model_of_universalHomeomorphism
      R S A
  obtain ⟨I, hI, hRI, hfiniteI, hEtaleI, ⟨e₀⟩⟩ :=
    Etale.exists_finite_model_of_finite_radicial (R := R) (S := S₀) (A := A₀)
  refine ⟨I, hI, hRI, hfiniteI, hEtaleI, ⟨?_⟩⟩
  exact (TensorProduct.cancelBaseChange R S₀ S S I).symm.trans
    ((TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S) e₀).trans e.symm)

end Algebra
