/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Etale.FiniteRadicialSplittingCover
public import Nyll.SchemeTheory.FiniteEtale.Algebra.ProductBaseChangeComparison
public import Nyll.SchemeTheory.Descent.RadicialModelCoaction
public import Nyll.SchemeTheory.FiniteEtale.Algebra.FaithfullyFlatDescent
public import Nyll.SchemeTheory.Descent.AlgebraCoaction
public import Nyll.SchemeTheory.Descent.InvariantScalarExtensionComparison
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.RingHom.Finite
public import Mathlib.RingTheory.Etale.Pi
public import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-!
# Essential surjectivity along finite radicial surjections

The lower spectrum has an actual finite affine étale splitting cover. The
product of its split local models has a concrete scalar-extension comparison
with the given upper algebra. Its transported coaction descends uniquely
along the radicial map. Effective faithfully flat descent then produces a
finite étale invariant algebra over the original ring, and the invariant
comparison recovers the given upper algebra after scalar extension.

No flatness or finite-presentation assumption is imposed on the finite
radicial surjection itself.
-/

@[expose] public noncomputable section

open AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Algebra

private theorem exists_model_of_etale_faithfullyFlat_cover
    {R B : Type u} [CommRing R] [CommRing B]
    (f : R →+* B) (S M A : Type u)
    [CommRing S] [CommRing M] [CommRing A]
    [Algebra R S] [Algebra B M] [Algebra S A]
    [Module.Finite B M] [Etale B M]
    [IsIntegralHom (Spec.map (CommRingCat.ofHom (algebraMap R S)))]
    [UniversallyInjective (Spec.map (CommRingCat.ofHom (algebraMap R S)))]
    [Surjective (Spec.map (CommRingCat.ofHom (algebraMap R S)))]
    (hf : f.FaithfullyFlat) :
    let : Algebra R B := f.toAlgebra;
    let : Algebra R M := Algebra.compHom M f;
    ∀ (_ : IsScalarTower R B M),
    let : Algebra (S ⊗[R] B) (S ⊗[R] M) :=
      TensorProduct.baseChangeAlgebra R S B M;
    let : IsScalarTower S (S ⊗[R] B) (S ⊗[R] M) :=
      TensorProduct.baseChangeAlgebra_isScalarTower R S B M;
    Etale R B →
      ((S ⊗[R] M) ≃ₐ[S ⊗[R] B] (S ⊗[R] B) ⊗[S] A) →
      ∃ (I : Type u) (_ : CommRing I) (_ : Algebra R I),
        Module.Finite R I ∧ Etale R I ∧ Nonempty (S ⊗[R] I ≃ₐ[S] A) := by
  intro hRB hRM hTower hEU hEUTower hBEtale e
  obtain ⟨ρ, hcounit, hcoassoc, hcomparison⟩ :=
    Descent.exists_coaction_of_radicial_model R S B M A e
  obtain ⟨hε, hδ⟩ :=
    Descent.nativeCoactionAxioms_of_pointwise f M ρ hcounit hcoassoc
  let I := FaithfullyFlatDescent.invariants f M ρ
  obtain ⟨hfinite, hEtale⟩ :=
    FaithfullyFlatDescent.invariants_finite_etale f M hf ρ hε hδ
  exact ⟨I, inferInstance, inferInstance, hfinite, hEtale,
    ⟨FaithfullyFlatDescent.invariantsScalarExtensionEquiv
      f S M A hf ρ hε hδ e hcomparison⟩⟩

/-- Every finite étale algebra over a finite radicial surjective algebra is
the scalar extension of an actual finite étale algebra over the lower ring. -/
theorem Etale.exists_finite_model_of_finite_radicial
    {R S A : Type u} [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra S A] [Module.Finite R S]
    [Module.Finite S A] [Etale S A]
    [UniversallyInjective (Spec.map (CommRingCat.ofHom (algebraMap R S)))]
    [Surjective (Spec.map (CommRingCat.ofHom (algebraMap R S)))] :
    ∃ (I : Type u) (_ : CommRing I) (_ : Algebra R I),
      Module.Finite R I ∧ Etale R I ∧ Nonempty (S ⊗[R] I ≃ₐ[S] A) := by
  classical
  obtain ⟨ι, hι, D, hD, hRD, hDEtale, n, hf, _, hfiniteM, hEtaleM, hmodels⟩ :=
    AlgebraicGeometry.Etale.exists_finite_split_cover_of_finite_radicial
      (R := R) (S := S) (A := A)
  let B := ∀ i : ι, D i
  let M := ∀ i : ι, Fin (n i) → D i
  let : Algebra (S ⊗[R] B) (S ⊗[R] M) := TensorProduct.baseChangeAlgebra R S B M
  let : IsScalarTower S (S ⊗[R] B) (S ⊗[R] M) :=
    TensorProduct.baseChangeAlgebra_isScalarTower R S B M
  obtain ⟨e⟩ := TensorProduct.nonempty_product_baseChange_model
    (R := R) (S := S) (A := A) D n (fun i ↦ (hmodels i).some)
  have hf' : (algebraMap R B).FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.mpr hf
  have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  have hdesc := exists_model_of_etale_faithfullyFlat_cover (algebraMap R B) S M A hf'
  have hRM : Algebra.compHom M (algebraMap R B) = (inferInstance : Algebra R M) :=
    Algebra.algebra_ext _ _ (fun r ↦ (IsScalarTower.algebraMap_apply R B M r).symm)
  rw [toAlgebra_algebraMap, hRM] at hdesc
  exact hdesc (inferInstance : IsScalarTower R B M) (inferInstance : Etale R B) e

end Algebra
