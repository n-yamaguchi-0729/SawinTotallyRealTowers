/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Kummer.Concrete.FixedSubgroupCharacterDescent
import Nyll.GaloisCohomology.Kummer.Concrete.AbsoluteH1TrivialCharacter
import Nyll.GaloisCohomology.Kummer.Concrete.SemilinearRestriction
import Nyll.GaloisCohomology.Kummer.Concrete.GaloisClosureCharacterConjugation
import Mathlib.Algebra.Algebra.Tower

/-!
# The action on a descended character

An invariant character of a finite normal intermediate field descends across
a coprime degree. If the lower automorphism acts trivially on H¹, every lift
to that intermediate field fixes this character. The proof constructs one
ambient lift and uses its actual compatibility with both fields.
-/

namespace KummerTheory

variable {K Ω : Type*} [Field K] [Field Ω]
  [Algebra K Ω] [IsAlgClosure K Ω]
  (E : IntermediateField K Ω) [FiniteDimensional K E]

attribute [local instance] closureOverIntermediate

/-- Restriction along the same ambient lift transfers invariance of an actual
extension character to its character on the intermediate field. -/
private theorem invariant_of_semilinear_extension
    {A : Type*} [CommGroup A] [TopologicalSpace A] [T1Space A]
    (f : Gal(AlgebraicClosure E/E) →ₜ* A) (ψ : Gal(Ω/K) →ₜ* A)
    (hψ : ∀ σ : E.fixingSubgroup, ψ (σ : Gal(Ω/K)) =
      f (absoluteGaloisClosureEquiv E Ω (fixingSubgroupContinuousEquiv E σ)))
    (τ : K ≃+* K) (υ : E ≃+* E) (a : Ω ≃+* Ω)
    (haK : ∀ x : K, a (algebraMap K Ω x) = algebraMap K Ω (τ x))
    (haE : ∀ x : E, a (algebraMap E Ω x) = algebraMap E Ω (υ x))
    (hψinv : ∀ ρ : Gal(Ω/K), ψ (semilinearGaloisConjugate τ a haK ρ) = ψ ρ)
    (σ : Gal(AlgebraicClosure E/E)) : f (absoluteGaloisConjugate υ σ) = f σ := by
  let e : Gal(Ω/E) ≃ₜ* Gal(AlgebraicClosure E/E) := absoluteGaloisClosureEquiv E Ω
  have hrestriction (ρ : Gal(Ω/E)) : ψ (ρ.restrictScalars K) = f (e ρ) := by
    have h := hψ (E.fixingSubgroupEquiv.symm ρ)
    have hscalar : (E.fixingSubgroupEquiv.symm ρ : Gal(Ω/K)) =
        ρ.restrictScalars K := by
      apply AlgEquiv.ext
      intro x
      rfl
    rw [fixingSubgroupContinuousEquiv_apply, MulEquiv.apply_symm_apply, hscalar] at h
    exact h
  obtain ⟨ρ, rfl⟩ := e.surjective σ
  have hrelative : f (e (semilinearGaloisConjugate υ a haE ρ)) = f (e ρ) := by
    rw [← hrestriction, semilinearGaloisConjugate_restrictScalars
      τ υ a haK haE, ← hrestriction]
    exact hψinv (ρ.restrictScalars K)
  exact (absoluteGaloisClosureEquiv_character_conjugation υ a haE f ρ).symm.trans hrelative

variable {F : Type*} [Field F] [Algebra F K] [CharZero K] [Normal K E]

/-- Trivial action on the lower field's H¹ fixes an upper invariant character
whose modulus is coprime to the intermediate degree. The extension character
and both closure actions are constructed from the given field data. -/
theorem absoluteCharacter_invariant_of_trivial_lowerH1Action
    (n : ℕ) (hdegree : (Module.finrank K E).Coprime n)
    (f : Gal(AlgebraicClosure E/E) →ₜ* Multiplicative (ZMod n))
    (hinv : ∀ (δ : Gal(E/K)) (σ : Gal(AlgebraicClosure E/E)),
      f (absoluteGaloisConjugate δ.toRingEquiv σ) = f σ)
    (τ : Gal(K/F)) (υ : E ≃+* E)
    (hυ : ∀ x : K, υ (algebraMap K E x) = algebraMap K E (τ x))
    (hτ : relativeGaloisH1Action (n := n) F K τ = 1)
    (σ : Gal(AlgebraicClosure E/E)) :
    f (absoluteGaloisConjugate υ σ) = f σ := by
  obtain ⟨ψ, hψ⟩ := exists_character_extension_of_coprime_finrank E n hdegree f hinv
  let a : Ω ≃+* Ω := IsAlgClosure.equivOfEquiv Ω Ω υ
  have haE : ∀ x : E, a (algebraMap E Ω x) = algebraMap E Ω (υ x) :=
    IsAlgClosure.equivOfEquiv_algebraMap Ω Ω υ
  have haK (x : K) : a (algebraMap K Ω x) = algebraMap K Ω (τ x) := by
    rw [IsScalarTower.algebraMap_apply K E Ω x, haE, hυ,
      ← IsScalarTower.algebraMap_apply K E Ω]
  exact invariant_of_semilinear_extension E f ψ hψ τ.toRingEquiv υ a haK haE
    (semilinearCharacter_invariant_of_relativeH1Action_eq_one τ hτ a haK ψ) σ

end KummerTheory
