/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Kummer.Concrete.SemilinearConjugation
import Mathlib.Algebra.Algebra.Tower
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Normal.Defs

/-!
# Restriction of semilinear Galois conjugation

Conjugation by the same ambient field automorphism commutes with restriction
of scalars. For two field towers, restriction to a normal field supplies the
lower automorphism and its actual compatibility with the upper automorphism.
An ambient lift then inherits this lower semilinearity through the tower.
-/

namespace KummerTheory

section ScalarTower

variable {K L Ω : Type*} [Field K] [Field L] [Field Ω]
  [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]

/-- Conjugation by one ambient automorphism commutes with restriction of
scalars between its two fields of semilinearity. -/
theorem semilinearGaloisConjugate_restrictScalars
    (τK : K ≃+* K) (τL : L ≃+* L) (a : Ω ≃+* Ω)
    (haK : ∀ x : K, a (algebraMap K Ω x) = algebraMap K Ω (τK x))
    (haL : ∀ x : L, a (algebraMap L Ω x) = algebraMap L Ω (τL x))
    (σ : Gal(Ω/L)) :
    (semilinearGaloisConjugate τL a haL σ).restrictScalars K =
      semilinearGaloisConjugate τK a haK (σ.restrictScalars K) := by
  apply AlgEquiv.ext
  intro x
  change a (σ (a.symm x)) = a (σ (a.symm x))
  rfl

end ScalarTower

section NormalRestriction

variable (F K L E : Type*) [Field F] [Field K] [Field L] [Field E]
  [Algebra F K] [Algebra F L] [Algebra F E] [Algebra K E] [Algebra L E]
  [IsScalarTower F K E] [IsScalarTower F L E] [Normal F K]

/-- The actual restriction from `Gal(E/L)` to `Gal(K/F)` preserves evaluation
on the embedded normal field. No compositum or surjectivity assumption is needed. -/
theorem restrictRestrictAlgEquivMapHom_algebraMap
    (τ : Gal(E/L)) (x : K) :
    τ (algebraMap K E x) = algebraMap K E
      (IntermediateField.restrictRestrictAlgEquivMapHom F K L E τ x) :=
  ((MulSemiringAction.toAlgAut Gal(E/L) F E τ).restrictNormal_commutes K x).symm

variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra E Ω]
  [IsScalarTower K E Ω]

/-- A lift of the upper automorphism lies over its actual restriction to the
normal field. The lower compatibility is generated from restriction and the
scalar tower, rather than supplied as a comparison hypothesis. -/
theorem semilinear_restrictRestrictAlgEquivMapHom_algebraMap
    (τ : Gal(E/L)) (a : Ω ≃+* Ω)
    (ha : ∀ x : E, a (algebraMap E Ω x) = algebraMap E Ω (τ x))
    (x : K) :
    a (algebraMap K Ω x) = algebraMap K Ω
      (IntermediateField.restrictRestrictAlgEquivMapHom F K L E τ x) := by
  rw [IsScalarTower.algebraMap_apply K E Ω x, ha,
    restrictRestrictAlgEquivMapHom_algebraMap F K L E τ x,
    ← IsScalarTower.algebraMap_apply K E Ω]

end NormalRestriction

end KummerTheory
