/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Nyll.GaloisCohomology.Kummer.Concrete.RootCharacters
import Nyll.GaloisCohomology.Kummer.Concrete.SemilinearConjugation
import Nyll.GaloisCohomology.Kummer.Concrete.SemilinearConjugationTopology

/-!
# Conjugation of absolute Galois automorphisms by a field automorphism

A chosen extension of a field automorphism to its algebraic closure conjugates
base-linear automorphisms to base-linear automorphisms. Root quotients transform
by the same extension; this is the concrete identity underlying Kummer naturality.
-/

namespace KummerTheory

variable {K : Type*} [Field K]

/-- Conjugate an absolute Galois automorphism by the chosen extension of `τ`. -/
noncomputable def absoluteGaloisConjugate (τ : K ≃+* K)
    (σ : Gal(AlgebraicClosure K/K)) : Gal(AlgebraicClosure K/K) :=
  semilinearGaloisConjugate τ
    (IsAlgClosure.equivOfEquiv (AlgebraicClosure K) (AlgebraicClosure K) τ)
    (IsAlgClosure.equivOfEquiv_algebraMap (AlgebraicClosure K) (AlgebraicClosure K) τ) σ

/-- The chosen conjugation is an automorphism of the absolute Galois group. -/
noncomputable def absoluteGaloisConjugateEquiv (τ : K ≃+* K) :
    Gal(AlgebraicClosure K/K) ≃* Gal(AlgebraicClosure K/K) :=
  semilinearGaloisConjugateEquiv τ
    (IsAlgClosure.equivOfEquiv (AlgebraicClosure K) (AlgebraicClosure K) τ)
    (IsAlgClosure.equivOfEquiv_algebraMap (AlgebraicClosure K) (AlgebraicClosure K) τ)

/-- Evaluation of the bundled chosen conjugation. -/
theorem absoluteGaloisConjugateEquiv_apply (τ : K ≃+* K)
    (σ : Gal(AlgebraicClosure K/K)) :
    absoluteGaloisConjugateEquiv τ σ = absoluteGaloisConjugate τ σ := by
  rfl

/-- The chosen conjugation is continuous in the Krull topology. -/
theorem absoluteGaloisConjugateEquiv_continuous (τ : K ≃+* K) :
    Continuous (absoluteGaloisConjugateEquiv τ) :=
  semilinearGaloisConjugateEquiv_continuous τ
    (IsAlgClosure.equivOfEquiv (AlgebraicClosure K) (AlgebraicClosure K) τ)
    (IsAlgClosure.equivOfEquiv_algebraMap (AlgebraicClosure K) (AlgebraicClosure K) τ)

/-- The absolute Galois conjugation, with continuity in both directions. -/
noncomputable def absoluteGaloisConjugateContinuousEquiv (τ : K ≃+* K) :
    Gal(AlgebraicClosure K/K) ≃ₜ* Gal(AlgebraicClosure K/K) :=
  semilinearGaloisConjugateContinuousEquiv τ
    (IsAlgClosure.equivOfEquiv (AlgebraicClosure K) (AlgebraicClosure K) τ)
    (IsAlgClosure.equivOfEquiv_algebraMap (AlgebraicClosure K) (AlgebraicClosure K) τ)

/-- Evaluation of the continuous chosen conjugation. -/
theorem absoluteGaloisConjugateContinuousEquiv_apply (τ : K ≃+* K)
    (σ : Gal(AlgebraicClosure K/K)) :
    absoluteGaloisConjugateContinuousEquiv τ σ = absoluteGaloisConjugate τ σ := by
  rfl

/-- The conjugated automorphism is evaluated by conjugating in the closure. -/
theorem absoluteGaloisConjugate_apply (τ : K ≃+* K)
    (σ : Gal(AlgebraicClosure K/K)) (x : AlgebraicClosure K) :
    absoluteGaloisConjugate τ σ x =
      IsAlgClosure.equivOfEquiv (AlgebraicClosure K) (AlgebraicClosure K) τ
        (σ ((IsAlgClosure.equivOfEquiv (AlgebraicClosure K) (AlgebraicClosure K) τ).symm x)) := by
  rfl

/-- Root quotients commute with semilinear conjugation in the algebraic closure. -/
theorem rootQuotient_absoluteGaloisConjugate (τ : K ≃+* K)
    (β : (AlgebraicClosure K)ˣ) (σ : Gal(AlgebraicClosure K/K)) :
    rootQuotient (K := K)
      (Units.map (IsAlgClosure.equivOfEquiv (AlgebraicClosure K)
        (AlgebraicClosure K) τ).toMonoidHom β) (absoluteGaloisConjugate τ σ) =
      Units.map (IsAlgClosure.equivOfEquiv (AlgebraicClosure K)
        (AlgebraicClosure K) τ).toMonoidHom (rootQuotient (K := K) β σ) := by
  apply Units.ext
  simp only [rootQuotient, AlgEquiv.smul_units_def, Units.val_div_eq_div_val, Units.coe_map]
  change absoluteGaloisConjugate τ σ
      (IsAlgClosure.equivOfEquiv (AlgebraicClosure K) (AlgebraicClosure K)
        τ (β : AlgebraicClosure K)) /
      IsAlgClosure.equivOfEquiv (AlgebraicClosure K) (AlgebraicClosure K)
        τ (β : AlgebraicClosure K) =
    IsAlgClosure.equivOfEquiv (AlgebraicClosure K) (AlgebraicClosure K) τ
      (σ (β : AlgebraicClosure K) / (β : AlgebraicClosure K))
  rw [absoluteGaloisConjugate_apply, RingEquiv.symm_apply_apply, map_div₀]

end KummerTheory
