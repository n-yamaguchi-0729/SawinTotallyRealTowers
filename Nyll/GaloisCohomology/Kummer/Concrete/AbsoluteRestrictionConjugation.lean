/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Topology.AbsoluteGaloisLiftComparison
import Nyll.GaloisCohomology.Kummer.Concrete.AbsoluteConjugation

/-!
# Comparing restriction and semilinear absolute Galois conjugation

Restriction along the inverse field automorphism and conjugation by a chosen
extension of the field automorphism agree on all commutative characters.
-/

namespace KummerTheory

variable {K A : Type*} [Field K] [CommGroup A] [TopologicalSpace A]

/-- Character pullback along the inverse field automorphism is the existing
semilinear conjugation action, independently of closure-lift choices. -/
theorem character_map_symm_eq_absoluteGaloisConjugate
    (τ : K ≃+* K) (χ : Gal(AlgebraicClosure K/K) →ₜ* A)
    (σ : Gal(AlgebraicClosure K/K)) :
    χ (Field.absoluteGaloisGroup.map τ.symm.toRingHom σ) =
      χ (absoluteGaloisConjugate τ σ) := by
  let e := IsAlgClosure.equivOfEquiv (AlgebraicClosure K) (AlgebraicClosure K) τ
  have he (x : K) : e (algebraMap K (AlgebraicClosure K) x) =
      algebraMap K (AlgebraicClosure K) (τ x) :=
    IsAlgClosure.equivOfEquiv_algebraMap (AlgebraicClosure K) (AlgebraicClosure K) τ x
  apply Field.absoluteGaloisGroup.character_map_apply_of_lift
    τ.symm.toRingHom e.symm.toRingHom ?_ σ (absoluteGaloisConjugate τ σ) ?_ χ
  · intro x
    apply e.injective
    exact (e.apply_symm_apply _).trans
      ((he (τ.symm x)).trans
        (congrArg (algebraMap K (AlgebraicClosure K)) (τ.apply_symm_apply x))).symm
  · intro x
    change e.symm (e (σ (e.symm x))) = σ (e.symm x)
    exact e.symm_apply_apply _

end KummerTheory
