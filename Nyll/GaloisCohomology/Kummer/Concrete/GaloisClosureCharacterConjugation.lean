/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Kummer.Concrete.GaloisClosureConjugation
import Nyll.GaloisCohomology.Kummer.Concrete.AbsoluteAbelianizationAction
import Nyll.ProCGroups.Abelian.TopologicalAbelianization
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Closure conjugation evaluated by continuous characters

The comparison on topological abelianization identifies the values of a
continuous abelian character after actual and chosen semilinear conjugation.
-/

namespace KummerTheory

open ProCGroups.Abelian

variable {K Ω A : Type*} [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  [CommGroup A] [TopologicalSpace A] [T1Space A]

/-- A continuous abelian character evaluates concrete semilinear conjugation
through the closure comparison as the canonical absolute conjugation. -/
theorem absoluteGaloisClosureEquiv_character_conjugation
    (τ : K ≃+* K) (a : Ω ≃+* Ω)
    (ha : ∀ k : K, a (algebraMap K Ω k) = algebraMap K Ω (τ k))
    (f : Gal(AlgebraicClosure K/K) →ₜ* A) (σ : Gal(Ω/K)) :
    f (absoluteGaloisClosureEquiv K Ω (semilinearGaloisConjugate τ a ha σ)) =
      f (absoluteGaloisConjugate τ (absoluteGaloisClosureEquiv K Ω σ)) := by
  have hconj := galoisClosureTransport_abelianization_conjugation_mk
    (IsAlgClosure.equiv K Ω (AlgebraicClosure K)) τ a ha σ
  rw [TopologicalAbelianization.congr_apply_mk,
    TopologicalAbelianization.congr_apply_mk,
    absoluteGaloisAbelianizationAction_apply_mk] at hconj
  have hvalue := congrArg (TopologicalAbelianization.lift f) hconj
  rw [TopologicalAbelianization.lift_apply_mk,
    TopologicalAbelianization.lift_apply_mk] at hvalue
  exact hvalue

end KummerTheory
