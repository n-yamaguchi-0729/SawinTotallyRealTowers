/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Kummer.Concrete.GaloisClosureTransport
import Nyll.GaloisCohomology.Kummer.Concrete.SemilinearClosureTransport
import Nyll.GaloisCohomology.Kummer.Concrete.SemilinearConjugation
import Nyll.GaloisCohomology.Kummer.Concrete.SemilinearConjugationTopology
import Nyll.GaloisCohomology.Kummer.Concrete.AbsoluteAbelianizationAction
import Nyll.GaloisCohomology.Kummer.Concrete.AbsoluteConjugation
import Nyll.ProCGroups.Abelian.TopologicalAbelianization
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Comparing conjugation with the canonical absolute Galois action

Changing the algebraic closure intertwines concrete semilinear conjugation
with the canonical action on topological abelianization. Both the closure
equivalence and the comparison are constructed from the given field data.
-/

namespace KummerTheory

open ProCGroups.Abelian

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]

/-- On quotient representatives, transport of any actual lift agrees with
the canonical action defined using the selected algebraic closure. -/
theorem galoisClosureTransport_abelianization_conjugation_mk
    (e : Ω ≃ₐ[K] AlgebraicClosure K) (τ : K ≃+* K) (a : Ω ≃+* Ω)
    (ha : ∀ k : K, a (algebraMap K Ω k) = algebraMap K Ω (τ k))
    (σ : Gal(Ω/K)) :
    TopologicalAbelianization.congr (galoisClosureTransport e)
        (TopologicalAbelianization.mk Gal(Ω/K) (semilinearGaloisConjugate τ a ha σ)) =
      absoluteGaloisAbelianizationAction τ
        (TopologicalAbelianization.congr (galoisClosureTransport e)
          (TopologicalAbelianization.mk Gal(Ω/K) σ)) := by
  rw [TopologicalAbelianization.congr_apply_mk, TopologicalAbelianization.congr_apply_mk,
    absoluteGaloisAbelianizationAction_apply_mk]
  change TopologicalAbelianization.mk Gal(AlgebraicClosure K/K)
      (AlgEquiv.autCongr e (semilinearGaloisConjugate τ a ha σ)) = _
  rw [autCongr_semilinearGaloisConjugate]
  unfold absoluteGaloisConjugate
  exact (map_semilinearGaloisConjugate_eq
    (TopologicalAbelianization.mk Gal(AlgebraicClosure K/K)) τ
    (transportSemilinearEquiv e a)
    (IsAlgClosure.equivOfEquiv (AlgebraicClosure K) (AlgebraicClosure K) τ)
    (transportSemilinearEquiv_algebraMap τ e a ha)
    (IsAlgClosure.equivOfEquiv_algebraMap (AlgebraicClosure K) (AlgebraicClosure K) τ)
    (AlgEquiv.autCongr e σ)).symm

variable (K Ω) [IsAlgClosure K Ω]

/-- The relative Galois group of any algebraic closure is continuously
isomorphic to the absolute Galois group defined using `AlgebraicClosure`. -/
noncomputable def absoluteGaloisClosureEquiv :
    Gal(Ω/K) ≃ₜ* Gal(AlgebraicClosure K/K) :=
  galoisClosureTransport (IsAlgClosure.equiv K Ω (AlgebraicClosure K))

/-- The corresponding continuous comparison on topological abelianization. -/
noncomputable def absoluteGaloisClosureAbelianizationEquiv :
    _root_.TopologicalAbelianization Gal(Ω/K) ≃ₜ*
      _root_.TopologicalAbelianization Gal(AlgebraicClosure K/K) :=
  TopologicalAbelianization.congr (absoluteGaloisClosureEquiv K Ω)

/-- The closure comparison intertwines the actual semilinear action with
the canonical action on the abelianized absolute Galois group. -/
theorem absoluteGaloisClosureAbelianizationEquiv_conjugation
    (τ : K ≃+* K) (a : Ω ≃+* Ω)
    (ha : ∀ k : K, a (algebraMap K Ω k) = algebraMap K Ω (τ k))
    (x : _root_.TopologicalAbelianization Gal(Ω/K)) :
    absoluteGaloisClosureAbelianizationEquiv K Ω
        (TopologicalAbelianization.congr (semilinearGaloisConjugateContinuousEquiv τ a ha) x) =
      absoluteGaloisAbelianizationAction τ (absoluteGaloisClosureAbelianizationEquiv K Ω x) := by
  obtain ⟨σ, rfl⟩ := TopologicalAbelianization.surjective_mk Gal(Ω/K) x
  rw [TopologicalAbelianization.congr_apply_mk,
    semilinearGaloisConjugateContinuousEquiv_apply]
  exact galoisClosureTransport_abelianization_conjugation_mk
    (IsAlgClosure.equiv K Ω (AlgebraicClosure K)) τ a ha σ

end KummerTheory
