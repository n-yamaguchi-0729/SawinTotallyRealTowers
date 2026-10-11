/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import Nyll.GaloisCohomology.Kummer.Concrete.GaloisClosureTransport
import Nyll.GaloisCohomology.Kummer.Concrete.SemilinearClosureTransport
import Nyll.GaloisCohomology.Kummer.Concrete.SemilinearConjugation
import Nyll.GaloisCohomology.Kummer.Concrete.SemilinearConjugationTopology
import Nyll.GaloisCohomology.Kummer.Concrete.SeparableClosureConjugation
import Nyll.GaloisCohomology.Kummer.Concrete.AbsoluteConjugation
import Nyll.GaloisCohomology.Kummer.Concrete.AbsoluteAbelianizationAction
import Nyll.ValuedFieldTheory.Valuation.Completion.SeparableClosureAutTopology
import Nyll.ProCGroups.Abelian.TopologicalAbelianizationFunctoriality

/-!
# Absolute Galois abelianization using a separable closure

The comparison factors through the canonical separable closure and restriction
from the algebraic closure. Independence of the chosen semilinear lift proves
compatibility with the actual absolute action, including imperfect fields.
-/

namespace KummerTheory
open ProCGroups.Abelian
variable (K Ω : Type*) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

/-- A separable closure gives the same topological absolute Galois group. -/
noncomputable def separableAbsoluteGaloisClosureEquiv :
    Gal(Ω/K) ≃ₜ* Gal(AlgebraicClosure K/K) :=
  (galoisClosureTransport (IsSepClosure.equiv K Ω (SeparableClosure K))).trans
    (ValuationTheory.Completion.separableClosureAutContinuousEquiv K).symm

/-- The corresponding comparison on actual topological abelianizations. -/
noncomputable def separableAbsoluteGaloisClosureAbelianizationEquiv :
    _root_.TopologicalAbelianization Gal(Ω/K) ≃ₜ*
      _root_.TopologicalAbelianization Gal(AlgebraicClosure K/K) :=
  TopologicalAbelianization.congr (separableAbsoluteGaloisClosureEquiv K Ω)

/-- Comparison through a separable closure respects semilinear conjugation. -/
theorem separableAbsoluteGaloisClosureAbelianizationEquiv_conjugation
    (τ : K ≃+* K) (a : Ω ≃+* Ω)
    (ha : ∀ k : K, a (algebraMap K Ω k) = algebraMap K Ω (τ k))
    (x : _root_.TopologicalAbelianization Gal(Ω/K)) :
    separableAbsoluteGaloisClosureAbelianizationEquiv K Ω
        (TopologicalAbelianization.congr (semilinearGaloisConjugateContinuousEquiv τ a ha) x) =
      absoluteGaloisAbelianizationAction τ
        (separableAbsoluteGaloisClosureAbelianizationEquiv K Ω x) := by
  obtain ⟨σ, rfl⟩ := TopologicalAbelianization.surjective_mk Gal(Ω/K) x
  rw [TopologicalAbelianization.congr_apply_mk,
    semilinearGaloisConjugateContinuousEquiv_apply]
  change TopologicalAbelianization.congr (separableAbsoluteGaloisClosureEquiv K Ω)
    (TopologicalAbelianization.mk Gal(Ω/K) (semilinearGaloisConjugate τ a ha σ)) = _
  rw [TopologicalAbelianization.congr_apply_mk]
  change _ = absoluteGaloisAbelianizationAction τ
    (TopologicalAbelianization.congr (separableAbsoluteGaloisClosureEquiv K Ω)
      (TopologicalAbelianization.mk Gal(Ω/K) σ))
  rw [TopologicalAbelianization.congr_apply_mk, absoluteGaloisAbelianizationAction_apply_mk]
  let e := IsSepClosure.equiv K Ω (SeparableClosure K)
  let r := ValuationTheory.Completion.separableClosureAutContinuousEquiv K
  let f : Gal(SeparableClosure K/K) →*
      _root_.TopologicalAbelianization Gal(AlgebraicClosure K/K) :=
    (TopologicalAbelianization.mk Gal(AlgebraicClosure K/K)).comp r.symm.toMulEquiv.toMonoidHom
  change f (AlgEquiv.autCongr e (semilinearGaloisConjugate τ a ha σ)) =
    TopologicalAbelianization.mk Gal(AlgebraicClosure K/K)
      (absoluteGaloisConjugate τ (r.symm (AlgEquiv.autCongr e σ)))
  rw [autCongr_semilinearGaloisConjugate]
  rw [map_semilinearGaloisConjugate_eq f τ (separableClosureEquivOfEquiv τ)
    (transportSemilinearEquiv e a) (separableClosureEquivOfEquiv_algebraMap τ)
    (transportSemilinearEquiv_algebraMap τ e a ha)]
  apply congrArg (TopologicalAbelianization.mk Gal(AlgebraicClosure K/K))
  apply r.injective
  change r (r.symm (semilinearGaloisConjugate τ (separableClosureEquivOfEquiv τ)
    (separableClosureEquivOfEquiv_algebraMap τ) (AlgEquiv.autCongr e σ))) = _
  rw [ContinuousMulEquiv.apply_symm_apply]
  change _ = ValuationTheory.Completion.separableClosureAutEquiv K
    (absoluteGaloisConjugate τ (r.symm (AlgEquiv.autCongr e σ)))
  rw [separableClosureAutEquiv_absoluteGaloisConjugate]
  exact congrArg (semilinearGaloisConjugate τ (separableClosureEquivOfEquiv τ)
    (separableClosureEquivOfEquiv_algebraMap τ)) (r.apply_symm_apply _).symm

end KummerTheory
