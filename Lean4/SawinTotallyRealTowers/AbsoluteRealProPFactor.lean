/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.AbsoluteRealKernelField
import SawinTotallyRealTowers.AbsoluteRealProPRestriction
import SawinTotallyRealTowers.FiniteRealPExtension
import SawinTotallyRealTowers.MaximalRealProPOutside
import SawinTotallyRealTowers.RamificationSupport
import SawinTotallyRealTowers.RealCompositum
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.AbsoluteDiscreteKernelField
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.AbsoluteMuPTopRep
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FinitePlaceH2Localization
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FinitePlaceUnramifiedH1
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FinitePlaceInertiaFixedUnramified
import ClassFieldTheory.AlgebraicNumberTheory.Completion.ChosenLocalization
import ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.CompletionToIdeal
import ClassFieldTheory.AlgebraicNumberTheory.NumberField.FiniteUnramifiedTower
import ValuedFieldTheory.Ramification.GaloisValuation.AbsoluteGalois.InfiniteGaloisCorrespondence
import ProCGroups.Topologies.QuotientMaps
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.Topology.Algebra.ContinuousMonoidHom

set_option autoImplicit false

/-!
# Factoring representations through the maximal real pro-p compositum

A discrete p-group representation killing finite inertia outside the chosen
support and the real Artin value of negative one has an actual finite Galois
kernel field satisfying the defining local conditions. Its inclusion in the
constructed compositum gives a continuous factorization through restriction.
The target need not be finite, and the argument does not require p to be odd.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTower.Sawin

open ClassFieldTower.Martinet.Shafarevich

-- Keep the algebraic-closure and intermediate-field scalar structures
-- generic until the two local comparisons have been proved.
section KernelLocalization

private local instance kernelLocalizationGalois
    (F : Type) [Field F] [NumberField F]
    {Q : Type*} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
    (s : Field.absoluteGaloisGroup F →ₜ* Q) :
    IsGalois F (absoluteDiscreteKernelField F s) :=
  absoluteDiscreteKernelField_isGalois F s

private theorem discreteKernel_chosenUnramified
    (F : Type) [Field F] [NumberField F]
    {Q : Type*} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
    (s : Field.absoluteGaloisGroup F →ₜ* Q) (v : HeightOneSpectrum (𝓞 F))
    (hs : ∀ σ : finitePlaceAbsoluteInertiaSubgroup F v,
      s (finitePlaceAbsoluteDecompositionInclusion F v
        (finitePlaceAbsoluteInertiaInclusion F v σ)) = 1) :
    ChosenFinitePlaceIsUnramified (K := F) (L := absoluteDiscreteKernelField F s) v := by
  apply chosenFinitePlaceIsUnramified_of_absoluteInertiaFixes F
    (absoluteDiscreteKernelField F s) v
  intro σ x
  have hFixed : (σ.1.1 : Gal(AlgebraicClosure F/F)) ∈
      (absoluteDiscreteKernelField F s).fixingSubgroup := by
    rw [absoluteDiscreteKernelField_fixingSubgroup]
    exact hs σ
  exact hFixed x

end KernelLocalization

private theorem discreteKernel_eq_one_of_fixes
    (F : Type) [Field F] [NumberField F]
    {Q : Type*} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
    (s : Field.absoluteGaloisGroup F →ₜ* Q) (σ : Field.absoluteGaloisGroup F)
    (hFix : ∀ x : absoluteDiscreteKernelField F s,
      (absoluteGaloisGroupContinuousMulEquiv F σ) (x : AlgebraicClosure F) = x) :
    s σ = 1 := by
  have hFixed : (absoluteGaloisGroupContinuousMulEquiv F σ) ∈
      (absoluteDiscreteKernelField F s).fixingSubgroup := hFix
  rw [absoluteDiscreteKernelField_fixingSubgroup] at hFixed
  exact hFixed

/-- Killing the specified finite inertia and real conjugation gives a
continuous factor through the actual maximal real pro-p extension. -/
theorem exists_maximalRealProPOutside_factor_of_inertia_and_infiniteArtin_trivial
    (p : ℕ) (T : Set (HeightOneSpectrum (𝓞 ℚ)))
    {Q : Type*} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
    (hP : IsPGroup p Q) (s : Field.absoluteGaloisGroup ℚ →ₜ* Q)
    (hs : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ T →
      ∀ σ : finitePlaceAbsoluteInertiaSubgroup ℚ v,
        s (finitePlaceAbsoluteDecompositionInclusion ℚ v
          (finitePlaceAbsoluteInertiaInclusion ℚ v σ)) = 1)
    (hInfinity : s (absoluteInfinitePlaceArtinNegOne ℚ Rat.infinitePlace) = 1) :
    ∃ t : (maximalRealProPOutside p T ≃ₐ[ℚ] maximalRealProPOutside p T) →ₜ* Q,
      t.comp (absoluteToMaximalRealProPOutside p T) = s := by
  let M : IntermediateField ℚ (AlgebraicClosure ℚ) := absoluteDiscreteKernelField ℚ s
  let : IsGalois ℚ M := absoluteDiscreteKernelField_isGalois ℚ s
  let : NumberField M := NumberField.of_module_finite ℚ M
  have hPM : IsPGroup p (M ≃ₐ[ℚ] M) :=
    absoluteDiscreteKernelField_isPGroup ℚ s p hP
  have hFinite : IsUnramifiedAtFinitePlacesOutside ℚ M T := by
    intro P hPOutside
    apply isUnramifiedAt_at_finitePlaceAbove_of_chosenFinitePlaceIsUnramified
      (finitePlaceBelow (K := ℚ) P) P rfl
    exact discreteKernel_chosenUnramified ℚ s (finitePlaceBelow (K := ℚ) P)
      (hs (finitePlaceBelow (K := ℚ) P) hPOutside)
  have hReal : IsTotallyReal M := by
    apply absoluteDiscreteKernelField_isTotallyReal_of_infiniteArtin ℚ s
    intro v
    rw [Subsingleton.elim v Rat.infinitePlace]
    exact hInfinity
  have hInfinite : IsUnramifiedAtInfinitePlaces ℚ M :=
    (isUnramifiedAtInfinitePlaces_rat_iff_isTotallyReal M).mpr hReal
  let E : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ) :=
    { toIntermediateField := M
      finiteDimensional := inferInstance
      isGalois := absoluteDiscreteKernelField_isGalois ℚ s }
  have hM : M ≤ maximalRealProPOutside p T :=
    le_maximalRealProPOutside ⟨E, hPM, hFinite, hInfinite⟩
  have hKer : (absoluteToMaximalRealProPOutside p T).toMonoidHom.ker ≤
      s.toMonoidHom.ker := by
    intro σ hσ
    rw [absoluteToMaximalRealProPOutside_ker] at hσ
    apply discreteKernel_eq_one_of_fixes ℚ s σ
    intro x
    exact hσ ⟨x, hM x.property⟩
  let q : (Field.absoluteGaloisGroup ℚ ⧸
      (absoluteToMaximalRealProPOutside p T).toMonoidHom.ker) →ₜ* Q :=
    ProCGroups.QuotientGroup.liftₜ
      (absoluteToMaximalRealProPOutside p T).toMonoidHom.ker s hKer
  let e := absoluteRealProPOutsideQuotientEquiv p T
  refine ⟨q.comp e.symm, ?_⟩
  ext σ
  change q (e.symm (absoluteToMaximalRealProPOutside p T σ)) = s σ
  rw [← absoluteRealProPOutsideQuotientEquiv_mk p T σ, e.symm_apply_apply]
  exact ProCGroups.QuotientGroup.liftₜ_apply_mk
    (absoluteToMaximalRealProPOutside p T).toMonoidHom.ker s hKer σ

end ClassFieldTower.Sawin
