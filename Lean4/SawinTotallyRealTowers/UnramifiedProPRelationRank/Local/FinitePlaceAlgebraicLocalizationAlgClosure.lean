/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ValuedFieldTheory.Ramification.HilbertRamification.AlgebraicLocalizationTopology
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FinitePlaceH2Localization
import ClassFieldTheory.AlgebraicNumberTheory.Completion.LocalizedValuation
import Mathlib.Analysis.Normed.Field.Dense
import Mathlib.FieldTheory.AlgebraicClosure

set_option autoImplicit false
/-!
# Algebraic localization as a local algebraic closure

For an extension of a nonarchimedean absolute value to an algebraically
closed algebraic extension, its completion is algebraically closed.  Krasner's
lemma then shows that the algebraic localization inside that completion is
itself algebraically closed.  Together with its existing algebraicity theorem,
this identifies the algebraic localization as an algebraic closure of the
completed base field.
-/

open Polynomial
open scoped Topology

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open AlgebraicNumberTheory.Valuations

universe u v

variable {K : Type u} {L : Type v}
variable [Field K] [Field L] [Algebra K L]
variable [CharZero K] [Algebra.IsAlgebraic K L] [IsAlgClosed L]

private theorem fieldAlgebra_isTorsionFree
    {F E : Type*} [Field F] [Field E] [Algebra F E] :
    Module.IsTorsionFree F E :=
  Module.IsTorsionFree.of_smul_eq_zero fun r x h ↦ by
    rw [Algebra.smul_def] at h
    rcases mul_eq_zero.mp h with hr | hx
    · exact Or.inl ((algebraMap F E).injective (by simpa using hr))
    · exact Or.inr hx

omit [Algebra.IsAlgebraic K L] in
/-- The completion of an algebraically closed algebraic extension at an
extended nonarchimedean absolute value remains algebraically closed. -/
theorem absoluteValueExtensionCompletion_isAlgClosed
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (hvKna : IsNonarchimedean (vK : K → ℝ))
    (w : AbsoluteValueExtension vK L) :
    IsAlgClosed w.1.Completion := by
  let _ : CharZero L :=
    charZero_of_injective_algebraMap (algebraMap K L).injective
  let _ : Algebra L w.1.Completion :=
    AbsoluteValue.extensionCompletionAlgebra (K := L) w.1
  let _ : CharZero w.1.Completion :=
    charZero_of_injective_algebraMap
      (algebraMap L w.1.Completion).injective
  let hCompletionNormedField : NormedField w.1.Completion := inferInstance
  let _ : NontriviallyNormedField w.1.Completion :=
    absoluteValueExtension_completionNontriviallyNormedField w.1
      (w.isNontrivial hvK)
  let _ : NormedField w.1.Completion := hCompletionNormedField
  let hwna : IsNonarchimedean (w.1 : L → ℝ) :=
    absoluteValueExtension_isNonarchimedean vK hvKna w
  let _ : IsUltrametricDist w.1.Completion :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
      (AbsoluteValue.completionAbsoluteValue_isNonarchimedean w.1 hwna)
  apply IsAlgClosed.of_denseRange (K := L) (L := w.1.Completion)
  rw [Metric.denseRange_iff]
  intro x epsilon hepsilon
  obtain ⟨y, hy⟩ :=
    (AbsoluteValue.denseRange_toCompletion w.1).exists_dist_lt
      x hepsilon
  exact ⟨y, by
    change dist x (AbsoluteValue.toCompletion w.1 y) < epsilon
    exact hy⟩

/-- The algebraic localization inside the completed algebraically closed
extension is algebraically closed. -/
theorem absoluteValueAlgebraicLocalization_isAlgClosed
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (hvKna : IsNonarchimedean (vK : K → ℝ))
    (w : AbsoluteValueExtension vK L) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    IsAlgClosed
      (AbsoluteValue.algebraicLocalization vK w.1 w.2) := by
  let _ : CharZero L :=
    charZero_of_injective_algebraMap (algebraMap K L).injective
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let _ := hK
  let _ : SMul K w.1.Completion := hK.toSMul
  let hCompletionAlgebra := AbsoluteValue.completionAlgebra vK w.1 w.2
  let _ := hCompletionAlgebra
  let E := AbsoluteValue.algebraicLocalization vK w.1 w.2
  let C := w.1.Completion
  let _ : Algebra.IsAlgebraic vK.Completion E :=
    AbsoluteValue.algebraicLocalization_isAlgebraic vK w.1 w.2
  let _ : NormedAlgebra vK.Completion C :=
    absoluteValueExtension_completionNormedAlgebra vK w
  let _ : IsAlgClosed C :=
    absoluteValueExtensionCompletion_isAlgClosed vK hvK hvKna w
  let A := algebraicClosure vK.Completion C
  let hBaseNormedField : NormedField vK.Completion := inferInstance
  let _ : NontriviallyNormedField vK.Completion :=
    absoluteValueExtension_completionNontriviallyNormedField vK hvK
  let _ : NormedField vK.Completion := hBaseNormedField
  let _ : IsUltrametricDist vK.Completion :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
      (AbsoluteValue.completionAbsoluteValue_isNonarchimedean
        vK hvKna)
  let _ : CharZero vK.Completion :=
    charZero_of_injective_algebraMap
      (algebraMap K vK.Completion).injective
  let hANormedAlgebra : NormedAlgebra vK.Completion A :=
    SubalgebraClass.toNormedAlgebra A
  let _ := hANormedAlgebra
  let hAAlgebraic : Algebra.IsAlgebraic vK.Completion A :=
    algebraicClosure.isAlgebraic vK.Completion C
  let _ := hAAlgebraic
  let _ : IsAlgClosed A := IsAlgClosure.isAlgClosed vK.Completion
  have hEA : E = A := by
    apply le_antisymm
    · exact le_algebraicClosure vK.Completion C E
    · intro x hx
      classical
      let xA : A := ⟨x, hx⟩
      let S : Finset A :=
        {z ∈ ((minpoly vK.Completion xA).rootSet A).toFinset | z ≠ xA}
      let delta : ℝ := if hS : S.Nonempty then
          Finset.min' (S.image fun z ↦ ‖xA - z‖)
            (Finset.image_nonempty.mpr hS)
        else 1
      have hdelta_le : ∀ z : A,
          IsConjRoot vK.Completion xA z → xA ≠ z →
            delta ≤ ‖xA - z‖ := by
        intro z hz hne
        by_cases hS : S.Nonempty
        · simp only [delta, hS, ↓reduceDIte]
          apply Finset.min'_le (S.image fun y ↦ ‖xA - y‖) ‖xA - z‖
          apply Finset.mem_image_of_mem
          simp only [Finset.mem_filter, Set.mem_toFinset, S]
          rw [← isConjRoot_iff_mem_minpoly_rootSet
            (Algebra.IsIntegral.isIntegral xA)]
          exact ⟨hz, hne.symm⟩
        · simp only [delta, hS, ↓reduceDIte]
          simp only [Finset.not_nonempty_iff_eq_empty,
            Finset.filter_eq_empty_iff, Set.mem_toFinset, not_not, S] at hS
          have hzroot : z ∈ (minpoly vK.Completion xA).rootSet A := by
            rw [← isConjRoot_iff_mem_minpoly_rootSet
              (Algebra.IsIntegral.isIntegral xA)]
            exact hz
          exact (hne (hS hzroot).symm).elim
      have hdelta_pos : 0 < delta := by
        by_cases hS : S.Nonempty
        · simp only [delta, hS, ↓reduceDIte,
            Finset.lt_min'_iff, Finset.mem_image,
            forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
          intro z hz
          simp only [Finset.mem_filter, Set.mem_toFinset, S] at hz
          rw [norm_pos_iff, sub_ne_zero]
          exact hz.2.symm
        · simp [delta, hS]
      obtain ⟨y, hy⟩ :=
        (AbsoluteValue.denseRange_toCompletion w.1).exists_dist_lt
          x hdelta_pos
      let yC : C := AbsoluteValue.toCompletion w.1 y
      have hyE : yC ∈ E :=
        (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 y).property
      have hyA : yC ∈ A :=
        (le_algebraicClosure vK.Completion C E) hyE
      let yA : A := ⟨yC, hyA⟩
      have hxy : ‖xA - yA‖ < delta := by
        change ‖x - AbsoluteValue.toCompletion w.1 y‖ < delta
        simpa only [dist_eq_norm] using hy
      let _ : IsKrasner vK.Completion A :=
        @IsKrasner.of_completeSpace vK.Completion A
          (inferInstance : NormedField A)
          (inferInstance : NontriviallyNormedField vK.Completion)
          (inferInstance : CompleteSpace vK.Completion)
          (inferInstance : IsUltrametricDist vK.Completion)
          hANormedAlgebra hAAlgebraic
      have hxadjoin : xA ∈
          IntermediateField.adjoin vK.Completion ({yA} : Set A) := by
        apply IsKrasner.krasner
        · exact (minpoly.irreducible
            (Algebra.IsIntegral.isIntegral xA)).separable
        · exact IsAlgClosed.splits _
        · exact Algebra.IsIntegral.isIntegral yA
        · intro z hz hne
          exact lt_of_lt_of_le hxy (hdelta_le z hz hne)
      have hadjoin : IntermediateField.adjoin
          vK.Completion ({yA} : Set A) ≤ E.comap A.val := by
        apply IntermediateField.adjoin_le_iff.mpr
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst z
        exact hyE
      exact hadjoin hxadjoin
  exact IsAlgClosed.of_ringEquiv (k := A) E
    (IntermediateField.equivOfEq hEA).symm.toRingEquiv

/-- The algebraic localization is an algebraic closure of the completed base
field. -/
theorem absoluteValueAlgebraicLocalization_isAlgClosure
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (hvKna : IsNonarchimedean (vK : K → ℝ))
    (w : AbsoluteValueExtension vK L) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    letI : Module.IsTorsionFree vK.Completion
        (AbsoluteValue.algebraicLocalization vK w.1 w.2) :=
      fieldAlgebra_isTorsionFree
    IsAlgClosure vK.Completion
      (AbsoluteValue.algebraicLocalization vK w.1 w.2) := by
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let _ := hK
  let _ : SMul K w.1.Completion := hK.toSMul
  let _ := AbsoluteValue.completionAlgebra vK w.1 w.2
  let _ : Module.IsTorsionFree vK.Completion
      (AbsoluteValue.algebraicLocalization vK w.1 w.2) :=
    fieldAlgebra_isTorsionFree
  exact
    { isAlgClosed :=
        absoluteValueAlgebraicLocalization_isAlgClosed vK hvK hvKna w
      isAlgebraic :=
        AbsoluteValue.algebraicLocalization_isAlgebraic vK w.1 w.2 }

open NumberField IsDedekindDomain
open scoped NumberField

/-- At a number-field finite place, the selected algebraic localization is an
algebraic closure of the adic completion. -/
theorem finitePlaceAlgebraicLocalization_isAlgClosure
    (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    let vF := NumberField.HeightOneSpectrum.adicAbv F v
    let w := finitePlaceAbsoluteValueExtension F v
    letI hF := AbsoluteValue.extensionCompletionAlgebra (K := F) w.1
    letI : SMul F w.1.Completion := hF.toSMul
    letI := AbsoluteValue.completionAlgebra vF w.1 w.2
    letI : Module.IsTorsionFree vF.Completion
        (AbsoluteValue.algebraicLocalization vF w.1 w.2) :=
      fieldAlgebra_isTorsionFree
    IsAlgClosure vF.Completion
      (AbsoluteValue.algebraicLocalization vF w.1 w.2) := by
  let vF := NumberField.HeightOneSpectrum.adicAbv F v
  let w := finitePlaceAbsoluteValueExtension F v
  exact absoluteValueAlgebraicLocalization_isAlgClosure vF
    (RayClass.adicAbv_isNontrivial v)
    (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv F v) w

/-- The algebraic-closure comparison used by the decomposition-group
topological equivalence below. -/
noncomputable def absoluteValueAlgebraicLocalizationAlgEquivAlgebraicClosure
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (hvKna : IsNonarchimedean (vK : K → ℝ))
    (w : AbsoluteValueExtension vK L) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    AbsoluteValue.algebraicLocalization vK w.1 w.2 ≃ₐ[vK.Completion]
      AlgebraicClosure vK.Completion := by
  letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  letI : SMul K w.1.Completion := hK.toSMul
  letI := AbsoluteValue.completionAlgebra vK w.1 w.2
  let E := AbsoluteValue.algebraicLocalization vK w.1 w.2
  letI : Module.IsTorsionFree vK.Completion E :=
    fieldAlgebra_isTorsionFree
  letI : IsAlgClosure vK.Completion E :=
    absoluteValueAlgebraicLocalization_isAlgClosure vK hvK hvKna w
  exact IsAlgClosure.equiv vK.Completion E (AlgebraicClosure vK.Completion)

/-- A choice of algebraic-closure comparison transports the decomposition
group to the absolute Galois group of the completed base field. -/
noncomputable def
    absoluteValueDecompositionGroupContinuousMulEquivAbsoluteGaloisGroup
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (hvKna : IsNonarchimedean (vK : K → ℝ))
    (w : AbsoluteValueExtension vK L) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    HilbertRamification.absoluteValueDecompositionGroup K w.1 ≃ₜ*
      Field.absoluteGaloisGroup vK.Completion := by
  letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  letI : SMul K w.1.Completion := hK.toSMul
  letI := AbsoluteValue.completionAlgebra vK w.1 w.2
  let E := AbsoluteValue.algebraicLocalization vK w.1 w.2
  letI : Module.IsTorsionFree vK.Completion E :=
    fieldAlgebra_isTorsionFree
  letI : IsAlgClosure vK.Completion E :=
    absoluteValueAlgebraicLocalization_isAlgClosure vK hvK hvKna w
  let e : E ≃ₐ[vK.Completion] AlgebraicClosure vK.Completion :=
    IsAlgClosure.equiv vK.Completion E (AlgebraicClosure vK.Completion)
  let hAut : (E ≃ₐ[vK.Completion] E) ≃ₜ*
      Field.absoluteGaloisGroup vK.Completion :=
    { toMulEquiv := AlgEquiv.autCongr e
      continuous_toFun :=
        RamificationTheory.Field.absoluteGaloisGroup.algEquiv_autCongr_continuous e
      continuous_invFun :=
        RamificationTheory.Field.absoluteGaloisGroup.algEquiv_autCongr_symm_continuous e }
  exact
    (decompositionGroupContinuousMulEquivAlgebraicLocalizationAut
      vK hvK w).trans hAut

/-- The selected finite-place decomposition group is topologically isomorphic
to the absolute Galois group of the adic completion.  The equivalence depends
on the choice made by `IsAlgClosure.equiv`. -/
noncomputable def
    finitePlaceDecompositionGroupContinuousMulEquivAbsoluteGaloisGroup
    (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    finitePlaceAbsoluteDecompositionGroup F v ≃ₜ*
      Field.absoluteGaloisGroup
        (NumberField.HeightOneSpectrum.adicAbv F v).Completion := by
  let vF := NumberField.HeightOneSpectrum.adicAbv F v
  let w := finitePlaceAbsoluteValueExtension F v
  exact
    absoluteValueDecompositionGroupContinuousMulEquivAbsoluteGaloisGroup vF
      (RayClass.adicAbv_isNontrivial v)
      (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv F v) w

end ClassFieldTower.Martinet.Shafarevich
