/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.AbsoluteDiscreteKernelField
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FinitePlaceInertiaFixedUnramified
import SawinTotallyRealTowers.UnramifiedProPRelationRank.RelationRank.AbsoluteUnramifiedGaloisSequence
import ProCGroups.Topologies.QuotientMaps

set_option autoImplicit false
/-!
# Inertia-trivial discrete p-representations factor through the maximal tower

The actual open-kernel fixed field is finite Galois with p-group Galois group.
Pointwise absolute inertia triviality makes it unramified at finite primes;
odd p makes its infinite primes unramified. Its inclusion in the maximal
everywhere-unramified pro-p field then gives the continuous quotient factor.

The target need not itself be finite: discreteness already makes the actual
kernel open. Only the fixed field's Galois and number-field proof instances
are installed, with all field algebra structures inherited canonically.
-/

open NumberField IsDedekindDomain
open scoped NumberField
noncomputable section
namespace ClassFieldTower.Martinet.Shafarevich
open ClassFieldTower.Martinet ProCGroups

variable (F : Type) [Field F] [NumberField F]
variable (p : ℕ) [Fact p.Prime]
variable {Q : Type*} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]

/-- A continuous discrete p-representation killing every selected absolute
finite-place inertia has an actual continuous maximal-unramified factor. -/
theorem exists_maxEverywhereUnramifiedProP_factor_of_inertia_trivial
    (hpOdd : Odd p) (hP : IsPGroup p Q)
    (s : Field.absoluteGaloisGroup F →ₜ* Q)
    (hs : ∀ v : HeightOneSpectrum (𝓞 F),
      ∀ sigma : finitePlaceAbsoluteInertiaSubgroup F v,
        s (finitePlaceAbsoluteDecompositionInclusion F v
          (finitePlaceAbsoluteInertiaInclusion F v sigma)) = 1) :
    ∃ t : MaxEverywhereUnramifiedProPGaloisGroup F p →ₜ* Q,
      t.comp (absoluteToMaxEverywhereUnramifiedProP F p) = s := by
  let M := absoluteDiscreteKernelField F s
  let _ : IsGalois F M := absoluteDiscreteKernelField_isGalois F s
  let _ : NumberField M := NumberField.of_module_finite F M
  have hPM : IsPGroup p Gal(M/F) := absoluteDiscreteKernelField_isPGroup F s p hP
  have hfin : IsUnramifiedAtFinitePlaces F M := by
    apply finitePlacesUnramified_of_absoluteInertiaFixes F M
    intro v sigma x
    have hker : (sigma.1.1 : Gal(AlgebraicClosure F/F)) ∈ M.fixingSubgroup := by
      rw [absoluteDiscreteKernelField_fixingSubgroup]
      exact hs v sigma
    exact hker x
  have hinf : IsUnramifiedAtInfinitePlaces F M := by
    apply IsUnramifiedAtInfinitePlaces_of_odd_card_aut
    obtain ⟨r, hr⟩ := hPM.exists_card_eq
    rw [hr]
    exact hpOdd.pow
  have hM : M ≤ maximalEverywhereUnramifiedProP F p :=
    le_maximalEverywhereUnramifiedProP F p M hPM
      (everywhereUnramified_of_finitePlaces_of_infinitePlaces hfin hinf)
  have hker : (absoluteUnramifiedKernel F p).toSubgroup ≤ s.toMonoidHom.ker := by
    intro sigma hsigma
    have hfixed : (absoluteGaloisGroupContinuousMulEquiv F sigma) ∈ M.fixingSubgroup := by
      intro x
      exact hsigma ⟨x, hM x.property⟩
    rw [absoluteDiscreteKernelField_fixingSubgroup] at hfixed
    exact hfixed
  let q : (Field.absoluteGaloisGroup F ⧸
      (absoluteUnramifiedKernel F p).toSubgroup) →ₜ* Q :=
    QuotientGroup.liftₜ (absoluteUnramifiedKernel F p).toSubgroup s hker
  let e := absoluteUnramifiedQuotientContinuousMulEquiv F p
  refine ⟨q.comp e.symm, ?_⟩
  ext sigma
  change q (e.symm (absoluteToMaxEverywhereUnramifiedProP F p sigma)) = s sigma
  have he : e (QuotientGroup.mk sigma) = absoluteToMaxEverywhereUnramifiedProP F p sigma := rfl
  rw [← he, e.symm_apply_apply]
  rfl

end ClassFieldTower.Martinet.Shafarevich
