/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.RelationRank.AbsoluteUnramifiedH2Localization
import SawinTotallyRealTowers.UnramifiedProPRelationRank.RelationRank.FinitePlaceAbsoluteInertiaKernel
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FinitePlaceInertiaTransport
import ProCGroups.Topologies.QuotientMaps

set_option autoImplicit false
/-!
# Vanishing of localized unramified degree-two classes

At a finite place, absolute restriction to the maximal everywhere-unramified
pro-`p` extension kills inertia.  It therefore factors through the unramified
quotient of the selected decomposition group.  The chosen local comparison
identifies that quotient with the standard local unramified quotient, whose
continuous degree-two cohomology with trivial `ZMod p` coefficients vanishes.
-/

open CategoryTheory NumberField IsDedekindDomain
open scoped NNReal NumberField ValuativeRel

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.Cohomology
open ClassFieldTower.Martinet
open LocalClassFieldTheory
open LocalFieldTheory
open ProCGroups

variable (F : Type) [Field F] [NumberField F]
variable (p : ℕ) [Fact p.Prime]

/-- Absolute restriction from a finite-place decomposition group factors
through its unramified quotient. -/
noncomputable def finitePlaceUnramifiedToMaxEverywhereUnramifiedProP
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    finitePlaceAbsoluteDecompositionGroup F v ⧸
        finitePlaceAbsoluteInertiaSubgroup F v →ₜ*
      MaxEverywhereUnramifiedProPGaloisGroup F p := by
  let f := (absoluteToMaxEverywhereUnramifiedProP F p).comp
    (finitePlaceAbsoluteDecompositionInclusion F v)
  have hker : finitePlaceAbsoluteInertiaSubgroup F v ≤
      f.toMonoidHom.ker := by
    intro sigma hsigma
    let tau : finitePlaceAbsoluteInertiaSubgroup F v := ⟨sigma, hsigma⟩
    have htau :
        (tau.1.1 : Field.absoluteGaloisGroup F) ∈
          (absoluteUnramifiedKernel F p).toSubgroup :=
      finitePlaceAbsoluteInertia_mem_absoluteUnramifiedKernel F p v tau
    have htauKer :
        (tau.1.1 : Field.absoluteGaloisGroup F) ∈
          (absoluteToMaxEverywhereUnramifiedProP F p).toMonoidHom.ker := by
      rw [absoluteToMaxEverywhereUnramifiedProP_ker]
      exact htau
    have hz : absoluteToMaxEverywhereUnramifiedProP F p
        (tau.1.1 : Field.absoluteGaloisGroup F) = 1 :=
      MonoidHom.mem_ker.mp htauKer
    exact hz
  exact QuotientGroup.liftₜ
    (finitePlaceAbsoluteInertiaSubgroup F v) f hker

@[simp]
theorem finitePlaceUnramifiedToMaxEverywhereUnramifiedProP_mk
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F))
    (sigma : finitePlaceAbsoluteDecompositionGroup F v) :
    finitePlaceUnramifiedToMaxEverywhereUnramifiedProP F p v
        (QuotientGroup.mk' (finitePlaceAbsoluteInertiaSubgroup F v) sigma) =
      absoluteToMaxEverywhereUnramifiedProP F p sigma.1 := by
  rfl

/-- The degree-two cohomology of the unramified quotient selected at a finite
place is trivial. -/
theorem finitePlaceUnramifiedQuotientH2_subsingleton
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    Subsingleton
      (continuousCohomologyZModPLifted p
        (finitePlaceAbsoluteDecompositionGroup F v ⧸
          finitePlaceAbsoluteInertiaSubgroup F v) 2) := by
  let vF := NumberField.HeightOneSpectrum.adicAbv F v
  let hvFna := NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv F v
  let _ : Valued vF.Completion NNReal :=
    finitePlaceCompletionValued vF hvFna
  let _ : ValuativeRel vF.Completion :=
    finitePlaceCompletionValuativeRel vF hvFna
  let _ : IsNonarchimedeanLocalField vF.Completion :=
    finitePlaceNormCompletionIsNonarchimedeanLocalField F v
  let e := continuousCohomologyZModPLiftedLinearEquiv (p := p)
    (finitePlaceUnramifiedQuotientContinuousMulEquiv F v) 2
  constructor
  intro x y
  apply e.symm.injective
  exact @Subsingleton.elim
    (continuousCohomologyZModPLifted p
      (LocalUnramifiedGaloisQuotient vF.Completion) 2)
    (localUnramifiedQuotientH2_subsingleton vF.Completion p)
    (e.symm x) (e.symm y)

/-- Each finite-place localization of a degree-two class inflated from the
maximal everywhere-unramified pro-`p` quotient vanishes. -/
theorem absoluteUnramifiedH2LocalizationFamily_component_eq_zero
    (x : continuousCohomologyZModPLifted p
      (MaxEverywhereUnramifiedProPGaloisGroup F p) 2)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    absoluteUnramifiedH2LocalizationFamily F p x v = 0 := by
  rw [absoluteUnramifiedH2LocalizationFamily_component]
  let q := quotientProjection (finitePlaceAbsoluteInertiaSubgroup F v)
  let f := finitePlaceUnramifiedToMaxEverywhereUnramifiedProP F p v
  have hfactor :
      (absoluteToMaxEverywhereUnramifiedProP F p).comp
          (finitePlaceAbsoluteDecompositionInclusion F v) =
        f.comp q := by
    ext sigma
    rfl
  rw [hfactor, continuousCohomologyZModPMapLifted_comp,
    ConcreteCategory.comp_apply]
  have hz :
      (continuousCohomologyZModPMapLifted p f 2).hom x = 0 :=
    @Subsingleton.elim
      (continuousCohomologyZModPLifted p
        (finitePlaceAbsoluteDecompositionGroup F v ⧸
          finitePlaceAbsoluteInertiaSubgroup F v) 2)
      (finitePlaceUnramifiedQuotientH2_subsingleton F p v)
      ((continuousCohomologyZModPMapLifted p f 2).hom x) 0
  rw [hz]
  exact map_zero (continuousCohomologyZModPMapLifted p q 2).hom

/-- Localization after inflation from the maximal everywhere-unramified
pro-`p` quotient is the zero linear map. -/
theorem absoluteUnramifiedH2LocalizationFamily_eq_zero :
    absoluteUnramifiedH2LocalizationFamily F p = 0 := by
  ext x v
  exact absoluteUnramifiedH2LocalizationFamily_component_eq_zero F p x v

end ClassFieldTower.Martinet.Shafarevich
