/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FinitePlaceInertiaTransport
public import Nyll.GaloisCohomology.ProfiniteIntegers.ProfiniteIntegerCore
public import Nyll.ProCGroups.Generation.Basic
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueAlgebraicClosureDegree
public import Nyll.SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.LocalUnramifiedH2Vanishing

/-!
# Arithmetic Frobenius in an absolute decomposition group

The existing local residue comparison identifies the quotient by inertia
with the profinite integers. The class of arithmetic Frobenius is the
inverse image of additive one, and a representative is chosen in the
actual absolute decomposition group.
-/

@[expose] public section

open NumberField IsDedekindDomain
open scoped NumberField
noncomputable section

namespace ClassFieldTower.Sawin

open ClassFieldTower.Martinet.Shafarevich ClassFormation
open AlgebraicNumberTheory.Valuations ProCGroups.Generation

variable (F : Type) [Field F] [NumberField F]
variable (v : HeightOneSpectrum (𝓞 F))

/-- The unramified absolute decomposition quotient has its actual residue degree. -/
def finitePlaceUnramifiedDegreeEquiv :
    (finitePlaceAbsoluteDecompositionGroup F v ⧸
      finitePlaceAbsoluteInertiaSubgroup F v) ≃ₜ* ZHatMul := by
  let vF := NumberField.HeightOneSpectrum.adicAbv F v
  let hvFna := NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv F v
  letI : Valued vF.Completion NNReal := finitePlaceCompletionValued vF hvFna
  letI : ValuativeRel vF.Completion := finitePlaceCompletionValuativeRel vF hvFna
  letI : IsNonarchimedeanLocalField vF.Completion :=
    finitePlaceNormCompletionIsNonarchimedeanLocalField F v
  exact (finitePlaceUnramifiedQuotientContinuousMulEquiv F v).trans
    (localUnramifiedQuotientContinuousMulEquiv vF.Completion)

/-- Decomposition transport and unramified quotient coordinates preserve the
actual local residue degree of each original automorphism. -/
theorem finitePlaceUnramifiedDegreeEquiv_mk
    (sigma : finitePlaceAbsoluteDecompositionGroup F v) :
    let vF := NumberField.HeightOneSpectrum.adicAbv F v
    let hvFna := NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv F v
    let : Valued vF.Completion NNReal := finitePlaceCompletionValued vF hvFna
    let : ValuativeRel vF.Completion := finitePlaceCompletionValuativeRel vF hvFna
    let : IsNonarchimedeanLocalField vF.Completion :=
      finitePlaceNormCompletionIsNonarchimedeanLocalField F v
    finitePlaceUnramifiedDegreeEquiv F v
      (QuotientGroup.mk' (finitePlaceAbsoluteInertiaSubgroup F v) sigma) =
      LocalClassFieldTheory.localResidueDegree vF.Completion
        (finitePlaceDecompositionGroupContinuousMulEquivSeparableAbsoluteGaloisGroup
          F v sigma) := by
  intro vF hvFna hValued hValuative hLocal
  change localUnramifiedQuotientContinuousMulEquiv vF.Completion
    (finitePlaceUnramifiedQuotientContinuousMulEquiv F v
      (QuotientGroup.mk' (finitePlaceAbsoluteInertiaSubgroup F v) sigma)) = _
  rw [finitePlaceUnramifiedQuotientContinuousMulEquiv_mk,
    localUnramifiedQuotientContinuousMulEquiv_mk]

/-- The residue-degree-one class of arithmetic Frobenius. -/
def finitePlaceArithmeticFrobeniusClass :
    finitePlaceAbsoluteDecompositionGroup F v ⧸ finitePlaceAbsoluteInertiaSubgroup F v :=
  (finitePlaceUnramifiedDegreeEquiv F v).symm (Multiplicative.ofAdd (1 : ZHat))

/-- An actual absolute decomposition element representing arithmetic Frobenius. -/
def finitePlaceArithmeticFrobeniusLift : finitePlaceAbsoluteDecompositionGroup F v :=
  Classical.choose ((QuotientGroup.mk'_surjective (finitePlaceAbsoluteInertiaSubgroup F v))
    (finitePlaceArithmeticFrobeniusClass F v))

@[simp]
theorem finitePlaceArithmeticFrobeniusLift_mk :
    QuotientGroup.mk' (finitePlaceAbsoluteInertiaSubgroup F v)
        (finitePlaceArithmeticFrobeniusLift F v) =
      finitePlaceArithmeticFrobeniusClass F v :=
  Classical.choose_spec ((QuotientGroup.mk'_surjective (finitePlaceAbsoluteInertiaSubgroup F v))
    (finitePlaceArithmeticFrobeniusClass F v))

@[simp]
theorem finitePlaceArithmeticFrobeniusLift_degree :
    finitePlaceUnramifiedDegreeEquiv F v
      (QuotientGroup.mk' (finitePlaceAbsoluteInertiaSubgroup F v)
        (finitePlaceArithmeticFrobeniusLift F v)) = Multiplicative.ofAdd (1 : ZHat) := by
  rw [finitePlaceArithmeticFrobeniusLift_mk]
  exact (finitePlaceUnramifiedDegreeEquiv F v).apply_symm_apply _

open LocalClassFieldTheory RamificationTheory.HilbertRamification.ValuationSubring in
/-- Any representative of the arithmetic Frobenius class acts on the actual
residue algebraic closure by the residue-cardinality power. In particular, this
action is independent of the representative, and has the arithmetic orientation. -/
theorem finitePlaceResidueAction_of_arithmeticFrobeniusClass
    (sigma : finitePlaceAbsoluteDecompositionGroup F v)
    (hsigma : QuotientGroup.mk' (finitePlaceAbsoluteInertiaSubgroup F v) sigma =
      finitePlaceArithmeticFrobeniusClass F v) :
    let vF := NumberField.HeightOneSpectrum.adicAbv F v
    let hvFna := NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv F v
    let : Valued vF.Completion NNReal := finitePlaceCompletionValued vF hvFna
    let : ValuativeRel vF.Completion := finitePlaceCompletionValuativeRel vF hvFna
    let : IsNonarchimedeanLocalField vF.Completion :=
      finitePlaceNormCompletionIsNonarchimedeanLocalField F v
    ∀ x : selectedResidueField (localSeparableValuationSubring vF.Completion),
      localSeparableResidueAlgAction vF.Completion
        (finitePlaceDecompositionGroupContinuousMulEquivSeparableAbsoluteGaloisGroup
          F v sigma) x =
        x ^ Fintype.card
          (decompositionResidueField vF.Completion
            (localSeparableValuationSubring vF.Completion)) := by
  intro vF hvFna hValued hValuative hLocal x
  have : Algebra.IsAlgebraic
      (decompositionResidueField vF.Completion (localSeparableValuationSubring vF.Completion))
      (selectedResidueField (localSeparableValuationSubring vF.Completion)) :=
    (decompositionResidueExtension_normal (K := vF.Completion)
      (localSeparableValuationSubring vF.Completion)).toIsAlgebraic
  have hdegree : localResidueDegree vF.Completion
      (finitePlaceDecompositionGroupContinuousMulEquivSeparableAbsoluteGaloisGroup
        F v sigma) = Multiplicative.ofAdd (1 : ZHat) := by
    rw [← finitePlaceUnramifiedDegreeEquiv_mk F v sigma, hsigma]
    exact (finitePlaceUnramifiedDegreeEquiv F v).apply_symm_apply _
  exact apply_eq_pow_card_of_residueAbsoluteDegreeIn
    (decompositionResidueField vF.Completion (localSeparableValuationSubring vF.Completion))
    (selectedResidueField (localSeparableValuationSubring vF.Completion))
    (localSeparableResidueAlgAction vF.Completion
      (finitePlaceDecompositionGroupContinuousMulEquivSeparableAbsoluteGaloisGroup F v sigma))
    hdegree x

/-- The chosen Frobenius class generates the whole unramified decomposition quotient. -/
theorem finitePlaceArithmeticFrobeniusClass_topologicallyGenerates :
    ProCGroups.Generation.TopologicallyGenerates
      ({finitePlaceArithmeticFrobeniusClass F v} :
        Set (finitePlaceAbsoluteDecompositionGroup F v ⧸
          finitePlaceAbsoluteInertiaSubgroup F v)) := by
  let e := finitePlaceUnramifiedDegreeEquiv F v
  let f : ZHatMul →ₜ* (finitePlaceAbsoluteDecompositionGroup F v ⧸
      finitePlaceAbsoluteInertiaSubgroup F v) :=
    { toFun := fun z ↦ e.symm z
      map_one' := e.symm.map_one
      map_mul' := e.symm.map_mul
      continuous_toFun := e.symm.continuous }
  have h := ProCGroups.Generation.topologicallyGenerates_image_of_continuousMonoidHom_surjective
    f e.symm.surjective zHatOne_topologicallyGenerates
  rw [Set.image_singleton] at h
  exact h

end ClassFieldTower.Sawin
