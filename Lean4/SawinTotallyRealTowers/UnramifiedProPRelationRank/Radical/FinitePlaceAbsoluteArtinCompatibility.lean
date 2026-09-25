/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.FinitePlaceDecompositionAdicEquiv
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FinitePlaceAbsoluteArtinAction
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.LocalAbsoluteArtinSemilinear
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.FinitePlaceCompletionValuationCompatibility
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Global.GlobalMaximalAbelianRestriction
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Global.MaximalAbelianFiniteProjection
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.FinitePlaceH1AdicRestriction
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.LocalReciprocityCharacterPairing

set_option autoImplicit false
/-!
# Actual global--local Artin compatibility for finite-place characters

The selected algebraic-localization embedding first gives equality of the
finite Artin actions.  Finite projections identify the maximal-abelian global
value, and semilinear naturality transports its representative to the concrete
adic completion.  Consequently actual global character restriction and local
reciprocity evaluate to the same value, without roots of unity in the base field.
-/

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open NumberField IsDedekindDomain LocalClassFieldTheory GlobalClassFieldTheory.Reciprocity

variable (F : Type) [Field F] [NumberField F]
variable (v : HeightOneSpectrum (RingOfIntegers F))

/-- The selected global algebraic closure embedded into the absolute-value
completion model used by finite global reciprocity. -/
noncomputable def finitePlaceAlgebraicClosureToAbsoluteCompletion :
    AlgebraicClosure F →ₐ[F] AlgebraicClosure (HeightOneSpectrum.adicAbv F v).Completion where
  toRingHom := (finitePlaceCompletionAlgebraicClosureRingEquiv F v).symm.toRingHom.comp
    (finitePlaceAlgebraicClosureEmbedding F v)
  commutes' x := by
    apply (finitePlaceCompletionAlgebraicClosureRingEquiv F v).injective
    change (finitePlaceCompletionAlgebraicClosureRingEquiv F v)
      ((finitePlaceCompletionAlgebraicClosureRingEquiv F v).symm
        (finitePlaceAlgebraicClosureEmbedding F v (algebraMap F (AlgebraicClosure F) x))) = _
    rw [RingEquiv.apply_symm_apply, finitePlaceAlgebraicClosureEmbedding_algebraMap]
    change _ = finitePlaceCompletionAlgebraicClosureRingEquiv F v
      (algebraMap (HeightOneSpectrum.adicAbv F v).Completion _ (algebraMap F _ x))
    rw [finitePlaceCompletionAlgebraicClosureRingEquiv_algebraMap,
      (relativeFinitePlaceCompletionAlgEquiv v).commutes]

/-- The same embedding intertwines the actual decomposition action. -/
theorem finitePlaceAlgebraicClosureToAbsoluteCompletion_action
    (sigma : Gal(AlgebraicClosure (HeightOneSpectrum.adicAbv F v).Completion /
      (HeightOneSpectrum.adicAbv F v).Completion)) (x : AlgebraicClosure F) :
    sigma (finitePlaceAlgebraicClosureToAbsoluteCompletion F v x) =
      finitePlaceAlgebraicClosureToAbsoluteCompletion F v
        (((finitePlaceDecompositionGroupContinuousMulEquivAbsoluteGaloisGroup F v).symm
          sigma).val x) := by
  apply (finitePlaceCompletionAlgebraicClosureRingEquiv F v).injective
  change finitePlaceCompletionAlgebraicClosureRingEquiv F v
      (sigma ((finitePlaceCompletionAlgebraicClosureRingEquiv F v).symm
        (finitePlaceAlgebraicClosureEmbedding F v x))) =
    finitePlaceCompletionAlgebraicClosureRingEquiv F v
      ((finitePlaceCompletionAlgebraicClosureRingEquiv F v).symm
        (finitePlaceAlgebraicClosureEmbedding F v _))
  rw [RingEquiv.apply_symm_apply]
  have h := finitePlaceAlgebraicClosureEmbedding_action F v
    ((finitePlaceDecompositionGroupContinuousMulEquivAbsoluteGaloisGroup F v).symm sigma) x
  change absoluteGaloisGroupContinuousMulEquiv (v.adicCompletion F)
    (finitePlaceCompletionAbsoluteGaloisContinuousMulEquiv F v
      (finitePlaceDecompositionGroupContinuousMulEquivAbsoluteGaloisGroup F v
        ((finitePlaceDecompositionGroupContinuousMulEquivAbsoluteGaloisGroup F v).symm sigma)))
    (finitePlaceAlgebraicClosureEmbedding F v x) = _ at h
  have he :=
    (finitePlaceDecompositionGroupContinuousMulEquivAbsoluteGaloisGroup F v).apply_symm_apply
      (show Field.absoluteGaloisGroup
        (NumberField.HeightOneSpectrum.adicAbv F v).Completion from sigma)
  rw [he] at h
  exact h

local instance finitePlaceAbsoluteCompatibilitySourceValuativeRel :
    ValuativeRel (HeightOneSpectrum.adicAbv F v).Completion :=
  finitePlaceLocalArtinCompletionValuativeRel v

local instance finitePlaceAbsoluteCompatibilitySourceLocalField :
    IsNonarchimedeanLocalField (HeightOneSpectrum.adicAbv F v).Completion :=
  finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v

/-- An actual local Artin representative restricts to the one-place maximal
abelian global Artin value. -/
theorem finitePlaceAbsoluteArtin_lift_maximalAbelian
    (a : (v.adicCompletion F)ˣ)
    (sigma : Gal(AlgebraicClosure (HeightOneSpectrum.adicAbv F v).Completion /
      (HeightOneSpectrum.adicAbv F v).Completion))
    (hsigma : (QuotientGroup.mk
        (show Field.absoluteGaloisGroup (HeightOneSpectrum.adicAbv F v).Completion from sigma) :
        Field.absoluteGaloisGroupAbelianization (HeightOneSpectrum.adicAbv F v).Completion) =
      absoluteLocalArtinMap (HeightOneSpectrum.adicAbv F v).Completion
        (finitePlaceLocalArtinInput v a)) :
    globalMaximalAbelianRestriction F
        ((finitePlaceDecompositionGroupContinuousMulEquivAbsoluteGaloisGroup F v).symm sigma).val =
      maximalAbelianGlobalArtin F (IdeleGroup.finitePlaceIdeleClass v a) := by
  let delta := (finitePlaceDecompositionGroupContinuousMulEquivAbsoluteGaloisGroup F v).symm sigma
  apply maximalAbelianGalois_ext_of_finite_restrictions F
  intro E
  let : NumberField E := NumberField.of_module_finite F E
  rw [maximalAbelianGlobalArtin_finitePlace_finiteProjection]
  let i : E →ₐ[F] AlgebraicClosure F :=
    (separableClosure F (AlgebraicClosure F)).val.comp
      ((_root_.maximalAbelianExtension F).val.comp E.val)
  apply AlgEquiv.ext
  intro z
  apply i.injective
  have hfinite := finitePlaceAbsoluteArtin_lift_action F E v
    ((finitePlaceAlgebraicClosureToAbsoluteCompletion F v).comp i) a sigma hsigma z
  have haction := finitePlaceAlgebraicClosureToAbsoluteCompletion_action F v sigma (i z)
  have hglobal : delta.val (i z) =
      i (chosenFinitePlaceArtinMonoidHom (K := F) (L := E) v a z) :=
    (finitePlaceAlgebraicClosureToAbsoluteCompletion F v).injective
      (haction.symm.trans hfinite)
  let s := RamificationTheory.Field.absoluteGaloisGroup.separableClosureContinuousMulEquiv F delta.val
  have hE := AlgEquiv.restrictNormal_commutes (globalMaximalAbelianRestriction F delta.val) E z
  have hM := AlgEquiv.restrictNormal_commutes s (_root_.maximalAbelianExtension F)
    (algebraMap E (_root_.maximalAbelianExtension F) z)
  have hrestriction : i (AlgEquiv.restrictNormalHom E
      (globalMaximalAbelianRestriction F delta.val) z) = delta.val (i z) := by
    exact (congrArg (fun x : _root_.maximalAbelianExtension F ↦
        (((x : SeparableClosure F) : AlgebraicClosure F))) hE).trans
      (congrArg (fun x : SeparableClosure F ↦ (x : AlgebraicClosure F)) hM)
  exact hrestriction.trans hglobal

local instance finitePlaceAbsoluteCompatibilityTargetValuativeRel :
    ValuativeRel (v.adicCompletion F) := finitePlaceAdicCompletionValuativeRel F v

local instance finitePlaceAbsoluteCompatibilityTargetLocalField :
    IsNonarchimedeanLocalField (v.adicCompletion F) :=
  finitePlaceAdicCompletionIsNonarchimedeanLocalField F v

/-- The actual completion comparison sends an Artin representative to one
for the concrete adic completion. -/
theorem finitePlaceCompletionArtin_lift
    (a : (v.adicCompletion F)ˣ)
    (sigma : Gal(AlgebraicClosure (HeightOneSpectrum.adicAbv F v).Completion /
      (HeightOneSpectrum.adicAbv F v).Completion))
    (hsigma : (QuotientGroup.mk
        (show Field.absoluteGaloisGroup (HeightOneSpectrum.adicAbv F v).Completion from sigma) :
        Field.absoluteGaloisGroupAbelianization (HeightOneSpectrum.adicAbv F v).Completion) =
      absoluteLocalArtinMap (HeightOneSpectrum.adicAbv F v).Completion
        (finitePlaceLocalArtinInput v a)) :
    (QuotientGroup.mk (finitePlaceCompletionAbsoluteGaloisContinuousMulEquiv F v sigma) :
      Field.absoluteGaloisGroupAbelianization (v.adicCompletion F)) =
      absoluteLocalArtinMap (v.adicCompletion F) a := by
  let C := (HeightOneSpectrum.adicAbv F v).Completion
  let c := (relativeFinitePlaceCompletionAlgEquiv v).toRingEquiv
  have h := absoluteLocalArtinMap_semilinear_lift C (v.adicCompletion F) c
    (finitePlaceCompletionAlgebraicClosureRingEquiv F v)
    (finitePlaceCompletionAlgebraicClosureRingEquiv_algebraMap F v)
    (finitePlaceCompletion_semilinearValuationCompatible F v)
    (finitePlaceLocalArtinInput v a) sigma hsigma
  have ha : Units.map c.toMonoidHom (finitePlaceLocalArtinInput v a) = a := by
    have hc : c = finitePlaceCompletionRingEquiv v :=
      (finitePlaceCompletionRingEquiv_eq_relative v).symm
    rw [hc]
    exact (finitePlaceCompletionUnitsContinuousMulEquiv v).apply_symm_apply a
  rw [ha] at h
  exact h

variable (p : ℕ) [Fact p.Prime]

local instance finitePlaceAbsoluteCompatibilityCharacterTopology :
    TopologicalSpace (Multiplicative (ZMod p)) := ⊥

local instance finitePlaceAbsoluteCompatibilityCharacterDiscreteTopology :
    DiscreteTopology (Multiplicative (ZMod p)) := discreteTopology_bot _

/-- Actual global--local Artin compatibility evaluated by a continuous mod-`p`
character of the maximal abelian global extension. -/
theorem localReciprocityUnitCharacter_globalMaximalAbelian
    (psi : Gal(_root_.maximalAbelianExtension F / F) →ₜ* Multiplicative (ZMod p))
    (a : (v.adicCompletion F)ˣ) :
    localReciprocityUnitCharacter (v.adicCompletion F) p
        (finitePlaceAbsoluteH1AdicRestriction F p v
          (Additive.ofMul (psi.comp (globalMaximalAbelianRestriction F)))) a =
      psi (maximalAbelianGlobalArtin F (IdeleGroup.finitePlaceIdeleClass v a)) := by
  let C := (HeightOneSpectrum.adicAbv F v).Completion
  obtain ⟨sigma, hsigma⟩ := QuotientGroup.mk_surjective
    (absoluteLocalArtinMap C (finitePlaceLocalArtinInput v a))
  have hlocal := finitePlaceCompletionArtin_lift F v a sigma hsigma
  have hglobal := finitePlaceAbsoluteArtin_lift_maximalAbelian F v a sigma hsigma
  let chi := finitePlaceAbsoluteH1AdicRestriction F p v
    (Additive.ofMul (psi.comp (globalMaximalAbelianRestriction F)))
  change localReciprocityAbelianCharacter (v.adicCompletion F) p chi
    (absoluteLocalArtinMap (v.adicCompletion F) a) = _
  rw [← hlocal, localReciprocityAbelianCharacter_mk]
  change psi (globalMaximalAbelianRestriction F
    ((finitePlaceDecompositionAdicContinuousMulEquiv F v).symm
      (finitePlaceCompletionAbsoluteGaloisContinuousMulEquiv F v sigma)).val) = _
  change psi (globalMaximalAbelianRestriction F
    ((finitePlaceDecompositionGroupContinuousMulEquivAbsoluteGaloisGroup F v).symm
      ((finitePlaceCompletionAbsoluteGaloisContinuousMulEquiv F v).symm
        (finitePlaceCompletionAbsoluteGaloisContinuousMulEquiv F v sigma))).val) = _
  rw [ContinuousMulEquiv.symm_apply_apply, hglobal]

end ClassFieldTower.Martinet.Shafarevich
