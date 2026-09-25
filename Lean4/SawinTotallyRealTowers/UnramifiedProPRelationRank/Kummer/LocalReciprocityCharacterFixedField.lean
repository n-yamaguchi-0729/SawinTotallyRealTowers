/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.LocalClassFieldTheory.Infinite.AbsoluteArtinRestriction
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.LocalReciprocityCharacterPairing
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.LocalKummerInertia

set_option autoImplicit false
/-!
# The finite local field cut out by a mod-`p` character

The finite abelian field is constructed from the character's actual open
kernel.  Its finite character recovers absolute Artin evaluation, and
inertia-triviality puts inertia in the field's fixing subgroup.
-/

open scoped Topology

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.ProP LocalClassFieldTheory

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable (p : ℕ) [Fact p.Prime]

local instance localReciprocityFixedFieldTopology : TopologicalSpace (ZMod p) := ⊥
local instance localReciprocityFixedFieldDiscreteTopology : DiscreteTopology (ZMod p) :=
  discreteTopology_bot _
local instance localReciprocityFixedFieldH1Module
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    Module (ZMod p) (ContinuousH1ZMod (p := p) (G := G)) := continuousH1ZModModule

/-- The absolute character in the separable-closure abelianization model. -/
noncomputable def localReciprocitySeparableAbelianCharacter
    (chi : ContinuousH1ZMod (p := p) (G := Field.absoluteGaloisGroup K)) :
    localAbsoluteAbelianProfinite K →ₜ* Multiplicative (ZMod p) :=
  (localReciprocityAbelianCharacter K p chi).comp
    (ContinuousMonoidHom.toContinuousMonoidHom
      (separableToStandardAbsoluteAbelianizationEquiv K))

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
@[simp]
theorem localReciprocitySeparableAbelianCharacter_mk
    (chi : ContinuousH1ZMod (p := p) (G := Field.absoluteGaloisGroup K))
    (sigma : Gal(SeparableClosure K / K)) :
    localReciprocitySeparableAbelianCharacter K p chi (QuotientGroup.mk sigma) =
      Multiplicative.ofAdd
        (localStandardH1LinearEquivSeparable p K chi (Additive.ofMul sigma)) := rfl

/-- The actual open kernel of the finite-valued abelian character. -/
noncomputable def localReciprocityCharacterKernel
    (chi : ContinuousH1ZMod (p := p) (G := Field.absoluteGaloisGroup K)) :
    OpenNormalSubgroup (localAbsoluteAbelianProfinite K) where
  toSubgroup := (localReciprocitySeparableAbelianCharacter K p chi).toMonoidHom.ker
  isOpen' := (isOpen_discrete {1}).preimage
    (localReciprocitySeparableAbelianCharacter K p chi).continuous_toFun
  isNormal' := MonoidHom.normal_ker _

/-- The finite abelian extension cut out by the given local character. -/
noncomputable abbrev localReciprocityCharacterField
    (chi : ContinuousH1ZMod (p := p) (G := Field.absoluteGaloisGroup K)) :
    IntermediateField K (SeparableClosure K) :=
  absoluteFiniteQuotientField K (localReciprocityCharacterKernel K p chi)

/-- The faithful character on the actual finite Galois group. -/
noncomputable def localReciprocityFiniteCharacter
    (chi : ContinuousH1ZMod (p := p) (G := Field.absoluteGaloisGroup K)) :
    Gal(localReciprocityCharacterField K p chi / K) →* Multiplicative (ZMod p) :=
  (QuotientGroup.lift (localReciprocityCharacterKernel K p chi).toSubgroup
    (localReciprocitySeparableAbelianCharacter K p chi).toMonoidHom le_rfl).comp
      (absoluteFiniteQuotientEquiv K
        (localReciprocityCharacterKernel K p chi)).symm.toMulEquiv.toMonoidHom

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The finite character agrees with the original character after restriction. -/
theorem localReciprocityFiniteCharacter_restriction
    (chi : ContinuousH1ZMod (p := p) (G := Field.absoluteGaloisGroup K))
    (x : localAbsoluteAbelianProfinite K) :
    localReciprocityFiniteCharacter K p chi
        (absoluteAbelianRestriction K (localReciprocityCharacterField K p chi) x) =
      localReciprocitySeparableAbelianCharacter K p chi x := by
  refine QuotientGroup.induction_on x fun sigma ↦ ?_
  rw [absoluteAbelianRestriction_mk]
  change localReciprocityFiniteCharacter K p chi
    (AlgEquiv.restrictNormalHom
      (absoluteFiniteQuotientField K (localReciprocityCharacterKernel K p chi)) sigma) = _
  rw [← absoluteFiniteQuotientEquiv_mk_mk]
  change QuotientGroup.lift (localReciprocityCharacterKernel K p chi).toSubgroup
    (localReciprocitySeparableAbelianCharacter K p chi).toMonoidHom le_rfl
    ((absoluteFiniteQuotientEquiv K (localReciprocityCharacterKernel K p chi)).symm
      ((absoluteFiniteQuotientEquiv K (localReciprocityCharacterKernel K p chi))
        (QuotientGroup.mk (QuotientGroup.mk sigma : localAbsoluteAbelianProfinite K)))) = _
  rw [ContinuousMulEquiv.symm_apply_apply]
  rfl

/-- Actual finite Artin evaluation recovers the power-class pairing. -/
theorem localReciprocityFiniteCharacter_artin
    (chi : ContinuousH1ZMod (p := p) (G := Field.absoluteGaloisGroup K)) (a : Kˣ) :
    (localReciprocityFiniteCharacter K p chi
        (abelianLocalArtinMap K (localReciprocityCharacterField K p chi) a)).toAdd =
      localReciprocityH1PowerClassPairing K p chi
        (Additive.ofMul (QuotientGroup.mk' (powMonoidHom p : Kˣ →* Kˣ).range a)) := by
  rw [← separableAbsoluteLocalArtinMap_restriction,
    localReciprocityFiniteCharacter_restriction]
  rfl

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem absoluteFiniteQuotientField_fixingSubgroup
    (N : OpenNormalSubgroup (localAbsoluteAbelianProfinite K)) :
    (absoluteFiniteQuotientField K N).fixingSubgroup =
      (absoluteFiniteQuotientPreimage K N).toSubgroup :=
  InfiniteGalois.fixingSubgroup_fixedField (absoluteFiniteQuotientClosedPreimage K N)

private theorem localIntrinsicUnramifiedH1_apply_inertia
    (psi : ContinuousH1ZMod (p := p) (G := Gal(SeparableClosure K / K)))
    (hpsi : psi ∈ localIntrinsicUnramifiedH1 K p)
    (sigma : localIntrinsicInertiaSubgroup K) :
    psi (Additive.ofMul sigma.1) = 0 := by
  change localIntrinsicH1InertiaRestriction K p psi = 0 at hpsi
  have h := congrArg (fun f : ContinuousH1ZMod (p := p)
      (G := localIntrinsicInertiaSubgroup K) ↦ f (Additive.ofMul sigma)) hpsi
  exact h

/-- An inertia-trivial character cuts out an inertia-fixed finite field. -/
theorem localReciprocityCharacterField_inertia_le
    (chi : ContinuousH1ZMod (p := p) (G := Field.absoluteGaloisGroup K))
    (hchi : localStandardH1LinearEquivSeparable p K chi ∈
      localIntrinsicUnramifiedH1 K p) :
    MonoidHom.ker (localResidueDegree K).toMonoidHom ≤
      (localReciprocityCharacterField K p chi).fixingSubgroup := by
  change MonoidHom.ker (localResidueDegree K).toMonoidHom ≤
    (absoluteFiniteQuotientField K (localReciprocityCharacterKernel K p chi)).fixingSubgroup
  rw [absoluteFiniteQuotientField_fixingSubgroup]
  intro sigma hsigma
  have hmem : localAbsoluteAbelianizationQuotientMap K sigma ∈
      localReciprocityCharacterKernel K p chi := by
    change localAbsoluteAbelianizationQuotientMap K sigma ∈
      (localReciprocityCharacterKernel K p chi).toSubgroup
    rw [show (localReciprocityCharacterKernel K p chi).toSubgroup =
      (localReciprocitySeparableAbelianCharacter K p chi).toMonoidHom.ker from rfl,
      MonoidHom.mem_ker]
    change localReciprocitySeparableAbelianCharacter K p chi (QuotientGroup.mk sigma) = 1
    rw [localReciprocitySeparableAbelianCharacter_mk]
    apply Multiplicative.toAdd.injective
    exact localIntrinsicUnramifiedH1_apply_inertia K p
      (localStandardH1LinearEquivSeparable p K chi) hchi ⟨sigma, hsigma⟩
  exact hmem

end ClassFieldTower.Martinet.Shafarevich
