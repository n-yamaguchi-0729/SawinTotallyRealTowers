/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.FinitePlaceH1AdicRestriction
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.FiniteSupportLocalReciprocityIdeleCharacter
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.EmptySupportKummerCokernel

set_option autoImplicit false
/-! # The linear radical pairing of a finite family of decomposition characters -/

open NumberField IsDedekindDomain
open scoped NumberField Topology BigOperators
noncomputable section
namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.ProP

variable (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime]

local instance finiteDecompositionRadicalTopology : TopologicalSpace (ZMod p) := ⊥
local instance finiteDecompositionRadicalDiscrete : DiscreteTopology (ZMod p) :=
  discreteTopology_bot _
local instance finiteDecompositionRadicalValuative (v : HeightOneSpectrum (𝓞 F)) :
    ValuativeRel (v.adicCompletion F) := finitePlaceAdicCompletionValuativeRel F v
local instance finiteDecompositionRadicalLocalField (v : HeightOneSpectrum (𝓞 F)) :
    IsNonarchimedeanLocalField (v.adicCompletion F) :=
  finitePlaceAdicCompletionIsNonarchimedeanLocalField F v
local instance finiteDecompositionRadicalModule
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    Module (ZMod p) (ContinuousH1ZMod (p := p) (G := G)) := continuousH1ZModModule

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

/-- Restrict the sum of localized reciprocity pairings to the global ideal radical.
The input consists of actual characters on the absolute decomposition groups. -/
def finiteSupportDecompositionRadicalPairing :
    (∀ v : ↥S, ContinuousH1ZMod (p := p)
      (G := finitePlaceAbsoluteDecompositionGroup F v.1)) →ₗ[ZMod p]
      Module.Dual (ZMod p) (idealPowerRadicalModP F p) where
  toFun chi := absolutePowerClassDualRestriction F p
    (finiteSupportLocalReciprocityPowerClassFunctional F p S
      (fun v => finitePlaceDecompositionH1ToAdic F p v.1 (chi v)))
  map_add' chi psi := by
    rw [← map_add (absolutePowerClassDualRestriction F p)]
    apply congrArg (absolutePowerClassDualRestriction F p)
    ext a
    simp only [finiteSupportLocalReciprocityPowerClassFunctional_apply,
      Pi.add_apply, map_add, LinearMap.add_apply, Finset.sum_add_distrib]
  map_smul' c chi := by
    change absolutePowerClassDualRestriction F p _ = c • absolutePowerClassDualRestriction F p _
    rw [← map_smul (absolutePowerClassDualRestriction F p)]
    apply congrArg (absolutePowerClassDualRestriction F p)
    ext a
    simp only [finiteSupportLocalReciprocityPowerClassFunctional_apply,
      Pi.smul_apply, map_smul, LinearMap.smul_apply, ← Finset.smul_sum]

/-- Evaluation is the finite sum of the transported local characters' values. -/
theorem finiteSupportDecompositionRadicalPairing_apply
    (chi : ∀ v : ↥S, ContinuousH1ZMod (p := p)
      (G := finitePlaceAbsoluteDecompositionGroup F v.1))
    (a : idealPowerRadicalModP F p) :
    finiteSupportDecompositionRadicalPairing F p S chi a =
      ∑ v : ↥S, localReciprocityH1PowerClassPairing (v.1.adicCompletion F) p
        (finitePlaceDecompositionH1ToAdic F p v.1 (chi v))
        (finitePlacePowerClassLocalization F p v.1
          (idealPowerRadicalToAbsolutePowerClassLinearMap F p a)) := by
  exact finiteSupportLocalReciprocityPowerClassFunctional_apply F p S
    (fun v => finitePlaceDecompositionH1ToAdic F p v.1 (chi v)) _

end ClassFieldTower.Martinet.Shafarevich
