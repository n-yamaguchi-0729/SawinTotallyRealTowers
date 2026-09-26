/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.FinitePlaceDecompositionAdicEquiv
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.FinitePlaceH1RamificationLocalization

set_option autoImplicit false
/-!
# Actual absolute-character restriction to the adic completion

The inverse of the decomposition--adic equivalence transports the already
constructed decomposition-group restriction to intrinsic local `H¹`.
-/

open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.ProP

variable (F : Type) [Field F] [NumberField F]
variable (p : ℕ) [Fact p.Prime]

local instance finitePlaceH1AdicCanonicalZModAddCommGroup : AddCommGroup (ZMod p) :=
  (ZMod.instField p).toDivisionRing.toAddCommGroup

local instance finitePlaceH1AdicCharacterTopology :
    TopologicalSpace (Multiplicative (ZMod p)) := ⊥

local instance finitePlaceH1AdicCharacterDiscreteTopology :
    DiscreteTopology (Multiplicative (ZMod p)) := discreteTopology_bot _

local instance finitePlaceH1AdicModule
    {q : ℕ} {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    Module (ZMod q) (ContinuousH1ZMod (p := q) (G := G)) :=
  continuousH1ZModModule

/-- Transport decomposition-group `H¹` through the actual inverse localization. -/
noncomputable def finitePlaceDecompositionH1ToAdic
    (v : HeightOneSpectrum (RingOfIntegers F)) :
    ContinuousH1ZMod (p := p) (G := finitePlaceAbsoluteDecompositionGroup F v) →ₗ[ZMod p]
      ContinuousH1ZMod (p := p) (G := Field.absoluteGaloisGroup (v.adicCompletion F)) := by
  let f :
      ContinuousH1ZMod (p := p) (G := finitePlaceAbsoluteDecompositionGroup F v) →+
        ContinuousH1ZMod (p := p) (G := Field.absoluteGaloisGroup (v.adicCompletion F)) :=
    { toFun := fun chi ↦ h1OfCharacter ((characterOfH1 chi).comp
       (ContinuousMonoidHom.toContinuousMonoidHom
         (finitePlaceDecompositionAdicContinuousMulEquiv F v).symm))
      map_zero' := by ext sigma; rfl
      map_add' := by intro chi psi; ext sigma; rfl }
  exact f.toZModLinearMap p

@[simp] theorem finitePlaceAdicH1Restriction_decompositionH1ToAdic
    (v : HeightOneSpectrum (RingOfIntegers F))
    (chi : ContinuousH1ZMod (p := p) (G := finitePlaceAbsoluteDecompositionGroup F v)) :
    finitePlaceAdicH1Restriction F p v (finitePlaceDecompositionH1ToAdic F p v chi) =
      chi := by
  ext sigma
  change chi (Additive.ofMul ((finitePlaceDecompositionAdicContinuousMulEquiv F v).symm
    (finitePlaceDecompositionAdicContinuousMulEquiv F v (Additive.toMul sigma)))) = chi sigma
  rw [ContinuousMulEquiv.symm_apply_apply]
  rfl

@[simp] theorem finitePlaceDecompositionH1ToAdic_adicH1Restriction
    (v : HeightOneSpectrum (RingOfIntegers F))
    (chi : ContinuousH1ZMod (p := p) (G := Field.absoluteGaloisGroup (v.adicCompletion F))) :
    finitePlaceDecompositionH1ToAdic F p v (finitePlaceAdicH1Restriction F p v chi) =
      chi := by
  ext sigma
  change chi (Additive.ofMul (finitePlaceDecompositionAdicContinuousMulEquiv F v
    ((finitePlaceDecompositionAdicContinuousMulEquiv F v).symm (Additive.toMul sigma)))) = chi sigma
  rw [ContinuousMulEquiv.apply_symm_apply]
  rfl

/-- Actual global absolute-character restriction, now valued in intrinsic adic `H¹`. -/
noncomputable def finitePlaceAbsoluteH1AdicRestriction
    (v : HeightOneSpectrum (RingOfIntegers F)) :
    absoluteContinuousZModCharacterModP F p →ₗ[ZMod p]
      ContinuousH1ZMod (p := p) (G := Field.absoluteGaloisGroup (v.adicCompletion F)) :=
  (finitePlaceDecompositionH1ToAdic F p v).comp
    (finitePlaceAbsoluteH1DecompositionRestriction F p v)

/-- Pulling back the intrinsic local restriction recovers the original actual
decomposition-group restriction, with no change of character. -/
@[simp] theorem finitePlaceAbsoluteH1AdicRestriction_decomposition
    (v : HeightOneSpectrum (RingOfIntegers F))
    (chi : absoluteContinuousZModCharacterModP F p) :
    finitePlaceAdicH1Restriction F p v (finitePlaceAbsoluteH1AdicRestriction F p v chi) =
      finitePlaceAbsoluteH1DecompositionRestriction F p v chi :=
  finitePlaceAdicH1Restriction_decompositionH1ToAdic F p v _

end ClassFieldTower.Martinet.Shafarevich
