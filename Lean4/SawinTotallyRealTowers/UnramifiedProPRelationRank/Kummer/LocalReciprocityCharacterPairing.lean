/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.AbsoluteKummerH1Linear
import ProCGroups.ProP.ContinuousH1
import ClassFieldTheory.LocalClassFieldTheory.Infinite.ProfiniteLocalReciprocity
import ProCGroups.Topologies.QuotientMaps
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.ZMod
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Instances.ZMod

set_option autoImplicit false
/-!
# Local reciprocity pairing without coefficient roots of unity

Evaluate a continuous mod-`p` Galois character on the absolute local Artin
map.  The resulting functional descends to actual multiplicative power
classes.  Dense image of the Artin map makes the pairing faithful in the
character variable.  No primitive root or Kummer trivialization is used.
-/

open scoped Topology

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.ProP LocalClassFieldTheory

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable (p : ℕ) [Fact p.Prime]

local instance localReciprocityPairingCanonicalZModAddCommGroup : AddCommGroup (ZMod p) :=
  (ZMod.instField p).toDivisionRing.toAddCommGroup

local instance localReciprocityCharacterTopology : TopologicalSpace (ZMod p) := ⊥
local instance localReciprocityCharacterDiscreteTopology : DiscreteTopology (ZMod p) :=
  discreteTopology_bot _
local instance localReciprocityCharacterH1Module :
    Module (ZMod p) (ContinuousH1ZMod (p := p) (G := Field.absoluteGaloisGroup K)) :=
  continuousH1ZModModule

/-- A continuous character descends through the closed commutator subgroup. -/
noncomputable def localReciprocityAbelianCharacter
    (chi : ContinuousH1ZMod (p := p) (G := Field.absoluteGaloisGroup K)) :
    Field.absoluteGaloisGroupAbelianization K →ₜ* Multiplicative (ZMod p) := by
  let f := characterOfH1 chi
  apply ProCGroups.QuotientGroup.liftₜ _ f
  exact Subgroup.topologicalClosure_minimal _
    (Abelianization.commutator_subset_ker f.toMonoidHom)
    (ProCGroups.ContinuousMonoidHom.isClosed_ker f)

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
@[simp]
theorem localReciprocityAbelianCharacter_mk
    (chi : ContinuousH1ZMod (p := p) (G := Field.absoluteGaloisGroup K))
    (sigma : Field.absoluteGaloisGroup K) :
    localReciprocityAbelianCharacter K p chi (QuotientGroup.mk sigma) =
      Multiplicative.ofAdd (chi (Additive.ofMul sigma)) := rfl

/-- Evaluate a local Galois character on the absolute Artin map. -/
noncomputable def localReciprocityUnitCharacter
    (chi : ContinuousH1ZMod (p := p) (G := Field.absoluteGaloisGroup K)) :
    Kˣ →ₜ* Multiplicative (ZMod p) :=
  (localReciprocityAbelianCharacter K p chi).comp (absoluteLocalArtinMap K)

/-- The Artin evaluation descends to the quotient by actual `p`-th powers. -/
noncomputable def localReciprocityPowerClassCharacter
    (chi : ContinuousH1ZMod (p := p) (G := Field.absoluteGaloisGroup K)) :
    (Kˣ ⧸ (powMonoidHom p : Kˣ →* Kˣ).range) →* Multiplicative (ZMod p) := by
  refine QuotientGroup.lift (powMonoidHom p : Kˣ →* Kˣ).range
    (localReciprocityUnitCharacter K p chi).toMonoidHom ?_
  rintro _ ⟨a, rfl⟩
  rw [MonoidHom.mem_ker, powMonoidHom_apply, map_pow]
  apply Multiplicative.toAdd.injective
  simp

/-- The power-class functional attached to a continuous local character. -/
noncomputable def localReciprocityPowerClassFunctional
    (chi : ContinuousH1ZMod (p := p) (G := Field.absoluteGaloisGroup K)) :
    Module.Dual (ZMod p) (absolutePowerClassModP K p) := by
  letI : Module (ZMod p)
      (Additive (Kˣ ⧸ (powMonoidHom p : Kˣ →* Kˣ).range)) :=
    KummerTheory.additiveZModModuleOfPowEqOne p
      (absolutePowerClassQuotient_pow_eq_one K p)
  exact (localReciprocityPowerClassCharacter K p chi).toAdditiveLeft.toZModLinearMap p

@[simp]
theorem localReciprocityPowerClassFunctional_mk
    (chi : ContinuousH1ZMod (p := p) (G := Field.absoluteGaloisGroup K)) (a : Kˣ) :
    localReciprocityPowerClassFunctional K p chi
        (Additive.ofMul (QuotientGroup.mk' (powMonoidHom p : Kˣ →* Kˣ).range a)) =
      (localReciprocityAbelianCharacter K p chi (absoluteLocalArtinMap K a)).toAdd := rfl

/-- The local reciprocity pairing, linear in the continuous `H¹` character
and in the actual power class; no roots-of-unity hypothesis is needed. -/
noncomputable def localReciprocityH1PowerClassPairing :
    ContinuousH1ZMod (p := p) (G := Field.absoluteGaloisGroup K) →ₗ[ZMod p]
      Module.Dual (ZMod p) (absolutePowerClassModP K p) := by
  let f : ContinuousH1ZMod (p := p) (G := Field.absoluteGaloisGroup K) →+
      Module.Dual (ZMod p) (absolutePowerClassModP K p) :=
    { toFun := localReciprocityPowerClassFunctional K p
      map_zero' := by
        ext x
        change (localReciprocityPowerClassCharacter K p 0 x.toMul).toAdd = 0
        generalize x.toMul = q
        refine QuotientGroup.induction_on q fun a ↦ ?_
        change (localReciprocityAbelianCharacter K p 0 (absoluteLocalArtinMap K a)).toAdd = 0
        generalize absoluteLocalArtinMap K a = y
        refine QuotientGroup.induction_on y fun sigma ↦ ?_
        rfl
      map_add' := by
        intro chi psi
        ext x
        change (localReciprocityPowerClassCharacter K p (chi + psi) x.toMul).toAdd =
          (localReciprocityPowerClassCharacter K p chi x.toMul).toAdd +
            (localReciprocityPowerClassCharacter K p psi x.toMul).toAdd
        generalize x.toMul = q
        refine QuotientGroup.induction_on q fun a ↦ ?_
        change (localReciprocityAbelianCharacter K p (chi + psi)
            (absoluteLocalArtinMap K a)).toAdd =
          (localReciprocityAbelianCharacter K p chi (absoluteLocalArtinMap K a)).toAdd +
            (localReciprocityAbelianCharacter K p psi (absoluteLocalArtinMap K a)).toAdd
        generalize absoluteLocalArtinMap K a = y
        refine QuotientGroup.induction_on y fun sigma ↦ ?_
        rfl }
  exact f.toZModLinearMap p

@[simp]
theorem localReciprocityH1PowerClassPairing_mk
    (chi : ContinuousH1ZMod (p := p) (G := Field.absoluteGaloisGroup K)) (a : Kˣ) :
    localReciprocityH1PowerClassPairing K p chi
        (Additive.ofMul (QuotientGroup.mk' (powMonoidHom p : Kˣ →* Kˣ).range a)) =
      (localReciprocityAbelianCharacter K p chi (absoluteLocalArtinMap K a)).toAdd := rfl

/-- Dense Artin image detects every continuous local mod-`p` character. -/
theorem localReciprocityH1PowerClassPairing_injective :
    Function.Injective (localReciprocityH1PowerClassPairing K p) := by
  intro chi psi h
  have hab : localReciprocityAbelianCharacter K p chi =
      localReciprocityAbelianCharacter K p psi := by
    apply ContinuousMonoidHom.ext
    apply congrFun
    apply (absoluteLocalArtinMap_denseRange K).equalizer
      (localReciprocityAbelianCharacter K p chi).continuous_toFun
      (localReciprocityAbelianCharacter K p psi).continuous_toFun
    funext a
    apply Multiplicative.toAdd.injective
    exact LinearMap.congr_fun h
      (Additive.ofMul (QuotientGroup.mk' (powMonoidHom p : Kˣ →* Kˣ).range a))
  apply ContinuousAddMonoidHom.ext
  intro sigma
  exact congrArg Multiplicative.toAdd
    (DFunLike.congr_fun hab (QuotientGroup.mk sigma.toMul))

end ClassFieldTower.Martinet.Shafarevich
