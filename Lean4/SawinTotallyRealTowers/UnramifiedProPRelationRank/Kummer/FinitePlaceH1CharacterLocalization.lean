/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.AbsoluteKummerH1Linear
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FinitePlaceH2Localization
import GaloisCohomology.Kummer.Concrete.SUnitPreparation.PrimePowerKernelCoordinates
import Mathlib.LinearAlgebra.Pi

set_option autoImplicit false
/-!
# Finite-place restriction of absolute mod-p characters

Continuous mod-`p` characters of the absolute Galois group restrict to the absolute
decomposition subgroup at every finite place.  This file linearizes each restriction and
assembles all of them into a dependent product.
-/

open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open KummerTheory

variable (F : Type) [Field F] [NumberField F]
variable (p : ℕ) [Fact p.Prime]

local instance finitePlaceH1CharacterTopology :
    TopologicalSpace (Multiplicative (ZMod p)) := ⊥

local instance finitePlaceH1CharacterDiscreteTopology :
    DiscreteTopology (Multiplicative (ZMod p)) :=
  discreteTopology_bot _

/-- Every mod-`p` character of a finite-place decomposition subgroup has exponent dividing `p`. -/
theorem finitePlaceDecompositionContinuousZModCharacter_pow_eq_one
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F))
    (chi : finitePlaceAbsoluteDecompositionGroup F v →ₜ*
      Multiplicative (ZMod p)) :
    chi ^ p = 1 := by
  apply ContinuousMonoidHom.ext
  intro sigma
  rw [ContinuousMonoidHom.pow_apply, ContinuousMonoidHom.one_toFun]
  apply Multiplicative.ofAdd.injective
  change p • (chi sigma).toAdd = 0
  simp

/-- Continuous mod-`p` characters of the absolute decomposition subgroup at `v`, with their
canonical `ZMod p`-module structure. -/
noncomputable def finitePlaceDecompositionContinuousZModCharacterModP
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    ModuleCat (ZMod p) := by
  letI : Module (ZMod p)
      (Additive
        (finitePlaceAbsoluteDecompositionGroup F v →ₜ*
          Multiplicative (ZMod p))) :=
    additiveZModModuleOfPowEqOne p
      (finitePlaceDecompositionContinuousZModCharacter_pow_eq_one F p v)
  exact ModuleCat.of (ZMod p)
    (Additive
      (finitePlaceAbsoluteDecompositionGroup F v →ₜ*
        Multiplicative (ZMod p)))

/-- Restriction of absolute characters to the decomposition subgroup, as an additive map. -/
def finitePlaceH1CharacterRestrictionAddHom
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    Additive
        (Field.absoluteGaloisGroup F →ₜ* Multiplicative (ZMod p)) →+
      Additive
        (finitePlaceAbsoluteDecompositionGroup F v →ₜ*
          Multiplicative (ZMod p)) where
  toFun chi := Additive.ofMul <|
    (Additive.toMul chi).comp (finitePlaceAbsoluteDecompositionInclusion F v)
  map_zero' := by
    apply Additive.toMul.injective
    ext sigma
    rfl
  map_add' chi psi := by
    apply Additive.toMul.injective
    ext sigma
    rfl

/-- Restriction of absolute continuous mod-`p` characters to the decomposition subgroup at `v`. -/
noncomputable def finitePlaceH1CharacterRestriction
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    absoluteContinuousZModCharacterModP F p →ₗ[ZMod p]
      finitePlaceDecompositionContinuousZModCharacterModP F p v := by
  letI : Module (ZMod p)
      (Additive
        (Field.absoluteGaloisGroup F →ₜ* Multiplicative (ZMod p))) :=
    additiveZModModuleOfPowEqOne p
      (absoluteContinuousZModCharacter_pow_eq_one F p)
  letI : Module (ZMod p)
      (Additive
        (finitePlaceAbsoluteDecompositionGroup F v →ₜ*
          Multiplicative (ZMod p))) :=
    additiveZModModuleOfPowEqOne p
      (finitePlaceDecompositionContinuousZModCharacter_pow_eq_one F p v)
  change
    Additive
        (Field.absoluteGaloisGroup F →ₜ* Multiplicative (ZMod p)) →ₗ[ZMod p]
      Additive
        (finitePlaceAbsoluteDecompositionGroup F v →ₜ*
          Multiplicative (ZMod p))
  exact (finitePlaceH1CharacterRestrictionAddHom F p v).toZModLinearMap p

/-- Restriction is evaluation after the continuous decomposition-group inclusion. -/
@[simp]
theorem finitePlaceH1CharacterRestriction_apply
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F))
    (chi : absoluteContinuousZModCharacterModP F p)
    (sigma : finitePlaceAbsoluteDecompositionGroup F v) :
    (Additive.toMul
        (show Additive
            (finitePlaceAbsoluteDecompositionGroup F v →ₜ*
              Multiplicative (ZMod p))
          from finitePlaceH1CharacterRestriction F p v chi)) sigma =
      (Additive.toMul
        (show Additive
            (Field.absoluteGaloisGroup F →ₜ* Multiplicative (ZMod p))
          from chi)) (finitePlaceAbsoluteDecompositionInclusion F v sigma) :=
  rfl

/-- The dependent product of finite-place decomposition-character modules. -/
abbrev FinitePlaceH1CharacterLocalizationTarget :=
  (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) →
    finitePlaceDecompositionContinuousZModCharacterModP F p v

/-- Simultaneous restriction of an absolute mod-`p` character at every finite place. -/
noncomputable def finitePlaceH1CharacterRestrictionFamily :
    absoluteContinuousZModCharacterModP F p →ₗ[ZMod p]
      FinitePlaceH1CharacterLocalizationTarget F p :=
  LinearMap.pi fun v ↦ finitePlaceH1CharacterRestriction F p v

/-- Each component of simultaneous restriction is the corresponding finite-place map. -/
@[simp]
theorem finitePlaceH1CharacterRestrictionFamily_apply
    (chi : absoluteContinuousZModCharacterModP F p)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    finitePlaceH1CharacterRestrictionFamily F p chi v =
      finitePlaceH1CharacterRestriction F p v chi :=
  rfl

/-- Evaluation of a component is ordinary character restriction. -/
@[simp]
theorem finitePlaceH1CharacterRestrictionFamily_apply_apply
    (chi : absoluteContinuousZModCharacterModP F p)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F))
    (sigma : finitePlaceAbsoluteDecompositionGroup F v) :
    (Additive.toMul
        (show Additive
            (finitePlaceAbsoluteDecompositionGroup F v →ₜ*
              Multiplicative (ZMod p))
          from finitePlaceH1CharacterRestrictionFamily F p chi v)) sigma =
      (Additive.toMul
        (show Additive
            (Field.absoluteGaloisGroup F →ₜ* Multiplicative (ZMod p))
          from chi)) (finitePlaceAbsoluteDecompositionInclusion F v sigma) :=
  rfl

end ClassFieldTower.Martinet.Shafarevich
