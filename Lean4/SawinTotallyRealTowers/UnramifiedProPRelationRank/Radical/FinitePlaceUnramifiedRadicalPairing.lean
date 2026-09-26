/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.LocalReciprocityUnramifiedValuation
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.FinitePlaceValuationDiagonal
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.EmptySupportKummerCokernel
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.FinitePlaceAdicInertiaTransport

set_option autoImplicit false
/-!
# Unramified reciprocity characters on the ideal radical

An ideal-radical class has valuation zero modulo the coefficient prime at
every finite place. Consequently, unramified local characters annihilate its
localization, and changing a character by an unramified character does not
change its value there. No roots-of-unity or parity hypothesis is needed.
-/

open NumberField IsDedekindDomain
open scoped NumberField Topology
noncomputable section
namespace ClassFieldTower.Martinet.Shafarevich
open ClassFieldTower.ProP

variable (F : Type) [Field F] [NumberField F]
variable (n : ℕ+) [Fact (n : ℕ).Prime]
variable (v : HeightOneSpectrum (𝓞 F))

local instance finitePlaceUnramifiedRadicalCanonicalZModAddCommGroup :
    AddCommGroup (ZMod (n : ℕ)) :=
  (ZMod.instField (n : ℕ)).toDivisionRing.toAddCommGroup

local instance finitePlaceUnramifiedRadicalValuativeRel : ValuativeRel (v.adicCompletion F) :=
  finitePlaceAdicCompletionValuativeRel F v
local instance finitePlaceUnramifiedRadicalLocalField :
    IsNonarchimedeanLocalField (v.adicCompletion F) :=
  finitePlaceAdicCompletionIsNonarchimedeanLocalField F v
local instance finitePlaceUnramifiedRadicalTopology : TopologicalSpace (ZMod (n : ℕ)) := ⊥
local instance finitePlaceUnramifiedRadicalDiscrete : DiscreteTopology (ZMod (n : ℕ)) :=
  discreteTopology_bot _
local instance finitePlaceUnramifiedRadicalH1Module
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    Module (ZMod (n : ℕ)) (ContinuousH1ZMod (p := (n : ℕ)) (G := G)) := continuousH1ZModModule

/-- An ideal-radical class has zero local valuation modulo the prime. -/
theorem finitePlaceLocalPowerClassValuation_idealRadical_eq_zero
    (a : idealPowerRadicalModP F (n : ℕ)) :
    finitePlaceLocalPowerClassValuation F (n : ℕ) v
      (finitePlacePowerClassLocalization F (n : ℕ) v
        (idealPowerRadicalToAbsolutePowerClassLinearMap F (n : ℕ) a)) = 0 := by
  rw [finitePlaceLocalPowerClassValuation_localization]
  have hmem : idealPowerRadicalToAbsolutePowerClassLinearMap F (n : ℕ) a ∈
      LinearMap.ker (absolutePowerClassFiniteValuationLocalization F (n : ℕ)) := by
    rw [absolutePowerClassFiniteValuationLocalization_ker]
    exact ⟨a, rfl⟩
  exact congrArg (fun x : FiniteValuationDefectModP F (n : ℕ) =>
    (Additive.toMul x v).toAdd) (LinearMap.mem_ker.mp hmem)

/-- Unramified local reciprocity characters kill localized ideal radicals. -/
theorem finitePlaceUnramifiedReciprocityPairing_idealRadical_eq_zero
    (chi : ContinuousH1ZMod (p := (n : ℕ))
      (G := Field.absoluteGaloisGroup (v.adicCompletion F)))
    (hchi : chi ∈ localStandardUnramifiedH1 (v.adicCompletion F) n)
    (a : idealPowerRadicalModP F (n : ℕ)) :
    localReciprocityH1PowerClassPairing (v.adicCompletion F) (n : ℕ) chi
      (finitePlacePowerClassLocalization F (n : ℕ) v
        (idealPowerRadicalToAbsolutePowerClassLinearMap F (n : ℕ) a)) = 0 := by
  obtain ⟨c, hc⟩ := localReciprocityH1PowerClassPairing_mem_valuation_range
    (v.adicCompletion F) n chi hchi
  rw [← hc, localPowerClassValuationDualEmbedding_apply]
  change c * finitePlaceLocalPowerClassValuation F (n : ℕ) v
    (finitePlacePowerClassLocalization F (n : ℕ) v
      (idealPowerRadicalToAbsolutePowerClassLinearMap F (n : ℕ) a)) = 0
  rw [finitePlaceLocalPowerClassValuation_idealRadical_eq_zero, mul_zero]

/-- The reciprocity pairing on the ideal radical depends only on ramification. -/
theorem finitePlaceReciprocityPairing_idealRadical_eq_of_sub_unramified
    (chi psi : ContinuousH1ZMod (p := (n : ℕ))
      (G := Field.absoluteGaloisGroup (v.adicCompletion F)))
    (h : chi - psi ∈ localStandardUnramifiedH1 (v.adicCompletion F) n)
    (a : idealPowerRadicalModP F (n : ℕ)) :
    localReciprocityH1PowerClassPairing (v.adicCompletion F) (n : ℕ) chi
      (finitePlacePowerClassLocalization F (n : ℕ) v
        (idealPowerRadicalToAbsolutePowerClassLinearMap F (n : ℕ) a)) =
    localReciprocityH1PowerClassPairing (v.adicCompletion F) (n : ℕ) psi
      (finitePlacePowerClassLocalization F (n : ℕ) v
        (idealPowerRadicalToAbsolutePowerClassLinearMap F (n : ℕ) a)) := by
  have hh := finitePlaceUnramifiedReciprocityPairing_idealRadical_eq_zero F n v (chi - psi) h a
  rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at hh
  exact hh

/-- Equality on actual decomposition-group inertia suffices for equality of
the localized ideal-radical reciprocity pairing. -/
theorem finitePlaceDecompositionReciprocityPairing_idealRadical_eq_of_inertiaRestriction_eq
    (chi psi : ContinuousH1ZMod (p := (n : ℕ))
      (G := finitePlaceAbsoluteDecompositionGroup F v))
    (h : finitePlaceH1InertiaRestriction F (n : ℕ) v chi =
      finitePlaceH1InertiaRestriction F (n : ℕ) v psi)
    (a : idealPowerRadicalModP F (n : ℕ)) :
    localReciprocityH1PowerClassPairing (v.adicCompletion F) (n : ℕ)
      (finitePlaceDecompositionH1ToAdic F (n : ℕ) v chi)
      (finitePlacePowerClassLocalization F (n : ℕ) v
        (idealPowerRadicalToAbsolutePowerClassLinearMap F (n : ℕ) a)) =
    localReciprocityH1PowerClassPairing (v.adicCompletion F) (n : ℕ)
      (finitePlaceDecompositionH1ToAdic F (n : ℕ) v psi)
      (finitePlacePowerClassLocalization F (n : ℕ) v
        (idealPowerRadicalToAbsolutePowerClassLinearMap F (n : ℕ) a)) := by
  apply finitePlaceReciprocityPairing_idealRadical_eq_of_sub_unramified F n v
  rw [← map_sub, finitePlaceDecompositionH1ToAdic_mem_unramified_iff]
  change finitePlaceH1InertiaRestriction F (n : ℕ) v (chi - psi) = 0
  rw [map_sub, h, sub_self]

/-- Character-valued form: no passage to a chosen local cohomology
representative is required of a caller comparing two global lifts. -/
theorem finitePlaceDecompositionReciprocityPairing_idealRadical_eq_of_character_inertia_eq
    (chi psi : finitePlaceAbsoluteDecompositionGroup F v →ₜ* Multiplicative (ZMod (n : ℕ)))
    (h : chi.comp (finitePlaceAbsoluteInertiaInclusion F v) =
      psi.comp (finitePlaceAbsoluteInertiaInclusion F v))
    (a : idealPowerRadicalModP F (n : ℕ)) :
    localReciprocityH1PowerClassPairing (v.adicCompletion F) (n : ℕ)
      (finitePlaceDecompositionH1ToAdic F (n : ℕ) v (h1OfCharacter chi))
      (finitePlacePowerClassLocalization F (n : ℕ) v
        (idealPowerRadicalToAbsolutePowerClassLinearMap F (n : ℕ) a)) =
    localReciprocityH1PowerClassPairing (v.adicCompletion F) (n : ℕ)
      (finitePlaceDecompositionH1ToAdic F (n : ℕ) v (h1OfCharacter psi))
      (finitePlacePowerClassLocalization F (n : ℕ) v
        (idealPowerRadicalToAbsolutePowerClassLinearMap F (n : ℕ) a)) := by
  apply finitePlaceDecompositionReciprocityPairing_idealRadical_eq_of_inertiaRestriction_eq
    F n v
  ext sigma
  exact congrArg Multiplicative.toAdd (DFunLike.congr_fun h sigma.toMul)

end ClassFieldTower.Martinet.Shafarevich
