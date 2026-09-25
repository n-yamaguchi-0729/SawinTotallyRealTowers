/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.LocalUnramifiedArtinKummerAnnihilator
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.FinitePlaceCyclotomicMuPKummerComparison

set_option autoImplicit false
/-!
# Finite-place unramified Artin--Kummer localization

Global power classes are localized to actual adic completions and paired
against intrinsic unramified `H¹`.  The local kernel criterion is proved
from Artin--Kummer duality, including at primes above the coefficient prime.
The product of these local maps is the primal map for the empty-support
unramified Artin--Kummer cokernel.
-/

open NumberField IsDedekindDomain
open scoped NumberField

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.ProP KummerTheory

variable (K : Type) [Field K] [NumberField K]
variable (n : ℕ+) [Fact ((n : ℕ).Prime)]

local instance finitePlaceUnramifiedArtinKummerTopology :
    TopologicalSpace (ZMod (n : ℕ)) := ⊥
local instance finitePlaceUnramifiedArtinKummerDiscreteTopology :
    DiscreteTopology (ZMod (n : ℕ)) := discreteTopology_bot _
local instance finitePlaceUnramifiedArtinKummerModule
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    Module (ZMod (n : ℕ)) (ContinuousH1ZMod (p := (n : ℕ)) (G := G)) :=
  continuousH1ZModModule

local instance finitePlaceUnramifiedArtinKummerValuativeRel
    (v : HeightOneSpectrum (𝓞 K)) : ValuativeRel (v.adicCompletion K) :=
  finitePlaceAdicCompletionValuativeRel K v

local instance finitePlaceUnramifiedArtinKummerLocalField
    (v : HeightOneSpectrum (𝓞 K)) : IsNonarchimedeanLocalField (v.adicCompletion K) :=
  finitePlaceAdicCompletionIsNonarchimedeanLocalField K v

omit [Fact ((n : ℕ).Prime)] in
/-- A global primitive root remains primitive in the actual finite-place
adic completion. -/
theorem finitePlaceCompletion_primitiveRoots_nonempty
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (v : HeightOneSpectrum (𝓞 K)) :
    (primitiveRoots (n : ℕ) (v.adicCompletion K)).Nonempty := by
  obtain ⟨zeta, hzeta⟩ := hmu
  refine ⟨algebraMap K (v.adicCompletion K) zeta, ?_⟩
  apply (mem_primitiveRoots n.pos).2
  exact ((mem_primitiveRoots n.pos).1 hzeta).map_of_injective
    (algebraMap K (v.adicCompletion K)).injective

/-- Intrinsic unramified continuous `H¹` of the adic completion at `v`. -/
noncomputable def finitePlaceUnramifiedCompletionH1
    (v : HeightOneSpectrum (𝓞 K)) :
    Submodule (ZMod (n : ℕ))
      (ContinuousH1ZMod (p := (n : ℕ))
        (G := Field.absoluteGaloisGroup (v.adicCompletion K))) :=
  localStandardUnramifiedH1 (v.adicCompletion K) n

/-- Localize a global Kummer class and pair it against actual unramified
local `H¹` using the Artin--Kummer pairing. -/
noncomputable def finitePlaceUnramifiedArtinKummerLocalization
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (v : HeightOneSpectrum (𝓞 K)) :
    absolutePowerClassModP K (n : ℕ) →ₗ[ZMod (n : ℕ)]
      Module.Dual (ZMod (n : ℕ)) (finitePlaceUnramifiedCompletionH1 K n v) :=
  (localArtinKummerUnramifiedDualRestriction (v.adicCompletion K) n
    (finitePlaceCompletion_primitiveRoots_nonempty K n hmu v)).comp
    ((absoluteKummerContinuousH1LinearEquiv (v.adicCompletion K) (n : ℕ)
      (finitePlaceCompletion_primitiveRoots_nonempty K n hmu v)).toLinearMap.comp
      (finitePlacePowerClassLocalization K (n : ℕ) v))

/-- The intrinsic unramified annihilator condition on a localized global
class is precisely its zero normalized local valuation. -/
theorem finitePlaceUnramifiedArtinKummerLocalization_eq_zero_iff
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (v : HeightOneSpectrum (𝓞 K))
    (x : absolutePowerClassModP K (n : ℕ)) :
    finitePlaceUnramifiedArtinKummerLocalization K n hmu v x = 0 ↔
      finitePlaceLocalPowerClassValuation K (n : ℕ) v
        (finitePlacePowerClassLocalization K (n : ℕ) v x) = 0 := by
  exact localArtinKummerUnramifiedDualRestriction_kummer_eq_zero_iff
    (v.adicCompletion K) n
    (finitePlaceCompletion_primitiveRoots_nonempty K n hmu v)
    (finitePlacePowerClassLocalization K (n : ℕ) v x)

/-- The product of the duals of intrinsic unramified local `H¹` spaces. -/
abbrev FinitePlaceUnramifiedArtinKummerLocalizationTarget :=
  (v : HeightOneSpectrum (𝓞 K)) →
    Module.Dual (ZMod (n : ℕ)) (finitePlaceUnramifiedCompletionH1 K n v)

/-- The actual unramified Artin--Kummer localization map at all finite places. -/
noncomputable def finitePlaceUnramifiedArtinKummerLocalizationFamily
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    absolutePowerClassModP K (n : ℕ) →ₗ[ZMod (n : ℕ)]
      FinitePlaceUnramifiedArtinKummerLocalizationTarget K n :=
  LinearMap.pi (fun v ↦ finitePlaceUnramifiedArtinKummerLocalization K n hmu v)

@[simp]
theorem finitePlaceUnramifiedArtinKummerLocalizationFamily_apply
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (x : absolutePowerClassModP K (n : ℕ)) (v : HeightOneSpectrum (𝓞 K)) :
    finitePlaceUnramifiedArtinKummerLocalizationFamily K n hmu x v =
      finitePlaceUnramifiedArtinKummerLocalization K n hmu v x := rfl

/-- Membership in the family kernel is the pointwise unramified
annihilator condition at every finite place. -/
theorem finitePlaceUnramifiedArtinKummerLocalizationFamily_eq_zero_iff
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (x : absolutePowerClassModP K (n : ℕ)) :
    finitePlaceUnramifiedArtinKummerLocalizationFamily K n hmu x = 0 ↔
      ∀ v : HeightOneSpectrum (𝓞 K),
        finitePlaceLocalPowerClassValuation K (n : ℕ) v
          (finitePlacePowerClassLocalization K (n : ℕ) v x) = 0 := by
  constructor
  · intro hx v
    exact (finitePlaceUnramifiedArtinKummerLocalization_eq_zero_iff K n hmu v x).1
      (congrFun hx v)
  · intro hx
    funext v
    exact (finitePlaceUnramifiedArtinKummerLocalization_eq_zero_iff K n hmu v x).2
      (hx v)

end ClassFieldTower.Martinet.Shafarevich
