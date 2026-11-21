/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.SupportedIdeleH2Localization
public import Nyll.SawinTotallyRealTowers.UnramifiedProPRelationRank.Global.UnramifiedInfinitePlaceBlockH2

/-!
# Degree-two localization for archimedean-unramified extensions

For an extension unramified at every archimedean place and every finite place
outside `S`, the finite tensor coordinates in `S` determine a supported class.
-/

@[expose] public section

open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField TensorProduct

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.Cohomology CyclicCohomology
open AlgebraicNumberTheory.Valuations HilbertRamification LocalClassFieldTheory

variable (K L : Type) [Field K] [NumberField K]
variable [Field L] [NumberField L] [Algebra K L]
variable [FiniteDimensional K L] [IsGalois K L]

local notation "V" => HeightOneSpectrum (𝓞 K)
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "A∞" => (fun v : InfinitePlace K ↦ (InfinitePlace.Completion v ⊗[K] L)ˣ)
attribute [local instance] scalarTensorUnitsAction

omit [NumberField L] in
/-- Outside unramified integral blocks and unramified infinite blocks
leave only the S-indexed finite coordinates in degree two. -/
theorem sPlaceFactorsH2Localization_injective
    (hfin : ∀ v : V, v ∉ S → ChosenFinitePlaceIsUnramified (K := K) (L := L) v)
    (hinf : ∀ v : InfinitePlace K, (chosenInfinitePlaceAbove (L := L) v).IsUnramified K) :
    Function.Injective (sPlaceFactorsH2Localization K L S) := by
  intro x y h
  apply sPlaceFactorsH2_eq_of_localizations K L S hfin h
  funext v
  let _ : Subsingleton (groupCohomology (Rep.ofMulDistribMulAction Gal(L / K) (A∞ v)) 2) :=
    unramifiedInfinitePlaceBlockH2_subsingleton K L v (hinf v)
  exact Subsingleton.elim _ _

omit [NumberField L] in
/-- The actual supported-idele class is determined by the allowed finite
coordinates when all other local blocks are unramified. -/
theorem supportedSPlaceH2Localization_injective
    (hfin : ∀ v : V, v ∉ S → ChosenFinitePlaceIsUnramified (K := K) (L := L) v)
    (hinf : ∀ v : InfinitePlace K, (chosenInfinitePlaceAbove (L := L) v).IsUnramified K) :
    Function.Injective (supportedSPlaceH2Localization K L S) :=
  (sPlaceFactorsH2Localization_injective K L S hfin hinf).comp
    (supportedSPlaceCohomologyIso K L S).toLinearEquiv.injective

end ClassFieldTower.Martinet.Shafarevich
