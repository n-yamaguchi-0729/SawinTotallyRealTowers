/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.RelationRank.ArithmeticStageH2GlobalLift
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.FinitePlaceH1AdicRestriction
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.FiniteSupportLocalReciprocityIdeleCharacter
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.EmptySupportKummerCokernel
import GaloisCohomology.ProP.H2FiniteStageFamily

set_option autoImplicit false
/-!
# The actual radical functional of an arithmetic-stage degree-two class

Finite-stage mod-`p` H² is a finite set. The union of the ramification supports of all its
chosen global lifts is consequently one fixed finite set. On this set the actual local lift
differences, transported to the adic absolute Galois groups, pair with localized global
power classes. Restriction to the ideal-power radical gives a concrete functional for every
stage class. Its linearity and kernel are proved in the subsequent comparison leaves.
-/

open NumberField IsDedekindDomain
open scoped NumberField Topology

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.Cohomology ClassFieldTower.ProP ClassFieldTower.Martinet
open ProCGroups

variable (F : Type) [Field F] [NumberField F]
variable (n : ℕ+) [Fact (n : ℕ).Prime] (hpOdd : Odd (n : ℕ))
variable (U : OpenNormalSubgroup (MaxEverywhereUnramifiedProPGaloisGroup F (n : ℕ)))

local notation "StageQuotient" => MaxEverywhereUnramifiedProPGaloisGroup F (n : ℕ) ⧸
  (U : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F (n : ℕ)))
local notation "StageH2" => continuousCohomologyZModPLifted (n : ℕ) StageQuotient 2

local instance arithmeticRadicalFunctionalH2Finite : Finite StageH2 := by
  let : FiniteDimensional (ZMod (n : ℕ)) StageH2 :=
    finiteDimensional_degree_two_of_finite (p := (n : ℕ)) (inferInstance : Finite StageQuotient)
  exact Module.finite_of_finite (ZMod (n : ℕ))

local instance arithmeticRadicalFunctionalTopology : TopologicalSpace (ZMod (n : ℕ)) := ⊥
local instance arithmeticRadicalFunctionalDiscreteTopology : DiscreteTopology (ZMod (n : ℕ)) :=
  discreteTopology_bot _
local instance arithmeticRadicalFunctionalH1Module
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    Module (ZMod (n : ℕ)) (ContinuousH1ZMod (p := (n : ℕ)) (G := G)) := continuousH1ZModModule

/-- All chosen stage lifts ramify inside one finite set, since the stage H² itself is finite. -/
theorem arithmeticStageH2RamifiedPlaces_family_finite :
    (⋃ x : StageH2, (arithmeticStageH2GlobalRamifiedPlaces F n hpOdd U x :
      Set (HeightOneSpectrum (𝓞 F)))).Finite :=
  Set.finite_iUnion fun x => (arithmeticStageH2GlobalRamifiedPlaces F n hpOdd U x).finite_toSet

/-- A single finite support valid for the chosen global lift of every stage class. -/
def arithmeticStageH2UniformRamifiedPlaces : Finset (HeightOneSpectrum (𝓞 F)) :=
  (arithmeticStageH2RamifiedPlaces_family_finite F n hpOdd U).toFinset

/-- Each individual chosen lift's ramified set lies in the common support. -/
theorem arithmeticStageH2GlobalRamifiedPlaces_subset_uniform (x : StageH2) :
    arithmeticStageH2GlobalRamifiedPlaces F n hpOdd U x ⊆
      arithmeticStageH2UniformRamifiedPlaces F n hpOdd U := by
  intro v hv
  rw [arithmeticStageH2UniformRamifiedPlaces, Set.Finite.mem_toFinset]
  exact Set.mem_iUnion.mpr ⟨x, hv⟩

/-- Every chosen stage lift is unramified outside the fixed support. -/
theorem arithmeticStageH2GlobalLiftAtFinitePlace_inertia_le_ker_of_not_mem_uniform
    (x : StageH2) (v : HeightOneSpectrum (𝓞 F))
    (hv : v ∉ arithmeticStageH2UniformRamifiedPlaces F n hpOdd U) :
    finitePlaceAbsoluteInertiaSubgroup F v ≤
      (arithmeticStageH2GlobalLiftAtFinitePlace F n hpOdd U x v).toMonoidHom.ker :=
  arithmeticStageH2GlobalLiftAtFinitePlace_inertia_le_ker_of_not_mem F n hpOdd U x v
    (fun h => hv (arithmeticStageH2GlobalRamifiedPlaces_subset_uniform F n hpOdd U x h))

/-- The actual local difference character, in the adic absolute Galois model. -/
def arithmeticStageH2AdicLocalDifference (x : StageH2) (v : HeightOneSpectrum (𝓞 F)) :
    ContinuousH1ZMod (p := (n : ℕ)) (G := Field.absoluteGaloisGroup (v.adicCompletion F)) :=
  finitePlaceDecompositionH1ToAdic F (n : ℕ) v
    (h1OfCharacter (arithmeticStageH2GlobalLocalDifferenceCharacter F n hpOdd U x v))

/-- The finite local reciprocity functional on global power classes. -/
def arithmeticStageH2PowerClassFunctional (x : StageH2) :
    Module.Dual (ZMod (n : ℕ)) (absolutePowerClassModP F (n : ℕ)) :=
  finiteSupportLocalReciprocityPowerClassFunctional F (n : ℕ)
    (arithmeticStageH2UniformRamifiedPlaces F n hpOdd U)
    (fun v => arithmeticStageH2AdicLocalDifference F n hpOdd U x v.1)

/-- The radical functional built from actual global and local solutions of the embedding problem. -/
def arithmeticStageH2RadicalFunctional (x : StageH2) :
    Module.Dual (ZMod (n : ℕ)) (idealPowerRadicalModP F (n : ℕ)) :=
  absolutePowerClassDualRestriction F (n : ℕ)
    (arithmeticStageH2PowerClassFunctional F n hpOdd U x)

end ClassFieldTower.Martinet.Shafarevich
