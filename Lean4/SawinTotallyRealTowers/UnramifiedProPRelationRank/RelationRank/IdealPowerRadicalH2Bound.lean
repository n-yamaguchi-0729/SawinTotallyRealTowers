/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import GaloisCohomology.ProP.TrivialZModP
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Global.FrattiniClassField
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.IdealPowerRadicalRank
import Mathlib.LinearAlgebra.Dual.Lemmas

set_option autoImplicit false
/-!
# Numerical H² bounds from the ideal-power radical

An injection into the dual ideal-power radical gives finite-dimensionality
and the numerical term in Shafarevich's relation-rank bound.  The final
specialization replaces the `p`-class rank by the generator rank of the
maximal everywhere-unramified pro-`p` Galois group.
-/

open scoped NumberField Topology

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.Cohomology
open ClassFieldTower.ProP

universe u

variable (F : Type) [Field F] [NumberField F]
variable (p : ℕ) [Fact p.Prime]

/-- Any vector space injecting into the dual ideal-power radical is finite
dimensional and satisfies the arithmetic rank bound. -/
theorem finiteDimensional_and_finrank_le_idealPowerRadicalModPDual_of_injective
    {V : Type u} [AddCommGroup V] [Module (ZMod p) V]
    (f : V →ₗ[ZMod p]
      Module.Dual (ZMod p) (idealPowerRadicalModP F p))
    (hf : Function.Injective f) :
    FiniteDimensional (ZMod p) V ∧
      (open Classical in
        Module.finrank (ZMod p) V ≤
          pClassRank F p +
            (NumberField.InfinitePlace.nrRealPlaces F +
              NumberField.InfinitePlace.nrComplexPlaces F - 1) +
            (if ∃ ζ : F, IsPrimitiveRoot ζ p then 1 else 0)) := by
  classical
  let _ : AddCommGroup (ZMod p) :=
    (ZMod.instField p).toDivisionRing.toAddCommGroup
  let _ : Module (ZMod p) (ZMod p) := Semiring.toModule
  let : FiniteDimensional (ZMod p)
      (Module.Dual (ZMod p) (idealPowerRadicalModP F p)) :=
    idealPowerRadicalModPDual_finiteDimensional F p
  let : FiniteDimensional (ZMod p) V :=
    FiniteDimensional.of_injective f hf
  refine ⟨inferInstance, ?_⟩
  calc
    Module.finrank (ZMod p) V ≤
        Module.finrank (ZMod p)
          (Module.Dual (ZMod p) (idealPowerRadicalModP F p)) :=
      f.finrank_le_finrank_of_injective hf
    _ = pClassRank F p +
          (NumberField.InfinitePlace.nrRealPlaces F +
            NumberField.InfinitePlace.nrComplexPlaces F - 1) +
          (if ∃ ζ : F, IsPrimitiveRoot ζ p then 1 else 0) :=
      finrank_idealPowerRadicalModPDual F p

/-- The preceding consumer specialized to lifted continuous degree-two
cohomology. -/
theorem h2_finiteDimensional_and_rank_le_idealPowerRadicalModPDual_of_injective
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (f : continuousCohomologyZModPLifted p G 2 →ₗ[ZMod p]
      Module.Dual (ZMod p) (idealPowerRadicalModP F p))
    (hf : Function.Injective f) :
    FiniteDimensional (ZMod p) (continuousCohomologyZModPLifted p G 2) ∧
      (open Classical in
        Module.finrank (ZMod p) (continuousCohomologyZModPLifted p G 2) ≤
          pClassRank F p +
            (NumberField.InfinitePlace.nrRealPlaces F +
              NumberField.InfinitePlace.nrComplexPlaces F - 1) +
            (if ∃ ζ : F, IsPrimitiveRoot ζ p then 1 else 0)) :=
  finiteDimensional_and_finrank_le_idealPowerRadicalModPDual_of_injective
    F p f hf

/-- A bound by the radical dual, obtained for example from finite-stage
inflation ranges, yields the numerical Shafarevich bound for the maximal
everywhere-unramified group. -/
theorem maxEverywhereUnramified_h2_numerical_bound_of_finrank_le_radicalDual
    (hpOdd : Odd p)
    (hfinite : FiniteDimensional (ZMod p)
      (continuousCohomologyZModPLifted p
        (MaxEverywhereUnramifiedProPGaloisGroup F p) 2))
    (hle : Module.finrank (ZMod p)
        (continuousCohomologyZModPLifted p
          (MaxEverywhereUnramifiedProPGaloisGroup F p) 2) ≤
      Module.finrank (ZMod p)
        (Module.Dual (ZMod p) (idealPowerRadicalModP F p))) :
    FiniteDimensional (ZMod p)
        (continuousCohomologyZModPLifted p
          (MaxEverywhereUnramifiedProPGaloisGroup F p) 2) ∧
      (open Classical in
        Module.finrank (ZMod p)
            (continuousCohomologyZModPLifted p
              (MaxEverywhereUnramifiedProPGaloisGroup F p) 2) ≤
          topologicalGeneratorRank
              (MaxEverywhereUnramifiedProPGaloisGroup F p) +
            (NumberField.InfinitePlace.nrRealPlaces F +
              NumberField.InfinitePlace.nrComplexPlaces F - 1) +
            (if ∃ ζ : F, IsPrimitiveRoot ζ p then 1 else 0)) := by
  classical
  refine ⟨hfinite, ?_⟩
  calc
    Module.finrank (ZMod p)
        (continuousCohomologyZModPLifted p
          (MaxEverywhereUnramifiedProPGaloisGroup F p) 2) ≤
        Module.finrank (ZMod p)
          (Module.Dual (ZMod p) (idealPowerRadicalModP F p)) := hle
    _ = pClassRank F p +
          (NumberField.InfinitePlace.nrRealPlaces F +
            NumberField.InfinitePlace.nrComplexPlaces F - 1) +
          (if ∃ ζ : F, IsPrimitiveRoot ζ p then 1 else 0) :=
      finrank_idealPowerRadicalModPDual F p
    _ = topologicalGeneratorRank
            (MaxEverywhereUnramifiedProPGaloisGroup F p) +
          (NumberField.InfinitePlace.nrRealPlaces F +
            NumberField.InfinitePlace.nrComplexPlaces F - 1) +
          (if ∃ ζ : F, IsPrimitiveRoot ζ p then 1 else 0) := by
      rw [generatorRank_maxUnramified_eq_pClassRank F p hpOdd]

/-- Direct injection form of the maximal-group numerical bound. -/
theorem maxEverywhereUnramified_h2_numerical_bound_of_injective
    (hpOdd : Odd p)
    (f : continuousCohomologyZModPLifted p
        (MaxEverywhereUnramifiedProPGaloisGroup F p) 2 →ₗ[ZMod p]
      Module.Dual (ZMod p) (idealPowerRadicalModP F p))
    (hf : Function.Injective f) :
    FiniteDimensional (ZMod p)
        (continuousCohomologyZModPLifted p
          (MaxEverywhereUnramifiedProPGaloisGroup F p) 2) ∧
      (open Classical in
        Module.finrank (ZMod p)
            (continuousCohomologyZModPLifted p
              (MaxEverywhereUnramifiedProPGaloisGroup F p) 2) ≤
          topologicalGeneratorRank
              (MaxEverywhereUnramifiedProPGaloisGroup F p) +
            (NumberField.InfinitePlace.nrRealPlaces F +
              NumberField.InfinitePlace.nrComplexPlaces F - 1) +
            (if ∃ ζ : F, IsPrimitiveRoot ζ p then 1 else 0)) := by
  classical
  obtain ⟨hfinite, hle⟩ :=
    h2_finiteDimensional_and_rank_le_idealPowerRadicalModPDual_of_injective
      F p f hf
  apply maxEverywhereUnramified_h2_numerical_bound_of_finrank_le_radicalDual
    F p hpOdd hfinite
  rw [finrank_idealPowerRadicalModPDual F p]
  exact hle

end ClassFieldTower.Martinet.Shafarevich
