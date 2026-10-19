/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Ramification.LocalField.Core
import Nyll.ValuedFieldTheory.Ramification.LocalField.ResidueInertia
import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteUnramified
import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.GaloisIntegerRing

/-!
# Ramification groups of unramified local extensions

This file connects the concrete unramified-valued-extension predicate with
the actual upper ramification groups of a finite local extension.
-/



noncomputable section

namespace RamificationTheory.LocalField

open LocalFieldTheory
open RamificationTheory
open RamificationTheory.HilbertRamification
open RamificationTheory.HilbertRamification.Higher
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension
open scoped ValuativeRel

/-- The inertia group, equivalently the lower ramification group at zero, is
trivial for an actual finite unramified Galois extension of local fields. -/
private theorem localLowerRamificationGroup_zero_eq_bot_of_unramifiedValuation
    (K L : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    localLowerRamificationGroup K L 0 = ⊥ := by
  rw [localLowerRamificationGroup_zero_eq_residue_ker]
  exact (MonoidHom.ker_eq_bot_iff
    (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L)).mpr
      (galoisGroupResidueAlgEquivHomOfIsIntegralClosure_injective_of_unramifiedValuation K L)

/-- Every nonnegative upper ramification group of an actual finite
unramified Galois extension of local fields is trivial. -/
theorem localUpperRamificationGroup_eq_bot_of_unramifiedValuation
    (K L : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (t : ℝ) (ht : 0 ≤ t) :
    localUpperRamificationGroup K L t = ⊥ := by
  apply le_antisymm
  · calc
      localUpperRamificationGroup K L t ≤
          localUpperRamificationGroup K L 0 :=
        localUpperRamificationGroup_antitone K L ht
      _ = localLowerRamificationGroup K L 0 :=
        localUpperRamificationGroup_eq_localLowerRamificationGroup_of_nonpos
          K L 0 (by norm_num)
      _ = ⊥ :=
        localLowerRamificationGroup_zero_eq_bot_of_unramifiedValuation K L
  · exact bot_le

end RamificationTheory.LocalField
