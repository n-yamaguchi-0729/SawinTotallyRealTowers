/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormSubgroup
import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UnramifiedNormComparison
import ValuedFieldTheory.LocalField.NormUnits
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteUnramified
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Norm
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.SeparableNormValuation
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence

set_option autoImplicit false

/-!
# Base-field units are norms in a divisible unramified local tower

For finite local extensions K → L → M with M/L unramified, a base-field
unit has L-valuation divisible by e(L/K). If [M:L] divides that actual
ramification index, the unramified norm subgroup calculation produces a
unit of M whose field norm is the given base-field unit embedded in L.
-/

namespace LocalClassFieldTheory

open scoped ValuativeRel
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

/-- A base-field unit has an actual norm preimage when the unramified top
extension degree divides the ramification index of the lower extension. -/
theorem exists_normUnits_eq_mapBaseUnitsToExtensionUnits_of_finrank_dvd_ramificationIdx
    (K L M : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Field M] [ValuativeRel M] [TopologicalSpace M]
    [IsNonarchimedeanLocalField M]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Algebra L M] [FiniteDimensional L M] [IsGalois L M]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    [Valuation.HasExtension (ValuativeRel.valuation L)
      (ValuativeRel.valuation M)]
    [Module.Finite 𝒪[L] 𝒪[M]] [IsUnramifiedValuedExtension L M]
    (hd : Module.finrank L M ∣
      (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K]) (x : Kˣ) :
    ∃ y : Mˣ, normUnits L M y = mapBaseUnitsToExtensionUnits K L x := by
  have : IsIntegralClosure 𝒪[L] 𝒪[K] L :=
    localCompleteDVF_integerRing_isIntegralClosure K L
  have : IsIntegralClosure 𝒪[M] 𝒪[L] M :=
    localCompleteDVF_integerRing_isIntegralClosure L M
  have hmem : mapBaseUnitsToExtensionUnits K L x ∈ localNormSubgroup L M := by
    rw [normSubgroup_eq_unramifiedNormSubgroup_of_isIntegralClosure L M,
      mem_unramifiedNormSubgroup_iff, valuationMap_apply,
      v_mapBaseUnitsToExtensionUnits_eq_ramificationIdx_mul K L x]
    have hdInt : (Module.finrank L M : Int) ∣
        ((𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] : Int) :=
      Int.natCast_dvd_natCast.2 hd
    exact dvd_mul_of_dvd_left hdInt (v K (Additive.ofMul x))
  exact MonoidHom.mem_range.mp hmem

end LocalClassFieldTheory
