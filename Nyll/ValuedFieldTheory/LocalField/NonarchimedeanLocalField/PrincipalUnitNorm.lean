/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.GaloisIntegerRing
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Norm
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitActions
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueExtension
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.StandardOpenSubgroups
public import Nyll.ValuedFieldTheory.Ramification.Different.Powers

/-!
# Norms of principal units

The actual Galois norm is a product of conjugate units. Each conjugate preserves
the same maximal-ideal power upstairs; contraction to the base gives the safe
depth bound `r > e * (m - 1)`. No filtration compatibility is assumed.
-/

@[expose] public section

noncomputable section

universe u v

namespace LocalFieldTheory

open scoped BigOperators ValuativeRel
open _root_.LocalFieldTheory.IsNonarchimedeanLocalField

section IntegerRing

variable (K : Type u) (L : Type v) [Field K] [ValuativeRel K]
  [Field L] [ValuativeRel L] [Algebra K L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [IsIntegralClosure 𝒪[L] 𝒪[K] L]

/-- The integer-unit norm, embedded upstairs, is the product of the actual
restricted Galois automorphisms. -/
theorem integerUnitsMap_normIntegerUnits_eq_prod_gal
    [FiniteDimensional K L] [IsGalois K L] (a : 𝒪[L]ˣ) :
    integerUnitsMapOfValuationExtension K L (normIntegerUnits K L a) =
      ∏ σ : Gal(L / K),
        Units.mapEquiv (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ).toMulEquiv a := by
  apply integerUnitsToFieldUnits_injective L
  rw [map_prod]
  change mapBaseUnitsToExtensionUnits K L
      (normUnits K L (integerUnitsToFieldUnits L a)) = _
  rw [mapBaseUnits_normUnits_eq_prod_gal]
  apply Finset.prod_congr rfl
  intro σ _
  rfl

/-- Before contraction, the norm of a principal unit remains at the same
depth in the extension field. -/
theorem integerUnitsMap_normIntegerUnits_mem_principalUnits
    [FiniteDimensional K L] [IsGalois K L]
    {r : ℕ} {a : 𝒪[L]ˣ} (ha : a ∈ principalUnits L r) :
    integerUnitsMapOfValuationExtension K L (normIntegerUnits K L a) ∈
      principalUnits L r := by
  rw [integerUnitsMap_normIntegerUnits_eq_prod_gal]
  apply (principalUnits L r).prod_mem
  intro σ _
  exact principalUnits_integerRingEquiv_mem_self L r
    (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ) a ha

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace L] [IsNonarchimedeanLocalField L]

/-- Contracting principal units uses the actual ramification index of the
valuation-integer rings. -/
theorem principalUnits_of_integerUnitsMap_mem_of_depth
    {r m : ℕ} (hr : (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] * (m - 1) < r)
    {a : 𝒪[K]ˣ}
    (ha : integerUnitsMapOfValuationExtension K L a ∈ principalUnits L r) :
    a ∈ principalUnits K m := by
  let : Algebra.IsIntegral 𝒪[K] 𝒪[L] :=
    integerRing_algebra_isIntegral_of_isIntegralClosure K L
  apply RamificationTheory.DiscreteValuationRing.mem_maximalIdeal_pow_of_map_mem
    𝒪[K] 𝒪[L] hr
  change algebraMap 𝒪[K] 𝒪[L] ((a : 𝒪[K]) - 1) ∈ (𝓂[L] ^ r : Ideal 𝒪[L])
  rw [map_sub, map_one]
  exact ha

/-- A Galois norm sends depth `r` into depth `m` whenever
`r ≥ e * (m - 1) + 1`. The proof applies to wild extensions as well. -/
theorem normIntegerUnits_mem_principalUnits_of_depth
    [FiniteDimensional K L] [IsGalois K L]
    {r m : ℕ} (hr : (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] * (m - 1) < r)
    {a : 𝒪[L]ˣ} (ha : a ∈ principalUnits L r) :
    normIntegerUnits K L a ∈ principalUnits K m :=
  principalUnits_of_integerUnitsMap_mem_of_depth K L hr
    (integerUnitsMap_normIntegerUnits_mem_principalUnits K L ha)

end IntegerRing

/-- The safe principal-unit bound for the actual field-unit norm. Integral
closure of the valuation rings is supplied by finite separability. -/
theorem fieldPrincipalUnits_le_norm_preimage_of_isGalois
    (K : Type u) (L : Type v)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    {r m : ℕ} (hr : (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] * (m - 1) < r) :
    fieldPrincipalUnits L r ≤ (fieldPrincipalUnits K m).comap (normUnits K L) := by
  let : IsIntegralClosure 𝒪[L] 𝒪[K] L :=
    localCompleteDVF_integerRing_isIntegralClosure K L
  rintro u ⟨a, ha, rfl⟩
  exact ⟨normIntegerUnits K L a, normIntegerUnits_mem_principalUnits_of_depth K L hr ha, rfl⟩

end LocalFieldTheory
