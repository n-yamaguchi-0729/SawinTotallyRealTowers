/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitNorm

public import Mathlib.FieldTheory.Galois.Basic
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueGalois
public import Nyll.ValuedFieldTheory.LocalField.NormUnits

/-! # Principal-unit norms on the extension side -/


@[expose] public section

noncomputable section

universe u v

namespace LocalClassFieldTheory

open scoped ValuativeRel
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

/-- States the theorem `normIntegerUnits_to_fieldUnits`. -/
theorem normIntegerUnits_to_fieldUnits (K : Type u) (L : Type v)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [LocalFieldTheory.ValuativeExtension K L] (u : 𝒪[L]ˣ) :
    integerUnitsToFieldUnits K (normIntegerUnits K L u) =
      LocalFieldTheory.normUnits K L (integerUnitsToFieldUnits L u) := by
  ext
  rfl

/-- Actual integral-closure version of the base-extended norm on `U_L^n`.

This is the source map for the unramified norm product calculation; it
asserts only that the embedded norm remains in `U_L^n`. -/
noncomputable def principalUnitsNormExtensionSideOfIsIntegralClosure (K : Type u) (L : Type v)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [LocalFieldTheory.ValuativeExtension K L] (n : Nat) :
    principalUnits L n →* principalUnits L n where
  toFun u :=
    ⟨integerUnitsMapOfValuationExtension K L (normIntegerUnits K L u.1),
      LocalFieldTheory.integerUnitsMap_normIntegerUnits_mem_principalUnits K L u.2⟩
  map_one' := by
    apply Subtype.ext
    change integerUnitsMapOfValuationExtension K L (normIntegerUnits K L 1) = 1
    rw [map_one, map_one]
  map_mul' := by
    intro u v
    apply Subtype.ext
    change integerUnitsMapOfValuationExtension K L (normIntegerUnits K L (u.1 * v.1)) =
      integerUnitsMapOfValuationExtension K L (normIntegerUnits K L u.1) *
        integerUnitsMapOfValuationExtension K L (normIntegerUnits K L v.1)
    rw [map_mul, map_mul]

/-- States the theorem `principalUnitsNormExtensionSideOfIsIntegralClosure_apply`. -/
@[simp]
theorem principalUnitsNormExtensionSideOfIsIntegralClosure_apply (K : Type u) (L : Type v)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [LocalFieldTheory.ValuativeExtension K L]
    (n : Nat) (u : principalUnits L n) :
    ((principalUnitsNormExtensionSideOfIsIntegralClosure K L n u :
        principalUnits L n) : 𝒪[L]ˣ) =
      integerUnitsMapOfValuationExtension K L (normIntegerUnits K L u.1) :=
  rfl

/-- Actual integral-closure version: the base-extended norm on `U_L^n` is the
product of the actual integral-closure real Galois actions. -/
theorem principalUnitsNormExtensionSideOfIsIntegralClosure_eq_galoisGroup_prod
    (K : Type u) (L : Type v)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [LocalFieldTheory.ValuativeExtension K L]
    (n : Nat) (u : principalUnits L n) :
    principalUnitsNormExtensionSideOfIsIntegralClosure K L n u =
      Finset.univ.prod (fun σ : Gal(L / K) =>
        galoisGroupPrincipalUnitsMapEquivOfIsIntegralClosure K L n σ u) := by
  apply Subtype.ext
  simpa [principalUnitsNormExtensionSideOfIsIntegralClosure_apply,
    galoisGroupPrincipalUnitsMapEquivOfIsIntegralClosure_apply] using
    LocalFieldTheory.integerUnitsMap_normIntegerUnits_eq_prod_gal K L u.1

/-- Actual integral-closure version of the first-order norm-product
calculation before residue trace identification. -/
theorem
 principalUnitsNormExtensionSideOfIsIntegralClosure_oneAdd_sub_one_sub_sum_mem_maximalIdeal_pow_succ
    (K : Type u) (L : Type v) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [LocalFieldTheory.ValuativeExtension K L]
    (n : Nat) (hn : 1 ≤ n) (a : (𝓂[L] ^ n : Ideal 𝒪[L])) :
    (((principalUnitsNormExtensionSideOfIsIntegralClosure K L n
          (principalUnitOneAddOfMemPowSubgroup L hn (a : 𝒪[L]) a.2) :
        principalUnits L n) : 𝒪[L]ˣ) : 𝒪[L]) - 1 -
      (Finset.univ.sum fun σ : Gal(L / K) =>
        galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ (a : 𝒪[L])) ∈
        (𝓂[L] ^ (n + 1) : Ideal 𝒪[L]) := by
  classical
  rw [principalUnitsNormExtensionSideOfIsIntegralClosure_eq_galoisGroup_prod K L n
    (principalUnitOneAddOfMemPowSubgroup L hn (a : 𝒪[L]) a.2)]
  simpa [galoisGroupPrincipalUnitsMapEquivOfIsIntegralClosure,
    principalUnitsMapEquivOfIntegerRingEquiv,
    principalUnitOneAddOfMemPowSubgroup, principalUnitOneAddOfMemPow_val]
    using
      galoisGroup_prod_one_add_sub_one_sub_sum_mem_maximalIdeal_pow_succ_of_isIntegralClosure
        K L n hn a

/-- Actual integral-closure version of the base-extended norm on successive
principal-unit quotients. -/
def principalUnitsSuccQuotNormExtensionSideOfIsIntegralClosure (K : Type u) (L : Type v)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [LocalFieldTheory.ValuativeExtension K L] (n : Nat) :
    PrincipalUnitsSuccQuot L n →* PrincipalUnitsSuccQuot L n :=
  QuotientGroup.map
    ((principalUnits L (n + 1)).subgroupOf (principalUnits L n))
    ((principalUnits L (n + 1)).subgroupOf (principalUnits L n))
    (principalUnitsNormExtensionSideOfIsIntegralClosure K L n)
    (by
      intro u hu
      change ((principalUnitsNormExtensionSideOfIsIntegralClosure K L n u :
          principalUnits L n) : 𝒪[L]ˣ) ∈ principalUnits L (n + 1)
      simpa [principalUnitsNormExtensionSideOfIsIntegralClosure_apply] using
        LocalFieldTheory.integerUnitsMap_normIntegerUnits_mem_principalUnits K L hu)

/-- States the theorem `principalUnitsSuccQuotNormExtensionSideOfIsIntegralClosure_mk`. -/
@[simp]
theorem principalUnitsSuccQuotNormExtensionSideOfIsIntegralClosure_mk
    (K : Type u) (L : Type v)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [LocalFieldTheory.ValuativeExtension K L]
    (n : Nat) (u : principalUnits L n) :
    principalUnitsSuccQuotNormExtensionSideOfIsIntegralClosure K L n
        (QuotientGroup.mk u) =
      QuotientGroup.mk
        (principalUnitsNormExtensionSideOfIsIntegralClosure K L n u) :=
  rfl

/-- Actual integral-closure version: on `U_L^n/U_L^(n+1)`, the base-extended
norm is the product of the induced actual real Galois actions. -/
theorem principalUnitsSuccQuotNormExtensionSideOfIsIntegralClosure_eq_galoisGroup_prod
    (K : Type u) (L : Type v)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [LocalFieldTheory.ValuativeExtension K L]
    (n : Nat) (x : PrincipalUnitsSuccQuot L n) :
    principalUnitsSuccQuotNormExtensionSideOfIsIntegralClosure K L n x =
      Finset.univ.prod (fun σ : Gal(L / K) =>
        galoisGroupPrincipalUnitsSuccQuotMapEquivOfIsIntegralClosure K L n σ x) := by
  refine QuotientGroup.induction_on x ?_
  intro u
  rw [principalUnitsSuccQuotNormExtensionSideOfIsIntegralClosure_mk,
    principalUnitsNormExtensionSideOfIsIntegralClosure_eq_galoisGroup_prod]
  change (principalUnitsSuccQuotMk L n)
      (Finset.univ.prod (fun σ : Gal(L / K) =>
        galoisGroupPrincipalUnitsMapEquivOfIsIntegralClosure K L n σ u)) =
    Finset.univ.prod (fun σ : Gal(L / K) =>
      (principalUnitsSuccQuotMk L n)
        (galoisGroupPrincipalUnitsMapEquivOfIsIntegralClosure K L n σ u))
  exact map_prod (principalUnitsSuccQuotMk L n)
    (fun σ : Gal(L / K) =>
      galoisGroupPrincipalUnitsMapEquivOfIsIntegralClosure K L n σ u) Finset.univ

end LocalClassFieldTheory
