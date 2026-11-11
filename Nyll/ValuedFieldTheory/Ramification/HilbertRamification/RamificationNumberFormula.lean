/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ValuedFieldTheory.Ramification.Herbrand.DepthSum
public import Mathlib.SetTheory.Cardinal.Finite
public import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.RamificationNumber
public import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.HerbrandFunction

/-!
# Herbrand-function sum formula for a general discretely valued field

This is the field-facing, noncomplete form of
the Herbrand-function sum formula.  The monogenic integral-generator theorem
supplies the generator hidden inside
`intrinsicRamificationNumberOfUniqueExtension`; the public endpoint therefore
uses exactly the canonical standing hypotheses and has no generator parameter.
-/



@[expose] public section

noncomputable section

universe u v w x

namespace RamificationTheory.HilbertRamification
namespace Higher


variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
variable {base : ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
variable {target : ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
variable [FiniteDimensional K L] [base.valuation.HasExtension target.valuation]
variable [IsGalois K L]
variable [Algebra.IsSeparable base.residueField target.residueField]

local instance galoisFintype : Fintype Gal(L/K) :=
  Fintype.ofFinite Gal(L/K)

local instance subgroupFintype (H : Subgroup Gal(L/K)) : Fintype H :=
  Fintype.ofFinite H

local instance subgroupMembershipDecidable
    (H : Subgroup Gal(L/K)) (sigma : Gal(L/K)) : Decidable (sigma ∈ H) :=
  Classical.propDecidable _

open _root_.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration (
  truncatedLowerDepth
) in
/-- Pointwise ramification-number contribution for an element of inertia. -/
theorem truncate_intrinsicRamificationNumberOfUniqueExtension_eq_intrinsic_summand
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (m : ℕ) {s : ℝ} (hms : (m : ℝ) ≤ s) (hsm : s ≤ m + 1)
    (sigma : (lowerRamificationFiltrationOfUniqueExtension
      (base := base) (target := target) huniq).lower 0) :
    truncateENatAtDVF
        (intrinsicRamificationNumberOfUniqueExtension
          (base := base) (target := target) huniq (sigma : Gal(L/K)))
        (s + 1) =
      1 + ((truncatedLowerDepth (lowerRamificationFiltrationOfUniqueExtension (base := base)
        (target := target) huniq)) m sigma : ℝ) +
      (s - m) *
        (if (sigma : Gal(L/K)) ∈ (lowerRamificationFiltrationOfUniqueExtension
          (base := base) (target := target) huniq).lower (m + 1)
        then 1 else 0) :=
  truncate_depth_eq_intrinsic_summand_of_mem
    (lowerRamificationFiltrationOfUniqueExtension (base := base) (target := target) huniq)
    (intrinsicRamificationNumberOfUniqueExtension (base := base) (target := target) huniq)
    (fun n sigma =>
      mem_lowerRamificationGroup_nat_iff_intrinsicRamificationNumberOfUniqueExtension_ge
        (base := base) (target := target) huniq n sigma)
    m hms hsm sigma

/-- States the theorem
`truncate_intrinsicRamificationNumberOfUniqueExtension_eq_zero_of_not_mem_inertia`. -/
theorem truncate_intrinsicRamificationNumberOfUniqueExtension_eq_zero_of_not_mem_inertia
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    {s : ℝ} (hs : -1 ≤ s) {sigma : Gal(L/K)}
    (hsigma : sigma ∉ (lowerRamificationFiltrationOfUniqueExtension
      (base := base) (target := target) huniq).lower 0) :
    truncateENatAtDVF
        (intrinsicRamificationNumberOfUniqueExtension
          (base := base) (target := target) huniq sigma) (s + 1) = 0 :=
  truncate_depth_eq_zero_of_not_mem_lower_zero
    (lowerRamificationFiltrationOfUniqueExtension (base := base) (target := target) huniq)
    (intrinsicRamificationNumberOfUniqueExtension (base := base) (target := target) huniq)
    (fun n sigma =>
      mem_lowerRamificationGroup_nat_iff_intrinsicRamificationNumberOfUniqueExtension_ge
        (base := base) (target := target) huniq n sigma)
    hs hsigma

/-- States the theorem
`sum_truncate_intrinsicRamificationNumberOfUniqueExtension_eq_sum_inertia`. -/
theorem sum_truncate_intrinsicRamificationNumberOfUniqueExtension_eq_sum_inertia
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    {s : ℝ} (hs : -1 ≤ s) :
    (∑ sigma : Gal(L/K), truncateENatAtDVF
      (intrinsicRamificationNumberOfUniqueExtension
        (base := base) (target := target) huniq sigma) (s + 1)) =
    ∑ sigma : (lowerRamificationFiltrationOfUniqueExtension
        (base := base) (target := target) huniq).lower 0,
      truncateENatAtDVF
        (intrinsicRamificationNumberOfUniqueExtension
          (base := base) (target := target) huniq (sigma : Gal(L/K))) (s + 1) :=
  sum_truncate_depth_eq_sum_lower_zero_of_mem
    (lowerRamificationFiltrationOfUniqueExtension (base := base) (target := target) huniq)
    (intrinsicRamificationNumberOfUniqueExtension (base := base) (target := target) huniq)
    (fun n sigma =>
      mem_lowerRamificationGroup_nat_iff_intrinsicRamificationNumberOfUniqueExtension_ge
        (base := base) (target := target) huniq n sigma)
    hs

open _root_.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration (
  card_lower_succ_eq_sum_indicator
  truncatedLowerDepth
) in
/-- States the theorem
`sum_inertia_truncate_intrinsicRamificationNumberOfUniqueExtension_eq_intrinsic`. -/
theorem sum_inertia_truncate_intrinsicRamificationNumberOfUniqueExtension_eq_intrinsic
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (m : ℕ) {s : ℝ} (hms : (m : ℝ) ≤ s) (hsm : s ≤ m + 1) :
    (∑ sigma : (lowerRamificationFiltrationOfUniqueExtension
        (base := base) (target := target) huniq).lower 0,
      truncateENatAtDVF
        (intrinsicRamificationNumberOfUniqueExtension
          (base := base) (target := target) huniq (sigma : Gal(L/K))) (s + 1)) =
      Nat.card ((lowerRamificationFiltrationOfUniqueExtension
        (base := base) (target := target) huniq).lower 0) +
      (∑ sigma : (lowerRamificationFiltrationOfUniqueExtension
          (base := base) (target := target) huniq).lower 0,
        ((truncatedLowerDepth (lowerRamificationFiltrationOfUniqueExtension (base := base)
          (target := target) huniq)) m sigma : ℝ)) +
      (s - m) * Nat.card ((lowerRamificationFiltrationOfUniqueExtension
        (base := base) (target := target) huniq).lower (m + 1)) :=
  sum_lower_zero_truncate_depth_eq_intrinsic_of_mem
    (lowerRamificationFiltrationOfUniqueExtension (base := base) (target := target) huniq)
    (intrinsicRamificationNumberOfUniqueExtension (base := base) (target := target) huniq)
    (fun n sigma =>
      mem_lowerRamificationGroup_nat_iff_intrinsicRamificationNumberOfUniqueExtension_ge
        (base := base) (target := target) huniq n sigma)
    m hms hsm

open _root_.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration (
  herbrandFunction
  herbrandFunction_eq_depth_sum_of_mem_Icc
  herbrandFunction_of_nonpos
) in
/-- The Herbrand-function sum formula under the stated discretely valued field
assumptions.  The generator from the monogenic integral-generator theorem is internal to the
canonical
ramification number, so this endpoint has no generator hypothesis. -/
theorem herbrandFunctionOfUniqueExtension_eq_intrinsicRamificationNumber_sum
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    {s : ℝ} (hs : -1 ≤ s) :
    herbrandFunctionOfUniqueExtension
        (base := base) (target := target) huniq s =
      (1 / Nat.card ((lowerRamificationFiltrationOfUniqueExtension
        (base := base) (target := target) huniq).lower 0) : ℝ) *
        (∑ sigma : Gal(L/K), truncateENatAtDVF
          (intrinsicRamificationNumberOfUniqueExtension
            (base := base) (target := target) huniq sigma) (s + 1)) - 1 :=
  herbrandFunction_eq_depth_sum_of_mem
    (lowerRamificationFiltrationOfUniqueExtension (base := base) (target := target) huniq)
    (intrinsicRamificationNumberOfUniqueExtension (base := base) (target := target) huniq)
    (fun n sigma =>
      mem_lowerRamificationGroup_nat_iff_intrinsicRamificationNumberOfUniqueExtension_ge
        (base := base) (target := target) huniq n sigma)
    hs

end Higher
end RamificationTheory.HilbertRamification
