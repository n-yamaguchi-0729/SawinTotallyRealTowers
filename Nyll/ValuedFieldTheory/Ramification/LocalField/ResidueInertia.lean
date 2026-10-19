/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Ramification.LocalField.Core
import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.GaloisIntegerRing
import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueGalois

/-!
# Local inertia as the kernel of the actual residue action

This comparison uses the canonical integer ring of the given local field,
and identifies it with the valuation ring used by the existing filtration.
-/

noncomputable section

namespace RamificationTheory.LocalField

open LocalFieldTheory RamificationTheory RamificationTheory.HilbertRamification
open RamificationTheory.HilbertRamification.Higher
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension
open scoped ValuativeRel

/-- The zeroth lower group is the kernel of the actual residue-field action,
with the canonical integer ring of the given extension field. -/
theorem localLowerRamificationGroup_zero_eq_residue_ker
    (K L : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]] :
    localLowerRamificationGroup K L 0 =
      (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker := by
  let base := localCompleteDVF K
  let target := localCompleteDVF L
  let chosenTarget := chosenLocalExtensionCompleteDVF K L
  let hExtTarget : base.valuation.HasExtension target.valuation := by
    change (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)
    infer_instance
  let huniqChosen :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension
        base.toDVF chosenTarget.toDVF :=
    chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension K L
  let huniqTarget :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension
        base.toDVF target.toDVF :=
    hasUniqueValuationExtension_of_finite_separable base target
  have hvaluationSubring :
      chosenTarget.valuation.valuationSubring = target.valuation.valuationSubring := by
    rw [← _root_.Valuation.isEquiv_iff_valuationSubring]
    exact chosenLocalExtensionCompleteDVF_hasUniqueValuationExtension K L target.valuation
  change lowerRamificationGroup
    (base := base.toDVF) (target := chosenTarget.toDVF) huniqChosen 0 = _
  rw [lowerRamificationGroup_eq_of_valuationSubring_eq
    huniqChosen huniqTarget hvaluationSubring 0]
  have hInteger : target.valuation.valuationSubring.toSubring =
      (ValuativeRel.valuation L).integer := rfl
  let eInteger : target.valuationSubring ≃+* 𝒪[L] :=
    RingEquiv.subringCongr hInteger
  have hmap (σ : Gal(L/K)) (a : target.valuationSubring) :
      eInteger (valuationSubringAutOfUniqueExtension
        (base := base.toDVF) (target := target.toDVF) huniqTarget σ a - a) =
      galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ (eInteger a) - eInteger a := by
    apply Subtype.ext
    rfl
  have hmem (a : target.valuationSubring) :
      eInteger a ∈ (𝓂[L] : Ideal 𝒪[L]) ↔ a ∈ target.maximalIdeal := by
    rw [IsLocalRing.mem_maximalIdeal, map_mem_nonunits_iff eInteger,
      ← IsLocalRing.mem_maximalIdeal]
  apply Subgroup.ext
  intro σ
  rw [galoisGroupResidueAlgEquivHomOfIsIntegralClosure_mem_ker_iff_sub_mem_maximalIdeal]
  have hlower := mem_lowerRamificationGroup_nat_iff
    (base := base.toDVF) (target := target.toDVF) huniqTarget 0 σ
  simp only [Nat.cast_zero, Nat.zero_add, pow_one] at hlower
  rw [hlower]
  constructor
  · intro h x
    obtain ⟨a, rfl⟩ := eInteger.surjective x
    rw [← hmap, hmem]
    exact h a
  · intro h a
    apply (hmem _).mp
    rw [hmap]
    exact h (eInteger a)

/-- Upper inertia is the kernel of the canonical residue action. -/
theorem localUpperRamificationGroup_zero_eq_residue_ker
    (K L : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]] :
    localUpperRamificationGroup K L 0 =
      (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker := by
  rw [localUpperRamificationGroup_eq_localLowerRamificationGroup_of_nonpos
    K L 0 le_rfl, localLowerRamificationGroup_zero_eq_residue_ker]

end RamificationTheory.LocalField
