/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.HenselianResidueAction
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension

/-!
# Restriction of trivial Henselian residue actions

Trivial residue action remains trivial on an intermediate Galois extension
through the canonical residue-field maps of the chosen valuations.
-/

namespace RamificationTheory.HilbertRamification.ValuationSubring

open IsLocalRing

variable {K L Ω Γ Δ Θ : Type*} [Field K] [Field L] [Field Ω]
  [Algebra K L] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω]
  [IsGalois K L] [IsGalois K Ω]
  [LinearOrderedCommGroupWithZero Γ] [LinearOrderedCommGroupWithZero Δ]
  [LinearOrderedCommGroupWithZero Θ]
  (v : _root_.Valuation K Γ) (w : _root_.Valuation L Δ) (z : _root_.Valuation Ω Θ)
  [v.HasExtension w] [w.HasExtension z] [v.HasExtension z]
  [HenselianRing v.valuationSubring (maximalIdeal v.valuationSubring)]

/-- Trivial residue action remains trivial after restriction to an intermediate
Galois extension, with the canonical residue-field maps of the chosen valuations. -/
theorem henselianResidueAction_restrictNormal_eq_one
    (σ : Gal(Ω/K)) (hσ : henselianResidueAction v z σ = 1) :
    henselianResidueAction v w (σ.restrictNormal L) = 1 := by
  apply AlgEquiv.ext
  intro x
  obtain ⟨a, rfl⟩ := residue_surjective x
  rw [henselianResidueAction_residue]
  change residue w.valuationSubring
      ((henselianGalToDecomposition v w (σ.restrictNormal L)) • a) =
    residue w.valuationSubring a
  apply (ValuationTheory.DiscreteValuationField.Valuation.residue_algebraMap_eq_iff_of_hasExtension
    w z _ a).mp
  have heq : algebraMap w.valuationSubring z.valuationSubring
      ((henselianGalToDecomposition v w (σ.restrictNormal L)) • a) =
      (henselianGalToDecomposition v z σ) •
        algebraMap w.valuationSubring z.valuationSubring a := by
    apply Subtype.ext
    exact σ.restrictNormal_commutes L (a : L)
  rw [heq]
  have h := congrArg (fun τ => τ (residue z.valuationSubring
    (algebraMap w.valuationSubring z.valuationSubring a))) hσ
  exact h

end RamificationTheory.HilbertRamification.ValuationSubring
