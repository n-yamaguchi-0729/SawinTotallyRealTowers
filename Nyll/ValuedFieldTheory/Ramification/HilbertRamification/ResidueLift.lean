/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence

/-!
# Lifting residue automorphisms through a decomposition group

For a chosen valuation on a Galois extension, every automorphism of its
residue field over the residue field of the decomposition field lifts to an
ambient Galois automorphism stabilizing the chosen valuation.  This is the
elementwise form of the residue-action exact sequence.
-/

noncomputable section

universe u v

namespace RamificationTheory.HilbertRamification.ValuationSubring

variable (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
variable [IsGalois K L]

/-- Every residue-field automorphism over the residue field of the
decomposition field is induced by an ambient Galois automorphism stabilizing
the selected valuation ring. -/
theorem exists_galoisAutomorphism_stabilizing_of_residueAutomorphism
    (A : _root_.ValuationSubring L)
    (tau : selectedResidueField A ≃ₐ[decompositionResidueField K A]
      selectedResidueField A) :
    ∃ sigma : L ≃ₐ[K] L,
      ∃ hsigma : sigma ∈ decompositionGroup K A,
        decompositionGroupResidueAction (K := K) A ⟨sigma, hsigma⟩ = tau := by
  obtain ⟨sigma, hsigma⟩ :=
    decompositionGroupResidueAction_surjective (K := K) A tau
  exact ⟨sigma, sigma.property, hsigma⟩

end RamificationTheory.HilbertRamification.ValuationSubring
