/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Cyclotomic intermediate fields inside an algebraic closure

A primitive root in the given closure generates an actual cyclotomic
intermediate field. The characteristic only needs to avoid the root order.
-/

namespace ValuationTheory.DiscreteValuationField

/-- An algebraic closure contains a cyclotomic intermediate field whenever
the root order is nonzero in the base field. -/
theorem exists_cyclotomic_intermediateField
    (K Ω : Type*) [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (n : ℕ) [NeZero (n : K)] :
    ∃ E : IntermediateField K Ω, IsCyclotomicExtension {n} K E := by
  have : NeZero n := .of_neZero_natCast K
  have : NeZero (n : Ω) := by
    simpa only [map_natCast] using
      (‹NeZero (n : K)›.of_injective (algebraMap K Ω).injective)
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω n
  exact ⟨IntermediateField.adjoin K {ζ},
    hζ.intermediateField_adjoin_isCyclotomicExtension K⟩

end ValuationTheory.DiscreteValuationField
