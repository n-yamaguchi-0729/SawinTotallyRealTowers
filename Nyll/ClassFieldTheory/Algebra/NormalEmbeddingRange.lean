/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.FieldTheory.Galois.GaloisClosure

/-!
# Equality of normal field realizations

All embeddings of a normal extension into the same ambient field have the
same field range. This separates independence of the embedded subfield
from independence of its chosen parameterization.
-/

@[expose] public section

noncomputable section

namespace AlgHom

/-- The field range of an embedding of a finite Galois extension, bundled
with its inherited finiteness and Galois structure. -/
def finiteGaloisFieldRange {K L Ω : Type*} [Field K] [Field L] [Field Ω]
    [Algebra K L] [Algebra K Ω] [FiniteDimensional K L] [IsGalois K L]
    (i : L →ₐ[K] Ω) : FiniteGaloisIntermediateField K Ω where
  toIntermediateField := i.fieldRange
  finiteDimensional := i.equivFieldRange.toLinearEquiv.finiteDimensional
  isGalois := IsGalois.of_algEquiv i.equivFieldRange

/-- Two embeddings of a normal extension have the same intermediate-field image. -/
theorem fieldRange_eq_of_normal
    {K L Ω : Type*} [Field K] [Field L] [Field Ω]
    [Algebra K L] [Algebra K Ω] [Normal K L] (i j : L →ₐ[K] Ω) : i.fieldRange = j.fieldRange := by
  let e : L ≃ₐ[K] i.fieldRange := AlgEquiv.ofInjectiveField i
  have hnormal : Normal K i.fieldRange := Normal.of_algEquiv e
  have h := AlgHom.fieldRange_of_normal (j.comp e.symm.toAlgHom)
  rw [← AlgHom.map_fieldRange, AlgEquiv.fieldRange_eq_top, ← AlgHom.fieldRange_eq_map] at h
  exact h.symm

end AlgHom

namespace ClassFieldTheory

variable {K L Ω : Type*} [Field K] [Field L] [Field Ω]
    [Algebra K L] [Algebra K Ω] [Normal K L]

/-- Two realizations of a normal extension differ by an automorphism of that extension. -/
theorem exists_embedding_comp_aut_eq_of_normal (i j : L →ₐ[K] Ω) :
    ∃ σ : Gal(L/K), ∀ x : L, j (σ x) = i x := by
  let e := IntermediateField.equivOfEq (AlgHom.fieldRange_eq_of_normal i j)
  refine ⟨(i.equivFieldRange.trans e).trans j.equivFieldRange.symm, fun x => ?_⟩
  exact congrArg Subtype.val (j.equivFieldRange.apply_symm_apply (e (i.equivFieldRange x)))

end ClassFieldTheory
