/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.FieldTheory.Finite.Extension
public import Mathlib.FieldTheory.Galois.GaloisClosure
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Actual finite intermediate fields of each positive degree

These declarations are relocated, with their original names and bodies, from
`ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueAlgebraicClosureDegree`.
The native finite field extension is embedded into the specified algebraically
closed field, and its actual image has the original prescribed degree.
-/

@[expose] public section

namespace LocalClassFieldTheory

noncomputable section

universe u v

variable (k : Type u) [Field k] [Fintype k]
variable (Omega : Type v) [Field Omega] [Algebra k Omega] [IsAlgClosed Omega]

omit [Fintype k] in
/-- A finite field has prime characteristic. -/
theorem finiteResidueBaseRingCharPrime [Finite k] : Fact (ringChar k).Prime :=
  ⟨CharP.char_is_prime k (ringChar k)⟩

attribute [local instance] finiteResidueBaseRingCharPrime

/-- Embed the degree-`n` finite extension of `k` into the given residue
algebraic closure.  This choice is used only to prove that all profinite
coordinates are detected. -/
noncomputable def finiteResidueExtensionEmbeddingInto
    (n : ℕ) [NeZero n] :
    FiniteField.Extension k (ringChar k) n →ₐ[k] Omega := by
  letI : Module.IsTorsionFree k Omega :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (algebraMap k Omega).injective
  exact IsAlgClosed.lift (R := k)
    (S := FiniteField.Extension k (ringChar k) n) (M := Omega)

/-- The image of the degree-`n` finite extension in the given residue
algebraic closure. -/
noncomputable def finiteResidueIntermediateFieldIn
    (n : ℕ) [NeZero n] : IntermediateField k Omega :=
  (⊤ : IntermediateField k
      (FiniteField.Extension k (ringChar k) n)).map
    (finiteResidueExtensionEmbeddingInto k Omega n)

/-- The model finite field is canonically isomorphic to its embedded image. -/
noncomputable def finiteResidueExtensionEquivIntermediateIn
    (n : ℕ) [NeZero n] :
    FiniteField.Extension k (ringChar k) n ≃ₐ[k]
      finiteResidueIntermediateFieldIn k Omega n :=
  IntermediateField.topEquiv.symm.trans
    (IntermediateField.equivMap ⊤
      (finiteResidueExtensionEmbeddingInto k Omega n))

/-- An actual degree-`n` finite Galois intermediate field in any residue
algebraic closure. -/
noncomputable def finiteResidueGaloisIntermediateFieldIn
    (n : ℕ) [NeZero n] : FiniteGaloisIntermediateField k Omega where
  toIntermediateField := finiteResidueIntermediateFieldIn k Omega n
  finiteDimensional := Module.Finite.equiv
    (finiteResidueExtensionEquivIntermediateIn k Omega n).toLinearEquiv
  isGalois := IsGalois.of_algEquiv
    (finiteResidueExtensionEquivIntermediateIn k Omega n)

/-- States the theorem `finrank_finiteResidueGaloisIntermediateFieldIn`. -/
@[simp]
theorem finrank_finiteResidueGaloisIntermediateFieldIn
    (n : ℕ) [NeZero n] :
    Module.finrank k
        (finiteResidueGaloisIntermediateFieldIn k Omega n) = n := by
  calc
    Module.finrank k
        (finiteResidueGaloisIntermediateFieldIn k Omega n) =
        Module.finrank k
          (FiniteField.Extension k (ringChar k) n) :=
      (finiteResidueExtensionEquivIntermediateIn k Omega n).toLinearEquiv.finrank_eq.symm
    _ = n := FiniteField.finrank_extension k (ringChar k) n

end

end LocalClassFieldTheory
