/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.FiniteAbelianCompositum
public import Nyll.ClassFieldTheory.Algebra.NormalEmbeddingRange
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ConcreteReciprocityTransport
public import Nyll.ClassFieldTheory.Algebra.FiniteAbstractFixedField
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.SeparableClosureEmbedding

/-!
# Compatible presentations in the separable closure

Normality makes the fixed field attached to a finite Galois extension
independent of its embedding. Compatible embeddings give compatible
isomorphisms with these fixed fields.
-/

@[expose] public section

noncomputable section

universe u v w

namespace FunctionField

open ClassFormation LocalClassFieldTheory

variable (K : Type u) [Field K]

/-- The base fixed field in the separable closure is the original base field. -/
def finiteGaloisBaseFixedFieldEquiv :
    K ≃ₐ[K] abstractFixedField K (SeparableClosure K) (intrinsicFiniteAbstractBase K).field :=
  (IntermediateField.botEquiv K (SeparableClosure K)).symm.trans
    (IntermediateField.equivOfEq (InfiniteGalois.fixedField_fixingSubgroup ⊥).symm)

variable (L : Type v) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- The chosen embedding identifies the extension with the field fixed by its
own concrete fixing subgroup. -/
def finiteGaloisEmbeddedFixedFieldEquiv (i : L →ₐ[K] SeparableClosure K) :
    L ≃ₐ[K] abstractFixedField K (SeparableClosure K)
      (finiteGaloisAbstractExtensionOfEmbedding K L i).field :=
  (finiteGaloisFieldRangeEquivOfEmbedding K L i).trans
    (IntermediateField.equivOfEq (InfiniteGalois.fixedField_fixingSubgroup
      (finiteGaloisFieldRangeOfEmbedding K L i)).symm)

/-- An explicit embedding identifies a Galois extension with its canonical fixed field. -/
def finiteGaloisFixedFieldEquivOfEmbedding (i : L →ₐ[K] SeparableClosure K) :
    L ≃ₐ[K] abstractFixedField K (SeparableClosure K) (finiteGaloisAbstractExtension K L).field :=
  (finiteGaloisFieldRangeEquivOfEmbedding K L i).trans
    (IntermediateField.equivOfEq
      ((InfiniteGalois.fixedField_fixingSubgroup
          (AlgebraicNumberTheory.finiteGaloisFieldRange K L)).trans
        (AlgHom.fieldRange_eq_of_normal
          (AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K L) i)).symm)

/-- The fixed-field isomorphism has exactly the chosen ambient embedding as its value. -/
theorem finiteGaloisFixedFieldEquivOfEmbedding_val
    (i : L →ₐ[K] SeparableClosure K) (x : L) :
    (finiteGaloisFixedFieldEquivOfEmbedding K L i x : SeparableClosure K) = i x := rfl

variable (M : Type w) [Field M] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [FiniteDimensional K M] [IsGalois K M]

/-- A tower of finite Galois fields gives the reversed inclusion of their fixing subgroups. -/
theorem finiteGaloisAbstractExtension_le_of_tower :
    (finiteGaloisAbstractExtension K M).field.toSubgroup ≤
      (finiteGaloisAbstractExtension K L).field.toSubgroup := by
  let i := AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K M
  let j := AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K L
  change i.fieldRange.fixingSubgroup ≤ j.fieldRange.fixingSubgroup
  rw [AlgHom.fieldRange_eq_of_normal j (i.comp (IsScalarTower.toAlgHom K L M))]
  apply IntermediateField.fixingSubgroup_le
  rintro x ⟨y, rfl⟩
  exact ⟨algebraMap L M y, rfl⟩

/-- Compatible embeddings yield a commuting square of the actual fixed-field inclusions. -/
theorem finiteGaloisFixedFieldEquivOfEmbedding_tower
    (i : M →ₐ[K] SeparableClosure K) (x : L) :
    finiteGaloisFixedFieldEquivOfEmbedding K M i (algebraMap L M x) =
      IntermediateField.inclusion
        (abstractFixedField_le K (SeparableClosure K)
          (finiteGaloisAbstractExtension_le_of_tower K L M))
        (finiteGaloisFixedFieldEquivOfEmbedding K L
          (i.comp (IsScalarTower.toAlgHom K L M)) x) := by
  apply Subtype.ext
  rfl

end FunctionField
