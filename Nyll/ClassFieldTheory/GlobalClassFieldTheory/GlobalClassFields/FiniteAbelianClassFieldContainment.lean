/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.NumberFieldNormResidue
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.NormTowerConductor
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.OrderReversal

/-!
# Containment of finite abelian class fields

For actual finite abelian extensions of a number field, containment is
exactly reverse containment of their genuine idèle-class norm ranges.

The fixing subgroups are computed in the separable closure of the original
number field, using the same standard norm ranges as finite reciprocity.
-/



@[expose] public section

universe u v w

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open ClassFormation
open LocalClassFieldTheory
open NumberField
open RamificationTheory
open Reciprocity

variable {K : Type u} [Field K] [NumberField K]

/-- The abstract finite abelian subextension of the original separable closure. -/
noncomputable def numberFieldAbelianSubextensionOfEmbedding
    (L : Type v) [Field L] [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
    (i : L →ₐ[K] SeparableClosure K) :
    FiniteAbelianSubextension (baseField Gal(SeparableClosure K/K)) where
  toFiniteGaloisExtension := standardNumberFieldGaloisSubextensionOfEmbedding K L i
  commutative := by
    let M := finiteAbelianAbstractExtensionOfEmbedding K L i
    have hBase : intrinsicAbstractBase K = baseField Gal(SeparableClosure K/K) :=
      closedFixingSubgroup_bot_eq_baseField K (SeparableClosure K)
    have commutativeOfField {B : ClosedSubgroup Gal(SeparableClosure K/K)}
        (hB : intrinsicAbstractBase K = B) (J : FiniteGaloisSubextension B)
        (hJ : J.field = M.field) : IsMulCommutative J.extensionQuotient := by
      subst B
      have h : J = M.toFiniteGaloisExtension := FiniteGaloisSubextension.ext hJ
      exact h.symm ▸ M.commutative
    exact commutativeOfField hBase _ rfl

/-- An algebra embedding of finite extensions reverses inclusion of
their genuine idèle-class norm ranges. -/
theorem ideleClassNorm_range_le_of_algHom
    (L₁ : Type v) (L₂ : Type w)
    [Field L₁] [NumberField L₁]
    [Field L₂] [NumberField L₂]
    [Algebra K L₁] [Algebra K L₂]
    [FiniteDimensional K L₁] [FiniteDimensional K L₂]
    [IsAbelianGalois K L₁] [IsAbelianGalois K L₂]
    (f : L₁ →ₐ[K] L₂) :
    (_root_.ideleClassNorm K L₂).range ≤
      (_root_.ideleClassNorm K L₁).range := by
  let : Algebra L₁ L₂ :=
    f.toRingHom.toAlgebra
  let : IsScalarTower K L₁ L₂ :=
    IsScalarTower.of_algebraMap_eq fun x => by
      exact (f.commutes x).symm
  let : FiniteDimensional L₁ L₂ :=
    FiniteDimensional.right K L₁ L₂
  exact
    ideleClassNorm_range_le_of_tower
      (K := K) (M := L₁) (L := L₂)

/-- Reverse inclusion of genuine idèle-class norm ranges constructs an
actual algebra embedding of the corresponding finite abelian
extensions over the original base field. -/
noncomputable def finiteAbelianExtensionEmbeddingOfNormRangeLE
    (L₁ : Type v) (L₂ : Type w)
    [Field L₁] [NumberField L₁]
    [Field L₂] [NumberField L₂]
    [Algebra K L₁] [Algebra K L₂]
    [FiniteDimensional K L₁] [FiniteDimensional K L₂]
    [IsAbelianGalois K L₁] [IsAbelianGalois K L₂]
    (h :
      (_root_.ideleClassNorm K L₂).range ≤
        (_root_.ideleClassNorm K L₁).range) :
    L₁ →ₐ[K] L₂ := by
  let i₁ := AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K L₁
  let i₂ := AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K L₂
  let J₁ := numberFieldAbelianSubextensionOfEmbedding L₁ i₁
  let J₂ := numberFieldAbelianSubextensionOfEmbedding L₂ i₂
  let e := ideleClassEquivBaseFixed K
  have h₁ : J₁.normSubgroup (ideleClassRepresentation K) =
      (_root_.ideleClassNorm K L₁).range.toAddSubgroup.map e.toAddMonoidHom :=
    standardNumberFieldGaloisSubextensionOfEmbedding_normSubgroup K L₁ i₁
  have h₂ : J₂.normSubgroup (ideleClassRepresentation K) =
      (_root_.ideleClassNorm K L₂).range.toAddSubgroup.map e.toAddMonoidHom :=
    standardNumberFieldGaloisSubextensionOfEmbedding_normSubgroup K L₂ i₂
  have hNorm : J₂.normSubgroup (ideleClassRepresentation K) ≤
      J₁.normSubgroup (ideleClassRepresentation K) := by
    rw [h₂, h₁]
    exact AddSubgroup.map_mono h
  have hOrder : J₁ ≤ J₂ :=
    (FiniteAbelianSubextension.le_iff_normSubgroup_le
      (numberFieldCyclotomicIdeleClassValuationData K)
      (ideleClassRepresentation_satisfiesClassFieldAxiom K)
      (FiniteAbstractField.base Gal(SeparableClosure K/K)) J₁ J₂).2 hNorm
  have hRange : i₁.fieldRange ≤ i₂.fieldRange := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup i₂.fieldRange]
    apply (IntermediateField.le_fixedField_iff_le_fixingSubgroup
      i₂.fieldRange.fixingSubgroup i₁.fieldRange).2
    exact hOrder
  exact i₂.equivFieldRange.symm.toAlgHom.comp
    ((IntermediateField.inclusion hRange).comp i₁.equivFieldRange.toAlgHom)

/-- Reverse norm-range inclusion implies actual field containment over
the original number field. -/
theorem finiteAbelianExtension_nonempty_algHom_of_normRange_le
    (L₁ : Type v) (L₂ : Type w)
    [Field L₁] [NumberField L₁]
    [Field L₂] [NumberField L₂]
    [Algebra K L₁] [Algebra K L₂]
    [FiniteDimensional K L₁] [FiniteDimensional K L₂]
    [IsAbelianGalois K L₁] [IsAbelianGalois K L₂]
    (h :
      (_root_.ideleClassNorm K L₂).range ≤
        (_root_.ideleClassNorm K L₁).range) :
    Nonempty (L₁ →ₐ[K] L₂) :=
  ⟨finiteAbelianExtensionEmbeddingOfNormRangeLE
    (K := K) L₁ L₂ h⟩

/-- Actual containment of finite abelian extensions is equivalent to
reverse inclusion of their genuine idèle-class norm ranges. -/
theorem nonempty_algHom_iff_ideleClassNorm_range_le
    (L₁ : Type v) (L₂ : Type w)
    [Field L₁] [NumberField L₁]
    [Field L₂] [NumberField L₂]
    [Algebra K L₁] [Algebra K L₂]
    [FiniteDimensional K L₁] [FiniteDimensional K L₂]
    [IsAbelianGalois K L₁] [IsAbelianGalois K L₂] :
    Nonempty (L₁ →ₐ[K] L₂) ↔
      (_root_.ideleClassNorm K L₂).range ≤
        (_root_.ideleClassNorm K L₁).range := by
  constructor
  · rintro ⟨f⟩
    exact
      ideleClassNorm_range_le_of_algHom
        (K := K) L₁ L₂ f
  · exact
      finiteAbelianExtension_nonempty_algHom_of_normRange_le
        (K := K) L₁ L₂

/-- Equality of genuine norm ranges characterizes isomorphism of
finite abelian extensions over the original number field. -/
theorem nonempty_algEquiv_iff_ideleClassNorm_range_eq
    (L₁ : Type v) (L₂ : Type w)
    [Field L₁] [NumberField L₁]
    [Field L₂] [NumberField L₂]
    [Algebra K L₁] [Algebra K L₂]
    [FiniteDimensional K L₁] [FiniteDimensional K L₂]
    [IsAbelianGalois K L₁] [IsAbelianGalois K L₂] :
    Nonempty (L₁ ≃ₐ[K] L₂) ↔
      (_root_.ideleClassNorm K L₁).range =
        (_root_.ideleClassNorm K L₂).range := by
  constructor
  · rintro ⟨e⟩
    apply le_antisymm
    · exact
        ideleClassNorm_range_le_of_algHom
          (K := K) L₂ L₁ e.symm.toAlgHom
    · exact
        ideleClassNorm_range_le_of_algHom
          (K := K) L₁ L₂ e.toAlgHom
  · intro h
    let f :
        L₁ →ₐ[K] L₂ :=
      finiteAbelianExtensionEmbeddingOfNormRangeLE
        (K := K) L₁ L₂ h.symm.le
    let g : L₂ →ₐ[K] L₁ := finiteAbelianExtensionEmbeddingOfNormRangeLE (K := K) L₂ L₁ h.le
    have hdim : Module.finrank K L₁ = Module.finrank K L₂ :=
      le_antisymm (f.toLinearMap.finrank_le_finrank_of_injective f.injective)
        (g.toLinearMap.finrank_le_finrank_of_injective g.injective)
    have hsurjective :
        Function.Surjective f :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        hdim (f := f.toLinearMap)).mp f.injective
    exact
      ⟨AlgEquiv.ofBijective f
        ⟨f.injective, hsurjective⟩⟩

end GlobalClassFields
end GlobalClassFieldTheory
