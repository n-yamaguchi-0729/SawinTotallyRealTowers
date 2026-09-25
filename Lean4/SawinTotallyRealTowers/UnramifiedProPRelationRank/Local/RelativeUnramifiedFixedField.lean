/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields
import ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius
import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ValuationContinuity
import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField
import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteResidueFinrankTransfer
import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum
import Mathlib.Algebra.Algebra.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteUnramified
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueExtension

set_option autoImplicit false

namespace LocalClassFieldTheory

open scoped ValuativeRel
open ClassFormation LocalFieldTheory CyclicCohomology
open LocalFieldTheory.IsNonarchimedeanLocalField

noncomputable section

private theorem valuationInteger_scalarTower
    (A B C : Type) [Field A] [Field B] [Field C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [ValuativeRel A] [ValuativeRel B] [ValuativeRel C]
    [Valuation.HasExtension (ValuativeRel.valuation A) (ValuativeRel.valuation B)]
    [Valuation.HasExtension (ValuativeRel.valuation B) (ValuativeRel.valuation C)]
    [Valuation.HasExtension (ValuativeRel.valuation A) (ValuativeRel.valuation C)] :
    IsScalarTower 𝒪[A] 𝒪[B] 𝒪[C] := by
  apply IsScalarTower.of_algebraMap_eq'
  ext x
  exact IsScalarTower.algebraMap_apply A B C (x : A)

private theorem valuationResidue_scalarTower
    (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [IsLocalRing A] [IsLocalRing B] [IsLocalRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap B C)]
    [IsLocalHom (algebraMap A C)] :
    IsScalarTower (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)
      (IsLocalRing.ResidueField C) := inferInstance

private theorem valuationResidue_finrank_mul
    (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [IsLocalRing A] [IsLocalRing B] [IsLocalRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap B C)]
    [IsLocalHom (algebraMap A C)] :
    (@Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) _ _
      (IsLocalRing.ResidueField.instModule (R := A) (S := B))) *
    (@Module.finrank (IsLocalRing.ResidueField B) (IsLocalRing.ResidueField C) _ _
      (IsLocalRing.ResidueField.instModule (R := B) (S := C))) =
    (@Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField C) _ _
      (IsLocalRing.ResidueField.instModule (R := A) (S := C))) :=
  @Module.finrank_mul_finrank
    (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) (IsLocalRing.ResidueField C)
    _ _ _
    (IsLocalRing.ResidueField.instModule (R := A) (S := B))
    (IsLocalRing.ResidueField.instModule (R := B) (S := C))
    (IsLocalRing.ResidueField.instModule (R := A) (S := C))
    (valuationResidue_scalarTower A B C) _ _ _ _

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The canonical unramified degree kernel over an absolutely finite field,
with finiteness of its upper endpoint obtained from the actual quotient tower. -/
abbrev relativeUnramifiedFiniteExtension
    (H : FiniteAbstractField (Gal(SeparableClosure K / K)))
    (m : ℕ) (hm : 0 < m) :
    FiniteAbstractFieldExtension (Gal(SeparableClosure K / K)) := by
  let U := (localResidueDatum K).finiteUnramifiedExtension
    (H.toFiniteResidueAbstractField (localResidueDatum K)) m hm
  have : Finite (H.field.toSubgroup ⧸
      extensionSubgroup H.field U.field U.below) := U.finite
  exact FiniteAbstractFieldExtension.ofInclusion U.field H U.below

/-- The actual fixed field, retained in the original K-separable closure. -/
abbrev relativeUnramifiedFixedField
    (H : FiniteAbstractField (Gal(SeparableClosure K / K)))
    (m : ℕ) (hm : 0 < m) : IntermediateField K (SeparableClosure K) :=
  abstractFixedField K (SeparableClosure K)
    (relativeUnramifiedFiniteExtension K H m hm).field.field

/-- The canonical inclusion of the lower fixed field in the unramified field. -/
def relativeUnramifiedFixedField_inclusion
    (H : FiniteAbstractField (Gal(SeparableClosure K / K)))
    (m : ℕ) (hm : 0 < m) :
    abstractFixedField K (SeparableClosure K) H.field →ₐ[K]
      relativeUnramifiedFixedField K H m hm :=
  IntermediateField.inclusion
    (abstractFixedField_le K (SeparableClosure K)
      (relativeUnramifiedFiniteExtension K H m hm).below)

/-- The lower-field scalar structure is exactly the actual field inclusion. -/
@[reducible]
def relativeUnramifiedFixedField_algebra
    (H : FiniteAbstractField (Gal(SeparableClosure K / K)))
    (m : ℕ) (hm : 0 < m) :
    Algebra (abstractFixedField K (SeparableClosure K) H.field)
      (relativeUnramifiedFixedField K H m hm) :=
  (relativeUnramifiedFixedField_inclusion K H m hm).toRingHom.toAlgebra

private def relativeUnramifiedFixedField_equivRelative
    (H : FiniteAbstractField (Gal(SeparableClosure K / K)))
    (m : ℕ) (hm : 0 < m) :
    letI := relativeUnramifiedFixedField_algebra K H m hm
    relativeUnramifiedFixedField K H m hm ≃ₐ[
      abstractFixedField K (SeparableClosure K) H.field]
      abstractRelativeFixedField K (SeparableClosure K) (K := H.field)
        (relativeUnramifiedFiniteExtension K H m hm).below := by
  letI := relativeUnramifiedFixedField_algebra K H m hm
  exact {
    toFun := fun x => ⟨x.1, x.2⟩
    invFun := fun x => ⟨x.1, x.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl
    commutes' := fun _ => rfl }

attribute [local instance] relativeUnramifiedFixedField_algebra

private theorem relativeUnramifiedFixedField_scalarTower
    (H : FiniteAbstractField (Gal(SeparableClosure K / K)))
    (m : ℕ) (hm : 0 < m) :
    IsScalarTower K (abstractFixedField K (SeparableClosure K) H.field)
      (relativeUnramifiedFixedField K H m hm) :=
  IsScalarTower.of_algebraMap_eq' rfl

attribute [local instance] relativeUnramifiedFixedField_scalarTower

/-- The fixed field is an actual finite extension of the original local field. -/
theorem relativeUnramifiedFixedField_absoluteFiniteDimensional
    (H : FiniteAbstractField (Gal(SeparableClosure K / K)))
    (m : ℕ) (hm : 0 < m) :
    FiniteDimensional K (relativeUnramifiedFixedField K H m hm) :=
  abstractFixedField_finiteDimensional K (SeparableClosure K)
    (relativeUnramifiedFiniteExtension K H m hm).field.field
    (relativeUnramifiedFiniteExtension K H m hm).field.finite

/-- The relative unramified fixed field is an actual finite extension. -/
theorem relativeUnramifiedFixedField_finiteDimensional
    (H : FiniteAbstractField (Gal(SeparableClosure K / K)))
    (m : ℕ) (hm : 0 < m) :
    FiniteDimensional (abstractFixedField K (SeparableClosure K) H.field)
      (relativeUnramifiedFixedField K H m hm) :=
  abstractFixedField_relativeFiniteDimensional K (SeparableClosure K)
    H.field (relativeUnramifiedFiniteExtension K H m hm).field.field
    (relativeUnramifiedFiniteExtension K H m hm).below H.finite
    (relativeUnramifiedFiniteExtension K H m hm).finiteQuotient

/-- The actual relative fixed field has exactly the prescribed degree. -/
theorem relativeUnramifiedFixedField_finrank
    (H : FiniteAbstractField (Gal(SeparableClosure K / K)))
    (m : ℕ) (hm : 0 < m) :
    Module.finrank (abstractFixedField K (SeparableClosure K) H.field)
      (relativeUnramifiedFixedField K H m hm) = m := by
  let U := (localResidueDatum K).finiteUnramifiedExtension
    (H.toFiniteResidueAbstractField (localResidueDatum K)) m hm
  have : Finite (H.field.toSubgroup ⧸
      extensionSubgroup H.field U.field U.below) := U.finite
  have hdegree :
      ((DegreeData.FiniteAbstractExtension.ofInclusion U.field H.field U.below).degree : ℕ) =
        Module.finrank (abstractFixedField K (SeparableClosure K) H.field)
          (abstractRelativeFixedField K (SeparableClosure K) U.below) :=
    finiteAbstractExtension_degree_eq_finrank K (SeparableClosure K)
      H.field U.field U.below U.normal H.finite U.finite
  rw [(relativeUnramifiedFixedField_equivRelative K H m hm).toLinearEquiv.finrank_eq,
    ← hdegree]
  exact (localResidueDatum K).finiteUnramifiedExtension_degree
    (H.toFiniteResidueAbstractField (localResidueDatum K)) m hm

/-- Normality of the actual reduction kernel makes its relative fixed field Galois. -/
theorem relativeUnramifiedFixedField_isGalois
    (H : FiniteAbstractField (Gal(SeparableClosure K / K)))
    (m : ℕ) (hm : 0 < m) :
    IsGalois (abstractFixedField K (SeparableClosure K) H.field)
      (relativeUnramifiedFixedField K H m hm) := by
  let U := (localResidueDatum K).finiteUnramifiedExtension
    (H.toFiniteResidueAbstractField (localResidueDatum K)) m hm
  have : IsGalois (abstractFixedField K (SeparableClosure K) H.field)
      (abstractRelativeFixedField K (SeparableClosure K) U.below) :=
    abstractRelativeFixedField_isGalois K (SeparableClosure K)
      H.field U.field U.below U.normal
  exact IsGalois.of_algEquiv
    (relativeUnramifiedFixedField_equivRelative K H m hm).symm

private theorem relativeUnramifiedFixedField_integer_isLocalHom
    (H : FiniteAbstractField (Gal(SeparableClosure K / K))) (m : ℕ) (hm : 0 < m)
    [ValuativeRel (abstractFixedField K (SeparableClosure K) H.field)]
    [ValuativeRel (relativeUnramifiedFixedField K H m hm)]
    [Valuation.HasExtension
      (ValuativeRel.valuation (abstractFixedField K (SeparableClosure K) H.field))
      (ValuativeRel.valuation (relativeUnramifiedFixedField K H m hm))] :
    IsLocalHom (algebraMap
      𝒪[abstractFixedField K (SeparableClosure K) H.field]
      𝒪[relativeUnramifiedFixedField K H m hm]) := by
  have : IsLocalHom (algebraMap
      (abstractFixedField K (SeparableClosure K) H.field)
      (relativeUnramifiedFixedField K H m hm)) := ⟨fun x hx =>
    isUnit_iff_ne_zero.mpr fun h => hx.ne_zero (by rw [h, map_zero])⟩
  exact Valuation.HasExtension.instIsLocalHomValuationInteger
    (vR := ValuativeRel.valuation (abstractFixedField K (SeparableClosure K) H.field))
    (vS := ValuativeRel.valuation (relativeUnramifiedFixedField K H m hm))

attribute [local instance] relativeUnramifiedFixedField_integer_isLocalHom

section Residue

variable (H : FiniteAbstractField (Gal(SeparableClosure K / K)))
  (m : ℕ) (hm : 0 < m)

variable [ValuativeRel (abstractFixedField K (SeparableClosure K) H.field)]
  [TopologicalSpace (abstractFixedField K (SeparableClosure K) H.field)]
  [IsNonarchimedeanLocalField (abstractFixedField K (SeparableClosure K) H.field)]
  [ValuativeRel (relativeUnramifiedFixedField K H m hm)]
  [TopologicalSpace (relativeUnramifiedFixedField K H m hm)]
  [IsNonarchimedeanLocalField (relativeUnramifiedFixedField K H m hm)]
  [Valuation.HasExtension (ValuativeRel.valuation K)
    (ValuativeRel.valuation (abstractFixedField K (SeparableClosure K) H.field))]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation (relativeUnramifiedFixedField K H m hm))]
  [Valuation.HasExtension
    (ValuativeRel.valuation (abstractFixedField K (SeparableClosure K) H.field))
    (ValuativeRel.valuation (relativeUnramifiedFixedField K H m hm))]

private theorem relativeUnramifiedFixedField_faithfulSMul
    (H : FiniteAbstractField (Gal(SeparableClosure K / K)))
    (m : ℕ) (hm : 0 < m) :
    FaithfulSMul (abstractFixedField K (SeparableClosure K) H.field)
      (relativeUnramifiedFixedField K H m hm) :=
  (faithfulSMul_iff_algebraMap_injective
    (abstractFixedField K (SeparableClosure K) H.field)
    (relativeUnramifiedFixedField K H m hm)).2
      (algebraMap (abstractFixedField K (SeparableClosure K) H.field)
        (relativeUnramifiedFixedField K H m hm)).injective

attribute [local instance] relativeUnramifiedFixedField_faithfulSMul

/-- The residue field of the actual relative degree-kernel extension also has
exactly the prescribed degree, for its compatible local valuations. -/
theorem relativeUnramifiedFixedField_residue_finrank :
    @Module.finrank 𝓀[abstractFixedField K (SeparableClosure K) H.field]
      𝓀[relativeUnramifiedFixedField K H m hm] _ _
        (IsLocalRing.ResidueField.instModule
          (R := 𝒪[abstractFixedField K (SeparableClosure K) H.field])
          (S := 𝒪[relativeUnramifiedFixedField K H m hm])) = m := by
  let F := abstractFixedField K (SeparableClosure K) H.field
  let N := relativeUnramifiedFixedField K H m hm
  let E := relativeUnramifiedFiniteExtension K H m hm
  let : Algebra 𝓀[K] 𝓀[F] :=
    IsLocalRing.ResidueField.instAlgebra (R := 𝒪[K]) (S := 𝒪[F])
  let : Algebra 𝓀[K] 𝓀[N] :=
    IsLocalRing.ResidueField.instAlgebra (R := 𝒪[K]) (S := 𝒪[N])
  let : Algebra 𝓀[F] 𝓀[N] :=
    IsLocalRing.ResidueField.instAlgebra (R := 𝒪[F]) (S := 𝒪[N])
  have : FiniteDimensional K F :=
    abstractFixedField_finiteDimensional K (SeparableClosure K) H.field H.finite
  have : FiniteDimensional F N :=
    relativeUnramifiedFixedField_finiteDimensional K H m hm
  have : FiniteDimensional K N :=
    relativeUnramifiedFixedField_absoluteFiniteDimensional K H m hm
  have hbase : (H.residueDegree (localResidueDatum K) : ℕ) =
      @Module.finrank 𝓀[K] 𝓀[F] _ _
        (IsLocalRing.ResidueField.instModule (R := 𝒪[K]) (S := 𝒪[F])) :=
    localResidueDatum_residueDegree_eq_residueFinrank K H
  have htop : (E.field.residueDegree (localResidueDatum K) : ℕ) =
      @Module.finrank 𝓀[K] 𝓀[N] _ _
        (IsLocalRing.ResidueField.instModule (R := 𝒪[K]) (S := 𝒪[N])) :=
    localResidueDatum_residueDegree_eq_residueFinrank K E.field
  have hrelative : (E.residueDegree (localResidueDatum K) : ℕ) = m :=
    (localResidueDatum K).finiteUnramifiedExtension_residueDegree
      (H.toFiniteResidueAbstractField (localResidueDatum K)) m hm
  have habstract :=
    (E.toFiniteResidueAbstractExtension (localResidueDatum K)).residueDegree_mul_absoluteResidueDegree
      (localResidueDatum K)
  change (E.residueDegree (localResidueDatum K) : ℕ) *
      (H.residueDegree (localResidueDatum K) : ℕ) =
        (E.field.residueDegree (localResidueDatum K) : ℕ) at habstract
  rw [hrelative, hbase, htop] at habstract
  have : IsScalarTower 𝒪[K] 𝒪[F] 𝒪[N] := valuationInteger_scalarTower K F N
  have : IsScalarTower 𝓀[K] 𝓀[F] 𝓀[N] :=
    valuationResidue_scalarTower 𝒪[K] 𝒪[F] 𝒪[N]
  have hactual := valuationResidue_finrank_mul 𝒪[K] 𝒪[F] 𝒪[N]
  have hbasePos : 0 < @Module.finrank 𝓀[K] 𝓀[F] _ _
      (IsLocalRing.ResidueField.instModule (R := 𝒪[K]) (S := 𝒪[F])) := by
    rw [← hbase]
    exact (H.residueDegree (localResidueDatum K)).property
  apply Nat.eq_of_mul_eq_mul_left hbasePos
  exact hactual.trans ((Nat.mul_comm
    (@Module.finrank 𝓀[K] 𝓀[F] _ _
      (IsLocalRing.ResidueField.instModule (R := 𝒪[K]) (S := 𝒪[F]))) m).trans habstract).symm


/-- The relative degree-kernel fixed field is unramified for the compatible
local valuations, as witnessed by its actual maximal-ideal ramification index. -/
theorem relativeUnramifiedFixedField_isUnramifiedValuedExtension
    [FiniteDimensional (abstractFixedField K (SeparableClosure K) H.field) (relativeUnramifiedFixedField K H m hm)]
    [Module.Finite 𝒪[(abstractFixedField K (SeparableClosure K) H.field)] 𝒪[(relativeUnramifiedFixedField K H m hm)]] :
    IsUnramifiedValuedExtension (abstractFixedField K (SeparableClosure K) H.field)
      (relativeUnramifiedFixedField K H m hm) := by
  let F := abstractFixedField K (SeparableClosure K) H.field
  let N := relativeUnramifiedFixedField K H m hm
  have hfund :=
    maximalIdeal_ramificationIdx_mul_residue_finrank_eq_finrank F N
  have hp : (𝓂[F] : Ideal 𝒪[F]) ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField
      (IsLocalRing.maximalIdeal.isMaximal 𝒪[F])
      (IsDiscreteValuationRing.not_isField 𝒪[F])
  have : Module.IsTorsionFree F N :=
    Module.IsTorsionFree.of_smul_eq_zero fun r x h => by
      rw [Algebra.smul_def] at h
      rcases mul_eq_zero.mp h with hr | hx
      · exact Or.inl ((algebraMap F N).injective (by simpa using hr))
      · exact Or.inr hx
  have : Module.IsTorsionFree 𝒪[F] 𝒪[N] := inferInstance
  rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ hp,
    relativeUnramifiedFixedField_residue_finrank K H m hm,
    relativeUnramifiedFixedField_finrank K H m hm] at hfund
  refine ⟨?_⟩
  apply Nat.eq_of_mul_eq_mul_right hm
  exact hfund.trans (one_mul m).symm

end Residue

end
end LocalClassFieldTheory
