/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.IdentityComponent
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.FiniteAbelianClassFieldCorrespondence
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.NormConductor
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalNormResidue
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.FiniteIndexNormClassField
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.NumberFieldNormResidue
public import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields
public import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension

/-!
# Construction of a closed finite-index class field

This leaf fixes the finite Galois norm neighbourhood, abstract subextension,
and canonical fixed-field presentation attached to a closed finite-index
idèle-class subgroup. Norm-range and reciprocity statements live in later
leaves so their elaboration environments do not remain resident here.
-/



@[expose] public section

universe u

open scoped IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open Reciprocity ClassFormation CyclicCohomology LocalClassFieldTheory

variable {K : Type u} [Field K] [NumberField K]

/-- The concrete finite Galois norm neighbourhood used to construct
the class field of `H`. -/
noncomputable abbrev closedFiniteIndexClassFieldNormAmbient
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] : Type u :=
  closedFiniteIndexNormAmbient (K := K) H hclosed

/-- The named norm-neighbourhood containment used by the selected
ordinary class-field construction. -/
theorem closedFiniteIndexClassFieldNormAmbient_normRange_le
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    (_root_.ideleClassNorm K
      (closedFiniteIndexClassFieldNormAmbient
        (K := K) H hclosed)).range ≤ H := by
  simpa only [closedFiniteIndexClassFieldNormAmbient] using
    (closedFiniteIndexSubgroup_has_finiteGaloisNormNeighborhood
      (K := K) H hclosed)

private theorem intrinsicBase_fixedField_isAbelianGalois
    (J : FiniteAbelianSubextension (baseField Gal(SeparableClosure K/K))) :
    IsAbelianGalois K (abstractFixedField K (SeparableClosure K) J.field) := by
  let Ω := SeparableClosure K
  let B := baseField Gal(Ω/K)
  let F := abstractFixedField K Ω J.field
  let F₀ := abstractFixedField K Ω B
  let E := abstractRelativeFixedField K Ω J.below
  have hSurj : Function.Surjective B.toSubgroup.subtype := by
    intro σ
    refine ⟨⟨σ, ?_⟩, rfl⟩
    change σ ∈ (baseField Gal(Ω/K)).toSubgroup
    rw [baseField_toSubgroup]
    exact Subgroup.mem_top _
  have hMap : (extensionSubgroup B J.field J.below).map B.toSubgroup.subtype =
    J.field.toSubgroup := by
    ext σ
    constructor
    · rintro ⟨τ, hτ, rfl⟩
      exact hτ
    · intro hσ
      exact ⟨⟨σ, J.below hσ⟩, hσ, rfl⟩
  have hNormal : J.field.toSubgroup.Normal := by
    have h := J.normal.map B.toSubgroup.subtype hSurj
    rw [hMap] at h
    exact h
  let : IsGalois K F := (InfiniteGalois.normal_iff_isGalois F).1 (by
    rw [InfiniteGalois.fixingSubgroup_fixedField J.field]
    exact hNormal)
  let : IsAbelianGalois F₀ E := finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois J
  have hBot : F₀ = (⊥ : IntermediateField K Ω) := by
    have h := InfiniteGalois.fixedField_fixingSubgroup (⊥ : IntermediateField K Ω)
    change abstractFixedField K Ω (RamificationTheory.closedFixingSubgroup K Ω (⊥
      : IntermediateField K Ω)) =
      (⊥ : IntermediateField K Ω) at h
    rw [closedFixingSubgroup_bot_eq_baseField] at h
    exact h
  let e : K ≃ₐ[K] F₀ :=
    (IntermediateField.botEquiv K Ω).symm.trans (IntermediateField.equivOfEq hBot.symm)
  let : IsScalarTower K F₀ E := IsScalarTower.of_algebraMap_eq' rfl
  let : IsGalois K E := inferInstanceAs (IsGalois K F)
  change IsAbelianGalois K E
  exact IsAbelianGalois.of_base_equiv e.toRingEquiv (fun x =>
    (IsScalarTower.algebraMap_apply K F₀ E x).trans
      (congrArg (algebraMap F₀ E) (e.commutes x).symm))

/-- The finite abelian class field of a closed finite-index subgroup,
expressed in the original absolute Galois group. -/
noncomputable def closedFiniteIndexClassFieldSubextension
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K))) [H.FiniteIndex] :
    FiniteAbelianSubextension (baseField Gal(SeparableClosure K/K)) :=
  Classical.choose (exists_standardNumberFieldClassField_of_normRange_le K
    (closedFiniteIndexClassFieldNormAmbient H hclosed) H
    (closedFiniteIndexClassFieldNormAmbient_normRange_le H hclosed))

/-- The class field of a closed finite-index idèle-class subgroup inside
the fixed separable closure of its original base. -/
noncomputable def closedFiniteIndexClassField
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K))) [H.FiniteIndex] :
    IntermediateField K (SeparableClosure K) :=
  abstractFixedField K (SeparableClosure K)
    (closedFiniteIndexClassFieldSubextension H hclosed).field

instance closedFiniteIndexClassField_finiteDimensional
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K))) [H.FiniteIndex] :
    FiniteDimensional K (closedFiniteIndexClassField H hclosed) :=
  abstractFixedField_finiteDimensional K (SeparableClosure K)
    (closedFiniteIndexClassFieldSubextension H hclosed).field
    (closedFiniteIndexClassFieldSubextension H hclosed).finite

instance closedFiniteIndexClassField_isAbelianGalois
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K))) [H.FiniteIndex] :
    IsAbelianGalois K (closedFiniteIndexClassField H hclosed) :=
  intrinsicBase_fixedField_isAbelianGalois (closedFiniteIndexClassFieldSubextension H hclosed)

/-- The class field realizes the subgroup as an actual determinant-norm range. -/
theorem closedFiniteIndexClassField_ideleClassNorm_range
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K))) [H.FiniteIndex] :
    (_root_.ideleClassNorm K (closedFiniteIndexClassField H hclosed)).range = H :=
  Classical.choose_spec (exists_standardNumberFieldClassField_of_normRange_le K
    (closedFiniteIndexClassFieldNormAmbient H hclosed) H
    (closedFiniteIndexClassFieldNormAmbient_normRange_le H hclosed))

/-- A closed finite-index subgroup has a finite abelian class field in the
original separable closure, with its actual determinant-norm range. -/
theorem exists_closedFiniteIndexClassField_original
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K))) [H.FiniteIndex] :
    ∃ F : IntermediateField K (SeparableClosure K),
      ∃ hF : FiniteDimensional K F,
        letI := hF
        IsAbelianGalois K F ∧ (_root_.ideleClassNorm K F).range = H :=
  ⟨closedFiniteIndexClassField H hclosed, inferInstance, inferInstance,
    closedFiniteIndexClassField_ideleClassNorm_range H hclosed⟩

/-- Every open idèle-class subgroup is the norm range of a finite abelian
extension in the original separable closure. -/
theorem exists_openSubgroupClassField_original
    (H : Subgroup (IdeleClassGroup K)) (hH : IsOpen (H : Set (IdeleClassGroup K))) :
    ∃ F : IntermediateField K (SeparableClosure K),
      ∃ hF : FiniteDimensional K F,
        letI := hF
        IsAbelianGalois K F ∧ (_root_.ideleClassNorm K F).range = H := by
  let : H.FiniteIndex := ideleClassOpenSubgroup_finiteIndex K H hH
  exact exists_closedFiniteIndexClassField_original H (H.isClosed_of_isOpen hH)

end GlobalClassFields
end GlobalClassFieldTheory
