/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldUnramifiedMaximality
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.FiniteAbelianClassFieldContainment
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.SmallHilbertTowerConjugation
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalCore
public import Nyll.GaloisCohomology.Cyclic.NormKernelVanishing

/-!
# The maximal everywhere-unramified abelian subextension

The selected small Hilbert class field is characterized in actual field
order.  Its rational absolute class-formation norm subgroup is exactly
the intrinsic small-Hilbert subgroup of its fixed-field base.  The
order-reversing finite abelian classification then places every actual
finite abelian extension unramified at all finite and infinite places
inside the selected field.
-/



@[expose] public section

open ClassFieldTheory

universe u v

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open ClassFormation KummerTheory
open IdealClassFieldTheory LocalClassFieldTheory NumberField Reciprocity


/-- The fixed-field idèle-class equivalence at the selected small-Hilbert
base, named once so later subgroup comparisons do not reconstruct it. -/
private noncomputable def smallHilbertClassFieldMaximalIdeleClassEquiv
    (K : Type u) [Field K] [NumberField K] :
    Additive (IdeleClassGroup (smallHilbertClassFieldBase K)) ≃+
      ambientFixedAddSubgroup (ideleClassRepresentation ℚ)
        (smallHilbertClassFieldBaseSubgroup K) :=
  rationalAbstractFixedFieldIdeleClassEquivFixed
    (smallHilbertClassFieldBaseSubgroup K)

/-- The intrinsic ordinary norm subgroup at the selected base, with its
additive carrier fixed in the declaration type. -/
private noncomputable def smallHilbertClassFieldMaximalIntrinsicNormSubgroup
    (K : Type u) [Field K] [NumberField K] :
    AddSubgroup (Additive (IdeleClassGroup (smallHilbertClassFieldBase K))) :=
  (smallHilbertClassFieldNormSubgroup
    (K := smallHilbertClassFieldBase K)).toAddSubgroup

/-- A short typed name for the transported intrinsic subgroup used below.
Keeping this endpoint opaque prevents the fixed-field aliases from being
re-elaborated when the inverse transport is applied. -/
private noncomputable def smallHilbertClassFieldMaximalNormEndpoint
    (K : Type u) [Field K] [NumberField K] :
    AddSubgroup
      (ambientFixedAddSubgroup (ideleClassRepresentation ℚ)
        (smallHilbertClassFieldBaseSubgroup K)) :=
  (smallHilbertClassFieldMaximalIntrinsicNormSubgroup K).map
    (smallHilbertClassFieldMaximalIdeleClassEquiv K).toAddMonoidHom

private theorem smallHilbertClassFieldMaximalNormEndpoint_eq_public
    (K : Type u) [Field K] [NumberField K] :
    smallHilbertClassFieldMaximalNormEndpoint K =
      smallHilbertNormSubgroupInRationalClassFormation
        (numberFieldTowerFiniteAbstractField K
          (smallHilbertClassFieldNormAmbient K)) := by
  rfl

/-- Mapping the selected abstract norm subgroup back to the ordinary
idèle-class group gives the named intrinsic subgroup. -/
private theorem smallHilbertClassFieldMaximalNormSubgroup_map_symm
    (K : Type u) [Field K] [NumberField K] :
    ((smallHilbertClassFieldSubextension K).normSubgroup
        (ideleClassRepresentation ℚ)).map
      (smallHilbertClassFieldMaximalIdeleClassEquiv K).symm.toAddMonoidHom =
        smallHilbertClassFieldMaximalIntrinsicNormSubgroup K := by
  let L :=
    smallHilbertClassFieldSubextension K
  let F :=
    smallHilbertClassFieldBase K
  let e :=
    rationalAbstractFixedFieldIdeleClassEquivFixed
      (smallHilbertClassFieldBaseSubgroup K)
  let hLfinite : Finite
      ((smallHilbertClassFieldBaseSubgroup K).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (smallHilbertClassFieldBaseSubgroup K)
          L.field L.below) :=
    L.finite
  calc
    (L.normSubgroup (ideleClassRepresentation ℚ)).map
        e.symm.toAddMonoidHom =
      (_root_.ideleClassNorm
        F (smallHilbertClassField K)).range.toAddSubgroup := by
      change
        (finiteNormSubgroup (ideleClassRepresentation ℚ)
            (smallHilbertClassFieldBaseSubgroup K)
            L.field L.below).map
            e.symm.toAddMonoidHom =
          (_root_.ideleClassNorm
            F (smallHilbertClassField K)).range.toAddSubgroup
      simpa only [L, F, e, smallHilbertClassField,
        smallHilbertClassFieldBase,
        smallHilbertClassFieldMaximalIdeleClassEquiv] using
        (map_rationalFiniteNormSubgroup_eq_ordinaryIdeleClassNormRange_concrete
          (smallHilbertClassFieldBaseSubgroup K)
          (smallHilbertClassFieldSubextension K).field
          (smallHilbertClassFieldSubextension K).below
          (smallHilbertClassFieldSubextension K).normal)
    _ = smallHilbertClassFieldMaximalIntrinsicNormSubgroup K := by
      exact
        congrArg Subgroup.toAddSubgroup
          (smallHilbertClassField_ideleClassNorm_range_eq_intrinsic
            (K := K))

private theorem smallHilbertClassFieldMaximalNormSubgroup_eq_endpoint
    (K : Type u) [Field K] [NumberField K] :
    (smallHilbertClassFieldSubextension K).normSubgroup
        (ideleClassRepresentation ℚ) =
      smallHilbertClassFieldMaximalNormEndpoint K := by
  exact ((AddSubgroup.map_symm_eq_iff_map_eq
    (K := smallHilbertClassFieldMaximalIntrinsicNormSubgroup K)
    (H := (smallHilbertClassFieldSubextension K).normSubgroup (ideleClassRepresentation ℚ))
    (e := smallHilbertClassFieldMaximalIdeleClassEquiv K)).1
    (smallHilbertClassFieldMaximalNormSubgroup_map_symm K)).symm

/-- The selected small Hilbert class-field subextension realizes exactly
the intrinsic small-Hilbert norm subgroup in the rational absolute class
formation. -/
@[simp]
theorem smallHilbertClassFieldSubextension_normSubgroup
    (K : Type u) [Field K] [NumberField K] :
    (smallHilbertClassFieldSubextension K).normSubgroup
        (ideleClassRepresentation ℚ) =
      smallHilbertNormSubgroupInRationalClassFormation
        (numberFieldTowerFiniteAbstractField K
          (smallHilbertClassFieldNormAmbient K)) := by
  calc
    (smallHilbertClassFieldSubextension K).normSubgroup
        (ideleClassRepresentation ℚ) =
      smallHilbertClassFieldMaximalNormEndpoint K :=
        smallHilbertClassFieldMaximalNormSubgroup_eq_endpoint K
    _ = smallHilbertNormSubgroupInRationalClassFormation
        (numberFieldTowerFiniteAbstractField K
          (smallHilbertClassFieldNormAmbient K)) :=
      smallHilbertClassFieldMaximalNormEndpoint_eq_public K

/-- The actual fixed-field extension represented by a finite abelian
subextension of the selected rational base is everywhere unramified.

Naming this predicate keeps the fixed-field instance tower out of the
signatures of every theorem which uses it. -/
def finiteAbelianSubextensionIsEverywhereUnramified
    (K : Type u) [Field K] [NumberField K]
    (P : FiniteAbelianSubextension
      (smallHilbertClassFieldBaseSubgroup K)) : Prop :=
  let F :=
    smallHilbertClassFieldBase K
  let E :=
    abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below
  letI hPfinite : Finite
      ((smallHilbertClassFieldBaseSubgroup K).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (smallHilbertClassFieldBaseSubgroup K)
          P.field P.below) :=
    P.finite
  letI : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ)
      (smallHilbertClassFieldBaseSubgroup K)
      P.field P.below inferInstance hPfinite
  letI : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : FiniteDimensional ℚ E :=
    FiniteDimensional.trans ℚ F E
  letI : NumberField E :=
    NumberField.of_module_finite ℚ E
  letI : IsGalois F E :=
    abstractRelativeFixedField_isGalois
      ℚ (SeparableClosure ℚ)
      (smallHilbertClassFieldBaseSubgroup K)
      P.field P.below P.normal
  IsEverywhereUnramified F E

/-- Every finite abelian subextension of the selected rational
fixed-field base which is unramified at every finite and infinite place
is contained in the selected small Hilbert class-field subextension. -/
theorem
    everywhereUnramifiedAbelianSubextension_le_smallHilbertClassFieldSubextension
    (K : Type u) [Field K] [NumberField K]
    (P : FiniteAbelianSubextension
      (smallHilbertClassFieldBaseSubgroup K)) :
    finiteAbelianSubextensionIsEverywhereUnramified K P →
      P ≤ smallHilbertClassFieldSubextension K := by
  let F :=
    smallHilbertClassFieldBase K
  let E :=
    abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below
  let hPfinite : Finite
      ((smallHilbertClassFieldBaseSubgroup K).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (smallHilbertClassFieldBaseSubgroup K)
          P.field P.below) :=
    P.finite
  let : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ)
      (smallHilbertClassFieldBaseSubgroup K)
      P.field P.below inferInstance hPfinite
  let : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional ℚ E :=
    FiniteDimensional.trans ℚ F E
  let : NumberField E :=
    NumberField.of_module_finite ℚ E
  let : IsGalois F E :=
    abstractRelativeFixedField_isGalois
      ℚ (SeparableClosure ℚ)
      (smallHilbertClassFieldBaseSubgroup K)
      P.field P.below P.normal
  intro hunramified
  change IsEverywhereUnramified F E at hunramified
  let KF :=
    numberFieldTowerFiniteAbstractField K
      (smallHilbertClassFieldNormAmbient K)
  exact
    everywhereUnramifiedFiniteAbelianSubextension_le_smallHilbertClassField
      KF (smallHilbertClassFieldSubextension K) P
      (smallHilbertClassFieldSubextension_normSubgroup K)
      hunramified

/-- The selected small Hilbert class field is genuinely everywhere
unramified, and its finite abelian subextension is maximal among all
actual everywhere-unramified abelian subextensions of the same rational
fixed-field base. -/
theorem
    smallHilbertClassFieldSubextension_isEverywhereUnramifiedAndMaximalAbelian
    (K : Type u) [Field K] [NumberField K] :
    IsEverywhereUnramified K (smallHilbertClassField K) ∧
      ∀ P : FiniteAbelianSubextension
          (smallHilbertClassFieldBaseSubgroup K),
        finiteAbelianSubextensionIsEverywhereUnramified K P →
          P ≤ smallHilbertClassFieldSubextension K := by
  constructor
  · exact smallHilbertClassField_isEverywhereUnramified K
  · intro P
    exact
      everywhereUnramifiedAbelianSubextension_le_smallHilbertClassFieldSubextension
        K P

/-- Every finite abelian extension of `K` which is unramified at all
finite and infinite places has a genuine `K`-embedding into the selected
small Hilbert class field of `K`. -/
theorem
    finiteAbelianExtension_nonempty_algHom_to_smallHilbertClassField_of_everywhereUnramified
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    [IsAbelianGalois K L]
    [IsUnramifiedAtInfinitePlaces K L]
    (hunramifiedFinite :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅) :
    Nonempty (L →ₐ[K] smallHilbertClassField K) := by
  apply
    finiteAbelianExtension_nonempty_algHom_of_normRange_le
      (K := K) L (smallHilbertClassField K)
  rw [smallHilbertClassField_ideleClassNorm_range_over_original]
  exact
    smallHilbertClassFieldNormSubgroup_le_ideleClassNorm_range_of_everywhereUnramified
      (K := K) (L := L) hunramifiedFinite

end GlobalClassFields
end GlobalClassFieldTheory
