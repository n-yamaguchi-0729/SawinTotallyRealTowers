/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.NormTopology
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitNormQuotient
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.NormConductor
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.MathlibTopologyComparison
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalCore
public import Nyll.GaloisCohomology.Cyclic.NormKernelVanishing
public import Nyll.GaloisCohomology.Kummer.Abstract.KummerDelta

/-!
# The norm topology and the ordinary idele-class topology

On every actual fixed field inside the rational separable closure, the
canonical fixed-part model identifies each abstract finite norm subgroup
with the range of the corresponding ordinary idele-class norm.  Since the
latter is open, every abstract norm-open subgroup becomes open in the
ordinary idele-class topology after transport to the actual fixed field.
-/



@[expose] public section

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open LocalClassFieldTheory

universe u v

section Standard

variable (k : Type u) [Field k] [NumberField k]

attribute [local instance] abstractRelativeFixedFieldNumberField

/-- A norm-open subgroup of a finite fixed part is open in the genuine
standard idèle-class topology of that field. -/
theorem standardNormOpenSubgroup_isOpen
    (H : FiniteAbstractField Gal(SeparableClosure k/k))
    [FiniteDimensional k (abstractFixedField k (SeparableClosure k) H.field)]
    (U : AddSubgroup (KummerTheory.ambientFixedAddSubgroup (ideleClassRepresentation k) H.field))
    (hU : IsNormOpen (ideleClassRepresentation k) H.field U) :
    let F := abstractFixedField k (SeparableClosure k) H.field
    IsOpen ((U.map (abstractFixedFieldIdeleClassEquivFixed k H.field).symm.toAddMonoidHom).carrier :
      Set (Additive (NumberField.IdeleClassGroup (𝓞 F) F))) := by
  intro F
  obtain ⟨J, hJ⟩ :=
    (normTopology_addSubgroup_isOpen_iff (ideleClassRepresentation k) H.field U).1 hU
  let E := abstractRelativeFixedField k (SeparableClosure k) J.below
  let : Finite
      (H.field.toSubgroup ⧸ CyclicCohomology.extensionSubgroup H.field J.field J.below) := J.finite
  let hJabsolute := FiniteGaloisSubextension.finite_extension_trans J.below (le_baseField H.field)
  let : FiniteDimensional k (abstractFixedField k (SeparableClosure k) J.field) :=
    abstractFixedField_finiteDimensional k (SeparableClosure k) J.field hJabsolute
  let : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional k (SeparableClosure k) H.field J.field
      J.below H.finite J.finite
  let : IsGalois F E :=
    abstractRelativeFixedField_isGalois k (SeparableClosure k) H.field J.field J.below J.normal
  have hmap := map_finiteNormSubgroup_eq_standardIdeleClassNormRange
    k H.field J.field J.below J.normal
  have hset := congrArg
    (fun V : AddSubgroup (Additive (NumberField.IdeleClassGroup (𝓞 F) F)) => V.carrier) hmap
  have hopen := GlobalClassFields.ideleClassNorm_range_isOpen (K := F) (L := E)
  refine AddSubgroup.isOpen_mono (AddSubgroup.map_mono hJ) ?_
  exact (congrArg IsOpen hset).mpr hopen

end Standard

/-- The transport of an abstract fixed-part subgroup to the ordinary
idele-class group of the corresponding rational fixed field. -/
noncomputable def rationalTransportedNormSubgroup
    (K : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    (H : AddSubgroup
      (KummerTheory.ambientFixedAddSubgroup
        (ideleClassRepresentation ℚ) K)) :
    let F := abstractFixedField ℚ (SeparableClosure ℚ) K
    let : FiniteDimensional ℚ F :=
      abstractFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) K hKfinite
    let : NumberField F := NumberField.of_module_finite ℚ F
    AddSubgroup (Additive (IdeleClassGroup F)) := by
  intro F sharedOwner2 sharedOwner3
  exact
    H.map
      (rationalAbstractFixedFieldIdeleClassEquivFixed
        K).symm.toAddMonoidHom

/-- Transporting a norm-open subgroup of the rational absolute
idele-class representation to the idele class group of its actual fixed
field produces an open subgroup for the ordinary idele-class topology. -/
theorem rationalNormOpenSubgroup_isOpen
    (K : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    (H : AddSubgroup
      (KummerTheory.ambientFixedAddSubgroup
        (ideleClassRepresentation ℚ) K))
    (hH : IsNormOpen (ideleClassRepresentation ℚ) K
      (H : Set
        (KummerTheory.ambientFixedAddSubgroup
          (ideleClassRepresentation ℚ) K))) :
    let F := abstractFixedField ℚ (SeparableClosure ℚ) K
    let : FiniteDimensional ℚ F :=
      abstractFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) K hKfinite
    let : NumberField F := NumberField.of_module_finite ℚ F
    IsOpen
      ((rationalTransportedNormSubgroup
          (hKfinite := hKfinite) K H :
        AddSubgroup (Additive (IdeleClassGroup F))) :
        Set (Additive (IdeleClassGroup F))) := by
  intro F hF hNF
  let B : FiniteAbstractField Gal(SeparableClosure ℚ/ℚ) := ⟨K, hKfinite⟩
  exact standardNormOpenSubgroup_isOpen ℚ B H hH

end Reciprocity
end GlobalClassFieldTheory
