/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Group.Subgroup.Map

public import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianClassification
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassFormation
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClassFieldRealization
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.CyclotomicDegreeOnNumberField
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FiniteGaloisRealization
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassNormTopology
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalCore
public import Nyll.GaloisCohomology.Cyclic.NormKernelVanishing
public import Nyll.GaloisCohomology.Kummer.Abstract.KummerDelta

/-!
# Class fields from ordinary idele-class norm neighbourhoods

An actual finite Galois norm subgroup contained in an ordinary
idele-class subgroup makes the transported subgroup norm-open in the
rational absolute class formation.  Finite abelian classification then
constructs its class field.  The final theorem below transports the
result back to the ordinary idele class group of the actual fixed field,
so its conclusion is an equality of genuine determinant-norm ranges.
-/



@[expose] public section

universe u v

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open ClassFormation
open LocalClassFieldTheory
open Reciprocity


variable
    (K : Type u) (L : Type v) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

attribute [instance] numberFieldTowerAbstractBaseFiniteDimensional
  numberFieldTowerAbstractBaseNumberField

/- The norm-open subgroup and its openness proof form one opaque value.  Both
the classification theorem and the topology comparison consume projections
of this same package. -/
private noncomputable def ordinaryNormOpenSubgroup
    (H : Subgroup (IdeleClassGroup K))
    (hLH : (_root_.ideleClassNorm K L).range ≤ H) :
    ClassFormation.FiniteAbelianSubextension.NormOpenAddSubgroup
      (ideleClassRepresentation ℚ)
      (numberFieldTowerBaseSubgroup K L) := by
  let f : Additive (IdeleClassGroup K) →+
      KummerTheory.ambientFixedAddSubgroup
        (ideleClassRepresentation ℚ) (numberFieldTowerBaseSubgroup K L) :=
    (numberFieldTowerIdeleClassEquivAmbientFixed K L).toAddMonoidHom
  refine ⟨H.toAddSubgroup.map f, ?_⟩
  exact numberFieldTowerTransport_isNormOpen_of_normRange_le K L H hLH

private theorem ordinaryNormOpenSubgroup_val
    (H : Subgroup (IdeleClassGroup K))
    (hLH : (_root_.ideleClassNorm K L).range ≤ H) :
    (ordinaryNormOpenSubgroup K L H hLH).1 =
      H.toAddSubgroup.map
        (numberFieldTowerIdeleClassEquivAmbientFixed K L).toAddMonoidHom :=
  rfl

section FixedBaseTransport

omit [FiniteDimensional K L] [IsGalois K L] in
private theorem numberFieldTowerIdeleClassEquivAmbientFixed_symm_apply
    (c : Additive (IdeleClassGroup K)) :
    (rationalAbstractFixedFieldIdeleClassEquivFixed
        (numberFieldTowerBaseSubgroup K L)).symm
      (numberFieldTowerIdeleClassEquivAmbientFixed K L c) =
        MulEquiv.toAdditive
          (ideleClassCongr
            (numberFieldTowerAbstractBaseFieldEquiv K L)) c := by
  let eFixed :=
    rationalAbstractFixedFieldIdeleClassEquivFixed
      (numberFieldTowerBaseSubgroup K L)
  let eBase :=
    MulEquiv.toAdditive
      (ideleClassCongr
        (numberFieldTowerAbstractBaseFieldEquiv K L))
  simpa only [numberFieldTowerIdeleClassEquivAmbientFixed,
    AddEquiv.trans_apply] using
      eFixed.symm_apply_apply (eBase c)

omit [FiniteDimensional K L] [IsGalois K L] in
private theorem numberFieldTowerIdeleClassEquivAmbientFixed_comp :
    let F := abstractFixedField ℚ (SeparableClosure ℚ) (numberFieldTowerBaseSubgroup K L)
    let eBase : Additive (IdeleClassGroup K) →+ Additive (IdeleClassGroup F) :=
      (MulEquiv.toAdditive
        (ideleClassCongr (numberFieldTowerAbstractBaseFieldEquiv K L))).toAddMonoidHom
    (rationalAbstractFixedFieldIdeleClassEquivFixed
        (numberFieldTowerBaseSubgroup K L)).symm.toAddMonoidHom.comp
      (numberFieldTowerIdeleClassEquivAmbientFixed K L).toAddMonoidHom = eBase := by
  intro F eBase
  apply AddMonoidHom.ext
  intro c
  exact
    numberFieldTowerIdeleClassEquivAmbientFixed_symm_apply
      K L (c : Additive (IdeleClassGroup K))

private theorem numberFieldTowerBaseTransport_isOpen_of_normRange_le_core
    (H : Subgroup (IdeleClassGroup K))
    (hLH : (_root_.ideleClassNorm K L).range ≤ H) :
    IsOpen
      (((H.toAddSubgroup).map
        (MulEquiv.toAdditive
          (ideleClassCongr
            (numberFieldTowerAbstractBaseFieldEquiv
              K L))).toAddMonoidHom :
        AddSubgroup
          (Additive
            (IdeleClassGroup
              (abstractFixedField ℚ (SeparableClosure ℚ)
                (numberFieldTowerBaseSubgroup K L))))) :
        Set
          (Additive
            (IdeleClassGroup
              (abstractFixedField ℚ (SeparableClosure ℚ)
                (numberFieldTowerBaseSubgroup K L))))) := by
  let B := numberFieldTowerBaseSubgroup K L
  let F := abstractFixedField ℚ (SeparableClosure ℚ) B
  let eFixed :
      Additive (IdeleClassGroup F) ≃+
        KummerTheory.ambientFixedAddSubgroup (ideleClassRepresentation ℚ) B :=
    rationalAbstractFixedFieldIdeleClassEquivFixed B
  let eBase : Additive (IdeleClassGroup K) ≃+ Additive (IdeleClassGroup F) :=
    MulEquiv.toAdditive
      (ideleClassCongr
        (numberFieldTowerAbstractBaseFieldEquiv K L))
  let eTower :
      Additive (IdeleClassGroup K) ≃+
        KummerTheory.ambientFixedAddSubgroup (ideleClassRepresentation ℚ) B :=
    numberFieldTowerIdeleClassEquivAmbientFixed K L
  let N : AddSubgroup
      (KummerTheory.ambientFixedAddSubgroup
        (ideleClassRepresentation ℚ) B) :=
    (ordinaryNormOpenSubgroup K L H hLH).1
  have hN :
      IsNormOpen (ideleClassRepresentation ℚ) B N :=
    (ordinaryNormOpenSubgroup K L H hLH).2
  have hopen :=
    rationalNormOpenSubgroup_isOpen B N hN
  have hcomp :
      eFixed.symm.toAddMonoidHom.comp
          eTower.toAddMonoidHom =
        (eBase.toAddMonoidHom : Additive (IdeleClassGroup K) →+ Additive (IdeleClassGroup F)) :=
    numberFieldTowerIdeleClassEquivAmbientFixed_comp K L
  have hmap :
      rationalTransportedNormSubgroup B N =
        H.toAddSubgroup.map eBase.toAddMonoidHom := by
    simpa only [rationalTransportedNormSubgroup, N,
      ordinaryNormOpenSubgroup_val, AddSubgroup.map_map] using
      congrArg
        (fun f : Additive (IdeleClassGroup K) →+
            Additive (IdeleClassGroup F) =>
          AddSubgroup.map (N := Additive (IdeleClassGroup F)) f H.toAddSubgroup)
        hcomp
  exact
    (congrArg
      (fun S : AddSubgroup (Additive (IdeleClassGroup F)) =>
        IsOpen (S : Set (Additive (IdeleClassGroup F))))
      hmap).mp hopen

end FixedBaseTransport

/-- A finite Galois norm neighbourhood inside an ordinary idele-class
subgroup produces a finite abelian subextension whose abstract norm
subgroup is exactly the transported ordinary subgroup. -/
theorem exists_finiteAbelianSubextension_normSubgroup_eq_of_normRange_le
    (H : Subgroup (IdeleClassGroup K))
    (hLH : (_root_.ideleClassNorm K L).range ≤ H) :
    ∃ M : FiniteAbelianSubextension
        (numberFieldTowerBaseSubgroup K L),
      M.normSubgroup (ideleClassRepresentation ℚ) =
        (H.toAddSubgroup).map
          (numberFieldTowerIdeleClassEquivAmbientFixed
            K L).toAddMonoidHom := by
  let :=
    numberFieldTowerBaseSubgroupAbsoluteQuotientFinite K L
  let B : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) :=
    { field := numberFieldTowerBaseSubgroup K L
      finite := numberFieldTowerBaseSubgroupAbsoluteQuotientFinite K L }
  let N := ordinaryNormOpenSubgroup K L H hLH
  obtain ⟨M, hM⟩ :
      ∃ M : FiniteAbelianSubextension
          (numberFieldTowerBaseSubgroup K L),
        FiniteAbelianSubextension.normSubgroupMap
            (ideleClassRepresentation ℚ) M = N :=
    FiniteAbelianSubextension.normSubgroupMap_surjective
      (Reciprocity.numberFieldCyclotomicIdeleClassValuationData ℚ)
      (ideleClassRepresentation_satisfiesClassFieldAxiom ℚ) B N
  refine ⟨M, ?_⟩
  rw [← FiniteAbelianSubextension.normSubgroupMap_val]
  rw [congrArg Subtype.val hM]
  exact ordinaryNormOpenSubgroup_val K L H hLH

/-- The ordinary subgroup transported from `K` to its compatible
embedded fixed-field copy is open whenever it contains an actual finite
Galois norm subgroup.  This is the concrete comparison between the norm
topology and the usual idele-class topology at the chosen realization. -/
theorem numberFieldTowerBaseTransport_isOpen_of_normRange_le
    (H : Subgroup (IdeleClassGroup K))
    (hLH : (_root_.ideleClassNorm K L).range ≤ H) :
    let B := numberFieldTowerBaseSubgroup K L
    let F := abstractFixedField ℚ (SeparableClosure ℚ) B
    IsOpen
      (((H.toAddSubgroup).map
        (MulEquiv.toAdditive
          (ideleClassCongr
            (numberFieldTowerAbstractBaseFieldEquiv
              K L))).toAddMonoidHom :
        AddSubgroup (Additive (IdeleClassGroup F))) :
        Set (Additive (IdeleClassGroup F))) := by
  exact
    numberFieldTowerBaseTransport_isOpen_of_normRange_le_core
      K L H hLH

/-- The finite abelian subextension selected from an ordinary norm
neighbourhood.  This is the unique choice point for the realization API
below. -/
noncomputable def ordinaryNormClassFieldSubextension
    (H : Subgroup (IdeleClassGroup K))
    (hLH : (_root_.ideleClassNorm K L).range ≤ H) :
    FiniteAbelianSubextension (numberFieldTowerBaseSubgroup K L) :=
  Classical.choose
    (exists_finiteAbelianSubextension_normSubgroup_eq_of_normRange_le
      K L H hLH)

/-- The selected subextension has the prescribed abstract norm subgroup. -/
theorem ordinaryNormClassFieldSubextension_normSubgroup
    (H : Subgroup (IdeleClassGroup K))
    (hLH : (_root_.ideleClassNorm K L).range ≤ H) :
    (ordinaryNormClassFieldSubextension K L H hLH).normSubgroup
        (ideleClassRepresentation ℚ) =
      H.toAddSubgroup.map
        (numberFieldTowerIdeleClassEquivAmbientFixed
          K L).toAddMonoidHom :=
  Classical.choose_spec
    (exists_finiteAbelianSubextension_normSubgroup_eq_of_normRange_le
      K L H hLH)

/-- The canonical fixed-field copy of the base used by every ordinary
norm-neighbourhood realization in the ambient extension `L / K`. -/
noncomputable abbrev ordinaryNormClassFieldBase : Type :=
  abstractFixedField ℚ (SeparableClosure ℚ)
    (numberFieldTowerBaseSubgroup K L)

/-- The actual relative fixed field of the selected ordinary class-field
subextension. -/
noncomputable abbrev ordinaryNormClassFieldExtension
    (H : Subgroup (IdeleClassGroup K))
    (hLH : (_root_.ideleClassNorm K L).range ≤ H) : Type :=
  abstractRelativeFixedField ℚ (SeparableClosure ℚ)
    (ordinaryNormClassFieldSubextension K L H hLH).below

noncomputable instance ordinaryNormClassFieldExtensionFiniteDimensional
    (H : Subgroup (IdeleClassGroup K))
    (hLH : (_root_.ideleClassNorm K L).range ≤ H) :
    FiniteDimensional (ordinaryNormClassFieldBase K L)
      (ordinaryNormClassFieldExtension K L H hLH) :=
  abstractRelativeFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ)
    (numberFieldTowerBaseSubgroup K L)
    (ordinaryNormClassFieldSubextension K L H hLH).field
    (ordinaryNormClassFieldSubextension K L H hLH).below
    (numberFieldTowerBaseSubgroupAbsoluteQuotientFinite K L)
    (ordinaryNormClassFieldSubextension K L H hLH).finite

noncomputable instance ordinaryNormClassFieldScalarTower
    (H : Subgroup (IdeleClassGroup K))
    (hLH : (_root_.ideleClassNorm K L).range ≤ H) :
    IsScalarTower ℚ (ordinaryNormClassFieldBase K L)
      (ordinaryNormClassFieldExtension K L H hLH) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

noncomputable instance ordinaryNormClassFieldAbsoluteFiniteDimensional
    (H : Subgroup (IdeleClassGroup K))
    (hLH : (_root_.ideleClassNorm K L).range ≤ H) :
    FiniteDimensional ℚ
      (ordinaryNormClassFieldExtension K L H hLH) :=
  FiniteDimensional.trans ℚ (ordinaryNormClassFieldBase K L)
    (ordinaryNormClassFieldExtension K L H hLH)

noncomputable instance ordinaryNormClassFieldExtensionNumberField
    (H : Subgroup (IdeleClassGroup K))
    (hLH : (_root_.ideleClassNorm K L).range ≤ H) :
    NumberField (ordinaryNormClassFieldExtension K L H hLH) :=
  NumberField.of_module_finite ℚ
    (ordinaryNormClassFieldExtension K L H hLH)

noncomputable instance ordinaryNormClassFieldExtensionIsGalois
    (H : Subgroup (IdeleClassGroup K))
    (hLH : (_root_.ideleClassNorm K L).range ≤ H) :
    IsGalois (ordinaryNormClassFieldBase K L)
      (ordinaryNormClassFieldExtension K L H hLH) :=
  abstractRelativeFixedField_isGalois
    ℚ (SeparableClosure ℚ)
    (numberFieldTowerBaseSubgroup K L)
    (ordinaryNormClassFieldSubextension K L H hLH).field
    (ordinaryNormClassFieldSubextension K L H hLH).below
    (ordinaryNormClassFieldSubextension K L H hLH).normal

noncomputable instance ordinaryNormClassFieldExtensionIsAbelianGalois
    (H : Subgroup (IdeleClassGroup K))
    (hLH : (_root_.ideleClassNorm K L).range ≤ H) :
    IsAbelianGalois (ordinaryNormClassFieldBase K L)
      (ordinaryNormClassFieldExtension K L H hLH) :=
  finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois
    (ordinaryNormClassFieldSubextension K L H hLH)

/-- The canonical equivalence from the original base to the selected
fixed-field base. -/
noncomputable abbrev ordinaryNormClassFieldBaseEquiv :
    K ≃ₐ[ℚ] ordinaryNormClassFieldBase K L :=
  numberFieldTowerAbstractBaseFieldEquiv K L

/-- The determinant-norm range of the selected ordinary class field is
the original subgroup transported to the canonical fixed-field base. -/
theorem ordinaryNormClassField_ideleClassNorm_range
    (H : Subgroup (IdeleClassGroup K))
    (hLH : (_root_.ideleClassNorm K L).range ≤ H) :
    (_root_.ideleClassNorm
      (ordinaryNormClassFieldBase K L)
      (ordinaryNormClassFieldExtension K L H hLH)).range.toAddSubgroup =
        H.toAddSubgroup.map
          (MulEquiv.toAdditive
            (ideleClassCongr
              (ordinaryNormClassFieldBaseEquiv K L))).toAddMonoidHom := by
  let M := ordinaryNormClassFieldSubextension K L H hLH
  let B := numberFieldTowerBaseSubgroup K L
  let hRelativeQuotientFinite : Finite
      (B.toSubgroup ⧸
        CyclicCohomology.extensionSubgroup B M.field M.below) :=
    M.finite
  let eFixed := rationalAbstractFixedFieldIdeleClassEquivFixed B
  let eTower := numberFieldTowerIdeleClassEquivAmbientFixed K L
  let f : Additive (IdeleClassGroup K) →+
      KummerTheory.ambientFixedAddSubgroup
        (ideleClassRepresentation ℚ) B :=
    eTower.toAddMonoidHom
  let g : KummerTheory.ambientFixedAddSubgroup
      (ideleClassRepresentation ℚ) B →+
        Additive (IdeleClassGroup (ordinaryNormClassFieldBase K L)) :=
    eFixed.symm.toAddMonoidHom
  let h : Additive (IdeleClassGroup K) →+
      Additive (IdeleClassGroup (ordinaryNormClassFieldBase K L)) :=
    (MulEquiv.toAdditive
      (ideleClassCongr
        (ordinaryNormClassFieldBaseEquiv K L))).toAddMonoidHom
  have hnorm :
      (M.normSubgroup (ideleClassRepresentation ℚ)).map
          g =
        (_root_.ideleClassNorm
          (ordinaryNormClassFieldBase K L)
          (ordinaryNormClassFieldExtension K L H hLH)).range.toAddSubgroup := by
    simpa only [FiniteAbelianSubextension.normSubgroup,
      M, B, ordinaryNormClassFieldBase,
      ordinaryNormClassFieldExtension] using
      (map_rationalFiniteNormSubgroup_eq_ordinaryIdeleClassNormRange_concrete
        B M.field M.below M.normal)
  have hcomp :
      g.comp f = h := by
    exact numberFieldTowerIdeleClassEquivAmbientFixed_comp K L
  calc
    (_root_.ideleClassNorm
          (ordinaryNormClassFieldBase K L)
          (ordinaryNormClassFieldExtension K L H hLH)).range.toAddSubgroup =
        (M.normSubgroup (ideleClassRepresentation ℚ)).map
          g := hnorm.symm
    _ =
        (H.toAddSubgroup.map f).map g := by
      exact
        congrArg
          (fun S : AddSubgroup
              (KummerTheory.ambientFixedAddSubgroup
                (ideleClassRepresentation ℚ) B) =>
            AddSubgroup.map
              (N := Additive (IdeleClassGroup (ordinaryNormClassFieldBase K L))) g S)
          (ordinaryNormClassFieldSubextension_normSubgroup
            K L H hLH)
    _ = H.toAddSubgroup.map h := by
      rw [AddSubgroup.map_map, hcomp]

/-- Transport the norm-range formula for the fixed-field realization used by
the Hilbert tower to multiplicative standard idèle classes. -/
theorem ordinaryNormClassField_ideleClassNorm_range_over_base
    (H : Subgroup (IdeleClassGroup K))
    (hLH : (_root_.ideleClassNorm K L).range ≤ H) :
    (_root_.ideleClassNorm (ordinaryNormClassFieldBase K L)
      (ordinaryNormClassFieldExtension K L H hLH)).range =
      H.map (ideleClassCongr (ordinaryNormClassFieldBaseEquiv K L)).toMonoidHom := by
  let e := ideleClassCongr (ordinaryNormClassFieldBaseEquiv K L)
  have hMap : (H.map e.toMonoidHom).toAddSubgroup =
      H.toAddSubgroup.map (MulEquiv.toAdditive e).toAddMonoidHom :=
    (MonoidHom.coe_toAdditive_map e.toMonoidHom H).symm
  exact congrArg AddSubgroup.toSubgroup
    ((ordinaryNormClassField_ideleClassNorm_range K L H hLH).trans hMap.symm)

end GlobalClassFields
end GlobalClassFieldTheory
