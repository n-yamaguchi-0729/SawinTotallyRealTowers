/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.GroupTheory.Abelianization.Defs
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Main
public import Nyll.ValuedFieldTheory.Ramification.GaloisValuation.IntermediateFieldRestriction
public import Mathlib.FieldTheory.Galois.Abelian

/-!
# Restriction naturality for the concrete local norm-residue symbol

The abstract class formation supplies restriction naturality.  This file
constructs the field-facing restriction map for two finite Galois intermediate
fields in the fixed separable closure and transports the naturality identity
to the concrete local norm-residue symbol.

The intermediate-field restriction is packaged here so callers do not have
to install the auxiliary `Algebra E F` and scalar-tower instances attached
to an inclusion `E ≤ F`.
-/



@[expose] public section

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation LocalClassFieldTheory
open scoped IsMulCommutative

universe u v

variable {K : Type u} {Omega : Type v}
  [Field K] [Field Omega] [Algebra K Omega]

section IntermediateRestriction

variable (K : Type) [Field K]
  [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

private theorem commGroup_abelianizationCongr_of
    {G H : Type*} [Group G] [CommGroup H]
    (q : G ≃* H) (x : G) :
    (Group.Abelianization.equivOfComm (H := H)).symm
        (q.abelianizationCongr (Group.Abelianization.of x)) =
      q x := by
  exact
    (congrArg (Group.Abelianization.equivOfComm (H := H)).symm
      (Group.abelianizationCongr_of q x)).trans
      ((Group.Abelianization.equivOfComm (H := H)).symm_apply_apply (q x))

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem intermediateFieldRestrict_abstractQuotient_mk
    (E F : IntermediateField K (SeparableClosure K)) (hEF : E ≤ F)
    [FiniteDimensional K E] [FiniteDimensional K F]
    [IsGalois K E] [IsGalois K F]
    (sigma : (intrinsicAbstractBase K).toSubgroup) :
    intermediateFieldRestrictNormalHom E F hEF
        (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K F F.val
          (QuotientGroup.mk sigma)) =
      finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K E E.val
        (QuotientGroup.mk (Subgroup.inclusion le_rfl sigma)) := by
  apply AlgEquiv.ext
  intro x
  apply E.val.injective
  calc
    E.val ((intermediateFieldRestrictNormalHom E F hEF)
        (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K F F.val
          (QuotientGroup.mk sigma)) x) =
      F.val
        ((finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K F F.val
            (QuotientGroup.mk sigma))
          (IntermediateField.inclusion hEF x)) :=
            intermediateFieldRestrictNormalHom_apply_val E F hEF _ x
    _ = sigma.1 (F.val (IntermediateField.inclusion hEF x)) := by
      exact finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding_mk_apply
        K F F.val sigma (IntermediateField.inclusion hEF x)
    _ = (Subgroup.inclusion le_rfl sigma).1 (E.val x) := rfl
    _ = E.val
        ((finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K E E.val
          (QuotientGroup.mk (Subgroup.inclusion le_rfl sigma))) x) := by
      exact (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding_mk_apply
        K E E.val (Subgroup.inclusion le_rfl sigma) x).symm

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem embeddedAbstractExtension_field_le
    (E F : IntermediateField K (SeparableClosure K)) (hEF : E ≤ F)
    [FiniteDimensional K E] [FiniteDimensional K F]
    [IsGalois K E] [IsGalois K F] :
    (finiteGaloisAbstractExtensionOfEmbedding K F F.val).field.toSubgroup ≤
      (finiteGaloisAbstractExtensionOfEmbedding K E E.val).field.toSubgroup := by
  change
    (closedFixingSubgroup K (SeparableClosure K)
        (AlgHom.fieldRange F.val)).toSubgroup ≤
      (closedFixingSubgroup K (SeparableClosure K)
        (AlgHom.fieldRange E.val)).toSubgroup
  simp only [IntermediateField.fieldRange_val]
  change F.fixingSubgroup ≤ E.fixingSubgroup
  exact E.fixingSubgroup_le hEF

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem intermediateFieldRestrict_abstractAbelianization_of_mk
    (E F : IntermediateField K (SeparableClosure K)) (hEF : E ≤ F)
    [FiniteDimensional K E] [FiniteDimensional K F]
    [IsAbelianGalois K E] [IsAbelianGalois K F]
    (sigma : (intrinsicAbstractBase K).toSubgroup) :
    intermediateFieldRestrictNormalHom E F hEF
        ((Group.Abelianization.equivOfComm (H := Gal(F / K))).symm
          ((finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
            K F F.val).abelianizationCongr
              (Group.Abelianization.of (QuotientGroup.mk sigma)))) =
      (Group.Abelianization.equivOfComm (H := Gal(E / K))).symm
        ((finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
          K E E.val).abelianizationCongr
            (normResidueNaturalityAbelianizedRestriction
              (intrinsicAbstractBase K) (intrinsicAbstractBase K)
              (finiteGaloisAbstractExtensionOfEmbedding K E E.val).field
              (finiteGaloisAbstractExtensionOfEmbedding K F F.val).field
              (finiteGaloisAbstractExtensionOfEmbedding K E E.val).below
              (finiteGaloisAbstractExtensionOfEmbedding K F F.val).below
              le_rfl (embeddedAbstractExtension_field_le K E F hEF)
              (Group.Abelianization.of (QuotientGroup.mk sigma)))) := by
  let B := intrinsicAbstractBase K
  let EE := finiteGaloisAbstractExtensionOfEmbedding K E E.val
  let EF := finiteGaloisAbstractExtensionOfEmbedding K F F.val
  let qE := finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K E E.val
  let qF := finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K F F.val
  have hrestriction :
      normResidueNaturalityAbelianizedRestriction
          B B EE.field EF.field EE.below EF.below le_rfl
          (embeddedAbstractExtension_field_le K E F hEF)
          (Group.Abelianization.of (QuotientGroup.mk sigma)) =
        Group.Abelianization.of
          (QuotientGroup.mk (Subgroup.inclusion le_rfl sigma)) :=
    normResidueNaturalityAbelianizedRestriction_of_mk
      B B EE.field EF.field EE.below EF.below le_rfl
      (embeddedAbstractExtension_field_le K E F hEF) sigma
  calc
    intermediateFieldRestrictNormalHom E F hEF
        ((Group.Abelianization.equivOfComm (H := Gal(F / K))).symm
          (qF.abelianizationCongr
            (Group.Abelianization.of (QuotientGroup.mk sigma)))) =
      intermediateFieldRestrictNormalHom E F hEF
        (qF (QuotientGroup.mk sigma)) :=
      congrArg (intermediateFieldRestrictNormalHom E F hEF)
        (commGroup_abelianizationCongr_of
          qF (QuotientGroup.mk sigma))
    _ = qE (QuotientGroup.mk (Subgroup.inclusion le_rfl sigma)) :=
      intermediateFieldRestrict_abstractQuotient_mk K E F hEF sigma
    _ = (Group.Abelianization.equivOfComm (H := Gal(E / K))).symm
        (qE.abelianizationCongr
          (Group.Abelianization.of
            (QuotientGroup.mk (Subgroup.inclusion le_rfl sigma)))) :=
      (commGroup_abelianizationCongr_of qE
        (QuotientGroup.mk (Subgroup.inclusion le_rfl sigma))).symm
    _ = (Group.Abelianization.equivOfComm (H := Gal(E / K))).symm
        (qE.abelianizationCongr
          (normResidueNaturalityAbelianizedRestriction
            B B EE.field EF.field EE.below EF.below le_rfl
            (embeddedAbstractExtension_field_le K E F hEF)
            (Group.Abelianization.of (QuotientGroup.mk sigma)))) :=
      congrArg
        (fun w => (Group.Abelianization.equivOfComm
          (H := Gal(E / K))).symm (qE.abelianizationCongr w))
        hrestriction.symm

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem intermediateFieldRestrict_abstractAbelianization
    (E F : IntermediateField K (SeparableClosure K)) (hEF : E ≤ F)
    [FiniteDimensional K E] [FiniteDimensional K F]
    [IsAbelianGalois K E] [IsAbelianGalois K F]
    (z : Group.Abelianization
      (finiteGaloisAbstractExtensionOfEmbedding K F F.val).extensionQuotient) :
    intermediateFieldRestrictNormalHom E F hEF
        ((Group.Abelianization.equivOfComm (H := Gal(F / K))).symm
          ((finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K F F.val).abelianizationCongr
            z)) =
      (Group.Abelianization.equivOfComm (H := Gal(E / K))).symm
        ((finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K E E.val).abelianizationCongr
          (normResidueNaturalityAbelianizedRestriction
            (intrinsicAbstractBase K) (intrinsicAbstractBase K)
            (finiteGaloisAbstractExtensionOfEmbedding K E E.val).field
            (finiteGaloisAbstractExtensionOfEmbedding K F F.val).field
            (finiteGaloisAbstractExtensionOfEmbedding K E E.val).below
            (finiteGaloisAbstractExtensionOfEmbedding K F F.val).below
            le_rfl (embeddedAbstractExtension_field_le K E F hEF) z)) := by
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective z
  obtain ⟨sigma, rfl⟩ := QuotientGroup.mk_surjective q
  exact
    intermediateFieldRestrict_abstractAbelianization_of_mk
      K E F hEF sigma

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- Restriction naturality for the concrete norm-residue symbol, before
specializing the three structures of the local class formation.  Both
extensions are literal intermediate fields of the fixed separable closure,
so the vertical Galois map is the actual restriction map above. -/
theorem concreteNormResidueAutomorphism_restrict
    (E F : IntermediateField K (SeparableClosure K)) (hEF : E ≤ F)
    [FiniteDimensional K E] [FiniteDimensional K F]
    [IsAbelianGalois K E] [IsAbelianGalois K F]
    (D : DegreeData (intrinsicAbsoluteGalois K))
    (v : ValuationData D (intrinsicAbsoluteUnits K))
    (hcf : SatisfiesClassFieldAxiom (intrinsicAbsoluteUnits K)) (a : Kˣ) :
    intermediateFieldRestrictNormalHom E F hEF
        ((Group.Abelianization.equivOfComm (H := Gal(F / K))).symm
          (concreteNormResidueSymbolOfEmbedding
            K F F.val D v hcf a)) =
      (Group.Abelianization.equivOfComm (H := Gal(E / K))).symm
        (concreteNormResidueSymbolOfEmbedding
          K E E.val D v hcf a) := by
  let B := intrinsicAbstractBase K
  let BF := intrinsicFiniteAbstractBase K
  let EE := finiteGaloisAbstractExtensionOfEmbedding K E E.val
  let EF := finiteGaloisAbstractExtensionOfEmbedding K F F.val
  let qE := finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K E E.val
  let qF := finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K F F.val
  let xE := embeddedBaseNormClass K E E.val a
  let xF := embeddedBaseNormClass K F F.val a
  have hFE : EF.field.toSubgroup ≤ EE.field.toSubgroup :=
    embeddedAbstractExtension_field_le K E F hEF
  let hEENormal : (extensionSubgroup B EE.field EE.below).Normal :=
    EE.normal
  let hEFNormal : (extensionSubgroup B EF.field EF.below).Normal :=
    EF.normal
  let hEEFinite : Finite
      (B.toSubgroup ⧸ extensionSubgroup B EE.field EE.below) :=
    EE.finite
  let hEFFinite : Finite
      (B.toSubgroup ⧸ extensionSubgroup B EF.field EF.below) :=
    EF.finite
  let hBBFinite : Finite
      (B.toSubgroup ⧸ extensionSubgroup B B le_rfl) := by
    have htop : extensionSubgroup B B le_rfl = ⊤ := by
      ext sigma
      constructor
      · intro _
        trivial
      · intro _
        exact sigma.2
    rw [htop]
    infer_instance
  let T : FiniteAbstractFieldExtension (intrinsicAbsoluteGalois K) := {
    field := BF
    base := BF
    below := le_rfl
    finiteQuotient := hBBFinite }
  let : (extensionSubgroup T.base.field EE.field EE.below).Normal := by
    change (extensionSubgroup B EE.field EE.below).Normal
    exact hEENormal
  let : (extensionSubgroup T.field.field EF.field EF.below).Normal := by
    change (extensionSubgroup B EF.field EF.below).Normal
    exact hEFNormal
  let : Finite
      (T.base.field.toSubgroup ⧸
        extensionSubgroup T.base.field EE.field EE.below) := by
    change Finite (B.toSubgroup ⧸ extensionSubgroup B EE.field EE.below)
    exact hEEFinite
  let : Finite
      (T.field.field.toSubgroup ⧸
        extensionSubgroup T.field.field EF.field EF.below) := by
    change Finite (B.toSubgroup ⧸ extensionSubgroup B EF.field EF.below)
    exact hEFFinite
  have hnorm : finiteReciprocityNaturalityNormMap (intrinsicAbsoluteUnits K)
        B B EE.field EF.field EE.below EF.below le_rfl hFE xF = xE := by
    let aB := baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
      (Additive.ofMul a)
    have hmap := finiteReciprocityNaturalityNormMap_finiteNormClass
      (intrinsicAbsoluteUnits K) B B EE.field EF.field EE.below EF.below le_rfl hFE aB
    exact hmap.trans (congrArg
      (finiteNormClass (intrinsicAbsoluteUnits K) B EE.field EE.below)
      (relativeNorm_self (intrinsicAbsoluteUnits K) B aB))
  have hraw := D.normResidueNaturality_norm_restriction
    (intrinsicAbsoluteUnits K) v hcf
    T EE.field EF.field EE.below EF.below hFE
  have hrawa := DFunLike.congr_fun hraw xF
  change _ =
    D.normResidueSymbol (intrinsicAbsoluteUnits K) v hcf BF EE
      (finiteReciprocityNaturalityNormMap (intrinsicAbsoluteUnits K) B B EE.field EF.field EE.below
        EF.below le_rfl hFE xF) at hrawa
  rw [hnorm] at hrawa
  let zF := D.normResidueSymbol (intrinsicAbsoluteUnits K) v hcf BF EF xF
  let zE := D.normResidueSymbol (intrinsicAbsoluteUnits K) v hcf BF EE xE
  have hz : normResidueNaturalityAbelianizedRestriction
        B B EE.field EF.field EE.below EF.below le_rfl hFE
        (Additive.toMul zF) = Additive.toMul zE := by
    exact congrArg Additive.toMul hrawa
  rw [concreteNormResidueSymbolOfEmbedding_eq_abstract
      K F F.val D v hcf a,
    concreteNormResidueSymbolOfEmbedding_eq_abstract
      K E E.val D v hcf a]
  change intermediateFieldRestrictNormalHom E F hEF
      ((Group.Abelianization.equivOfComm (H := Gal(F / K))).symm
        (qF.abelianizationCongr (Additive.toMul zF))) =
    (Group.Abelianization.equivOfComm (H := Gal(E / K))).symm
      (qE.abelianizationCongr (Additive.toMul zE))
  calc
    intermediateFieldRestrictNormalHom E F hEF
        ((Group.Abelianization.equivOfComm (H := Gal(F / K))).symm
          (qF.abelianizationCongr (Additive.toMul zF))) =
      (Group.Abelianization.equivOfComm (H := Gal(E / K))).symm
        (qE.abelianizationCongr
          (normResidueNaturalityAbelianizedRestriction
            B B EE.field EF.field EE.below EF.below le_rfl hFE
            (Additive.toMul zF))) :=
      intermediateFieldRestrict_abstractAbelianization
        K E F hEF (Additive.toMul zF)
    _ = (Group.Abelianization.equivOfComm (H := Gal(E / K))).symm
        (qE.abelianizationCongr (Additive.toMul zE)) :=
      congrArg
        (fun w => (Group.Abelianization.equivOfComm
          (H := Gal(E / K))).symm (qE.abelianizationCongr w)) hz

/-- Restriction naturality for the canonical local norm-residue symbol,
expressed through automorphisms of finite abelian intermediate fields. -/
theorem localArtinAutomorphism_restrict
    (E F : IntermediateField K (SeparableClosure K)) (hEF : E ≤ F)
    [FiniteDimensional K E] [FiniteDimensional K F]
    [IsAbelianGalois K E] [IsAbelianGalois K F] (a : Kˣ) :
    intermediateFieldRestrictNormalHom E F hEF
        ((Group.Abelianization.equivOfComm (H := Gal(F / K))).symm
          (localArtinMonoidHom K F a)) =
      (Group.Abelianization.equivOfComm (H := Gal(E / K))).symm
        (localArtinMonoidHom K E a) := by
  rw [localArtinMonoidHom_eq_of_embedding K F F.val,
    localArtinMonoidHom_eq_of_embedding K E E.val]
  exact concreteNormResidueAutomorphism_restrict
    K E F hEF
      (localResidueDatum K)
      (localHenselianValuation K)
      (separableClosureUnits_isClassFormation K) a

end IntermediateRestriction

end LocalClassFieldTheory
