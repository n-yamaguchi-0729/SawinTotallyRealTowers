/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.ClassEmbeddingBaseChange
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimit
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitFiniteEmbedding
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitFiniteTowerNormStatement
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.NormComparison
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.ClassGroup

/-!
# Proof of ordinary norm comparison in finite towers of rational fixed fields

This proof leaf installs the canonical finite-tower context once and splits
the normal-closure embedding calculation, the pointwise coset action, and the
finite product calculation into separate commands.  The public theorem is a
thin wrapper around those providers.
-/

@[expose] public section

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open LocalClassFieldTheory
open CyclicCohomology
open FiniteTowerNormCore

attribute [local instance] ideleClassDirectLimitSMul

private theorem rationalClassEmbedding_directLimit_smul
    (E : IntermediateField ℚ (SeparableClosure ℚ)) [FiniteDimensional ℚ E]
    (U : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ))
    (hEU : E ≤ U.toIntermediateField) (c : IdeleClassGroup E)
    (σ : Gal(SeparableClosure ℚ/ℚ)) :
    σ • rationalIntermediateIdeleClassToDirectLimit E c =
      rationalIntermediateIdeleClassToDirectLimit U
        (relativeIdeleClassBaseChangeMulEquiv (K := ℚ) (L := U)
          (RelativeIdeleGroup.classEmbedding
            ((AlgEquiv.restrictNormalHom (↥U.toIntermediateField) σ).toAlgHom.comp
              (IntermediateField.inclusion hEU))
            ((relativeIdeleClassBaseChangeMulEquiv (K := ℚ) (L := E)).symm c))) := by
  let d := (relativeIdeleClassBaseChangeMulEquiv (K := ℚ) (L := E)).symm c
  let τ := AlgEquiv.restrictNormalHom (↥U.toIntermediateField) σ
  let j := IntermediateField.inclusion hEU
  have hStage := rationalIntermediateIdeleClassToDirectLimit_classEmbedding E U hEU c
  have hAction := rationalRelativeIdeleClassToDirectLimit_smul U σ
    (RelativeIdeleGroup.classEmbedding j d)
  have hComp := classEmbedding_smul_eq_classEmbedding_comp j τ d
  have hEval := rationalFiniteGaloisIdeleClassToDirectLimit_baseChange U
    (RelativeIdeleGroup.classEmbedding (τ.toAlgHom.comp j) d)
  exact (congrArg (σ • ·) hStage).trans
    (hAction.trans ((congrArg (rationalRelativeIdeleClassToDirectLimit U) hComp).trans hEval.symm))

private theorem rationalIntermediateIdeleClassToDirectLimit_ordinaryExtension
    {E U : IntermediateField ℚ (SeparableClosure ℚ)}
    [FiniteDimensional ℚ E] [FiniteDimensional ℚ U] (h : E ≤ U) (x : IdeleClassGroup E) :
    let _ : Algebra E U := (IntermediateField.inclusion h).toRingHom.toAlgebra
    rationalIntermediateIdeleClassToDirectLimit U (ideleClassExtension E U x) =
      rationalIntermediateIdeleClassToDirectLimit E x := by
  intro hAlg
  let _ : IsScalarTower ℚ E U := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  let _ : FiniteDimensional E U := FiniteDimensional.right ℚ E U
  let d := (relativeIdeleClassBaseChangeMulEquiv (K := ℚ) (L := E)).symm x
  have h₀ := rationalIntermediateIdeleClassToDirectLimit_extension h d
  have hj : IntermediateField.inclusion h = IsScalarTower.toAlgHom ℚ E U := by
    ext a
    rfl
  let rU := relativeIdeleClassBaseChangeMulEquiv (K := ℚ) (L := U)
  have h₁ : rU (RelativeIdeleGroup.classEmbedding (IntermediateField.inclusion h) d) =
      ideleClassExtension E U x :=
    (congrArg (fun j => rU (RelativeIdeleGroup.classEmbedding j d)) hj).trans
      ((relativeIdeleClassBaseChange_classEmbedding_toAlgHom
        (K := ℚ) (M := E) (L := U) d).trans
        (congrArg (ideleClassExtension E U)
          ((relativeIdeleClassBaseChangeMulEquiv (K := ℚ) (L := E)).apply_symm_apply x)))
  let iE := rationalIntermediateIdeleClassToDirectLimit E
  let iU := rationalIntermediateIdeleClassToDirectLimit U
  exact (congrArg iU h₁).symm.trans
    (h₀.trans (congrArg iE
      ((relativeIdeleClassBaseChangeMulEquiv (K := ℚ) (L := E)).apply_symm_apply x)))

section RationalFiniteTower

variable
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hKfinite : Finite (rationalFixedFieldAbsoluteQuotient K)]
    [hfinite : Finite
      (rationalFixedFieldRelativeQuotient K L hLK)]

local notation "F₀" =>
  abstractFixedField ℚ (SeparableClosure ℚ) K
local notation "E₀" =>
  abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
local notation "N₀" =>
  IntermediateField.normalClosure F₀ E₀ (SeparableClosure ℚ)
local notation "EQ₀" => IntermediateField.restrictScalars ℚ E₀
local notation "NQ₀" => IntermediateField.restrictScalars ℚ N₀
local notation "U₀" => finiteIdeleClassNormalClosure ℚ NQ₀
local notation "Q₀" =>
  K.toSubgroup ⧸ extensionSubgroup K L hLK

private noncomputable local instance rationalFiniteTowerLowerFiniteDimensional :
    FiniteDimensional ℚ F₀ :=
  abstractFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ) K hKfinite

private noncomputable local instance rationalFiniteTowerUpperFiniteDimensional :
    FiniteDimensional F₀ E₀ :=
  abstractRelativeFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite

private local instance rationalFiniteTowerLowerUpperScalarTower :
    IsScalarTower ℚ F₀ E₀ :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

private noncomputable local instance rationalFiniteTowerUpperAbsoluteFiniteDimensional :
    FiniteDimensional ℚ E₀ :=
  FiniteDimensional.trans ℚ F₀ E₀

private noncomputable local instance rationalFiniteTowerRestrictedUpperFiniteDimensional :
    FiniteDimensional ℚ EQ₀ := by
  change FiniteDimensional ℚ E₀
  infer_instance

private noncomputable local instance rationalFiniteTowerLowerNumberField :
    NumberField F₀ :=
  NumberField.of_module_finite ℚ F₀

private noncomputable local instance rationalFiniteTowerUpperNumberField :
    NumberField E₀ :=
  NumberField.of_module_finite ℚ E₀

private local instance rationalFiniteTowerUpperSeparableClosureScalarTower :
    IsScalarTower F₀ E₀ (SeparableClosure ℚ) :=
  IsScalarTower.of_algebraMap_eq' (by
    ext x
    rfl)

omit hKfinite hfinite in
private theorem rationalFiniteTower_lower_le_upper :
    F₀ ≤ IntermediateField.restrictScalars ℚ E₀ :=
  abstractFixedField_le ℚ (SeparableClosure ℚ) hLK

omit hKfinite hfinite in
private theorem rationalFiniteTower_upper_le_normal :
    IntermediateField.restrictScalars ℚ E₀ ≤ NQ₀ := by
  intro x hx
  exact IntermediateField.le_normalClosure E₀ hx

omit hKfinite hfinite in
private theorem rationalFiniteTower_lower_le_normal :
    F₀ ≤ NQ₀ :=
  (rationalFiniteTower_lower_le_upper K L hLK).trans
    (rationalFiniteTower_upper_le_normal K L hLK)

private local instance rationalFiniteTowerNormalScalarTower :
    IsScalarTower ℚ F₀ N₀ :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

private noncomputable local instance rationalFiniteTowerNormalFiniteDimensional :
    FiniteDimensional F₀ N₀ :=
  normalClosure.is_finiteDimensional F₀ E₀ (SeparableClosure ℚ)

private noncomputable local instance rationalFiniteTowerNormalAbsoluteFiniteDimensional :
    FiniteDimensional ℚ N₀ :=
  FiniteDimensional.trans ℚ F₀ N₀

private noncomputable local instance rationalFiniteTowerNormalNumberField :
    NumberField N₀ :=
  NumberField.of_module_finite ℚ N₀

private noncomputable local instance rationalFiniteTowerRestrictedNormalFiniteDimensional :
    FiniteDimensional ℚ NQ₀ := by
  change FiniteDimensional ℚ N₀
  infer_instance

private theorem rationalFiniteTower_normal_le_rationalNormalClosure :
    NQ₀ ≤ (U₀ : IntermediateField ℚ (SeparableClosure ℚ)) := by
  change NQ₀ ≤ IntermediateField.normalClosure
    ℚ NQ₀ (SeparableClosure ℚ)
  exact IntermediateField.le_normalClosure NQ₀

private theorem rationalFiniteTower_lower_le_rationalNormalClosure :
    F₀ ≤ (U₀ : IntermediateField ℚ (SeparableClosure ℚ)) :=
  (rationalFiniteTower_lower_le_normal K L hLK).trans
    (rationalFiniteTower_normal_le_rationalNormalClosure K L hLK)

private theorem rationalFiniteTower_upper_le_rationalNormalClosure :
    IntermediateField.restrictScalars ℚ E₀ ≤
      (U₀ : IntermediateField ℚ (SeparableClosure ℚ)) :=
  (rationalFiniteTower_upper_le_normal K L hLK).trans
    (rationalFiniteTower_normal_le_rationalNormalClosure K L hLK)

private local instance rationalFiniteTowerRationalNormalClosureLowerAlgebra :
    Algebra F₀ U₀ :=
  (IntermediateField.inclusion
    (rationalFiniteTower_lower_le_rationalNormalClosure K L hLK)).toRingHom.toAlgebra

private local instance rationalFiniteTowerRationalNormalClosureUpperAlgebra :
    Algebra E₀ U₀ :=
  (IntermediateField.inclusion
    (rationalFiniteTower_upper_le_rationalNormalClosure K L hLK)).toRingHom.toAlgebra

private local instance rationalFiniteTowerRationalNormalClosureNormalAlgebra :
    Algebra N₀ U₀ :=
  (IntermediateField.inclusion
    (rationalFiniteTower_normal_le_rationalNormalClosure K L hLK)).toRingHom.toAlgebra

private local instance rationalFiniteTowerRationalNormalClosureLowerScalarTower :
    IsScalarTower ℚ F₀ U₀ :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

private local instance rationalFiniteTowerRationalNormalClosureUpperScalarTower :
    IsScalarTower ℚ E₀ U₀ :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

private local instance rationalFiniteTowerRationalNormalClosureNormalScalarTower :
    IsScalarTower ℚ N₀ U₀ :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

private local instance rationalFiniteTowerLowerUpperClosureScalarTower :
    IsScalarTower F₀ E₀ U₀ :=
  IsScalarTower.of_algebraMap_eq' (by
    ext x
    rfl)

private local instance rationalFiniteTowerLowerNormalClosureScalarTower :
    IsScalarTower F₀ N₀ U₀ :=
  IsScalarTower.of_algebraMap_eq' (by
    ext x
    rfl)

private local instance rationalFiniteTowerClosureSeparableClosureScalarTower :
    IsScalarTower F₀ U₀ (SeparableClosure ℚ) :=
  IsScalarTower.of_algebraMap_eq' (by
    ext x
    rfl)

private noncomputable local instance rationalFiniteTowerClosureOverUpperFiniteDimensional :
    FiniteDimensional E₀ U₀ :=
  FiniteDimensional.right ℚ E₀ U₀

private noncomputable local instance rationalFiniteTowerClosureOverLowerFiniteDimensional :
    FiniteDimensional F₀ U₀ :=
  FiniteDimensional.right ℚ F₀ U₀

private noncomputable local instance rationalFiniteTowerClosureOverNormalFiniteDimensional :
    FiniteDimensional N₀ U₀ :=
  FiniteDimensional.right ℚ N₀ U₀

private local instance rationalFiniteTowerLowerSeparableClosureGalois :
    IsGalois F₀ (SeparableClosure ℚ) :=
  IsGalois.tower_top_of_isGalois ℚ F₀ (SeparableClosure ℚ)

private local instance rationalFiniteTowerNormalGalois : IsGalois F₀ N₀ :=
  IsGalois.normalClosure F₀ E₀ (SeparableClosure ℚ)

private local instance rationalFiniteTowerClosureOverLowerGalois : IsGalois F₀ U₀ :=
  IsGalois.tower_top_of_isGalois ℚ F₀ U₀

private local instance rationalFiniteTowerClosureOverNormalGalois : IsGalois N₀ U₀ :=
  IsGalois.tower_top_of_isGalois ℚ N₀ U₀

private noncomputable local instance rationalFiniteTowerQuotientFintype : Fintype Q₀ :=
  Fintype.ofFinite Q₀

private noncomputable def rationalFiniteTowerCosetEquiv :
    Q₀ ≃ (E₀ →ₐ[F₀] N₀) :=
  (abstractFixedFieldCosetEquivAlgHom
    ℚ (SeparableClosure ℚ) K L hLK).trans
    (normalClosureAlgHomEquiv
      (F := F₀) (E := E₀) (L := SeparableClosure ℚ))

private noncomputable def rationalFiniteTowerNormalInclusion :
    N₀ →ₐ[F₀] U₀ :=
  algHomOfCompatibleRingHom
    (IntermediateField.inclusion
      (rationalFiniteTower_normal_le_rationalNormalClosure K L hLK)).toRingHom
    (fun _ => rfl)

private noncomputable def rationalFiniteTowerUpperInclusion :
    E₀ →ₐ[ℚ] U₀ :=
  IntermediateField.inclusion
    (rationalFiniteTower_upper_le_rationalNormalClosure K L hLK)

private noncomputable def rationalFiniteTowerRelativeClass
    (c : IdeleClassGroup E₀) :
    RelativeIdeleGroup.ClassGroup F₀ E₀ :=
  (_root_.relativeIdeleClassBaseChangeMulEquiv
    (K := F₀) (L := E₀)).symm c

private noncomputable def rationalFiniteTowerRationalRelativeClass
    (c : IdeleClassGroup E₀) :
    RelativeIdeleGroup.ClassGroup ℚ E₀ :=
  (_root_.relativeIdeleClassBaseChangeMulEquiv
    (K := ℚ) (L := E₀)).symm c

private noncomputable def rationalFiniteTowerEmbeddedClass
    (c : IdeleClassGroup E₀) (q : Q₀) : IdeleClassGroup U₀ :=
  _root_.relativeIdeleClassBaseChangeMulEquiv
    (K := F₀) (L := U₀)
    (RelativeIdeleGroup.classEmbedding
      ((rationalFiniteTowerNormalInclusion K L hLK).comp
        (rationalFiniteTowerCosetEquiv K L hLK q))
      (rationalFiniteTowerRelativeClass K L hLK c))

private theorem rationalFiniteTowerCoset_comp_normalInclusion
    (q : Q₀) :
    (IsScalarTower.toAlgHom F₀ U₀ (SeparableClosure ℚ)).comp
        ((rationalFiniteTowerNormalInclusion K L hLK).comp
          (rationalFiniteTowerCosetEquiv K L hLK q)) =
      abstractFixedFieldCosetToAlgHom
        ℚ (SeparableClosure ℚ) K L hLK q := by
  apply AlgHom.ext
  intro x
  change
    ((normalClosure.algHomEquiv
      F₀ E₀ (SeparableClosure ℚ))
        ((normalClosure.algHomEquiv
          F₀ E₀ (SeparableClosure ℚ)).symm
          (abstractFixedFieldCosetToAlgHom
            ℚ (SeparableClosure ℚ) K L hLK q))) x = _
  exact DFunLike.congr_fun
    ((normalClosure.algHomEquiv
      F₀ E₀ (SeparableClosure ℚ)).apply_symm_apply
      (abstractFixedFieldCosetToAlgHom
        ℚ (SeparableClosure ℚ) K L hLK q)) x

private theorem rationalFiniteTower_restrictedEmbedding
    (sigma : K.toSubgroup) :
    (AlgEquiv.restrictNormalHom U₀ sigma.1).toAlgHom.comp
        (rationalFiniteTowerUpperInclusion K L hLK) =
      ((rationalFiniteTowerNormalInclusion K L hLK).comp
        (rationalFiniteTowerCosetEquiv K L hLK
          (QuotientGroup.mk sigma))).restrictScalars ℚ := by
  apply AlgHom.ext
  intro x
  apply (IsScalarTower.toAlgHom ℚ U₀
    (SeparableClosure ℚ)).injective
  change
    algebraMap U₀ (SeparableClosure ℚ)
        ((AlgEquiv.restrictNormalHom U₀ sigma.1)
          (rationalFiniteTowerUpperInclusion K L hLK x)) =
      algebraMap U₀ (SeparableClosure ℚ)
        ((rationalFiniteTowerNormalInclusion K L hLK)
          (rationalFiniteTowerCosetEquiv K L hLK
            (QuotientGroup.mk sigma) x))
  calc
    algebraMap U₀ (SeparableClosure ℚ)
        ((AlgEquiv.restrictNormalHom U₀ sigma.1)
          (rationalFiniteTowerUpperInclusion K L hLK x)) =
      sigma.1
        (algebraMap U₀ (SeparableClosure ℚ)
          (rationalFiniteTowerUpperInclusion K L hLK x)) :=
      AlgEquiv.restrictNormal_commutes sigma.1 U₀
        (rationalFiniteTowerUpperInclusion K L hLK x)
    _ = sigma.1 (x : SeparableClosure ℚ) := by rfl
    _ = (abstractFixedFieldCosetToAlgHom
        ℚ (SeparableClosure ℚ) K L hLK
          (QuotientGroup.mk sigma)) x := by rfl
    _ = algebraMap U₀ (SeparableClosure ℚ)
        ((rationalFiniteTowerNormalInclusion K L hLK)
          (rationalFiniteTowerCosetEquiv K L hLK
            (QuotientGroup.mk sigma) x)) :=
      (DFunLike.congr_fun
        (rationalFiniteTowerCoset_comp_normalInclusion K L hLK
          (QuotientGroup.mk sigma)) x).symm

private theorem rationalFiniteTower_representativeAction
    (c : IdeleClassGroup E₀) (sigma : K.toSubgroup) :
    Additive.toMul
        (Additive.ofMul
          (sigma.1 •
            rationalIntermediateIdeleClassToDirectLimit EQ₀ c)) =
      rationalIntermediateIdeleClassToDirectLimit U₀
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := U₀)
          (RelativeIdeleGroup.classEmbedding
            ((AlgEquiv.restrictNormalHom U₀ sigma.1).toAlgHom.comp
              (rationalFiniteTowerUpperInclusion K L hLK))
            (rationalFiniteTowerRationalRelativeClass K L hLK c))) := by
  exact rationalClassEmbedding_directLimit_smul EQ₀ U₀
    (rationalFiniteTower_upper_le_rationalNormalClosure K L hLK) c sigma.1

private theorem rationalRelativeFixedFieldCosetActionPointwise
    (c : IdeleClassGroup E₀) (q : Q₀) :
    Additive.toMul
        ((relativeCosetAction (ideleClassRepresentation ℚ)
          K L hLK
          (rationalAbstractRelativeFixedFieldIdeleClassEquivFixedOfFiniteDimensional
            K L hLK (Additive.ofMul c)) q :
          Additive (ideleClassDirectLimit ℚ))) =
      rationalIntermediateIdeleClassToDirectLimit
        (U₀ : IntermediateField ℚ (SeparableClosure ℚ))
        (rationalFiniteTowerEmbeddedClass K L hLK c q) := by
  let dℚ := rationalFiniteTowerRationalRelativeClass K L hLK c
  let a := rationalAbstractRelativeFixedFieldIdeleClassEquivFixedOfFiniteDimensional
    K L hLK (Additive.ofMul c)
  let term (q : Q₀) : Additive (ideleClassDirectLimit ℚ) :=
    relativeCosetAction (ideleClassRepresentation ℚ) K L hLK a q
  let g := rationalIntermediateIdeleClassToDirectLimit U₀
  let P (q : Q₀) := (term q).toMul = g (rationalFiniteTowerEmbeddedClass K L hLK c q)
  have hp (σ : K.toSubgroup) : P (QuotientGroup.mk σ) := by
    let f := (rationalFiniteTowerNormalInclusion K L hLK).comp
      (rationalFiniteTowerCosetEquiv K L hLK (QuotientGroup.mk σ))
    let τ := AlgEquiv.restrictNormalHom U₀ σ.1
    let embed (j : EQ₀ →ₐ[ℚ] U₀) := g
      (relativeIdeleClassBaseChangeMulEquiv (K := ℚ) (L := U₀)
        (RelativeIdeleGroup.classEmbedding j dℚ))
    have h₀ := rationalFiniteTower_representativeAction K L hLK c σ
    have h₁ := congrArg embed (rationalFiniteTower_restrictedEmbedding K L hLK σ)
    have h₂ := congrArg g (relativeIdeleClassBaseChange_classEmbedding_changeBase
      (k := ℚ) (F := F₀) (E := E₀) (U := U₀) f c)
    change (term (QuotientGroup.mk σ)).toMul = _
    have hact : (term (QuotientGroup.mk σ)).toMul =
        σ.1 • rationalIntermediateIdeleClassToDirectLimit EQ₀ c := by
      exact congrArg Additive.toMul
        (relativeCosetAction_mk (ideleClassRepresentation ℚ) K L hLK a σ)
    exact hact.trans (h₀.trans (h₁.trans h₂))
  let mk : K.toSubgroup → Q₀ := QuotientGroup.mk
  have hm : Function.Surjective mk := QuotientGroup.mk_surjective
  exact (hm.forall.mpr hp) q

private theorem rationalFiniteTower_product_embeddedClass
    (c : IdeleClassGroup E₀) :
    ∏ q : Q₀, rationalFiniteTowerEmbeddedClass K L hLK c q =
      _root_.relativeIdeleClassBaseChangeMulEquiv
        (K := F₀) (L := U₀)
        (RelativeIdeleGroup.classEmbedding
          (rationalFiniteTowerNormalInclusion K L hLK)
          (RelativeIdeleGroup.classInclusion F₀ N₀
            (RelativeIdeleGroup.classNorm F₀ E₀
              (rationalFiniteTowerRelativeClass K L hLK c)))) := by
  unfold rationalFiniteTowerEmbeddedClass
  exact relativeIdeleClassBaseChange_prod_embeddings
    (rationalFiniteTowerCosetEquiv K L hLK)
    (rationalFiniteTowerNormalInclusion K L hLK)
    (rationalFiniteTowerRelativeClass K L hLK c)

private theorem rationalFiniteTowerNormalInclusion_eq_toAlgHom :
    rationalFiniteTowerNormalInclusion K L hLK =
      IsScalarTower.toAlgHom F₀ N₀ U₀ := by
  apply AlgHom.ext
  intro x
  rfl

private theorem rationalFiniteTowerLowerInclusion_eq_toAlgHom :
    IntermediateField.inclusion
        (rationalFiniteTower_lower_le_rationalNormalClosure K L hLK) =
      IsScalarTower.toAlgHom ℚ F₀ U₀ := by
  apply AlgHom.ext
  intro x
  rfl

private theorem rationalFiniteTower_ideleClassExtension_comp_apply
    (x : IdeleClassGroup F₀) :
    _root_.ideleClassExtension N₀ U₀
        (_root_.ideleClassExtension F₀ N₀ x) =
      _root_.ideleClassExtension F₀ U₀ x := by
  have hcomp :
      (_root_.ideleClassExtension N₀ U₀).comp
          (_root_.ideleClassExtension F₀ N₀) =
        _root_.ideleClassExtension F₀ U₀ :=
    _root_.ideleClassExtension_comp
      (K := F₀) (L := U₀) N₀
  exact DFunLike.congr_fun hcomp x

private theorem rationalFiniteTower_baseChange_classInclusion
    (x : IdeleClassGroup F₀) :
    _root_.relativeIdeleClassBaseChangeMulEquiv
        (K := F₀) (L := N₀)
        (RelativeIdeleGroup.classInclusion F₀ N₀ x) =
      _root_.ideleClassExtension F₀ N₀ x :=
  _root_.relativeIdeleClassBaseChangeMulEquiv_classInclusion
    (K := F₀) (L := N₀) x

private theorem
    rationalFiniteTower_baseChange_normalInclusion_classInclusion
    (x : IdeleClassGroup F₀) :
    _root_.relativeIdeleClassBaseChangeMulEquiv
        (K := F₀) (L := U₀)
        (RelativeIdeleGroup.classEmbedding
          (rationalFiniteTowerNormalInclusion K L hLK)
          (RelativeIdeleGroup.classInclusion F₀ N₀ x)) =
      _root_.ideleClassExtension F₀ U₀ x := by
  let d := RelativeIdeleGroup.classInclusion F₀ N₀ x
  let e := relativeIdeleClassBaseChangeMulEquiv (K := F₀) (L := U₀)
  have h₀ := congrArg (fun j : N₀ →ₐ[F₀] U₀ => e (RelativeIdeleGroup.classEmbedding j d))
    (rationalFiniteTowerNormalInclusion_eq_toAlgHom K L hLK)
  have h₁ := relativeIdeleClassBaseChange_classEmbedding_toAlgHom
    (K := F₀) (M := N₀) (L := U₀) d
  have h₂ := congrArg (ideleClassExtension N₀ U₀)
    (rationalFiniteTower_baseChange_classInclusion K L hLK x)
  exact h₀.trans (h₁.trans
    (h₂.trans (rationalFiniteTower_ideleClassExtension_comp_apply K L hLK x)))

private theorem rationalFiniteTower_directLimit_ideleClassExtension
    (x : IdeleClassGroup F₀) :
    rationalIntermediateIdeleClassToDirectLimit
        (U₀ : IntermediateField ℚ (SeparableClosure ℚ))
        (_root_.ideleClassExtension F₀ U₀ x) =
      rationalIntermediateIdeleClassToDirectLimit F₀ x := by
  exact rationalIntermediateIdeleClassToDirectLimit_ordinaryExtension
    (rationalFiniteTower_lower_le_rationalNormalClosure K L hLK) x

private theorem rationalFiniteTower_relativeClassNorm_eq_ordinaryNorm
    (c : IdeleClassGroup E₀) :
    RelativeIdeleGroup.classNorm F₀ E₀
        (rationalFiniteTowerRelativeClass K L hLK c) =
      _root_.ideleClassNorm F₀ E₀ c := by
  let d := rationalFiniteTowerRelativeClass K L hLK c
  have hd :
      _root_.relativeIdeleClassBaseChangeMulEquiv
          (K := F₀) (L := E₀) d = c := by
    dsimp only [d, rationalFiniteTowerRelativeClass]
    exact (_root_.relativeIdeleClassBaseChangeMulEquiv
      (K := F₀) (L := E₀)).apply_symm_apply c
  calc
    RelativeIdeleGroup.classNorm F₀ E₀ d =
        _root_.ideleClassNorm F₀ E₀
          (_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := F₀) (L := E₀) d) :=
      (ordinaryIdeleClassNorm_relativeIdeleClassBaseChange d).symm
    _ = _root_.ideleClassNorm F₀ E₀ c :=
      congrArg (_root_.ideleClassNorm F₀ E₀) hd

private theorem rationalFiniteTower_directLimit_extension_eq_norm
    (c : IdeleClassGroup E₀) :
    rationalIntermediateIdeleClassToDirectLimit
        (U₀ : IntermediateField ℚ (SeparableClosure ℚ))
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := F₀) (L := U₀)
          (RelativeIdeleGroup.classEmbedding
            (rationalFiniteTowerNormalInclusion K L hLK)
            (RelativeIdeleGroup.classInclusion F₀ N₀
              (RelativeIdeleGroup.classNorm F₀ E₀
                (rationalFiniteTowerRelativeClass K L hLK c))))) =
      rationalIntermediateIdeleClassToDirectLimit F₀
        (_root_.ideleClassNorm F₀ E₀ c) := by
  calc
    rationalIntermediateIdeleClassToDirectLimit
        (U₀ : IntermediateField ℚ (SeparableClosure ℚ))
        (_root_.relativeIdeleClassBaseChangeMulEquiv
        (K := F₀) (L := U₀)
        (RelativeIdeleGroup.classEmbedding
          (rationalFiniteTowerNormalInclusion K L hLK)
          (RelativeIdeleGroup.classInclusion F₀ N₀
            (RelativeIdeleGroup.classNorm F₀ E₀
              (rationalFiniteTowerRelativeClass K L hLK c))))) =
      rationalIntermediateIdeleClassToDirectLimit U₀
        (_root_.ideleClassExtension F₀ U₀
          (RelativeIdeleGroup.classNorm F₀ E₀
            (rationalFiniteTowerRelativeClass K L hLK c))) := by
      apply congrArg
        (rationalIntermediateIdeleClassToDirectLimit
          (U₀ : IntermediateField ℚ (SeparableClosure ℚ)))
      exact
        rationalFiniteTower_baseChange_normalInclusion_classInclusion
          K L hLK
          (RelativeIdeleGroup.classNorm F₀ E₀
            (rationalFiniteTowerRelativeClass K L hLK c))
    _ = rationalIntermediateIdeleClassToDirectLimit F₀
        (RelativeIdeleGroup.classNorm F₀ E₀
          (rationalFiniteTowerRelativeClass K L hLK c)) :=
      rationalFiniteTower_directLimit_ideleClassExtension K L hLK _
    _ = rationalIntermediateIdeleClassToDirectLimit F₀
        (_root_.ideleClassNorm F₀ E₀ c) := by
      apply congrArg (rationalIntermediateIdeleClassToDirectLimit F₀)
      exact rationalFiniteTower_relativeClassNorm_eq_ordinaryNorm K L hLK c

private theorem rationalFiniteTower_product_embeddings_eq_norm
    (c : IdeleClassGroup E₀) :
    ∏ q : Q₀,
        rationalIntermediateIdeleClassToDirectLimit
          (U₀ : IntermediateField ℚ (SeparableClosure ℚ))
          (rationalFiniteTowerEmbeddedClass K L hLK c q) =
      rationalIntermediateIdeleClassToDirectLimit F₀
        (_root_.ideleClassNorm F₀ E₀ c) := by
  let g := rationalIntermediateIdeleClassToDirectLimit
    (U₀ : IntermediateField ℚ (SeparableClosure ℚ))
  let b : Q₀ → IdeleClassGroup U₀ := fun q =>
    rationalFiniteTowerEmbeddedClass K L hLK c q
  have hprodMap (s : Finset Q₀) :
      g (s.prod b) = s.prod (fun q => g (b q)) := by
    exact map_prod g b s
  change (∏ q : Q₀, g (b q)) = _
  calc
    ∏ q : Q₀, g (b q) = g (∏ q : Q₀, b q) :=
      (hprodMap Finset.univ).symm
    _ = g (_root_.relativeIdeleClassBaseChangeMulEquiv
        (K := F₀) (L := U₀)
        (RelativeIdeleGroup.classEmbedding
          (rationalFiniteTowerNormalInclusion K L hLK)
          (RelativeIdeleGroup.classInclusion F₀ N₀
            (RelativeIdeleGroup.classNorm F₀ E₀
              (rationalFiniteTowerRelativeClass K L hLK c))))) := by
      exact congrArg g
        (rationalFiniteTower_product_embeddedClass K L hLK c)
    _ = rationalIntermediateIdeleClassToDirectLimit F₀
        (_root_.ideleClassNorm F₀ E₀ c) :=
      rationalFiniteTower_directLimit_extension_eq_norm K L hLK c

private theorem mapped_additive_sum_toMul
    {A B X : Type*} [CommMonoid A] [CommMonoid B] [Fintype X]
    (g : A →* B) (f : X → A) :
    (g.toAdditive (∑ x, Additive.ofMul (f x))).toMul = ∏ x, g (f x) := by
  rw [map_sum, toMul_sum]
  rfl

private theorem rationalFiniteTower_sum_embeddings_eq_norm
    (c : IdeleClassGroup E₀) :
    (rationalIntermediateIdeleClassToDirectLimit U₀).toAdditive
        (∑ q : Q₀, Additive.ofMul (rationalFiniteTowerEmbeddedClass K L hLK c q)) =
      Additive.ofMul (rationalIntermediateIdeleClassToDirectLimit F₀
        (_root_.ideleClassNorm F₀ E₀ c)) := by
  let g := rationalIntermediateIdeleClassToDirectLimit U₀
  let b : Q₀ → IdeleClassGroup U₀ := rationalFiniteTowerEmbeddedClass K L hLK c
  have h₁ := mapped_additive_sum_toMul (B := (ideleClassDirectLimit ℚ)) g b
  have h₂ := rationalFiniteTower_product_embeddings_eq_norm K L hLK c
  exact Additive.toMul.injective (h₁.trans h₂)

private theorem rationalAbstractRelativeFixedFieldNorm_val
    (c : IdeleClassGroup E₀) :
    (relativeNorm (ideleClassRepresentation ℚ) K L hLK
        (rationalAbstractRelativeFixedFieldIdeleClassEquivFixedOfFiniteDimensional
          K L hLK (Additive.ofMul c))).1 =
      Additive.ofMul (rationalIntermediateIdeleClassToDirectLimit F₀
        (_root_.ideleClassNorm F₀ E₀ c)) := by
  let a := rationalAbstractRelativeFixedFieldIdeleClassEquivFixedOfFiniteDimensional
    K L hLK (Additive.ofMul c)
  let g := rationalIntermediateIdeleClassToDirectLimit U₀
  let i := g.toAdditive
  let f (q : Q₀) := Additive.ofMul (rationalFiniteTowerEmbeddedClass K L hLK c q)
  have hPoint (q : Q₀) : relativeCosetAction (ideleClassRepresentation ℚ) K L hLK a q =
      i (f q) :=
    Additive.toMul.injective (rationalRelativeFixedFieldCosetActionPointwise K L hLK c q)
  have hSum := relativeNorm_eq_mapped_sum (ideleClassRepresentation ℚ) K L hLK a
    i (Equiv.refl Q₀) f hPoint
  have hValue := rationalFiniteTower_sum_embeddings_eq_norm K L hLK c
  exact hSum.trans hValue

private theorem rationalAbstractRelativeFixedFieldNormCore
    (c : IdeleClassGroup E₀) :
    relativeNorm (ideleClassRepresentation ℚ) K L hLK
        (rationalAbstractRelativeFixedFieldIdeleClassEquivFixedOfFiniteDimensional
          K L hLK (Additive.ofMul c)) =
      rationalAbstractFixedFieldIdeleClassEquivFixed K
        (Additive.ofMul (_root_.ideleClassNorm F₀ E₀ c)) := by
  apply Subtype.ext
  let b := Additive.ofMul (_root_.ideleClassNorm F₀ E₀ c)
  have hb : (rationalAbstractFixedFieldIdeleClassEquivFixed K b).1 =
      Additive.ofMul (rationalIntermediateIdeleClassToDirectLimit F₀ b.toMul) := by
    exact rationalAbstractFixedFieldIdeleClassEquivFixed_coe K b
  exact (rationalAbstractRelativeFixedFieldNorm_val K L hLK c).trans hb.symm

/-- The abstract relative norm agrees with the ordinary idèle-class norm
for every finite tower of rational fixed fields. -/
theorem
    rationalAbstractRelativeFixedFieldIdeleClassEquivFixed_relativeNorm_ofFiniteTower :
    rationalAbstractRelativeFixedFieldNormStatement K L hLK := by
  unfold rationalAbstractRelativeFixedFieldNormStatement
  intro F E c
  exact rationalAbstractRelativeFixedFieldNormCore K L hLK c

end RationalFiniteTower

end Reciprocity
end GlobalClassFieldTheory
