/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitExtensionAction
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimit
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitFiniteLevelCore
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.ClassEmbeddingBaseChange
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitStandardNorm
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.IdeleNorm
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.NormComparison
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.Tower
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.Herbrand
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.ClassGroup
public import Nyll.GaloisCohomology.Kummer.Abstract.KummerDelta

/-!
# Norms on rational fixed-field idele classes

Compatibility of fixed-field inclusion and relative norm with the actual
idele-class extension attached to the abstract subgroup tower.
-/



@[expose] public section

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open scoped NumberField
open ClassFormation
open LocalClassFieldTheory
open CyclicCohomology

attribute [local instance]
  ideleClassDirectLimitSMul rationalAbstractFixedFieldFiniteDimensional
  rationalAbstractTowerClassGroupCommGroup

private theorem repOfMulDistribMulAction_rho_toMul
    {G A : Type*} [Group G] [CommGroup A]
    [MulDistribMulAction G A]
    (g : G) (a : Additive A) :
    Additive.toMul
        ((Rep.ofMulDistribMulAction G A).ρ g a) =
      g • Additive.toMul a :=
  rfl

private theorem fintype_prod_comp_equiv
    {ι κ A : Type*}
    [Fintype ι] [Fintype κ] [CommMonoid A]
    (e : ι ≃ κ) (f : κ → A) :
    (∏ i, f (e i)) = ∏ k, f k :=
  Fintype.prod_equiv e
    (fun i => f (e i)) f (fun _ => rfl)

private theorem addEquiv_norm_toMul_eq_prod {Q C : Type*} [Group Q] [Fintype Q] [CommGroup C]
    (M : Rep ℤ Q) (e : M ≃+ Additive C) (x : M) :
    Additive.toMul (e (M.norm.asHom.hom x)) = ∏ q : Q, Additive.toMul (e (M.ρ q x)) := by
  change Additive.toMul (e ((∑ q : Q, M.ρ q) x)) = _
  rw [LinearMap.sum_apply, map_sum, toMul_sum]

private noncomputable def includedRelativeIdeleClassNormAdditiveValue
    (F E : Type)
    [Field F] [NumberField F]
    [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    (c : Additive (RelativeIdeleGroup.ClassGroup F E)) :
    Additive (RelativeIdeleGroup.ClassGroup F E) :=
  Additive.ofMul
    (RelativeIdeleGroup.classInclusion F E
      (RelativeIdeleGroup.classNorm F E
        (Additive.toMul c)))

private theorem rationalFixedPartExtension_inclusion
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (c : RelativeIdeleGroup.ClassGroup ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ) K)) :
    let F := abstractFixedField ℚ (SeparableClosure ℚ) K
    let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
    let : FiniteDimensional ℚ F :=
      abstractFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) K hKfinite
    let : FiniteDimensional F E :=
      abstractRelativeFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
    let : IsScalarTower ℚ F E :=
      IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
    let : FiniteDimensional ℚ E :=
      FiniteDimensional.trans ℚ F E
    let : NumberField F := NumberField.of_module_finite ℚ F
    let : NumberField E := NumberField.of_module_finite ℚ E
    let hFE : F ≤ E.restrictScalars ℚ := abstractFixedField_le ℚ (SeparableClosure ℚ) hLK
    let cE := RelativeIdeleGroup.classEmbedding (K := ℚ) (L := F) (M := E)
      (IntermediateField.inclusion hFE) c
    rationalAbstractRelativeFixedFieldIdeleClassEquivFixedOfFiniteDimensional K L hLK
        (Additive.ofMul (_root_.relativeIdeleClassBaseChangeMulEquiv (K := ℚ) (L := E) cE)) =
      fixedFieldInclusion (ideleClassRepresentation ℚ) K L hLK
        (rationalAbstractFixedFieldIdeleClassEquivFixed K
          (Additive.ofMul (_root_.relativeIdeleClassBaseChangeMulEquiv (K := ℚ) (L := F) c))) := by
  intro F E hFfinite hFEfinite htower hEfinite hFnumberField hEnumberField hFE cE
  let _ : FiniteDimensional ℚ (E.restrictScalars ℚ) := by
    change FiniteDimensional ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ) L)
    change FiniteDimensional ℚ E
    infer_instance
  let aK :
      KummerTheory.ambientFixedAddSubgroup
        (ideleClassRepresentation ℚ) K :=
    rationalAbstractFixedFieldIdeleClassEquivFixed K
      (Additive.ofMul
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := F) c))
  apply Subtype.ext
  calc
    _ =
        (rationalIdeleClassEquivFixed
          (E.restrictScalars ℚ)
          (Additive.ofMul
            (_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := E) cE))).1 := by
      rfl
    _ =
        (rationalIdeleClassEquivFixed F
          (Additive.ofMul
            (_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := F) c))).1 := by
      change
        Additive.ofMul
            (rationalIntermediateIdeleClassToDirectLimit
              (E.restrictScalars ℚ)
              (_root_.relativeIdeleClassBaseChangeMulEquiv
                (K := ℚ) (L := E.restrictScalars ℚ)
                (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := F) (M := E)
                  (IntermediateField.inclusion hFE) c))) =
          Additive.ofMul
            (rationalIntermediateIdeleClassToDirectLimit F
              (_root_.relativeIdeleClassBaseChangeMulEquiv
                (K := ℚ) (L := F) c))
      exact congrArg Additive.ofMul
        (rationalIntermediateIdeleClassToDirectLimit_extension hFE c)
    _ = aK.1 := by
      simpa only [aK, F] using
        (rationalAbstractFixedFieldIdeleClassEquivFixed_coe K
          (Additive.ofMul
            (_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := F) c))).symm
    _ =
        (fixedFieldInclusion (ideleClassRepresentation ℚ)
          K L hLK aK).1 := by
      exact
        (fixedFieldInclusion_coe (ideleClassRepresentation ℚ)
          K L hLK aK).symm

/-- The fixed-part inclusion from the lower abstract field to the upper
one becomes the existing relative idele-class inclusion under the
fixed-field realization. -/
theorem
    rationalAbstractExtensionIdeleClassEquiv_fixedFieldInclusion
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (c : RelativeIdeleGroup.ClassGroup ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ) K)) :
    let F := abstractFixedField ℚ (SeparableClosure ℚ) K
    let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
    let := hnormal
    let : FiniteDimensional ℚ F :=
      abstractFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) K hKfinite
    let : FiniteDimensional F E :=
      abstractRelativeFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
    let : IsScalarTower ℚ F E :=
      IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
    let : FiniteDimensional ℚ E :=
      FiniteDimensional.trans ℚ F E
    let : NumberField F := NumberField.of_module_finite ℚ F
    let : NumberField E := NumberField.of_module_finite ℚ E
    rationalAbstractExtensionIdeleClassEquiv K L hLK hnormal
        ((extensionFixedRepresentationEquiv
          (ideleClassRepresentation ℚ) K L hLK hnormal).symm
          (fixedFieldInclusion (ideleClassRepresentation ℚ)
            K L hLK
            (rationalAbstractFixedFieldIdeleClassEquivFixed K
              (Additive.ofMul
                (_root_.relativeIdeleClassBaseChangeMulEquiv
                  (K := ℚ) (L := F) c))))) =
      Additive.ofMul
        (RelativeIdeleGroup.classInclusion F E
          (_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := ℚ) (L := F) c)) := by
  intro F E hnormalInstance hFfinite hFEfinite htower hEfinite
    hFnumberField hEnumberField
  let _ : FiniteDimensional ℚ (E.restrictScalars ℚ) := by
    change FiniteDimensional ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ) L)
    change FiniteDimensional ℚ E
    infer_instance
  let hFE : F ≤ E.restrictScalars ℚ :=
    abstractFixedField_le ℚ (SeparableClosure ℚ) hLK
  let eAmbient :=
    extensionFixedRepresentationEquiv
      (ideleClassRepresentation ℚ) K L hLK hnormal
  let eFixed :
      Additive (IdeleClassGroup E) ≃+
        KummerTheory.ambientFixedAddSubgroup
          (ideleClassRepresentation ℚ) L :=
    rationalAbstractRelativeFixedFieldIdeleClassEquivFixedOfFiniteDimensional K L hLK
  let eRelative :
      Additive (RelativeIdeleGroup.ClassGroup ℚ E) ≃+
        Additive (IdeleClassGroup E) :=
    MulEquiv.toAdditive
      (_root_.relativeIdeleClassBaseChangeMulEquiv
        (K := ℚ) (L := E))
  let eTower :
      Additive (RelativeIdeleGroup.ClassGroup ℚ E) ≃+
        Additive (RelativeIdeleGroup.ClassGroup F E) :=
    MulEquiv.toAdditive
      ((TowerRelativeIdeleGroup.classGroupEquiv
        ℚ F E).symm.trans
        (towerRelativeIdeleClassBaseChangeMulEquiv
          ℚ F E))
  let aK :
      KummerTheory.ambientFixedAddSubgroup
        (ideleClassRepresentation ℚ) K :=
    rationalAbstractFixedFieldIdeleClassEquivFixed K
      (Additive.ofMul
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := F) c))
  let cE : RelativeIdeleGroup.ClassGroup ℚ E :=
    RelativeIdeleGroup.classEmbedding (K := ℚ) (L := F) (M := E)
      (IntermediateField.inclusion hFE) c
  let z : Additive (RelativeIdeleGroup.ClassGroup ℚ E) :=
    Additive.ofMul cE
  let y :
      (extensionFixedRepresentation (ideleClassRepresentation ℚ)
        K L hLK hnormal).V :=
    eAmbient.symm
      (fixedFieldInclusion (ideleClassRepresentation ℚ)
        K L hLK aK)
  have hFixed : eFixed (eRelative z) =
      fixedFieldInclusion (ideleClassRepresentation ℚ) K L hLK aK :=
    rationalFixedPartExtension_inclusion K L hLK c
  have hAmbient :
      eAmbient y = eFixed (eRelative z) := by
    calc
      eAmbient y =
          fixedFieldInclusion (ideleClassRepresentation ℚ)
            K L hLK aK :=
        eAmbient.apply_symm_apply _
      _ = eFixed (eRelative z) := hFixed.symm
  have hTower :
      eTower z =
        Additive.ofMul
          (RelativeIdeleGroup.classInclusion F E
            (_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := F) c)) := by
    apply Additive.toMul.injective
    change
      towerRelativeIdeleClassBaseChangeMulEquiv ℚ F E
          ((TowerRelativeIdeleGroup.classGroupEquiv
            ℚ F E).symm cE) =
        RelativeIdeleGroup.classInclusion F E
          (_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := ℚ) (L := F) c)
    exact
      FiniteTowerNormCore.relativeIdeleClassEmbedding_toAlgHom_towerBaseChange
        (K := ℚ) (M := F) (L := E) c
  let eOrd := MulEquiv.toAdditive
    (_root_.relativeIdeleClassBaseChangeMulEquiv (K := F) (L := E))
  change eOrd.symm (eFixed.symm (eAmbient y)) =
    Additive.ofMul
      (RelativeIdeleGroup.classInclusion F E
        (_root_.relativeIdeleClassBaseChangeMulEquiv (K := ℚ) (L := F) c))
  have hFirst := congrArg (fun a => eOrd.symm (eFixed.symm a)) hAmbient
  have hSecond := congrArg eOrd.symm (eFixed.symm_apply_apply (eRelative z))
  have hThird : eRelative z = eOrd (eTower z) := by
    apply Additive.toMul.injective
    exact (relativeIdeleClassBaseChangeMulEquiv_tower ℚ F E (Additive.toMul z)).symm
  exact hFirst.trans (hSecond.trans ((congrArg eOrd.symm hThird).trans
    ((eOrd.symm_apply_apply (eTower z)).trans hTower)))

/-- Under the fixed-field realization, the representation norm is the
existing relative idele-class norm, viewed in the upper class group by
the existing class inclusion. -/
theorem rationalAbstractExtensionIdeleClassEquiv_norm
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    [Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (x : (extensionFixedRepresentation (ideleClassRepresentation ℚ)
      K L hLK hnormal).V) :
    let F := abstractFixedField ℚ (SeparableClosure ℚ) K
    let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
    let := hnormal
    let : FiniteDimensional ℚ F :=
      abstractFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) K inferInstance
    let : FiniteDimensional F E :=
      abstractRelativeFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) K L hLK inferInstance inferInstance
    let : IsScalarTower ℚ F E :=
      IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
    let : FiniteDimensional ℚ E :=
      FiniteDimensional.trans ℚ F E
    let : NumberField F := NumberField.of_module_finite ℚ F
    let : NumberField E := NumberField.of_module_finite ℚ E
    let : IsGalois F E :=
      abstractRelativeFixedField_isGalois
        ℚ (SeparableClosure ℚ) K L hLK hnormal
    let M :=
      extensionFixedRepresentation (ideleClassRepresentation ℚ)
        K L hLK hnormal
    let e :=
      rationalAbstractExtensionIdeleClassEquiv K L hLK hnormal
    e (M.norm.asHom.hom x) =
      Additive.ofMul
        (RelativeIdeleGroup.classInclusion F E
          (RelativeIdeleGroup.classNorm F E
            (Additive.toMul (e x)))) := by
  intro F E hnormalInstance hFfinite hFEfinite htower hEfinite
    hFnumberField hEnumberField hGalois M e
  let _ : MulDistribMulAction (E ≃ₐ[F] E)
      (RelativeIdeleGroup.ClassGroup F E) :=
    RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction F E
  let Q := K.toSubgroup ⧸ extensionSubgroup K L hLK
  let _ : Fintype Q := Fintype.ofFinite Q
  let eQ :=
    abstractExtensionQuotientEquivGaloisGroup
      ℚ (SeparableClosure ℚ) K L hLK hnormal
  let c : RelativeIdeleGroup.ClassGroup F E :=
    Additive.toMul (e x)
  change e (M.norm.asHom.hom x) =
    includedRelativeIdeleClassNormAdditiveValue F E (e x)
  apply Additive.toMul.injective
  change Additive.toMul (e (M.norm.asHom.hom x)) =
    RelativeIdeleGroup.classInclusion F E (RelativeIdeleGroup.classNorm F E c)
  let e₀ : M ≃+ Additive (RelativeIdeleGroup.ClassGroup F E) := e
  refine (addEquiv_norm_toMul_eq_prod (C := RelativeIdeleGroup.ClassGroup F E) M e₀ x).trans ?_
  have hActionProd :
      (∏ q : Q, Additive.toMul (e (M.ρ q x))) =
        ∏ q : Q, eQ q • c := by
    apply Finset.prod_congr rfl
    intro q _
    have h := rationalAbstractExtensionIdeleClassEquiv_action K L hLK hnormal q x
    exact (congrArg Additive.toMul h).trans (repOfMulDistribMulAction_rho_toMul (eQ q) (e x))
  have hReindex :
      (∏ q : Q, eQ q • c) =
        ∏ τ : E ≃ₐ[F] E, τ • c := by
    exact fintype_prod_comp_equiv eQ.toEquiv
      (fun τ : E ≃ₐ[F] E => τ • c)
  have hNormProd :
      (∏ τ : E ≃ₐ[F] E, τ • c) =
        RelativeIdeleGroup.classInclusion F E
          (RelativeIdeleGroup.classNorm F E c) :=
    (RelativeIdeleGroup.classInclusion_ideleClassNorm_eq_prod_conjugates
      c).symm
  exact Eq.trans hActionProd (Eq.trans hReindex hNormProd)

/-- The relative norm in the rational absolute idele-class
representation is the existing relative idele-class norm on the two
actual fixed fields. -/
theorem
    rationalAbstractFixedFieldIdeleClassEquivFixed_relativeNorm
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (a : KummerTheory.ambientFixedAddSubgroup
      (ideleClassRepresentation ℚ) L) :
    let F := abstractFixedField ℚ (SeparableClosure ℚ) K
    let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
    let := hnormal
    let : FiniteDimensional ℚ F :=
      abstractFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) K hKfinite
    let : FiniteDimensional F E :=
      abstractRelativeFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
    let : IsScalarTower ℚ F E :=
      IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
    let : FiniteDimensional ℚ E :=
      FiniteDimensional.trans ℚ F E
    let : NumberField F := NumberField.of_module_finite ℚ F
    let : NumberField E := NumberField.of_module_finite ℚ E
    let : IsGalois F E :=
      abstractRelativeFixedField_isGalois
        ℚ (SeparableClosure ℚ) K L hLK hnormal
    let eAmbient :=
      extensionFixedRepresentationEquiv
        (ideleClassRepresentation ℚ) K L hLK hnormal
    let eK := rationalAbstractFixedFieldIdeleClassEquivFixed K
    let e :=
      rationalAbstractExtensionIdeleClassEquiv K L hLK hnormal
    eK.symm
        (relativeNorm (ideleClassRepresentation ℚ)
          K L hLK a) =
      Additive.ofMul
        (RelativeIdeleGroup.classNorm F E
          (Additive.toMul (e (eAmbient.symm a)))) := by
  intro F E hnormalInstance hFfinite hFEfinite htower hEfinite
    hFnumberField hEnumberField hGalois eAmbient eK e
  let : FiniteDimensional ℚ (abstractFixedField ℚ (SeparableClosure ℚ) L) :=
    inferInstanceAs (FiniteDimensional ℚ E)
  let eOrd := MulEquiv.toAdditive
    (_root_.relativeIdeleClassBaseChangeMulEquiv (K := F) (L := E))
  let eUpper := rationalAbstractRelativeFixedFieldIdeleClassEquivFixedOfFiniteDimensional K L hLK
  let b := e (eAmbient.symm a)
  let c : IdeleClassGroup E := (eOrd b).toMul
  have hb : eOrd b = eUpper.symm a := by
    change eOrd (eOrd.symm (eUpper.symm (eAmbient (eAmbient.symm a)))) = eUpper.symm a
    exact (eOrd.apply_symm_apply _).trans (congrArg eUpper.symm (eAmbient.apply_symm_apply a))
  have hUpper : abstractRelativeFixedFieldIdeleClassEquivFixed ℚ K L hLK
      (Additive.ofMul c) = a := by
    change eUpper (eOrd b) = a
    exact (congrArg eUpper hb).trans (eUpper.apply_symm_apply a)
  have h := abstractFixedFieldIdeleClassEquivFixed_norm ℚ K L hLK hnormal c
  have hNorm : NumberField.IdeleClassGroup.norm F E c =
      RelativeIdeleGroup.classNorm F E b.toMul :=
    ordinaryIdeleClassNorm_relativeIdeleClassBaseChange b.toMul
  let i := abstractFixedFieldIdeleClassEquivFixed ℚ K
  have hLeft := congrArg (relativeNorm (ideleClassRepresentation ℚ) K L hLK) hUpper.symm
  have hRight := congrArg (fun d => i (Additive.ofMul d)) hNorm
  apply eK.injective
  exact (eK.apply_symm_apply _).trans (hLeft.trans (h.trans hRight))

end Reciprocity
end GlobalClassFieldTheory
