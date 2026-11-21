/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.NormalEmbeddingRange
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.CyclotomicUnramifiedGeometricRestriction
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FiniteIdeleClassSystem
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalNormResidueNaturality
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalCore
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.SinglePlace
public import Nyll.ClassFieldTheory.Algebra.FiniteAbstractFixedField

/-!
# Cyclotomic unramified local--global compatibility

For an unramified finite abelian subextension of an abstract rational
fixed field, the actual global norm-residue homomorphism agrees on every
finite one-place idele class with the chosen local Artin homomorphism.
-/



@[expose] public section

open scoped IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open KummerTheory

@[reducible]
private def composeMonoidHom
    {M N P : Type*} [MulOne M] [MulOne N] [MulOne P]
    (f : M →* N) (g : N →* P) : M →* P :=
  g.comp f

attribute [local instance]
  naturalityAbstractFixedFieldBaseQuotientFinite
  naturalityAbstractFixedFieldRelativeQuotientFinite
  naturalityAbstractFixedFieldFiniteDimensional
  naturalityAbstractRelativeFixedFieldFiniteDimensional
  naturalityAbstractFixedFieldRelativeScalarTower
  naturalityAbstractRelativeFixedFieldAbsoluteFiniteDimensional
  naturalityAbstractFixedFieldNumberField
  naturalityAbstractRelativeFixedFieldNumberField
  naturalityAbstractRelativeFixedFieldIsAbelianGalois

private theorem
    restrictNormalHom_comp_infiniteGlobalArtinMonoidHom_of_tower
    (K E Ω : Type) [Field K] [NumberField K]
    [Field E] [NumberField E] [Algebra K E]
    [IsAbelianGalois K E]
    [Field Ω] [Algebra K Ω] [Algebra E Ω]
    [IsScalarTower K E Ω] [IsAbelianGalois K Ω] :
    (AlgEquiv.restrictNormalHom E).comp
        (infiniteGlobalArtinMonoidHom K Ω).toMonoidHom =
      globalArtinMonoidHom (K := K) (L := E) := by
  apply MonoidHom.ext
  intro a
  let j : E →ₐ[K] Ω := IsScalarTower.toAlgHom K E Ω
  let G : FiniteGaloisIntermediateField K Ω :=
    j.finiteGaloisFieldRange
  let _ : FiniteDimensional K G := G.finiteDimensional
  let _ : NumberField G :=
    NumberField.of_module_finite K G
  let _ : IsAbelianGalois K G :=
    IsAbelianGalois.of_algHom G.toIntermediateField.val
  let _ : Algebra E G :=
    j.equivFieldRange.toRingHom.toAlgebra
  let _ : SMul E G := Algebra.toSMul
  let _ : IsScalarTower K E G :=
    IsScalarTower.of_algHom j.equivFieldRange.toAlgHom
  let _ : IsScalarTower K G Ω :=
    IntermediateField.isScalarTower_mid G.toIntermediateField
  let _ : IsScalarTower E G Ω :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hProjection :
      AlgEquiv.restrictNormalHom G
          (infiniteGlobalArtinMonoidHom K Ω a) =
        globalArtinMonoidHom (K := K) (L := G) a :=
    restrictNormalHom_infiniteGlobalArtinMonoidHom K Ω a G
  calc
    AlgEquiv.restrictNormalHom E
          (infiniteGlobalArtinMonoidHom K Ω a) =
        AlgEquiv.restrictNormalHom E
          (AlgEquiv.restrictNormalHom G
            (infiniteGlobalArtinMonoidHom K Ω a)) :=
      IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply E G
        (infiniteGlobalArtinMonoidHom K Ω a)
    _ = AlgEquiv.restrictNormalHom E
          (globalArtinMonoidHom (K := K) (L := G) a) :=
      congrArg (AlgEquiv.restrictNormalHom E) hProjection
    _ = globalArtinMonoidHom (K := K) (L := E) a :=
      DFunLike.congr_fun
        (globalArtinMonoidHom_restrict_tower
          (K := K) (L := G) (E := E)) a

private theorem
    abstractFixedFieldGlobalNormResidueMonoidHom_eq_cyclotomicRestrictionComp
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension H.field)
    (hUnramified :
      L.toFiniteGaloisExtension.IsUnramified
        rationalCyclotomicDegreeData) :
    let rhs :=
      composeMonoidHom
        (abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom H)
        (abstractFixedFieldCyclotomicFiniteRestrictionMonoidHom
          H L hUnramified)
    abstractFixedFieldGlobalNormResidueMonoidHom H L = rhs := by
  dsimp only
  apply MonoidHom.ext
  intro c
  exact
    abstractFixedFieldGlobalNormResidueMonoidHom_eq_cyclotomicFiniteRestriction
      H L hUnramified c

private theorem
    abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom_comp_finitePlaceIdeleClass
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (v : IsDedekindDomain.HeightOneSpectrum
      (𝓞 (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field))) :
    let F :=
      LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field
    let U :=
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (rationalCyclotomicFieldInertia_le H.field)
    letI _ : IsAbelianGalois F U :=
      abstractFixedFieldCyclotomic_isAbelianGalois H
    composeMonoidHom
        (IdeleGroup.finitePlaceIdeleClass v)
        (abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom H) =
      composeMonoidHom
        (IdeleGroup.finitePlaceIdele v)
        (infiniteGlobalArtinMonoidHom F U).toMonoidHom := by
  dsimp only
  apply MonoidHom.ext
  intro x
  exact
    abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom_mk
      H (IdeleGroup.finitePlaceIdele v x)

/-- The cyclotomic construction of fixed-field reciprocity satisfies
finite-place local--global compatibility on every finite unramified
abelian subextension. -/
theorem
    abstractFixedFieldGlobalNormResidueMonoidHom_comp_finitePlaceIdeleClass
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension H.field)
    (hUnramified :
      L.toFiniteGaloisExtension.IsUnramified
        rationalCyclotomicDegreeData)
    (v : IsDedekindDomain.HeightOneSpectrum
      (𝓞 (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field))) :
    let F :=
      LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field
    let E :=
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below
    let v₀ : IsDedekindDomain.HeightOneSpectrum (𝓞 F) := v
    (abstractFixedFieldGlobalNormResidueMonoidHom H L).comp
        (IdeleGroup.finitePlaceIdeleClass v₀) =
      chosenFinitePlaceArtinMonoidHom (K := F) (L := E) v₀ := by
  intro F E v₀
  apply MonoidHom.ext
  intro x
  let x₀ : (v₀.adicCompletion F)ˣ := x
  let a : IdeleGroup F := IdeleGroup.finitePlaceIdele v₀ x₀
  let c : IdeleClassGroup F := IdeleGroup.finitePlaceIdeleClass v₀ x₀
  let finiteArtin : IdeleGroup F →* Gal(E/F) := globalArtinMonoidHom (K := F) (L := E)
  have h₄ := globalArtinMonoidHom_finitePlaceIdele (K := F) (L := E) v₀ x₀
  let U := LocalClassFieldTheory.abstractRelativeFixedField ℚ (SeparableClosure ℚ)
    (rationalCyclotomicFieldInertia_le H.field)
  let : Algebra F U := U.algebra'
  let : IsAbelianGalois F U := cyclotomicUnramifiedGeometricMaximalIsAbelianGalois H
  let : Algebra E U := abstractFixedFieldCyclotomicFiniteUnramifiedInclusionAlgebra H L hUnramified
  let : @IsScalarTower F E U Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algHom (abstractFixedFieldCyclotomicFiniteUnramifiedInclusion H L hUnramified)
  let restriction := abstractFixedFieldCyclotomicFiniteRestrictionMonoidHom H L hUnramified
  let ideleClassArtin := abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom H
  let infiniteArtin := infiniteGlobalArtinMonoidHom F U
  have h₁ : abstractFixedFieldGlobalNormResidueMonoidHom H L c =
      restriction (ideleClassArtin c) := DFunLike.congr_fun
    (abstractFixedFieldGlobalNormResidueMonoidHom_eq_cyclotomicRestrictionComp H L hUnramified) c
  have h₂ : ideleClassArtin c = infiniteArtin a := DFunLike.congr_fun
    (abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom_comp_finitePlaceIdeleClass H v) x
  have h₃ : restriction (infiniteArtin a) = finiteArtin a := by
    have hRestriction := abstractFixedFieldCyclotomicFiniteRestrictionMonoidHom_eq_restrictNormalHom
      H L hUnramified
    have hTower := restrictNormalHom_comp_infiniteGlobalArtinMonoidHom_of_tower F E U
    have hr := congrArg (fun f : Gal(U/F) →* Gal(E/F) => f (infiniteArtin a)) hRestriction
    have ht := DFunLike.congr_fun hTower a
    exact hr.trans ht
  let value : Gal(E/F) := restriction (infiniteArtin a)
  have hMiddle : restriction (ideleClassArtin c) = value :=
    congrArg (fun z : Gal(U/F) => restriction z) h₂
  have hLeft : abstractFixedFieldGlobalNormResidueMonoidHom H L c = value :=
    h₁.trans hMiddle
  have hRight := h₃.trans h₄
  have h := hLeft.trans hRight
  dsimp only [c, x₀] at h
  refine (MonoidHom.comp_apply (abstractFixedFieldGlobalNormResidueMonoidHom H L)
    (IdeleGroup.finitePlaceIdeleClass v₀) x).trans ?_
  exact h

/-- The canonical inclusion realization of a finite unramified abstract
fixed-field extension satisfies finite-place local--global compatibility. -/
theorem
    globalNormResidueMonoidHomOfEmbedding_comp_finitePlaceIdeleClass_of_abstractFixedFieldUnramified
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension H.field)
    (hUnramified :
      L.toFiniteGaloisExtension.IsUnramified
        rationalCyclotomicDegreeData)
    (v : IsDedekindDomain.HeightOneSpectrum
      (𝓞 (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field))) :
    let F :=
      LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field
    let E :=
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below
    let j : E →ₐ[ℚ] SeparableClosure ℚ :=
      E.val.restrictScalars ℚ
    (globalNormResidueMonoidHomOfEmbedding F E j).comp
        (IdeleGroup.finitePlaceIdeleClass v) =
      chosenFinitePlaceArtinMonoidHom
        (K := F) (L := E) v := by
  dsimp only
  rw [
    globalNormResidueMonoidHomOfEmbedding_abstractFixedFieldInclusion
      H L]
  exact
    abstractFixedFieldGlobalNormResidueMonoidHom_comp_finitePlaceIdeleClass
      H L hUnramified v

end Reciprocity
end GlobalClassFieldTheory
