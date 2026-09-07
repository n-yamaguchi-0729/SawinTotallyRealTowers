import SawinTotallyRealTowers.MaximalRealProPOutside
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.GaloisClosure
import ProCGroups.Profinite.OpenSubgroups

set_option autoImplicit false

/-!
# Finite arithmetic stages of the real pro-p compositum

An open normal subgroup determines an actual finite Galois fixed field.
Lifting it to the chosen algebraic closure gives an admissible finite layer.
The quotient is identified with that layer's Galois group. No rank estimate,
finite presentation, or infiniteness hypothesis enters this construction.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

universe u v

namespace ClassFieldTower.Sawin

/-- The finite Galois fixed field supplied by an open normal subgroup. -/
def openNormalFiniteGaloisField
    (K : Type u) (M : Type v) [Field K] [Field M] [Algebra K M] [IsGalois K M]
    (U : OpenNormalSubgroup (M ≃ₐ[K] M)) : FiniteGaloisIntermediateField K M := by
  let Uc : ClosedSubgroup (M ≃ₐ[K] M) :=
    ⟨(U : Subgroup (M ≃ₐ[K] M)), ProCGroups.openNormalSubgroup_isClosed U⟩
  let L : IntermediateField K M := IntermediateField.fixedField Uc.toSubgroup
  have hFix : L.fixingSubgroup = Uc.toSubgroup :=
    InfiniteGalois.fixingSubgroup_fixedField Uc
  exact
    { toIntermediateField := L
      finiteDimensional := (InfiniteGalois.isOpen_iff_finite L).mp (by
        rw [hFix]
        exact U.toOpenSubgroup.isOpen)
      isGalois := (InfiniteGalois.normal_iff_isGalois L).mp (by
        rw [hFix]
        exact U.isNormal') }

/-- The constructed intermediate field is the fixed field of the subgroup. -/
theorem openNormalFiniteGaloisField_toIntermediateField
    (K : Type u) (M : Type v) [Field K] [Field M] [Algebra K M] [IsGalois K M]
    (U : OpenNormalSubgroup (M ≃ₐ[K] M)) :
    (openNormalFiniteGaloisField K M U).toIntermediateField =
      IntermediateField.fixedField (U : Subgroup (M ≃ₐ[K] M)) := rfl

/-- The open normal quotient acts faithfully and fully on its finite fixed field. -/
def openNormalQuotientEquivFiniteGaloisField
    (K : Type u) (M : Type v) [Field K] [Field M] [Algebra K M] [IsGalois K M]
    (U : OpenNormalSubgroup (M ≃ₐ[K] M)) :
    ((M ≃ₐ[K] M) ⧸ (U : Subgroup (M ≃ₐ[K] M))) ≃*
      (openNormalFiniteGaloisField K M U ≃ₐ[K] openNormalFiniteGaloisField K M U) := by
  let Uc : ClosedSubgroup (M ≃ₐ[K] M) :=
    ⟨(U : Subgroup (M ≃ₐ[K] M)), ProCGroups.openNormalSubgroup_isClosed U⟩
  let : Uc.toSubgroup.Normal := U.isNormal'
  exact InfiniteGalois.normalAutEquivQuotient (k := K) (K := M) Uc

/-- The quotient action agrees with the original automorphism on the fixed field. -/
theorem openNormalQuotientEquivFiniteGaloisField_apply
    (K : Type u) (M : Type v) [Field K] [Field M] [Algebra K M] [IsGalois K M]
    (U : OpenNormalSubgroup (M ≃ₐ[K] M)) (σ : M ≃ₐ[K] M)
    (x : openNormalFiniteGaloisField K M U) :
    ((openNormalQuotientEquivFiniteGaloisField K M U
      (QuotientGroup.mk' (U : Subgroup (M ≃ₐ[K] M)) σ) x :
        openNormalFiniteGaloisField K M U) : M) = σ (x : M) := by
  let Uc : ClosedSubgroup (M ≃ₐ[K] M) :=
    ⟨(U : Subgroup (M ≃ₐ[K] M)), ProCGroups.openNormalSubgroup_isClosed U⟩
  let : Uc.toSubgroup.Normal := U.isNormal'
  change ((InfiniteGalois.normalAutEquivQuotient Uc σ) x : M) = σ (x : M)
  rw [InfiniteGalois.normalAutEquivQuotient_apply]
  exact AlgEquiv.restrictNormalHom_apply (IntermediateField.fixedField Uc.toSubgroup) σ x

private local instance realCompositumGalois
    (p : ℕ) (T : Set (HeightOneSpectrum (𝓞 ℚ))) :
    IsGalois ℚ (maximalRealProPOutside p T) := maximalRealProPOutside_isGalois p T

/-- The concrete arithmetic layer attached to an open normal subgroup of the
maximal real compositum. Its local conditions follow from containment. -/
def realProPOpenNormalStage
    (p : ℕ) (T : Set (HeightOneSpectrum (𝓞 ℚ)))
    (U : OpenNormalSubgroup
      (maximalRealProPOutside p T ≃ₐ[ℚ] maximalRealProPOutside p T)) :
    FiniteRealPExtension p T := by
  let L : FiniteGaloisIntermediateField ℚ (maximalRealProPOutside p T) :=
    openNormalFiniteGaloisField ℚ (maximalRealProPOutside p T) U
  let e : L.toIntermediateField ≃ₐ[ℚ] IntermediateField.lift L.toIntermediateField :=
    IntermediateField.liftAlgEquiv L.toIntermediateField
  letI : IsGalois ℚ L.toIntermediateField := L.isGalois
  let D : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ) :=
    { toIntermediateField := IntermediateField.lift L.toIntermediateField
      finiteDimensional := e.toLinearEquiv.finiteDimensional
      isGalois := IsGalois.of_algEquiv e }
  exact ⟨D, (isAdmissibleFiniteLayer_iff_le_maximalRealProPOutside p T D).mpr
    (IntermediateField.lift_le L.toIntermediateField)⟩

/-- The stage is the lift of the finite fixed field, with no auxiliary choice. -/
theorem realProPOpenNormalStage_field
    (p : ℕ) (T : Set (HeightOneSpectrum (𝓞 ℚ)))
    (U : OpenNormalSubgroup
      (maximalRealProPOutside p T ≃ₐ[ℚ] maximalRealProPOutside p T)) :
    (realProPOpenNormalStage p T U).val.toIntermediateField =
      IntermediateField.lift
        (IntermediateField.fixedField
          (U : Subgroup
            (maximalRealProPOutside p T ≃ₐ[ℚ] maximalRealProPOutside p T))) := rfl

/-- The quotient group is the Galois group of the constructed admissible layer. -/
def realProPOpenNormalQuotientEquivStage
    (p : ℕ) (T : Set (HeightOneSpectrum (𝓞 ℚ)))
    (U : OpenNormalSubgroup
      (maximalRealProPOutside p T ≃ₐ[ℚ] maximalRealProPOutside p T)) :
    ((maximalRealProPOutside p T ≃ₐ[ℚ] maximalRealProPOutside p T) ⧸
      (U : Subgroup
        (maximalRealProPOutside p T ≃ₐ[ℚ] maximalRealProPOutside p T))) ≃*
      ((realProPOpenNormalStage p T U).val ≃ₐ[ℚ] (realProPOpenNormalStage p T U).val) := by
  let L : FiniteGaloisIntermediateField ℚ (maximalRealProPOutside p T) :=
    openNormalFiniteGaloisField ℚ (maximalRealProPOutside p T) U
  exact (openNormalQuotientEquivFiniteGaloisField ℚ (maximalRealProPOutside p T) U).trans
    (AlgEquiv.autCongr (IntermediateField.liftAlgEquiv L.toIntermediateField))

/-- The quotient action on the arithmetic stage is the restriction of the
original automorphism, transported through the canonical lift. -/
theorem realProPOpenNormalQuotientEquivStage_apply
    (p : ℕ) (T : Set (HeightOneSpectrum (𝓞 ℚ)))
    (U : OpenNormalSubgroup
      (maximalRealProPOutside p T ≃ₐ[ℚ] maximalRealProPOutside p T))
    (σ : maximalRealProPOutside p T ≃ₐ[ℚ] maximalRealProPOutside p T)
    (x : (realProPOpenNormalStage p T U).val) :
    ((realProPOpenNormalQuotientEquivStage p T U
      (QuotientGroup.mk' (U : Subgroup
        (maximalRealProPOutside p T ≃ₐ[ℚ] maximalRealProPOutside p T)) σ) x :
          (realProPOpenNormalStage p T U).val) : AlgebraicClosure ℚ) =
      (σ ⟨(x : AlgebraicClosure ℚ),
        le_maximalRealProPOutside (realProPOpenNormalStage p T U) x.property⟩ :
          AlgebraicClosure ℚ) := by
  let L : FiniteGaloisIntermediateField ℚ (maximalRealProPOutside p T) :=
    openNormalFiniteGaloisField ℚ (maximalRealProPOutside p T) U
  let e : L.toIntermediateField ≃ₐ[ℚ] IntermediateField.lift L.toIntermediateField :=
    IntermediateField.liftAlgEquiv L.toIntermediateField
  change (e ((openNormalQuotientEquivFiniteGaloisField ℚ
    (maximalRealProPOutside p T) U σ) (e.symm x)) : AlgebraicClosure ℚ) = _
  have hAction := openNormalQuotientEquivFiniteGaloisField_apply ℚ
    (maximalRealProPOutside p T) U σ (e.symm x)
  exact congrArg (fun y : maximalRealProPOutside p T ↦ (y : AlgebraicClosure ℚ)) hAction

end ClassFieldTower.Sawin
