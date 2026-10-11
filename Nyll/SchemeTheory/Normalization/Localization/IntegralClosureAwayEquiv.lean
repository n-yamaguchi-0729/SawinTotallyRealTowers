/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Localization.Integral

/-!
# Localizing a normalization away from one element

The normalization of an away localization is the localization of the
original normalization.  This file records the comparison as an algebra
equivalence over the localized base and transports étaleness back to the
literal away map used by the global exponent obstruction.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe uA uK uL

variable {A : Type uA} {K : Type uK} {L : Type uL}
variable [CommRing A] [IsDomain A]
variable [Field K] [Field L]
variable [Algebra A K] [IsFractionRing A K]
variable [Algebra K L] [Algebra A L] [IsScalarTower A K L]

/-- The canonical map from `A[1/f]` to a field extension of the fraction
field of `A`. -/
@[reducible]
noncomputable def localizationAwayToExtensionAlgebra
    (f : A) (hf : f ≠ 0) : Algebra (Localization.Away f) L := by
  let mapAK : A →+* L := algebraMap A L
  have hfUnit : IsUnit (mapAK f) := by
    rw [isUnit_iff_ne_zero]
    intro hzero
    apply hf
    apply IsFractionRing.injective A K
    apply (algebraMap K L).injective
    calc
      algebraMap K L (algebraMap A K f) = algebraMap A L f :=
        (IsScalarTower.algebraMap_apply A K L f).symm
      _ = 0 := hzero
      _ = algebraMap K L (algebraMap A K 0) := by simp
  exact (IsLocalization.Away.lift f hfUnit).toAlgebra

omit [IsDomain A] in
/-- The canonical away-localization map to the extension field extends the
original map from `A`. -/
theorem localizationAwayToExtension_isScalarTower
    (f : A) (hf : f ≠ 0) :
    letI : Algebra (Localization.Away f) L :=
      localizationAwayToExtensionAlgebra (K := K) f hf
    IsScalarTower A (Localization.Away f) L := by
  let : Algebra (Localization.Away f) L :=
    localizationAwayToExtensionAlgebra (K := K) f hf
  exact IsScalarTower.of_algebraMap_eq'
    (IsLocalization.Away.lift_comp f _).symm

/-- The literal localization of the normalization away from `f` is
canonically equivalent, over `A[1/f]`, to the normalization of `A[1/f]` in
the same field. -/
noncomputable def localizationIntegralClosureAwayAlgEquiv
    (f : A) (hf : f ≠ 0) :
    let S := Localization.Away f
    let C := integralClosure A L
    let T := Localization.Away (algebraMap A C f)
    letI : Algebra S L :=
      localizationAwayToExtensionAlgebra (K := K) f hf
    letI : Algebra S T :=
      (Localization.awayMap (algebraMap A C) f).toAlgebra
    T ≃ₐ[S] integralClosure S L := by
  dsimp only
  let S := Localization.Away f
  let C := integralClosure A L
  let T := Localization.Away (algebraMap A C f)
  letI : Algebra S L :=
    localizationAwayToExtensionAlgebra (K := K) f hf
  letI : IsScalarTower A S L :=
    localizationAwayToExtension_isScalarTower (K := K) f hf
  let mapST : S →+* T := Localization.awayMap (algebraMap A C) f
  letI : Algebra S T := mapST.toAlgebra
  let E := integralClosure S L
  let liftCE : C →ₐ[A] E :=
    { toFun := fun x ↦ ⟨x.1, x.2.tower_top⟩
      map_one' := by rfl
      map_mul' := fun _ _ ↦ by rfl
      map_zero' := by rfl
      map_add' := fun _ _ ↦ by rfl
      commutes' := fun x ↦ by
        apply Subtype.ext
        simp only [Subalgebra.coe_algebraMap] }
  letI : Algebra C E := liftCE.toRingHom.toAlgebra
  letI : IsScalarTower A C E :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (liftCE.commutes x).symm
  letI : IsScalarTower C E L :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hfL : algebraMap A L f ≠ 0 := by
    intro hzero
    apply hf
    apply IsFractionRing.injective A K
    apply (algebraMap K L).injective
    calc
      algebraMap K L (algebraMap A K f) = algebraMap A L f :=
        (IsScalarTower.algebraMap_apply A K L f).symm
      _ = 0 := hzero
      _ = algebraMap K L (algebraMap A K 0) := by simp
  letI : IsLocalization.Away (algebraMap A L f) L :=
    IsLocalization.away_of_isUnit_of_bijective L
      (isUnit_iff_ne_zero.mpr hfL) Function.bijective_id
  have hACE : IsScalarTower A C E := inferInstance
  letI : IsLocalization.Away (algebraMap A C f) E :=
    @IsLocalization.Away.integralClosure
      A (inferInstance : CommRing A)
      L (inferInstance : CommRing L) (inferInstance : Algebra A L)
      S L (inferInstance : CommRing S) (inferInstance : CommRing L)
      (inferInstance : Algebra A S) (inferInstance : Algebra L L)
      (inferInstance : Algebra S L) (inferInstance : Algebra A L)
      (inferInstance : IsScalarTower A L L)
      (inferInstance : IsScalarTower A S L) f
      (inferInstance : IsLocalization.Away f S)
      (inferInstance : IsLocalization.Away (algebraMap A L f) L)
      liftCE.toRingHom.toAlgebra (inferInstance : IsScalarTower C E L) hACE
  let eC : T ≃ₐ[C] E :=
    IsLocalization.algEquiv (Submonoid.powers (algebraMap A C f)) T E
  refine
    { toRingEquiv := eC.toRingEquiv
      commutes' := fun z ↦ ?_ }
  apply DFunLike.congr_fun (f :=
      eC.toRingHom.comp (algebraMap S T))
    (g := algebraMap S E) ?_ z
  apply IsLocalization.ringHom_ext (Submonoid.powers f)
  apply DFunLike.ext _ _
  intro x
  simp only [RingHom.comp_apply]
  change eC (mapST (algebraMap A S x)) = algebraMap S E (algebraMap A S x)
  rw [show mapST (algebraMap A S x) =
      algebraMap C T (algebraMap A C x) by
    exact IsLocalization.map_eq _ x]
  rw [eC.commutes]
  rw [← IsScalarTower.algebraMap_apply A C E x,
    ← IsScalarTower.algebraMap_apply A S E x]

omit [IsDomain A] in
/-- Étaleness of the normalization after inverting `f` transports to the
literal away localization of the original normalization. -/
theorem localization_integralClosure_away_etale_of_local_integralClosure_etale
    (f : A) (hf : f ≠ 0) :
    let S := Localization.Away f
    let C := integralClosure A L
    let T := Localization.Away (algebraMap A C f)
    letI : Algebra S L :=
      localizationAwayToExtensionAlgebra (K := K) f hf
    letI : Algebra S T :=
      (Localization.awayMap (algebraMap A C) f).toAlgebra
    Algebra.Etale S (integralClosure S L) →
      Algebra.Etale S T := by
  dsimp only
  let S := Localization.Away f
  let C := integralClosure A L
  let T := Localization.Away (algebraMap A C f)
  let : Algebra S L :=
    localizationAwayToExtensionAlgebra (K := K) f hf
  let : Algebra S T :=
    (Localization.awayMap (algebraMap A C) f).toAlgebra
  intro h
  let : Algebra.Etale S (integralClosure S L) := h
  exact Algebra.Etale.of_equiv
    (localizationIntegralClosureAwayAlgEquiv
      (K := K) (L := L) f hf).symm

end EtaleFundamentalGroups

end
