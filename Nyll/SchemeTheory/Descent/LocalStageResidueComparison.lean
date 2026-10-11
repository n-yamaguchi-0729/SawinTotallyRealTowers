/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Mathlib.AlgebraicGeometry.Limits
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Localizing an actual stage at the contraction of a closed point

A ring map to a local ring factors through localization at the contracted
maximal ideal. The residue fiber of a scheme over the stage is unchanged by
this localization. These actual maps compare sections lifted at the local
stage with their pullbacks to the original closed fiber.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.LocalStageResidue

universe u

variable {B A : Type u} [CommRing B] [CommRing A] [IsLocalRing A]
variable (φ : B →+* A)

/-- The contraction of the original closed point to the stage. -/
abbrev prime : Ideal B := (IsLocalRing.maximalIdeal A).comap φ

/-- The actual factorization through localization at the contracted prime. -/
def localizationMap : Localization.AtPrime (prime φ) →+* A :=
  IsLocalization.lift (M := (prime φ).primeCompl) (g := φ) fun s => by
    classical
    apply Classical.not_not.mp
    exact s.property

lemma localizationMap_comp :
    (localizationMap φ).comp (algebraMap B (Localization.AtPrime (prime φ))) = φ :=
  IsLocalization.lift_comp _

/-- The spectrum map from the original local ring to the localized stage. -/
abbrev localSpecMap : Spec (CommRingCat.of A) ⟶
    Spec (CommRingCat.of (Localization.AtPrime (prime φ))) :=
  Spec.map (CommRingCat.ofHom (localizationMap φ))

/-- The localization morphism of the stage. -/
abbrev localizationSpec : Spec (CommRingCat.of (Localization.AtPrime (prime φ))) ⟶
    Spec (CommRingCat.of B) :=
  Spec.map (CommRingCat.ofHom (algebraMap B (Localization.AtPrime (prime φ))))

/-- The residue point of the localized stage uses its actual quotient map. -/
abbrev residueSpec : Spec (CommRingCat.of (prime φ).ResidueField) ⟶
    Spec (CommRingCat.of (Localization.AtPrime (prime φ))) :=
  Spec.map (CommRingCat.ofHom (IsLocalRing.residue (Localization.AtPrime (prime φ))))

/-- The original residue point of the stage. -/
abbrev stageResidueSpec : Spec (CommRingCat.of (prime φ).ResidueField) ⟶
    Spec (CommRingCat.of B) :=
  Spec.map (CommRingCat.ofHom (algebraMap B (prime φ).ResidueField))

/-- The closed residue point of the original local base. -/
abbrev topResidueSpec : Spec (CommRingCat.of (IsLocalRing.maximalIdeal A).ResidueField) ⟶
    Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A (IsLocalRing.maximalIdeal A).ResidueField))

/-- The actual residue-field extension from a stage to the original base. -/
abbrev residueMap : Spec (CommRingCat.of (IsLocalRing.maximalIdeal A).ResidueField) ⟶
    Spec (CommRingCat.of (prime φ).ResidueField) :=
  Spec.map (CommRingCat.ofHom
    (Ideal.ResidueField.map (prime φ) (IsLocalRing.maximalIdeal A) φ rfl))

@[reassoc]
lemma localSpecMap_localizationSpec :
    localSpecMap φ ≫ localizationSpec φ = Spec.map (CommRingCat.ofHom φ) := by
  rw [← Spec.map_comp]
  exact congrArg (fun h => Spec.map (CommRingCat.ofHom h)) (localizationMap_comp φ)

@[reassoc]
lemma residueSpec_localizationSpec :
    residueSpec φ ≫ localizationSpec φ = stageResidueSpec φ := by
  rw [← Spec.map_comp]
  congr 1

@[reassoc]
lemma residueMap_residueSpec :
    residueMap φ ≫ residueSpec φ = topResidueSpec (A := A) ≫ localSpecMap φ := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply IsLocalization.ringHom_ext (prime φ).primeCompl
  apply RingHom.ext
  intro b
  change Ideal.ResidueField.map (prime φ) (IsLocalRing.maximalIdeal A) φ rfl
      (algebraMap B (prime φ).ResidueField b) =
    algebraMap A (IsLocalRing.maximalIdeal A).ResidueField
      (localizationMap φ (algebraMap B (Localization.AtPrime (prime φ)) b))
  rw [Ideal.ResidueField.map_algebraMap]
  exact congrArg (algebraMap A (IsLocalRing.maximalIdeal A).ResidueField)
    (IsLocalization.lift_eq _ b).symm

@[reassoc]
lemma residueMap_stageResidueSpec :
    residueMap φ ≫ stageResidueSpec φ =
      topResidueSpec (A := A) ≫ Spec.map (CommRingCat.ofHom φ) := by
  rw [← residueSpec_localizationSpec, residueMap_residueSpec_assoc,
    localSpecMap_localizationSpec]

variable {P X : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of B))

/-- The actual stage after localization. -/
abbrev localizedScheme : Scheme.{u} := pullback q (localizationSpec φ)

/-- The actual proper structure map after localization. -/
abbrev localizedBaseMap : localizedScheme φ q ⟶
    Spec (CommRingCat.of (Localization.AtPrime (prime φ))) :=
  pullback.snd q (localizationSpec φ)

/-- The original stage fiber maps canonically to the localized stage. -/
def fiberToLocalized : pullback q (stageResidueSpec φ) ⟶ localizedScheme φ q :=
  pullback.lift (pullback.fst q (stageResidueSpec φ))
    (pullback.snd q (stageResidueSpec φ) ≫ residueSpec φ) (by
      rw [Category.assoc, residueSpec_localizationSpec, pullback.condition])

/-- Localization preserves the actual residue fiber. -/
lemma fiber_isPullback : IsPullback (fiberToLocalized φ q)
    (pullback.snd q (stageResidueSpec φ)) (localizedBaseMap φ q) (residueSpec φ) := by
  apply IsPullback.of_right (h₁₂ := pullback.fst q (localizationSpec φ))
    (h₂₂ := localizationSpec φ)
  · rw [fiberToLocalized, pullback.lift_fst, residueSpec_localizationSpec]
    exact IsPullback.of_hasPullback q (stageResidueSpec φ)
  · exact pullback.lift_snd _ _ _
  · exact IsPullback.of_hasPullback q (localizationSpec φ)

variable (f : X ⟶ Spec (CommRingCat.of A)) (t : X ⟶ P)
variable (w : t ≫ q = f ≫ Spec.map (CommRingCat.ofHom φ))

/-- The original scheme maps to the actual localized stage. -/
def lift : X ⟶ localizedScheme φ q :=
  pullback.lift t (f ≫ localSpecMap φ) (by
    rw [Category.assoc, localSpecMap_localizationSpec]
    exact w)

/-- The original closed fiber maps to the actual stage residue fiber. -/
def topFiberMap : pullback f (topResidueSpec (A := A)) ⟶
    pullback q (stageResidueSpec φ) :=
  pullback.map _ _ _ _ t (residueMap φ) (Spec.map (CommRingCat.ofHom φ))
    w.symm (residueMap_stageResidueSpec φ).symm

@[reassoc]
lemma topFiberMap_toLocalized :
    topFiberMap φ q f t w ≫ fiberToLocalized φ q =
      pullback.fst f (topResidueSpec (A := A)) ≫ lift φ q f t w := by
  apply pullback.hom_ext
  · simp only [Category.assoc, fiberToLocalized, pullback.lift_fst, topFiberMap,
      lift]
  · simp only [Category.assoc, fiberToLocalized, pullback.lift_snd, topFiberMap,
      pullback.lift_snd_assoc, lift]
    rw [residueMap_residueSpec, ← Category.assoc, ← pullback.condition, Category.assoc]

end AlgebraicGeometry.LocalStageResidue
