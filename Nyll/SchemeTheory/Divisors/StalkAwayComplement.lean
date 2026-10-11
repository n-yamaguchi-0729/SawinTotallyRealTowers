/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Divisors.LocalComplement
import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# The principal complement of a stalk ideal

This is the one-localization counterpart of `LocalComplement`: the actual
spectrum of the stalk localized away from a generator maps to the global
support complement, and the canonical maps form a pullback square.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u

variable {X : Scheme.{u}}

/-- A principal stalk ideal cuts out the corresponding basic open. -/
theorem fromSpecStalk_preimage_supportComplement_eq_basicOpen
    (I : X.IdealSheafData) (x : X) (d : X.presheaf.stalk x)
    (hd : I.stalkIdeal x = Ideal.span {d}) :
    X.fromSpecStalk x ⁻¹ᵁ I.supportComplement = PrimeSpectrum.basicOpen d := by
  rw [fromSpecStalk_preimage_supportComplement, hd,
    PrimeSpectrum.idealComplement_span_singleton]

/-- The actual pullback complement is the spectrum of the principal localization. -/
def stalkSupportComplementIsoSpecAway
    (I : X.IdealSheafData) (x : X) (d : X.presheaf.stalk x)
    (hd : I.stalkIdeal x = Ideal.span {d}) :
    (X.fromSpecStalk x ⁻¹ᵁ I.supportComplement).toScheme ≅
      Spec (.of (Localization.Away d)) :=
  (Spec (X.presheaf.stalk x)).isoOfEq
    (fromSpecStalk_preimage_supportComplement_eq_basicOpen I x d hd) ≪≫
      basicOpenIsoSpecAway (R := X.presheaf.stalk x) d

/-- The canonical map from the principal stalk complement to the global complement. -/
def stalkAwayToSupportComplement
    (I : X.IdealSheafData) (x : X) (d : X.presheaf.stalk x)
    (hd : I.stalkIdeal x = Ideal.span {d}) :
    Spec (.of (Localization.Away d)) ⟶ I.supportComplement :=
  (stalkSupportComplementIsoSpecAway I x d hd).inv ≫
    (X.fromSpecStalk x ∣_ I.supportComplement)

/-- The map from the principal localization lies over the original stalk map. -/
@[reassoc]
theorem stalkAwayToSupportComplement_comp_ι
    (I : X.IdealSheafData) (x : X) (d : X.presheaf.stalk x)
    (hd : I.stalkIdeal x = Ideal.span {d}) :
    stalkAwayToSupportComplement I x d hd ≫ I.supportComplement.ι =
      Spec.map (CommRingCat.ofHom
        (algebraMap (X.presheaf.stalk x) (Localization.Away d))) ≫ X.fromSpecStalk x := by
  rw [stalkAwayToSupportComplement, Category.assoc, morphismRestrict_ι, ← Category.assoc]
  congr 1
  change ((basicOpenIsoSpecAway (R := X.presheaf.stalk x) d).inv ≫
      ((Spec (X.presheaf.stalk x)).isoOfEq
        (fromSpecStalk_preimage_supportComplement_eq_basicOpen I x d hd)).inv) ≫
      (X.fromSpecStalk x ⁻¹ᵁ I.supportComplement).ι = _
  have hIso : ((Spec (X.presheaf.stalk x)).isoOfEq
      (fromSpecStalk_preimage_supportComplement_eq_basicOpen I x d hd)).inv ≫
        (X.fromSpecStalk x ⁻¹ᵁ I.supportComplement).ι =
      (show (Spec (X.presheaf.stalk x)).Opens from PrimeSpectrum.basicOpen d).ι :=
    Scheme.isoOfEq_inv_ι (Spec (X.presheaf.stalk x))
      (fromSpecStalk_preimage_supportComplement_eq_basicOpen I x d hd)
  have hBasic : (basicOpenIsoSpecAway (R := X.presheaf.stalk x) d).inv ≫
      (show (Spec (X.presheaf.stalk x)).Opens from PrimeSpectrum.basicOpen d).ι =
      Spec.map (CommRingCat.ofHom
        (algebraMap (X.presheaf.stalk x) (Localization.Away d))) :=
    (Iso.inv_comp_eq (basicOpenIsoSpecAway (R := X.presheaf.stalk x) d)).mpr
      (basicOpenIsoSpecAway_hom_SpecMap (R := X.presheaf.stalk x) d).symm
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => (basicOpenIsoSpecAway (R := X.presheaf.stalk x) d).inv ≫ k)
      hIso).trans hBasic)

/-- The actual principal stalk complement is the pullback of the global complement. -/
theorem isPullback_stalkAwayToSupportComplement
    (I : X.IdealSheafData) (x : X) (d : X.presheaf.stalk x)
    (hd : I.stalkIdeal x = Ideal.span {d}) :
    IsPullback (stalkAwayToSupportComplement I x d hd)
      (Spec.map (CommRingCat.ofHom
        (algebraMap (X.presheaf.stalk x) (Localization.Away d))))
      I.supportComplement.ι (X.fromSpecStalk x) := by
  apply IsOpenImmersion.isPullback
  · exact (stalkAwayToSupportComplement_comp_ι I x d hd).symm
  · rw [Scheme.Opens.opensRange_ι,
      Scheme.Hom.opensRange_localizationAway (R := X.presheaf.stalk x) d]
    exact fromSpecStalk_preimage_supportComplement_eq_basicOpen I x d hd

end AlgebraicGeometry.Scheme.IdealSheafData
