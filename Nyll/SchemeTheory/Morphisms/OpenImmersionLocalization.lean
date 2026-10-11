/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# Localizing inside the image of an open immersion

An open immersion restricts to an isomorphism over any open contained in its
image. For spectra, the canonical comparison with principal localization
then proves bijectivity of the actual localized ring map. This applies to
the principal neighborhood extracted from a normalization.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- An open immersion is an isomorphism over every open contained in its image. -/
theorem Scheme.Hom.isIso_morphismRestrict_of_le_opensRange
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (U : Y.Opens) (hU : U ≤ f.opensRange) : IsIso (f ∣_ U) := by
  have hopen : IsOpenImmersion (f ∣_ U) := by
    unfold morphismRestrict
    infer_instance
  have hsurj : Surjective (f ∣_ U) := ⟨by
    intro y
    obtain ⟨x, hx⟩ := hU y.property
    have hxU : f x ∈ U := hx.symm ▸ y.property
    refine ⟨⟨x, hxU⟩, ?_⟩
    apply Subtype.ext
    exact (morphismRestrict_base_coe f U ⟨x, hxU⟩).trans hx⟩
  exact (isIso_iff_isOpenImmersion_and_surjective (f ∣_ U)).mpr ⟨hopen, hsurj⟩

/-- If `D(r)` lies in the image of an open immersion of spectra, localization
at `r` makes the original ring map bijective. -/
theorem bijective_awayMap_of_basicOpen_le_opensRange
    {R S : CommRingCat.{u}} (f : R ⟶ S) [IsOpenImmersion (Spec.map f)]
    (r : R) (hr : PrimeSpectrum.basicOpen r ≤ (Spec.map f).opensRange) :
    Function.Bijective (Localization.awayMap f.hom r) := by
  have hrestr : IsIso (Spec.map f ∣_ PrimeSpectrum.basicOpen r) :=
    (Spec.map f).isIso_morphismRestrict_of_le_opensRange _ hr
  have : IsIso (Spec.map (CommRingCat.ofHom (Localization.awayMap f.hom r))) :=
    (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms Scheme)
      (SpecMapRestrictBasicOpenIso f r)).mp hrestr
  exact (isIso_SpecMap_iff
    (f := CommRingCat.ofHom (Localization.awayMap f.hom r))).mp inferInstance

end AlgebraicGeometry
