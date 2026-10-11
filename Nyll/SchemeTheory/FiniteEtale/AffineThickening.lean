/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.FiniteEtale.AffineEquivalence
public import Nyll.SchemeTheory.FiniteEtale.Algebra.HenselianBaseChange
public import Nyll.SchemeTheory.RingTheory.HenselianNilIdeal
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Finite étale covers of affine thickenings

A nil ideal defines a Henselian pair. Thus finite étale covers are unchanged
by its quotient. Factoring a surjective ring map through its kernel quotient,
and an affine closed immersion through a quotient spectrum, gives the same
result for every surjective closed immersion with affine target.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.FiniteEtale

local instance finiteEtaleInfStableUnderBaseChangeAffineThickening :
    MorphismProperty.IsStableUnderBaseChange
      ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) :=
  MorphismProperty.IsStableUnderBaseChange.inf

local instance finiteEtaleInfContainsIdentitiesAffineThickening :
    MorphismProperty.ContainsIdentities
      ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) where
  id_mem X := by
    have h : IsFiniteEtale (𝟙 X) :=
      (inferInstance : MorphismProperty.ContainsIdentities
        (@IsFiniteEtale : MorphismProperty Scheme.{u})).id_mem X
    exact ⟨h.toIsFinite, h.toEtale⟩

local instance finiteEtaleInfStableUnderCompositionAffineThickening :
    MorphismProperty.IsStableUnderComposition
      ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) where
  comp_mem f g hf hg := by
    have hf' : IsFiniteEtale f := @IsFiniteEtale.mk _ _ _ hf.1 hf.2
    have hg' : IsFiniteEtale g := @IsFiniteEtale.mk _ _ _ hg.1 hg.2
    have hfg : IsFiniteEtale (f ≫ g) :=
      (inferInstance : MorphismProperty.IsStableUnderComposition
        (@IsFiniteEtale : MorphismProperty Scheme.{u})).comp_mem f g hf' hg'
    exact ⟨hfg.toIsFinite, hfg.toEtale⟩

/-- Pullback by a scheme isomorphism is an equivalence on finite étale covers. -/
theorem pullback_isEquivalence_of_isIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    (MorphismProperty.Over.pullback
      ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ f).IsEquivalence := by
  let P : MorphismProperty Scheme.{u} := @IsFinite ⊓ @Etale
  let e : Functor.fromPUnit X ≅ Functor.fromPUnit Y :=
    Discrete.natIso fun _ ↦ asIso f
  let E : P.Over ⊤ X ≌ P.Over ⊤ Y :=
    MorphismProperty.Comma.mapRightIso (P := P) (Q := ⊤) (W := ⊤) (𝟭 Scheme) e
  have adj : E.functor ⊣ MorphismProperty.Over.pullback P ⊤ f :=
    MorphismProperty.Over.mapPullbackAdj P ⊤ f (P.of_isIso f) trivial
  exact Functor.isEquivalence_of_iso (E.toAdjunction.rightAdjointUniq adj)

/-- A composite preserves the finite étale category when each of its two maps does. -/
theorem pullback_comp_isEquivalence
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [(MorphismProperty.Over.pullback
      ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ f).IsEquivalence]
    [(MorphismProperty.Over.pullback
      ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ g).IsEquivalence] :
    (MorphismProperty.Over.pullback
      ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ (f ≫ g)).IsEquivalence :=
  Functor.isEquivalence_of_iso
    (MorphismProperty.Over.pullbackComp
      (P := (@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) (Q := ⊤) f g).symm

/-- Reduction by an arbitrary nil ideal leaves finite étale covers unchanged. -/
theorem pullback_quotient_isEquivalence_of_le_nilradical
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I ≤ nilradical R) :
    (MorphismProperty.Over.pullback
      ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).IsEquivalence := by
  let : HenselianRing R I := HenselianRing.of_le_nilradical I hI
  exact (pullback_specMap_isEquivalence_iff R (R ⧸ I)).mpr
    (CommAlgCat.FiniteEtale.baseChange_isEquivalence_of_henselian I)

/-- A surjective ring map with nil kernel induces an equivalence on finite
étale covers of spectra. -/
theorem pullback_specMap_isEquivalence_of_surjective_of_ker_le_nilradical
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) (hker : RingHom.ker f ≤ nilradical R) :
    (MorphismProperty.Over.pullback
      ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤
      (Spec.map (CommRingCat.ofHom f))).IsEquivalence := by
  let q : CommRingCat.of R ⟶ CommRingCat.of (R ⧸ RingHom.ker f) :=
    CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker f))
  let e : CommRingCat.of (R ⧸ RingHom.ker f) ≅ CommRingCat.of S :=
    (f.quotientKerEquivOfSurjective hf).toCommRingCatIso
  have hfactor : q ≫ e.hom = CommRingCat.ofHom f := by
    apply CommRingCat.hom_ext
    exact RingHom.ext fun _ ↦ rfl
  have hspec : Spec.map (CommRingCat.ofHom f) = Spec.map e.hom ≫ Spec.map q := by
    rw [← hfactor, Spec.map_comp]
  let : (MorphismProperty.Over.pullback
      ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ (Spec.map q)).IsEquivalence :=
    pullback_quotient_isEquivalence_of_le_nilradical (RingHom.ker f) hker
  let : (MorphismProperty.Over.pullback
      ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤
      (Spec.map e.hom)).IsEquivalence := pullback_isEquivalence_of_isIso _
  rw [hspec]
  exact pullback_comp_isEquivalence (Spec.map e.hom) (Spec.map q)

/-- Pullback along a surjective closed immersion with affine target is an
equivalence on the canonical category of finite étale covers. -/
theorem pullback_isEquivalence_of_isAffine_of_surjective_closedImmersion
    {X Y : Scheme.{u}} [IsAffine Y] (i : X ⟶ Y)
    [IsClosedImmersion i] [Surjective i] :
    (MorphismProperty.Over.pullback
      ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ i).IsEquivalence := by
  let P : MorphismProperty Scheme.{u} := @IsFinite ⊓ @Etale
  let j : X ⟶ Spec Γ(Y, ⊤) := i ≫ Y.isoSpec.hom
  obtain ⟨I, e, he⟩ := IsClosedImmersion.Spec_iff.mp
    (show IsClosedImmersion j from inferInstance)
  let q : Spec (CommRingCat.of (Γ(Y, ⊤) ⧸ I)) ⟶ Spec Γ(Y, ⊤) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let : Surjective (e.hom ≫ q) := by
    rw [← he]
    exact inferInstanceAs (Surjective j)
  let : Surjective q := Surjective.of_comp e.hom q
  have hsurj : Function.Surjective (PrimeSpectrum.comap (Ideal.Quotient.mk I)) :=
    q.surjective
  have hI : I ≤ nilradical Γ(Y, ⊤) := by
    have h := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical
      (Ideal.Quotient.mk I)).mp hsurj.denseRange
    simpa only [Ideal.mk_ker] using h
  let : (MorphismProperty.Over.pullback P ⊤ q).IsEquivalence :=
    pullback_quotient_isEquivalence_of_le_nilradical I hI
  let : (MorphismProperty.Over.pullback P ⊤ e.hom).IsEquivalence :=
    pullback_isEquivalence_of_isIso e.hom
  have hj : (MorphismProperty.Over.pullback P ⊤ j).IsEquivalence := by
    simpa only [he] using (pullback_comp_isEquivalence e.hom q)
  let : (MorphismProperty.Over.pullback P ⊤ Y.isoSpec.hom).IsEquivalence :=
    pullback_isEquivalence_of_isIso Y.isoSpec.hom
  let : (MorphismProperty.Over.pullback P ⊤ (i ≫ Y.isoSpec.hom)).IsEquivalence := hj
  let : (MorphismProperty.Over.pullback P ⊤ Y.isoSpec.hom ⋙
      MorphismProperty.Over.pullback P ⊤ i).IsEquivalence :=
    Functor.isEquivalence_of_iso
      (MorphismProperty.Over.pullbackComp (P := P) (Q := ⊤) i Y.isoSpec.hom)
  exact Functor.isEquivalence_of_comp_left
    (MorphismProperty.Over.pullback P ⊤ Y.isoSpec.hom)
    (MorphismProperty.Over.pullback P ⊤ i)

end AlgebraicGeometry.FiniteEtale
