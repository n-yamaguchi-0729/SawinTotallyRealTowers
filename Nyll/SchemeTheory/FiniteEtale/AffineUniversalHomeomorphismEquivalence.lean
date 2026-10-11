/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.FiniteEtale.Algebra.IntegralRadicialEssentialSurjectivity
public import Nyll.SchemeTheory.FiniteEtale.AffineEquivalence
public import Nyll.SchemeTheory.FiniteEtale.AffineThickening
public import Nyll.SchemeTheory.FiniteEtale.UniversalHomeomorphismFullyFaithful
public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.RingTheory.Etale.Finite

/-!
# Equivalence on finite étale covers of affine universal homeomorphisms

The constructed finite étale algebra model gives essential surjectivity of
the actual tensor-product functor. The affine comparison carries this result
to scheme pullback. Together with universal-homeomorphism full faithfulness,
this gives the finite étale equivalence for maps of spectra.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace CommAlgCat.FiniteEtale

/-- The actual models give essential surjectivity of tensor-product base change. -/
theorem baseChange_essSurj_of_universalHomeomorphism
    (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S]
    [UniversallyInjective (Spec.map (CommRingCat.ofHom (algebraMap R S)))]
    [Surjective (Spec.map (CommRingCat.ofHom (algebraMap R S)))] :
    (baseChange R S : CommAlgCat.FiniteEtale.{u} R ⥤
      CommAlgCat.FiniteEtale.{u} S).EssSurj := by
  constructor
  intro A
  obtain ⟨I, hI, hRI, hfiniteI, hEtaleI, ⟨e⟩⟩ :=
    Algebra.Etale.exists_finite_model_of_universalHomeomorphism R S A.obj
  exact ⟨CommAlgCat.FiniteEtale.of R I, ⟨CommAlgCat.FiniteEtale.isoMk e⟩⟩

end CommAlgCat.FiniteEtale

namespace AlgebraicGeometry.FiniteEtale

local instance finiteEtaleInfStableUnderBaseChangeAffineUniversalHomeomorphism :
    MorphismProperty.IsStableUnderBaseChange
      ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) :=
  MorphismProperty.IsStableUnderBaseChange.inf

/-- Finite étale scheme pullback on spectra is essentially surjective along
an integral, universally injective, surjective map. -/
theorem pullback_specMap_essSurj_of_universalHomeomorphism
    (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S]
    [UniversallyInjective (Spec.map (CommRingCat.ofHom (algebraMap R S)))]
    [Surjective (Spec.map (CommRingCat.ofHom (algebraMap R S)))] :
    (MorphismProperty.Over.pullback
      ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))).EssSurj := by
  let f : Spec (.of S) ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R S))
  let P : MorphismProperty Scheme.{u} := @IsFinite ⊓ @Etale
  have htransport (Q : MorphismProperty Scheme.{u}) [Q.IsStableUnderBaseChange]
      (hQ : Q = (@IsFiniteEtale : MorphismProperty Scheme.{u})) :
      (MorphismProperty.Over.pullback Q ⊤ f).EssSurj := by
    subst Q
    let F := FiniteEtale.pullback f
    let G := CommAlgCat.FiniteEtale.baseChange R S
    let ES := affineEquivalence (.of S)
    let : G.EssSurj := CommAlgCat.FiniteEtale.baseChange_essSurj_of_universalHomeomorphism R S
    let : (F.op ⋙ ES.functor).EssSurj :=
      Functor.essSurj_of_iso (affineEquivalenceCompBaseChangeIso R S)
    let : F.op.EssSurj := Functor.essSurj_of_comp_fully_faithful F.op ES.functor
    have hF : F.EssSurj := by
      constructor
      intro V
      obtain ⟨W, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage F.op (op V)
      exact ⟨W.unop, ⟨e.unop.symm⟩⟩
    exact hF
  exact htransport P IsFiniteEtale.eq_inf.symm

/-- Finite étale covers are invariant under affine universal homeomorphisms. -/
theorem pullback_specMap_isEquivalence_of_universalHomeomorphism
    (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S]
    [UniversallyInjective (Spec.map (CommRingCat.ofHom (algebraMap R S)))]
    [Surjective (Spec.map (CommRingCat.ofHom (algebraMap R S)))] :
    (MorphismProperty.Over.pullback
      ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))).IsEquivalence := by
  let f : Spec (.of S) ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R S))
  let : IsIntegralHom f := IsIntegralHom.SpecMap_iff.mpr
    (algebraMap_isIntegral_iff.mpr inferInstance)
  exact {
    faithful := pullback_faithful_of_integral_universallyInjective_surjective f
    full := pullback_full_of_integral_universallyInjective_surjective f
    essSurj := pullback_specMap_essSurj_of_universalHomeomorphism R S
  }

/-- The affine result is invariant under the canonical spectrum identifications;
only the target needs to be assumed affine, since the map is integral. -/
theorem pullback_isEquivalence_of_isAffine_of_universalHomeomorphism
    {X Y : Scheme.{u}} [IsAffine Y] (f : X ⟶ Y)
    [IsIntegralHom f] [UniversallyInjective f] [Surjective f] :
    (MorphismProperty.Over.pullback
      ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ f).IsEquivalence := by
  let : IsAffine X := isAffine_of_isAffineHom f
  let R := Γ(Y, ⊤)
  let S := Γ(X, ⊤)
  let : Algebra R S := f.appTop.hom.toAlgebra
  let q : Spec S ⟶ Spec R := Spec.map f.appTop
  let e : Arrow.mk f ≅ Arrow.mk q := arrowIsoSpecΓOfIsAffine f
  have hq : q = X.isoSpec.inv ≫ f ≫ Y.isoSpec.hom := by
    rw [← Scheme.isoSpec_hom_naturality f, Iso.inv_hom_id_assoc]
  let : IsIntegralHom q := by
    rw [hq]
    infer_instance
  let : MorphismProperty.RespectsIso
      (@UniversallyInjective : MorphismProperty Scheme.{u}) :=
    UniversallyInjective.respectsIso
  let : UniversallyInjective q :=
    (MorphismProperty.arrow_mk_iso_iff
      (@UniversallyInjective : MorphismProperty Scheme.{u}) e).mp inferInstance
  let : Surjective q :=
    (MorphismProperty.arrow_mk_iso_iff
      (@Surjective : MorphismProperty Scheme.{u}) e).mp inferInstance
  let : Algebra.IsIntegral R S :=
    algebraMap_isIntegral_iff.mp (IsIntegralHom.SpecMap_iff.mp
      (inferInstance : IsIntegralHom q))
  have hqSpec : Spec.map (CommRingCat.ofHom (algebraMap R S)) = q := by
    change Spec.map (CommRingCat.ofHom f.appTop.hom) = Spec.map f.appTop
    rw [CommRingCat.ofHom_hom]
  let : UniversallyInjective (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
    hqSpec.symm ▸ inferInstanceAs (UniversallyInjective q)
  let : Surjective (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
    hqSpec.symm ▸ inferInstanceAs (Surjective q)
  let P : MorphismProperty Scheme.{u} := @IsFinite ⊓ @Etale
  let : (MorphismProperty.Over.pullback P ⊤ q).IsEquivalence :=
    hqSpec ▸ pullback_specMap_isEquivalence_of_universalHomeomorphism R S
  let : (MorphismProperty.Over.pullback P ⊤ X.isoSpec.hom).IsEquivalence :=
    pullback_isEquivalence_of_isIso X.isoSpec.hom
  let : (MorphismProperty.Over.pullback P ⊤ Y.isoSpec.inv).IsEquivalence :=
    pullback_isEquivalence_of_isIso Y.isoSpec.inv
  let : (MorphismProperty.Over.pullback P ⊤ (q ≫ Y.isoSpec.inv)).IsEquivalence :=
    pullback_comp_isEquivalence q Y.isoSpec.inv
  have hfactor : f = X.isoSpec.hom ≫ q ≫ Y.isoSpec.inv := by
    change f = X.isoSpec.hom ≫ Spec.map f.appTop ≫ Y.isoSpec.inv
    rw [Scheme.isoSpec_hom_naturality_assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hfactor]
  exact pullback_comp_isEquivalence X.isoSpec.hom (q ≫ Y.isoSpec.inv)

end AlgebraicGeometry.FiniteEtale
