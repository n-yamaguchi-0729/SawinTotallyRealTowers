/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Pi1.FiniteEtale.Geometry

/-!
# Étale schemes over a field

This file proves the geometric decomposition used in the first half of
Stacks Project, Tag `02GL`: a scheme étale over a field is a coproduct of
spectra of finite separable field extensions.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory MorphismProperty Limits

namespace AlgebraicGeometry.Scheme.Etale

/-- A scheme étale over a field is a coproduct of spectra of finite separable
field extensions, indexed canonically by its points. -/
@[stacks 02GL "An étale scheme over a field is a disjoint union of spectra of finite separable \
field extensions."]
theorem exists_iso_sigmaSpec (K : Type u) [Field K]
    (X : (Spec (.of K)).Etale) :
    ∃ (L : X.left → CommRingCat.{u})
      (a : ∀ x, CommRingCat.of K ⟶ L x)
      (e : (∐ fun x ↦ Spec (L x)) ≅ X.left),
      (∀ x, IsField (L x)) ∧
        (∀ x, letI := (a x).hom.toAlgebra
          Module.Finite K (L x) ∧ Algebra.IsSeparable K (L x)) ∧
        e.hom ≫ X.hom = Sigma.desc (fun x ↦ Spec.map (a x)) := by
  let structureMap : X.left ⟶ Spec (.of K) := X.hom
  let : IsLocallyArtinian X.left := by
    rw [isLocallyArtinian_iff_openCover X.left.affineCover]
    intro i
    let Z := X.left.affineCover.X i
    let f : Z ⟶ Spec (.of K) := X.left.affineCover.f i ≫ structureMap
    have hf : AlgebraicGeometry.Etale f := inferInstance
    rw [HasRingHomProperty.iff_of_isAffine (P := @AlgebraicGeometry.Etale)] at hf
    let eK : Γ(Spec (CommRingCat.of K), ⊤) ≃+* K :=
      (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv
    algebraize [(f.appTop.hom.comp eK.symm.toRingHom)]
    have : Algebra.Etale K Γ(Z, ⊤) := by
      change (f.appTop.hom.comp eK.symm.toRingHom).Etale
      apply RingHom.Etale.respectsIso.2
      exact hf
    let : Module.Free K Γ(Z, ⊤) := Module.Free.of_divisionRing K Γ(Z, ⊤)
    have : Module.Finite K Γ(Z, ⊤) :=
      Algebra.FormallyUnramified.finite_of_free (R := K) (S := Γ(Z, ⊤))
    have : IsArtinianRing Γ(Z, ⊤) := isArtinian_of_tower K inferInstance
    have : IsLocallyArtinian (Spec Γ(Z, ⊤)) :=
      Scheme.isLocallyArtinianScheme_Spec.mpr inferInstance
    exact IsLocallyArtinian.of_isImmersion Z.isoSpec.hom
  let : DiscreteTopology X.left := inferInstance
  let U (x : X.left) : X.left.Opens := ⟨{x}, isOpen_discrete _⟩
  have hU (x : X.left) : IsAffineOpen (U x) :=
    IsAffineOpen.of_subsingleton Set.subsingleton_singleton
  let Y (x : X.left) : Scheme.{u} := (U x).toScheme
  let (x : X.left) : IsAffine (Y x) := hU x
  let g (x : X.left) : Y x ⟶ Spec (.of K) := (U x).ι ≫ structureMap
  let L (x : X.left) : CommRingCat.{u} := Γ(Y x, ⊤)
  let a (x : X.left) : CommRingCat.of K ⟶ L x :=
    (Scheme.ΓSpecIso (.of K)).inv ≫ (g x).appTop
  have hRingEtale (x : X.left) : (a x).hom.Etale := by
    have hf : AlgebraicGeometry.Etale (g x) := inferInstance
    rw [HasRingHomProperty.iff_of_isAffine (P := @AlgebraicGeometry.Etale)] at hf
    change ((g x).appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).Etale
    exact RingHom.Etale.respectsIso.right (g x).appTop.hom
      (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.symm hf
  have hField (x : X.left) : IsField (L x) := by
    let : Algebra K (L x) := (a x).hom.toAlgebra
    let : Algebra.Etale K (L x) := (hRingEtale x).toAlgebra
    let : _root_.IsReduced (L x) :=
      Algebra.FormallyUnramified.isReduced_of_field K (L x)
    let : Subsingleton (Y x) := by
      change Subsingleton (U x)
      exact ⟨fun p q ↦ Subtype.ext (Set.subsingleton_singleton p.property q.property)⟩
    let y : Y x := ⟨x, by simp [U]⟩
    let : Nontrivial (L x) :=
      PrimeSpectrum.nontrivial ((Y x).isoSpec.hom y)
    rw [← PrimeSpectrum.subsingleton_iff_isField_of_isReduced]
    constructor
    intro p q
    apply (Y x).isoSpec.hom.homeomorph.symm.injective
    exact Subsingleton.elim _ _
  have hFiniteSep (x : X.left) :
      letI := (a x).hom.toAlgebra
      Module.Finite K (L x) ∧ Algebra.IsSeparable K (L x) := by
    let : Algebra K (L x) := (a x).hom.toAlgebra
    let : Algebra.Etale K (L x) := (hRingEtale x).toAlgebra
    let : Field (L x) := (hField x).toField
    let : Module.Free K (L x) := Module.Free.of_divisionRing K (L x)
    exact ⟨Algebra.FormallyUnramified.finite_of_free (R := K) (S := L x),
      Algebra.FormallyUnramified.isSeparable K (L x)⟩
  let d : (∐ fun x ↦ Y x) ⟶ X.left := Sigma.desc fun x ↦ (U x).ι
  let : IsOpenImmersion d := by
    dsimp [d]
    apply isOpenImmersion_sigmaDesc
    intro x y hxy
    refine Set.disjoint_iff_forall_ne.mpr ?_
    rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩ hpq
    apply hxy
    have hp : (U x).ι p = x := by
      change p.1 = x
      have hp_mem : p.1 ∈ ({x} : Set X.left) := by
        change p.1 ∈ (U x : Set X.left)
        exact p.property
      simpa only [Set.mem_singleton_iff] using hp_mem
    have hq : (U y).ι q = y := by
      change q.1 = y
      have hq_mem : q.1 ∈ ({y} : Set X.left) := by
        change q.1 ∈ (U y : Set X.left)
        exact q.property
      simpa only [Set.mem_singleton_iff] using hq_mem
    exact hp.symm.trans (hpq.trans hq)
  have hd_surj : Function.Surjective d := by
    intro z
    let p : Y z := ⟨z, by simp [U]⟩
    refine ⟨Sigma.ι (fun x ↦ Y x) z p, ?_⟩
    rw [← Scheme.Hom.comp_apply, Sigma.ι_comp_desc]
    rfl
  have hd : d.opensRange = ⊤ := by
    apply TopologicalSpace.Opens.ext
    simpa only [Scheme.Hom.coe_opensRange, TopologicalSpace.Opens.coe_top] using
      Set.range_eq_univ.mpr hd_surj
  let : IsIso d :=
    isIso_of_isOpenImmersion_of_opensRange_eq_top d hd
  let e : (∐ fun x ↦ Spec (L x)) ≅ X.left :=
    (Sigma.mapIso (fun x ↦ (Y x).isoSpec)).symm ≪≫ asIso d
  have he : e.hom ≫ X.hom = Sigma.desc (fun x ↦ Spec.map (a x)) := by
    change e.hom ≫ structureMap = Sigma.desc (fun x ↦ Spec.map (a x))
    apply Sigma.hom_ext
    intro x
    calc
      (Sigma.ι (fun x ↦ Spec (L x)) x ≫ e.hom) ≫ structureMap =
          (Y x).isoSpec.inv ≫ (U x).ι ≫ structureMap := by
        simp only [e, Iso.trans_hom, Iso.symm_hom, Category.assoc,
          Sigma.ι_mapIso_inv_assoc, asIso_hom, d, Sigma.ι_comp_desc_assoc]
      _ = Spec.map (a x) := by
        simpa only [g, a, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] using
          (Scheme.isoSpec_inv_naturality (g x)).symm
      _ = Sigma.ι (fun x ↦ Spec (L x)) x ≫
          Sigma.desc (fun x ↦ Spec.map (a x)) :=
        (Sigma.ι_comp_desc (fun x ↦ Spec.map (a x)) x).symm
  exact ⟨L, a, e, hField, hFiniteSep, he⟩

end AlgebraicGeometry.Scheme.Etale
