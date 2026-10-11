/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Divisors.LocalScheme

/-!
# Local descriptions of support complements

This file identifies the complement of the support of an ideal sheaf near a
scheme point.  If the stalk ideal becomes principal after localizing at a
prime, the resulting open subscheme is canonically the spectrum of the
localization away from that principal generator.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace PrimeSpectrum

universe u

/-- The open complement of the closed set cut out by an ideal. -/
def idealComplement {R : Type u} [CommRing R] (J : Ideal R) :
    Opens (PrimeSpectrum R) :=
  ⟨(zeroLocus (J : Set R))ᶜ,
    (isClosed_zeroLocus (J : Set R)).isOpen_compl⟩

@[simp]
theorem mem_idealComplement {R : Type u} [CommRing R] (J : Ideal R)
    (p : PrimeSpectrum R) :
    p ∈ idealComplement J ↔ ¬ J ≤ p.asIdeal := by
  simp [idealComplement, mem_zeroLocus, SetLike.coe_subset_coe]

/-- Pulling an ideal complement back along a spectrum map extends the
defining ideal. -/
theorem preimage_idealComplement {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (J : Ideal A) :
    Spec.map (CommRingCat.ofHom f) ⁻¹ᵁ idealComplement J =
      idealComplement (J.map f) := by
  apply Opens.ext
  ext p
  change (¬ J ≤ Ideal.comap f p.asIdeal) ↔
    (¬ J.map f ≤ p.asIdeal)
  exact not_congr Ideal.map_le_iff_le_comap.symm

/-- The complement of the vanishing set of a principal ideal is the
corresponding basic open. -/
theorem idealComplement_span_singleton {R : Type u} [CommRing R]
    (f : R) :
    idealComplement (Ideal.span {f}) = basicOpen f := by
  apply Opens.ext
  ext p
  change (¬ Ideal.span {f} ≤ p.asIdeal) ↔ f ∉ p.asIdeal
  simp only [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]

end PrimeSpectrum

namespace AlgebraicGeometry.Scheme

universe u

variable (X : Scheme.{u}) (x : X)

/-- The canonical map from the spectrum of a prime localization of the stalk
at `x` back to `X`. -/
def localizationAtPrimeTo
    (P : Ideal (X.presheaf.stalk x)) [P.IsPrime] :
    Spec (.of (Localization.AtPrime P)) ⟶ X :=
  Spec.map (CommRingCat.ofHom
      (algebraMap (X.presheaf.stalk x) (Localization.AtPrime P))) ≫
    X.fromSpecStalk x

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u

variable {X Y : Scheme.{u}}

/-- The canonical open complement of the support of an ideal sheaf. -/
def supportComplement (I : X.IdealSheafData) : X.Opens := I.support.compl

@[simp]
theorem mem_supportComplement (I : X.IdealSheafData) (y : X) :
    y ∈ I.supportComplement ↔ y ∉ I.support := by
  rfl

/-- Formation of the support complement commutes with pullback of an ideal
sheaf. -/
@[simp]
theorem supportComplement_comap
    (I : Y.IdealSheafData) (f : X ⟶ Y) :
    (I.comap f).supportComplement = f ⁻¹ᵁ I.supportComplement := by
  apply Opens.ext
  ext x
  change (x ∉ (I.comap f).support) ↔ f x ∉ I.support
  rw [support_comap]
  rfl

/-- A point of the spectrum of `𝒪_{X,x}` lies over the support precisely when
its prime contains the stalk ideal. -/
theorem mem_support_fromSpecStalk_iff_stalkIdeal_le
    (I : X.IdealSheafData) (x : X)
    (p : Spec (X.presheaf.stalk x)) :
    X.fromSpecStalk x p ∈ I.support ↔ I.stalkIdeal x ≤ p.asIdeal := by
  constructor
  · intro hp
    let f := X.affineCover.f (X.affineCover.idx x)
    let U := f.opensRange
    let hU : IsAffineOpen U := isAffineOpen_opensRange f
    let hx : x ∈ U := X.affineCover.covers x
    let q : PrimeSpectrum Γ(X, U) :=
      Spec.map (X.presheaf.germ U x hx) p
    have hqU : hU.fromSpec q ∈ U := by
      change (hU.isoSpec.inv q).1 ∈ U
      exact (hU.isoSpec.inv q).2
    have heq : X.fromSpecStalk x p = hU.fromSpec q := by
      rw [← hU.fromSpecStalk_eq_fromSpecStalk hx]
      rfl
    have hqSupport : hU.fromSpec q ∈ I.support := by
      rwa [← heq]
    have hqZero : hU.fromSpec q ∈
        X.zeroLocus (I.ideal ⟨U, hU⟩ : Set Γ(X, U)) :=
      (I.mem_support_iff_of_mem hqU).mp hqSupport
    have hq : q ∈ PrimeSpectrum.zeroLocus
        (I.ideal ⟨U, hU⟩ : Set Γ(X, U)) := by
      exact (Set.ext_iff.mp
        (hU.fromSpec_preimage_zeroLocus
          (I.ideal ⟨U, hU⟩ : Set Γ(X, U))) q).mp hqZero
    rw [I.stalkIdeal_eq_map_ideal x ⟨U, hU⟩ hx,
      Ideal.map_le_iff_le_comap]
    rw [PrimeSpectrum.mem_zeroLocus] at hq
    exact hq
  · exact I.mem_support_fromSpecStalk_of_stalkIdeal_le x p

/-- On the spectrum of the stalk, the support complement is the complement
of the stalk ideal. -/
theorem fromSpecStalk_preimage_supportComplement
    (I : X.IdealSheafData) (x : X) :
    X.fromSpecStalk x ⁻¹ᵁ I.supportComplement =
      PrimeSpectrum.idealComplement (I.stalkIdeal x) := by
  apply Opens.ext
  ext p
  change (X.fromSpecStalk x p ∉ I.support) ↔
    (¬ I.stalkIdeal x ≤ p.asIdeal)
  exact not_congr (mem_support_fromSpecStalk_iff_stalkIdeal_le I x p)

/-- After localizing the stalk at a prime, the support complement is defined
by the extended stalk ideal. -/
theorem localizationAtPrimeTo_preimage_supportComplement
    (I : X.IdealSheafData) (x : X)
    (P : Ideal (X.presheaf.stalk x)) [P.IsPrime] :
    Scheme.localizationAtPrimeTo X x P ⁻¹ᵁ I.supportComplement =
      PrimeSpectrum.idealComplement
        ((I.stalkIdeal x).map
          (algebraMap (X.presheaf.stalk x) (Localization.AtPrime P))) := by
  rw [Scheme.localizationAtPrimeTo, Scheme.Hom.comp_preimage,
    fromSpecStalk_preimage_supportComplement,
    PrimeSpectrum.preimage_idealComplement]

/-- If the localized stalk ideal is generated by `f`, the local support
complement is the basic open `D(f)`. -/
theorem localizationAtPrimeTo_preimage_supportComplement_eq_basicOpen
    (I : X.IdealSheafData) (x : X)
    (P : Ideal (X.presheaf.stalk x)) [P.IsPrime]
    (f : Localization.AtPrime P)
    (hboundary :
      (I.stalkIdeal x).map
          (algebraMap (X.presheaf.stalk x) (Localization.AtPrime P)) =
        Ideal.span {f}) :
    Scheme.localizationAtPrimeTo X x P ⁻¹ᵁ I.supportComplement =
      PrimeSpectrum.basicOpen f := by
  rw [localizationAtPrimeTo_preimage_supportComplement, hboundary,
    PrimeSpectrum.idealComplement_span_singleton]

/-- The local support complement cut out by a principal stalk ideal is the
spectrum of the localization away from its generator. -/
def localizationAtPrimeSupportComplementIsoSpecAway
    (I : X.IdealSheafData) (x : X)
    (P : Ideal (X.presheaf.stalk x)) [P.IsPrime]
    (f : Localization.AtPrime P)
    (hboundary :
      (I.stalkIdeal x).map
          (algebraMap (X.presheaf.stalk x) (Localization.AtPrime P)) =
        Ideal.span {f}) :
    (Scheme.localizationAtPrimeTo X x P ⁻¹ᵁ
        I.supportComplement).toScheme ≅
      Spec (.of (Localization.Away f)) :=
  (Spec (.of (Localization.AtPrime P))).isoOfEq
      (localizationAtPrimeTo_preimage_supportComplement_eq_basicOpen
        I x P f hboundary) ≪≫
    basicOpenIsoSpecAway (R := .of (Localization.AtPrime P)) f

/-- The canonical morphism from the localized principal complement into the
global support complement. -/
def localizationAwayToSupportComplement
    (I : X.IdealSheafData) (x : X)
    (P : Ideal (X.presheaf.stalk x)) [P.IsPrime]
    (f : Localization.AtPrime P)
    (hboundary :
      (I.stalkIdeal x).map
          (algebraMap (X.presheaf.stalk x) (Localization.AtPrime P)) =
        Ideal.span {f}) :
    Spec (.of (Localization.Away f)) ⟶ I.supportComplement :=
  (localizationAtPrimeSupportComplementIsoSpecAway
      I x P f hboundary).inv ≫
    (Scheme.localizationAtPrimeTo X x P ∣_ I.supportComplement)

/-- The map to the support complement is the factorization of the canonical
map from the principal localization back to the ambient scheme. -/
@[reassoc]
theorem localizationAwayToSupportComplement_comp_ι
    (I : X.IdealSheafData) (x : X)
    (P : Ideal (X.presheaf.stalk x)) [P.IsPrime]
    (f : Localization.AtPrime P)
    (hboundary :
      (I.stalkIdeal x).map
          (algebraMap (X.presheaf.stalk x) (Localization.AtPrime P)) =
        Ideal.span {f}) :
    localizationAwayToSupportComplement I x P f hboundary ≫
        I.supportComplement.ι =
      Spec.map (CommRingCat.ofHom
          (algebraMap (Localization.AtPrime P) (Localization.Away f))) ≫
        Scheme.localizationAtPrimeTo X x P := by
  let V : (Spec (.of (Localization.AtPrime P))).Opens := PrimeSpectrum.basicOpen f
  let b : V.toScheme ≅ Spec (.of (Localization.Away f)) :=
    basicOpenIsoSpecAway (R := .of (Localization.AtPrime P)) f
  let e : (Scheme.localizationAtPrimeTo X x P ⁻¹ᵁ
      I.supportComplement).toScheme ≅ V.toScheme :=
    (Spec (.of (Localization.AtPrime P))).isoOfEq
      (localizationAtPrimeTo_preimage_supportComplement_eq_basicOpen I x P f hboundary)
  have he : e.inv ≫ (Scheme.localizationAtPrimeTo X x P ⁻¹ᵁ
      I.supportComplement).ι = V.ι :=
    Scheme.isoOfEq_inv_ι _
      (localizationAtPrimeTo_preimage_supportComplement_eq_basicOpen I x P f hboundary)
  have hb : b.inv ≫ V.ι = Spec.map (CommRingCat.ofHom
      (algebraMap (Localization.AtPrime P) (Localization.Away f))) := by
    calc
      b.inv ≫ V.ι = b.inv ≫ (b.hom ≫ Spec.map (CommRingCat.ofHom
          (algebraMap (Localization.AtPrime P) (Localization.Away f)))) :=
        congrArg (fun k => b.inv ≫ k)
          (basicOpenIsoSpecAway_hom_SpecMap
            (R := .of (Localization.AtPrime P)) f).symm
      _ = _ := b.inv_hom_id_assoc _
  change ((b.inv ≫ e.inv) ≫
      (Scheme.localizationAtPrimeTo X x P ∣_ I.supportComplement)) ≫
        I.supportComplement.ι = _
  rw [Category.assoc, morphismRestrict_ι]
  calc
    (b.inv ≫ e.inv) ≫
        (Scheme.localizationAtPrimeTo X x P ⁻¹ᵁ I.supportComplement).ι ≫
          Scheme.localizationAtPrimeTo X x P =
      (b.inv ≫ (e.inv ≫
        (Scheme.localizationAtPrimeTo X x P ⁻¹ᵁ I.supportComplement).ι)) ≫
          Scheme.localizationAtPrimeTo X x P := by
        simp only [Category.assoc]
    _ = (b.inv ≫ V.ι) ≫ Scheme.localizationAtPrimeTo X x P :=
      congrArg (fun k => (b.inv ≫ k) ≫ Scheme.localizationAtPrimeTo X x P) he
    _ = _ := congrArg (fun k => k ≫ Scheme.localizationAtPrimeTo X x P) hb

end AlgebraicGeometry.Scheme.IdealSheafData

end
