/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.AffineAnd
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.RingTheory.Localization.Away.Basic
import Nyll.SchemeTheory.Modules.QuasicoherentAffineLocalization

/-!
# Relative spectra of quasicoherent sheaves of commutative algebras

The input is an actual sheaf of commutative rings and its structure map from
the structure sheaf. Its underlying module is obtained by the existing
restriction-of-scalars functor. Quasicoherence of that native module supplies
the localization of the actual section rings. The existing affine Zariski
relative gluing construction then gives the scheme and its finite structure
morphism whenever the affine section algebras are finite.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.RelativeSpec

private theorem isFinite_comp_iso {Y Z W : Scheme.{u}}
    (f : Y ⟶ Z) (e : Z ≅ W) (hf : IsFinite f)
    (hRespect : MorphismProperty.RespectsIso (@IsFinite : MorphismProperty Scheme.{u})) :
    IsFinite (f ≫ e.hom) :=
  hRespect.toRespectsRight.postcomp e.hom e.isIso_hom f hf

variable {X : Scheme.{u}} {A : TopCat.Sheaf CommRingCat.{u} X}

/-- The underlying native module of a sheaf of commutative `𝒪_X`-algebras. -/
def underlyingModule (α : X.sheaf ⟶ A) : X.Modules :=
  let F : TopCat.Sheaf CommRingCat.{u} X ⥤ TopCat.Sheaf RingCat.{u} X :=
    sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})
  let AR : TopCat.Sheaf RingCat.{u} X := F.obj A
  let αR : X.ringCatSheaf ⟶ AR := F.map α
  let M : SheafOfModules.{u} AR := SheafOfModules.unit AR
  show SheafOfModules.{u} X.ringCatSheaf from
    { val := PresheafOfModules.restrictScalarsObj M.val αR.hom
      isSheaf := M.isSheaf }

/-- Quasicoherence of the underlying module makes the actual algebra
restriction on every affine basic open a ring localization. -/
theorem isLocalization_basicOpen (α : X.sheaf ⟶ A)
    [(underlyingModule α).IsQuasicoherent]
    (U : X.AffineZariskiSite) (f : Γ(X, U.1)) :
    let q := A.obj.map (homOfLE (X.basicOpen_le f)).op
    let : Algebra (A.obj.obj (op U.1)) (A.obj.obj (op (X.basicOpen f))) :=
      q.hom.toAlgebra
    IsLocalization.Away (α.hom.app (op U.1) f)
      (A.obj.obj (op (X.basicOpen f))) := by
  let B : CommRingCat.{u} := A.obj.obj (op U.1)
  let C : CommRingCat.{u} := A.obj.obj (op (X.basicOpen f))
  let q : B ⟶ C := A.obj.map (homOfLE (X.basicOpen_le f)).op
  let ι : Γ(X, U.1) →+* B := (α.hom.app (op U.1)).hom
  let ι' : Γ(X, X.basicOpen f) →+* C := (α.hom.app (op (X.basicOpen f))).hom
  let r : Γ(X, U.1) →+* Γ(X, X.basicOpen f) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
  let : Algebra B C := q.hom.toAlgebra
  change IsLocalization.Away (ι f) C
  have hnat (x : Γ(X, U.1)) : q.hom (ι x) = ι' (r x) := by
    exact (congrArg (fun e : Γ(X, U.1) ⟶ C => e.hom x)
      (α.hom.naturality (homOfLE (X.basicOpen_le f)).op)).symm
  obtain ⟨hsurj, hker⟩ :=
    Modules.basicOpenLocalization_of_isQuasicoherent
      (underlyingModule α) ⟨U.1, U.2⟩ f
  refine IsLocalization.Away.mk (ι f) ?_ ?_ ?_
  · change IsUnit (q.hom (ι f))
    rw [hnat]
    exact (RingedSpace.isUnit_res_basicOpen X.toRingedSpace f).map ι'
  · intro s
    obtain ⟨n, y, hy⟩ := hsurj s
    change q.hom y = ι' (r (f ^ n)) * s at hy
    refine ⟨n, y, ?_⟩
    change s * q.hom (ι f) ^ n = q.hom y
    have hp : q.hom (ι f) ^ n = ι' (r (f ^ n)) := by
      simp only [map_pow, hnat]
    rw [hp]
    exact (mul_comm s _).trans hy.symm
  · intro a b hab
    change q.hom a = q.hom b at hab
    have hz : (underlyingModule α).presheaf.map
        (homOfLE (X.basicOpen_le f)).op (a - b) = 0 := by
      change q.hom (a - b) = 0
      rw [map_sub, hab, sub_self]
    obtain ⟨n, hn⟩ := hker (a - b) hz
    refine ⟨n, ?_⟩
    change ι (f ^ n) * (a - b) = 0 at hn
    rw [map_pow, mul_sub, sub_eq_zero] at hn
    exact hn

/-- The affine diagram is cartesian on rings because its actual section
restriction maps are localizations. -/
theorem coequifibered (α : X.sheaf ⟶ A)
    [(underlyingModule α).IsQuasicoherent] :
    (Functor.whiskerLeft (AffineZariskiSite.toOpensFunctor X).op α.hom).Coequifibered := by
  apply AffineZariskiSite.coequifibered_iff_forall_isLocalizationAway.mpr
  intro U f
  exact isLocalization_basicOpen α U f

/-- The diagram of literal spectra of the section algebras. -/
def gluingData (α : X.sheaf ⟶ A)
    [(underlyingModule α).IsQuasicoherent] :
    (AffineZariskiSite.directedCover X).RelativeGluingData :=
  AffineZariskiSite.relativeGluingData (coequifibered α)

/-- The named gluing diagram uses the native locally directed colimit construction. -/
local instance gluingData_isLocallyDirected (α : X.sheaf ⟶ A)
    [(underlyingModule α).IsQuasicoherent] :
    ((gluingData α).functor ⋙ Scheme.forget).IsLocallyDirected :=
  Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin
    (gluingData α)

/-- The relative spectrum, constructed by gluing the affine section spectra. -/
def scheme (α : X.sheaf ⟶ A) [(underlyingModule α).IsQuasicoherent] : Scheme.{u} :=
  (gluingData α).glued

/-- The structure morphism of the actual relative spectrum. -/
def toBase (α : X.sheaf ⟶ A) [(underlyingModule α).IsQuasicoherent] : scheme α ⟶ X :=
  (gluingData α).toBase

/-- The covering by the literal spectra of the affine section algebras. -/
def openCover (α : X.sheaf ⟶ A) [(underlyingModule α).IsQuasicoherent] :
    (scheme α).OpenCover :=
  (gluingData α).cover

/-- The covering morphisms retain their native open-immersion proofs. -/
local instance openCover_isOpenImmersion (α : X.sheaf ⟶ A)
    [(underlyingModule α).IsQuasicoherent] (U : X.AffineZariskiSite) :
    IsOpenImmersion ((openCover α).f U) :=
  (openCover α).map_prop U

/-- Each affine model maps to the base by the given structure homomorphism. -/
@[reassoc]
theorem openCover_toBase (α : X.sheaf ⟶ A)
    [(underlyingModule α).IsQuasicoherent] (U : X.AffineZariskiSite) :
    (openCover α).f U ≫ toBase α =
      Spec.map (α.hom.app (op U.1)) ≫ U.2.fromSpec := by
  have h := (gluingData α).ι_toBase U
  change (openCover α).f U ≫ toBase α =
    (Spec.map (α.hom.app (op U.1)) ≫ U.2.isoSpec.inv) ≫ U.1.ι at h
  change (openCover α).f U ≫ toBase α =
    Spec.map (α.hom.app (op U.1)) ≫ (U.2.isoSpec.inv ≫ U.1.ι)
  exact h.trans (Category.assoc
    (Spec.map (α.hom.app (op U.1))) U.2.isoSpec.inv U.1.ι)

/-- The affine models are precisely the inverse images of the corresponding
affine opens of the base. -/
theorem toBase_preimage (α : X.sheaf ⟶ A)
    [(underlyingModule α).IsQuasicoherent] (U : X.AffineZariskiSite) :
    toBase α ⁻¹ᵁ U.1 = ((openCover α).f U).opensRange := by
  have h := (gluingData α).toBase_preimage_eq_opensRange_ι U
  change toBase α ⁻¹ᵁ U.1.ι.opensRange = ((openCover α).f U).opensRange at h
  rw [Opens.opensRange_ι] at h
  exact h

/-- The preimage of an affine open is the spectrum of its actual algebra
of sections. No affine representer is assumed as input. -/
def affineModelIso (α : X.sheaf ⟶ A)
    [(underlyingModule α).IsQuasicoherent] (U : X.AffineZariskiSite) :
    (toBase α ⁻¹ᵁ U.1).toScheme ≅ Spec (A.obj.obj (op U.1)) := by
  let j : (openCover α).X U ⟶ scheme α := (openCover α).f U
  have : IsOpenImmersion j := (openCover α).map_prop U
  let e : (toBase α ⁻¹ᵁ U.1).toScheme ≅ (openCover α).X U :=
    IsOpenImmersion.isoOfRangeEq (toBase α ⁻¹ᵁ U.1).ι j
      (by
        rw [Opens.range_ι]
        exact congrArg (fun V : (scheme α).Opens => (V : Set (scheme α)))
          (toBase_preimage α U))
  exact e

/-- The affine model is a cartesian chart over the corresponding open of `X`. -/
theorem isPullback_affineModel (α : X.sheaf ⟶ A)
    [(underlyingModule α).IsQuasicoherent] (U : X.AffineZariskiSite) :
    IsPullback (Spec.map (α.hom.app (op U.1)) ≫ U.2.isoSpec.inv)
      ((openCover α).f U) U.1.ι (toBase α) :=
  (gluingData α).isPullback_natTrans_ι_toBase U

/-- Restriction of algebra sections induces the actual transition map
between the affine charts of the glued relative spectrum. -/
@[reassoc]
theorem restriction_openCover (α : X.sheaf ⟶ A)
    [(underlyingModule α).IsQuasicoherent]
    {U V : X.AffineZariskiSite} (i : U ⟶ V) :
    Spec.map (A.obj.map ((AffineZariskiSite.toOpensFunctor X).map i).op) ≫
      (openCover α).f V = (openCover α).f U :=
  colimit.w (gluingData α).functor i

/-- A restriction of algebra sections is an open immersion on the actual
spectra. This is the map used in the gluing diagram. -/
theorem isOpenImmersion_restriction (α : X.sheaf ⟶ A)
    [(underlyingModule α).IsQuasicoherent]
    {U V : X.AffineZariskiSite} (i : U ⟶ V) :
    IsOpenImmersion
      (Spec.map (A.obj.map ((AffineZariskiSite.toOpensFunctor X).map i).op)) :=
  inferInstanceAs (IsOpenImmersion ((gluingData α).functor.map i))

/-- The transition over a basic open has exactly the expected basic-open image. -/
theorem restriction_opensRange (α : X.sheaf ⟶ A)
    [(underlyingModule α).IsQuasicoherent]
    (U : X.AffineZariskiSite) (f : Γ(X, U.1)) :
    let : IsOpenImmersion (Spec.map (A.obj.map (homOfLE (X.basicOpen_le f)).op)) :=
      isOpenImmersion_restriction α (homOfLE (U.basicOpen_le f))
    (Spec.map (A.obj.map (homOfLE (X.basicOpen_le f)).op)).opensRange =
      PrimeSpectrum.basicOpen (α.hom.app (op U.1) f) :=
  AffineZariskiSite.opensRange_relativeGluingData_map
    ((AffineZariskiSite.toOpensFunctor X).op ⋙ A.obj)
    (Functor.whiskerLeft (AffineZariskiSite.toOpensFunctor X).op α.hom)
    (coequifibered α) f

/-- The explicit affine isomorphism respects the structure maps. -/
@[reassoc]
theorem affineModelIso_toBase (α : X.sheaf ⟶ A)
    [(underlyingModule α).IsQuasicoherent] (U : X.AffineZariskiSite) :
    (affineModelIso α U).hom ≫ Spec.map (α.hom.app (op U.1)) =
      (toBase α ∣_ U.1) ≫ U.2.isoSpec.hom := by
  have hchart : (affineModelIso α U).hom ≫ (openCover α).f U =
      (toBase α ⁻¹ᵁ U.1).ι := by
    let j : (openCover α).X U ⟶ scheme α := (openCover α).f U
    have : IsOpenImmersion j := (openCover α).map_prop U
    have hrange : Set.range (toBase α ⁻¹ᵁ U.1).ι = Set.range j := by
      rw [Opens.range_ι]
      exact congrArg (fun V : (scheme α).Opens => (V : Set (scheme α)))
        (toBase_preimage α U)
    exact IsOpenImmersion.isoOfRangeEq_hom_fac (toBase α ⁻¹ᵁ U.1).ι j hrange
  apply (cancel_mono U.2.fromSpec).mp
  calc
    ((affineModelIso α U).hom ≫ Spec.map (α.hom.app (op U.1))) ≫ U.2.fromSpec =
        (affineModelIso α U).hom ≫
          (Spec.map (α.hom.app (op U.1)) ≫ U.2.fromSpec) :=
      Category.assoc _ _ _
    _ = (affineModelIso α U).hom ≫ ((openCover α).f U ≫ toBase α) :=
      congrArg (fun k => (affineModelIso α U).hom ≫ k) (openCover_toBase α U).symm
    _ = ((affineModelIso α U).hom ≫ (openCover α).f U) ≫ toBase α :=
      (Category.assoc _ _ _).symm
    _ = (toBase α ⁻¹ᵁ U.1).ι ≫ toBase α :=
      congrArg (fun k => k ≫ toBase α) hchart
    _ = (toBase α ∣_ U.1) ≫ U.1.ι := (morphismRestrict_ι (toBase α) U.1).symm
    _ = ((toBase α ∣_ U.1) ≫ U.2.isoSpec.hom) ≫ U.2.fromSpec :=
      ((Category.assoc (toBase α ∣_ U.1) U.2.isoSpec.hom U.2.fromSpec).trans
        (congrArg (fun k => (toBase α ∣_ U.1) ≫ k)
          (IsAffineOpen.isoSpec_hom_fromSpec U.2))).symm

/-- The constructed relative spectrum is finite over `X` when the affine
section algebras are finite over their structure rings. -/
theorem isFinite_toBase (α : X.sheaf ⟶ A)
    [(underlyingModule α).IsQuasicoherent]
    (hfinite : ∀ U : X.AffineZariskiSite, (α.hom.app (op U.1)).hom.Finite) :
    IsFinite (toBase α) := by
  have hAffine : HasAffineProperty (@IsFinite : MorphismProperty Scheme.{u})
      (affineAnd RingHom.Finite) :=
    (HasAffineProperty.affineAnd_iff (@IsFinite : MorphismProperty Scheme.{u})
      RingHom.finite_respectsIso RingHom.finite_localizationPreserves.away
      RingHom.finite_ofLocalizationSpan).mpr
        (fun {Y Z : Scheme.{u}} (g : Y ⟶ Z) => isFinite_iff g)
  have hLocal : IsZariskiLocalAtTarget (@IsFinite : MorphismProperty Scheme.{u}) :=
    ((HasAffineProperty.iff
      (P := (@IsFinite : MorphismProperty Scheme.{u}))
      (Q := affineAnd RingHom.Finite)).mp hAffine).1
  apply IsZariskiLocalAtTarget.of_openCover
    (P := (@IsFinite : MorphismProperty Scheme.{u}))
    (AffineZariskiSite.directedCover X)
  intro i
  let U : X.AffineZariskiSite := i
  let h := ((gluingData α).isPullback_natTrans_ι_toBase U).flip
  have hmodel : IsFinite ((gluingData α).natTrans.app U) := by
    let e : U.1.toScheme ≅ Spec Γ(X, U.1) := U.2.isoSpec
    change IsFinite (Spec.map (α.hom.app (op U.1)) ≫ e.inv)
    have hSpec : IsFinite (Spec.map (α.hom.app (op U.1))) :=
      (IsFinite.SpecMap_iff (α.hom.app (op U.1))).mpr (hfinite U)
    exact isFinite_comp_iso (Spec.map (α.hom.app (op U.1))) e.symm hSpec
      hLocal.toRespects
  have hfiniteComp : IsFinite (h.isoPullback.inv ≫ (gluingData α).natTrans.app U) :=
    inferInstance
  exact Eq.mp (congrArg IsFinite h.isoPullback_inv_snd) hfiniteComp

end AlgebraicGeometry.Scheme.RelativeSpec
