/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/

/-
Based on pi1 source (comparison revision; exact copied commit unverified):
https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/FundamentalGroup/Galois.lean
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Galois.IsFundamentalgroup
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import Mathlib.RingTheory.Etale.Finite
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.Topology.Connected.CardComponents
public import Mathlib.Topology.Connected.LocallyConnected
public import Nyll.SchemeTheory.Morphisms.ClosedImmersion
public import Nyll.SchemeTheory.Morphisms.Flat
public import Nyll.SchemeTheory.Etale.RingHom
public import Nyll.SchemeTheory.Morphisms.Smooth
public import Nyll.SchemeTheory.CategoryTheory.Over
public import Nyll.SchemeTheory.RingTheory.QuotientProducts
public import Nyll.SchemeTheory.FiniteEtale.Basic
public import Nyll.SchemeTheory.Morphisms.FlatRank

/-!
# Geometric infrastructure for finite étale schemes

This module contains the scheme-theoretic and over-field results used by the
finite étale category, independently of fundamental groups and Galois objects.
-/

@[expose] public section

universe u

noncomputable section


open CategoryTheory Limits


namespace AlgebraicGeometry

namespace FiniteEtale

variable (X : Scheme.{u})

/-- An étale map whose source ring is isomorphic to a field has a finite prime spectrum. -/
private lemma finite_primeSpectrum_of_etale_field
    {K A B : Type u} [Field K] [CommRing A] [CommRing B]
    (e : A ≃+* K) (g : A →+* B) (hg : g.Etale) :
    Finite (PrimeSpectrum B) := by
  let a : Algebra K B := (g.comp e.symm.toRingHom).toAlgebra
  have hEtale : Algebra.Etale K B := by
    change (g.comp e.symm.toRingHom).Etale
    exact RingHom.Etale.respectsIso.right g e.symm hg
  have hFinite : Module.Finite K B :=
    Algebra.FormallyUnramified.finite_of_free K B
  have hArtinian : IsArtinianRing B := isArtinian_of_tower K inferInstance
  infer_instance

lemma finite_of_isEtale_of_isAffineHom (X : Scheme.{u}) {Ω : Type u} [Field Ω]
    (f : X ⟶ Spec (.of Ω)) [Etale f] [IsAffineHom f] :
    Finite X := by
  have hAffine : IsAffine X := isAffine_of_isAffineHom f
  have hEtale : Etale f := inferInstance
  rw [HasRingHomProperty.iff_of_isAffine (P := @Etale)] at hEtale
  have hSpectrum : Finite (PrimeSpectrum Γ(X, ⊤)) :=
    finite_primeSpectrum_of_etale_field
      (Scheme.ΓSpecIso (.of Ω)).commRingCatIsoToRingEquiv f.appTop.hom hEtale
  exact Finite.of_equiv (PrimeSpectrum Γ(X, ⊤))
    X.isoSpec.schemeIsoToHomeo.toEquiv.symm

instance {Ω : Type u} [Field Ω] (X : FiniteEtale (Spec (.of Ω))) : Fintype X.left := by
  let f : X.left ⟶ Spec (.of Ω) := X.hom
  let hX : IsFiniteEtale f := X.2
  let : Etale f := hX.toEtale
  let : IsFinite f := hX.toIsFinite
  let : IsAffineHom f := inferInstance
  have : Finite X.left := finite_of_isEtale_of_isAffineHom X.left f
  exact Fintype.ofFinite X.left

/-- Take the finite set of points of a finite etale scheme over a field. -/
@[simps]
def forgetScheme (Ω : Type u) [Field Ω] : FiniteEtale (Spec (.of Ω)) ⥤ FintypeCat.{u} where
  obj X := FintypeCat.of X.left
  map {X Y} f := { hom := TypeCat.ofHom (⇑f.left : ↥X.left → ↥Y.left) }

variable (Ω : Type u) [Field Ω]

lemma _root_.AlgebraicGeometry.IsFiniteEtale.SpecMap_iff {R S : CommRingCat.{u}}
    {f : R ⟶ S} :
    IsFiniteEtale (Spec.map f) ↔ f.hom.FiniteEtale := by
  have := RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.FiniteEtale.respectsIso
  simp only [HasAffineProperty.iff_of_isAffine (P := @IsFiniteEtale), affineAnd, and_iff_right]
  exact MorphismProperty.arrow_mk_iso_iff (RingHom.toMorphismProperty RingHom.FiniteEtale)
    (arrowIsoΓSpecOfIsAffine f).symm

instance {ι : Type u} [Finite ι] (R : Type u) [CommRing R] :
    IsFiniteEtale (Spec.map <| CommRingCat.ofHom <| algebraMap R (ι → R)) := by
  rw [IsFiniteEtale.SpecMap_iff]
  change (algebraMap R (ι → R)).FiniteEtale
  rw [RingHom.finiteEtale_algebraMap_iff]
  constructor

/-- Construct the finite etale scheme whose section ring is the ring of functions from a finite
set to the field. -/
@[simps!]
def inventScheme (Ω : Type u) [Field Ω] : FintypeCat.{u} ⥤ FiniteEtale (Spec (.of Ω)) where
  obj S :=
    mk (Spec.map <| CommRingCat.ofHom <| algebraMap Ω (S → Ω))
  map {S T} f :=
    MorphismProperty.Over.homMk
      (Spec.map <| CommRingCat.ofHom <|
        RingHom.pi (fun s ↦ Pi.evalRingHom _ (f s))) <| by
      let a : CommRingCat.of Ω ⟶ CommRingCat.of (T → Ω) :=
        CommRingCat.ofHom (algebraMap Ω (T → Ω))
      let b : CommRingCat.of (T → Ω) ⟶ CommRingCat.of (S → Ω) :=
        CommRingCat.ofHom
          (RingHom.pi (fun s ↦ Pi.evalRingHom (fun _ ↦ Ω) (f s)))
      let c : CommRingCat.of Ω ⟶ CommRingCat.of (S → Ω) :=
        CommRingCat.ofHom (algebraMap Ω (S → Ω))
      change Spec.map b ≫ Spec.map a = Spec.map c
      rw [← Spec.map_comp]
      rfl
  map_id S := by
    apply MorphismProperty.Over.Hom.ext
    change
      Spec.map
          (CommRingCat.ofHom
            (RingHom.pi (fun s ↦
              Pi.evalRingHom (fun _ ↦ Ω)
                ((𝟙 S : S ⟶ S) s)))) =
        𝟙 (Spec (CommRingCat.of (S → Ω)))
    rw [← Spec.map_id]
    congr 2
  map_comp {S T W} f g := by
    apply MorphismProperty.Over.Hom.ext
    let a : CommRingCat.of (W → Ω) ⟶ CommRingCat.of (S → Ω) :=
      CommRingCat.ofHom
        (RingHom.pi (fun s ↦ Pi.evalRingHom (fun _ ↦ Ω) ((f ≫ g) s)))
    let b : CommRingCat.of (T → Ω) ⟶ CommRingCat.of (S → Ω) :=
      CommRingCat.ofHom
        (RingHom.pi (fun s ↦ Pi.evalRingHom (fun _ ↦ Ω) (f s)))
    let c : CommRingCat.of (W → Ω) ⟶ CommRingCat.of (T → Ω) :=
      CommRingCat.ofHom
        (RingHom.pi (fun t ↦ Pi.evalRingHom (fun _ ↦ Ω) (g t)))
    change Spec.map a = Spec.map b ≫ Spec.map c
    rw [← Spec.map_comp]
    congr 2

instance (S : FintypeCat.{u}) :
    Fintype (Spec (CommRingCat.of (S.obj → Ω))).toPresheafedSpace :=
  let f : Spec (CommRingCat.of (S.obj → Ω)) ⟶ Spec (.of Ω) :=
    Spec.map (CommRingCat.ofHom <| algebraMap Ω _)
  have : Etale f := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    simp only [CommRingCat.hom_ofHom, RingHom.etale_algebraMap]
    infer_instance
  have : Finite (Spec (CommRingCat.of (S.obj → Ω))).toPresheafedSpace :=
    finite_of_isEtale_of_isAffineHom _ f
  Fintype.ofFinite _

/-- Identify the points of the spectrum of a finite product of fields with its product indices. -/
def specPiEquiv (ι : Type u) [Finite ι] (K : Type u) [Field K] :
    Spec (.of (ι → K)) ≃ ι :=
  ((Equiv.sigmaUnique ι (fun _ : ι ↦ Spec (.of K))).symm.trans
    (PrimeSpectrum.sigmaToPiHomeo (fun _ : ι ↦ K)).toEquiv).symm

@[simp]
lemma specPiEquiv_symm_apply (ι : Type u) [Finite ι] (K : Type u) [Field K]
    (i : ι) : (specPiEquiv ι K).symm i =
      (Spec.map <| CommRingCat.ofHom <| Pi.evalRingHom _ i).base default := by
  rfl

/-- The points of the finite etale scheme constructed from a finite set recover that set
naturally. -/
def inventForgetIso : inventScheme Ω ⋙ forgetScheme Ω ≅ 𝟭 FintypeCat :=
  Iso.symm <| NatIso.ofComponents fun S ↦ by
    let e₀ : S.obj ≃ Spec (.of (S.obj → Ω)) := (specPiEquiv S.obj Ω).symm
    let e : ((𝟭 FintypeCat).obj S).obj ≃
        ((inventScheme Ω ⋙ forgetScheme Ω).obj S).obj := {
      toFun s := e₀ s
      invFun x := e₀.symm x
      left_inv s := e₀.left_inv s
      right_inv x := e₀.right_inv x }
    exact FintypeCat.equivEquivIso e

instance (X : Scheme.{u}) (R : CommRingCat.{u}) [X.Over (Spec R)] (U : X.Opens) :
    Algebra R Γ(X, U) :=
  ((((X ↘ Spec R)).appLE ⊤ U (by
      rw [Scheme.Hom.preimage_top]
      exact le_top)).hom.comp
    (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.symm.toRingHom).toAlgebra

instance (X : Scheme.{u}) (R : Type u) [CommRing R] [X.Over (Spec (.of R))] (U : X.Opens) :
    Algebra R Γ(X, U) :=
  ((((X ↘ Spec (.of R))).appLE ⊤ U (by
      rw [Scheme.Hom.preimage_top]
      exact le_top)).hom.comp
    (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm.toRingHom).toAlgebra

lemma appLE_comp_algebraMap {X Y : Scheme.{u}} (f : X ⟶ Y) (R : Type u) [CommRing R]
    [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))] [f.IsOver (Spec (.of R))]
    (U : Y.Opens) (V : X.Opens) (hUV : V ≤ f ⁻¹ᵁ U) :
    (f.appLE U V hUV).hom.comp (algebraMap R Γ(Y, U)) = algebraMap R Γ(X, V) := by
  ext r
  simp only [RingHom.algebraMap_toAlgebra, Iso.commRingCatIsoToRingEquiv,
    RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply]
  have hover : f ≫ Y ↘ Spec (.of R) = X ↘ Spec (.of R) :=
    HomIsOver.comp_over
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  rw [hover]

instance (X : Scheme.{u}) (R : Type u) [CommRing R] [X.Over (Spec (.of R))]
    [Etale (X ↘ Spec (.of R))] [IsAffineHom (X ↘ Spec (.of R))] :
    Algebra.Etale R Γ(X, ⊤) := by
  rw [← RingHom.etale_algebraMap, RingHom.algebraMap_toAlgebra]
  apply RingHom.Etale.respectsIso.2
  let _ : IsAffine X := isAffine_of_isAffineHom (X ↘ Spec (.of R))
  exact HasRingHomProperty.appLE
    (P := (@Etale : MorphismProperty Scheme.{u}))
    (f := X ↘ Spec (.of R)) (show Etale (X ↘ Spec (.of R)) from inferInstance)
    ⟨⊤, isAffineOpen_top _⟩ ⟨⊤, isAffineOpen_top _⟩ le_rfl

instance (X : Scheme.{u}) (R : Type u) [Field R] [X.Over (Spec (.of R))]
    [Etale (X ↘ Spec (.of R))] [IsAffineHom (X ↘ Spec (.of R))] :
    Module.Finite R Γ(X, ⊤) :=
  Algebra.FormallyUnramified.finite_of_free R Γ(X, ⊤)

@[simp]
lemma appTop_left_comp_algebraMap {X Y : FiniteEtale (Spec <| .of Ω)} (f : X ⟶ Y) :
    f.left.appTop.hom.comp (algebraMap Ω Γ(Y.left, ⊤)) = algebraMap Ω Γ(X.left, ⊤) := by
  let _ : f.left.IsOver (Spec (.of Ω)) := ⟨MorphismProperty.Over.w f⟩
  have hApp : f.left.appTop =
      f.left.appLE (⊤ : Y.left.Opens) (⊤ : X.left.Opens) le_rfl :=
    Scheme.Hom.app_eq_appLE f.left
  have hLE :
      (f.left.appLE (⊤ : Y.left.Opens) (⊤ : X.left.Opens) le_rfl).hom.comp
          (algebraMap Ω Γ(Y.left, ⊤)) = algebraMap Ω Γ(X.left, ⊤) :=
    appLE_comp_algebraMap f.left Ω
      (⊤ : Y.left.Opens) (⊤ : X.left.Opens) le_rfl
  exact (congrArg
    (fun k : Γ(Y.left, ⊤) ⟶ Γ(X.left, ⊤) ↦
      k.hom.comp (algebraMap Ω Γ(Y.left, ⊤))) hApp).trans hLE

@[simp]
lemma appTop_left_algebraMap {X Y : FiniteEtale (Spec <| .of Ω)} (f : X ⟶ Y) (x : Ω) :
    f.left.appTop.hom (algebraMap Ω Γ(Y.left, ⊤) x) = algebraMap Ω Γ(X.left, ⊤) x :=
  DFunLike.congr_fun (appTop_left_comp_algebraMap Ω f) x

instance {S : Scheme.{u}} (X : FiniteEtale S) : IsFiniteEtale (X.left ↘ S) :=
  X.prop

/-- Reindex the canonical decomposition of an étale algebra by an equivalent point type. -/
def etaleFunctionsAlgEquiv (K A : Type u) [Field K] [CommRing A] [Algebra K A]
    [Algebra.Etale K A] [IsSepClosed K] {ι : Type u} (e : ι ≃ PrimeSpectrum A) :
    A ≃ₐ[K] (ι → K) :=
  (Algebra.FormallyEtale.equivPiOfIsSepClosed K A).trans
    (AlgEquiv.piCongrLeft K (fun _ : ι ↦ K) e.symm)

/-- A finite etale scheme over a separably closed field is the spectrum of the ring of functions
on its points. -/
def _root_.AlgebraicGeometry.IsFiniteEtale.isoSpecFun [IsSepClosed Ω] (X : Scheme.{u})
    [X.Over (Spec (.of Ω))] [IsFiniteEtale (X ↘ Spec (.of Ω))] :
    X ≅ Spec (.of <| X → Ω) :=
  have : IsAffine X := isAffine_of_isAffineHom (X ↘ Spec (.of Ω))
  let e : X ≃ PrimeSpectrum Γ(X, ⊤) := X.isoSpec.schemeIsoToHomeo.toEquiv
  let o : Γ(X, ⊤) ≃ₐ[Ω] (X → Ω) := etaleFunctionsAlgEquiv Ω Γ(X, ⊤) e
  X.isoSpec ≪≫ Scheme.Spec.mapIso o.toRingEquiv.toCommRingCatIso.symm.op

/-- The canonical affine presentation recovers the structure map from the scalar map. -/
private lemma isoSpec_hom_comp_specMap_algebraMap
    {R : Type u} [CommRing R] (X : Scheme.{u})
    [X.Over (Spec (.of R))] [IsAffine X] :
    X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, ⊤))) =
      X ↘ Spec (.of R) := by
  have hApp : (X ↘ Spec (.of R)).appTop =
      (X ↘ Spec (.of R)).appLE ⊤ ⊤ le_rfl :=
    Scheme.Hom.app_eq_appLE (X ↘ Spec (.of R))
  change X.isoSpec.hom ≫ Spec.map
      ((Scheme.ΓSpecIso (.of R)).inv ≫
        (X ↘ Spec (.of R)).appLE ⊤ ⊤ le_rfl) = X ↘ Spec (.of R)
  rw [← hApp, Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality,
    Category.assoc, ← Scheme.isoSpec_Spec_inv, Iso.hom_inv_id, Category.comp_id]

/-- An algebra equivalence on affine global sections gives a morphism over the base ring. -/
private lemma isoSpec_hom_comp_specMap_algEquiv
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (X : Scheme.{u}) [X.Over (Spec (.of R))] [IsAffine X]
    (e : Γ(X, ⊤) ≃ₐ[R] A) :
    X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom e.symm.toRingEquiv.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R A)) = X ↘ Spec (.of R) := by
  have hScalar : CommRingCat.ofHom (algebraMap R A) ≫
      CommRingCat.ofHom e.symm.toRingEquiv.toRingHom =
        CommRingCat.ofHom (algebraMap R Γ(X, ⊤)) :=
    congrArg CommRingCat.ofHom (AlgHom.comp_algebraMap e.symm.toAlgHom)
  rw [← Spec.map_comp, hScalar]
  exact isoSpec_hom_comp_specMap_algebraMap X

@[reassoc (attr := simp)]
lemma _root_.AlgebraicGeometry.IsFiniteEtale.isoSpecFun_hom_SpecMap [IsSepClosed Ω]
    (X : Scheme.{u}) [X.Over (Spec (.of Ω))] [IsFiniteEtale (X ↘ Spec (.of Ω))] :
    (IsFiniteEtale.isoSpecFun Ω X).hom ≫
      Spec.map (CommRingCat.ofHom <| algebraMap Ω (X → Ω)) = X ↘ Spec (.of Ω) := by
  have hAffine : IsAffine X := isAffine_of_isAffineHom (X ↘ Spec (.of Ω))
  let e : Γ(X, ⊤) ≃ₐ[Ω] (X → Ω) :=
    etaleFunctionsAlgEquiv Ω Γ(X, ⊤) X.isoSpec.schemeIsoToHomeo.toEquiv
  simpa only [e, IsFiniteEtale.isoSpecFun, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom,
    Scheme.Spec_map, Quiver.Hom.unop_op, Iso.symm_hom, RingEquiv.toCommRingCatIso_inv,
    AlgEquiv.symm_toRingEquiv, RingEquiv.toRingHom_eq_coe, Category.assoc] using
    isoSpec_hom_comp_specMap_algEquiv X e

instance (priority := 900) [IsAffine X] (Y : FiniteEtale X) : IsAffine Y.left := by
  let f : Y.left ⟶ X := Y.hom
  let hY : IsFiniteEtale f := Y.2
  let : IsFinite f := hY.toIsFinite
  let : IsAffineHom f := inferInstance
  exact isAffine_of_isAffineHom f

/-- A finite etale scheme over a separably closed field is naturally recovered from its finite
set of points. -/
def forgetInventIso [IsSepClosed Ω] :
    𝟭 (FiniteEtale (Spec (.of Ω))) ≅ forgetScheme Ω ⋙ inventScheme Ω :=
  NatIso.ofComponents (fun X ↦ by
    let e₀ : X.left ≅ Spec (.of (X.left → Ω)) :=
      IsFiniteEtale.isoSpecFun Ω X.left
    let e : ((𝟭 (FiniteEtale (Spec <| .of Ω))).obj X).left ≅
        ((forgetScheme Ω ⋙ inventScheme Ω).obj X).left := {
      hom := e₀.hom
      inv := e₀.inv
      hom_inv_id := e₀.hom_inv_id
      inv_hom_id := e₀.inv_hom_id }
    exact MorphismProperty.Over.isoMk
      (P := (@IsFiniteEtale : MorphismProperty Scheme.{u}))
      (Q := (⊤ : MorphismProperty Scheme.{u}))
      (X := Spec (.of Ω)) e (by
      exact IsFiniteEtale.isoSpecFun_hom_SpecMap Ω X.left)) <| fun {X Y} f ↦ by
      apply MorphismProperty.Over.Hom.ext
      change f.left ≫ (IsFiniteEtale.isoSpecFun Ω Y.left).hom =
        (IsFiniteEtale.isoSpecFun Ω X.left).hom ≫
          Spec.map (CommRingCat.ofHom <| RingHom.pi fun s ↦
            Pi.evalRingHom (fun _ : Y.left ↦ Ω) (f.left.base s))
      simp only [IsFiniteEtale.isoSpecFun, Iso.trans_hom, Functor.mapIso_hom,
        Iso.op_hom, Iso.symm_hom, RingEquiv.toCommRingCatIso_inv, Scheme.Spec_map,
        Quiver.Hom.unop_op, Category.assoc]
      rw [← Scheme.isoSpec_hom_naturality_assoc]
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 2
      let cX : Γ(X.left, ⊤) ≃ₐ[Ω] (X.left → Ω) :=
        (Algebra.FormallyEtale.equivPiOfIsSepClosed Ω Γ(X.left, ⊤)).trans
          (AlgEquiv.piCongrLeft Ω (fun _ : X.left ↦ Ω)
            X.left.isoSpec.schemeIsoToHomeo.toEquiv.symm)
      let cY : Γ(Y.left, ⊤) ≃ₐ[Ω] (Y.left → Ω) :=
        (Algebra.FormallyEtale.equivPiOfIsSepClosed Ω Γ(Y.left, ⊤)).trans
          (AlgEquiv.piCongrLeft Ω (fun _ : Y.left ↦ Ω)
            Y.left.isoSpec.schemeIsoToHomeo.toEquiv.symm)
      let φ : (Y.left → Ω) →+* (X.left → Ω) :=
        RingHom.pi fun s ↦
          Pi.evalRingHom (fun _ : Y.left ↦ Ω) (f.left.base s)
      let af : Γ(Y.left, ⊤) →ₐ[Ω] Γ(X.left, ⊤) :=
        { __ := f.left.appTop.hom
          commutes' := appTop_left_algebraMap Ω f }
      ext x
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
      change f.left.appTop (cY.symm x) = cX.symm (φ x)
      apply cX.injective
      rw [cX.apply_symm_apply]
      ext s
      simp only [cX]
      refine (congrFun (AlgEquiv.piCongrLeft_apply
        (R := Ω) (A₁ := fun _ : X.left ↦ Ω)
        X.left.isoSpec.schemeIsoToHomeo.toEquiv.symm
        (Algebra.FormallyEtale.equivPiOfIsSepClosed Ω Γ(X.left, ⊤)
          (af (cY.symm x)))) s).trans ?_
      have hp : (X.left.isoSpec.schemeIsoToHomeo s).comap af =
          Y.left.isoSpec.schemeIsoToHomeo (f.left.base s) := by
        change (Spec.map f.left.appTop).base (X.left.isoSpec.hom.base s) = _
        rw [← Scheme.Hom.comp_apply, Scheme.isoSpec_hom_naturality,
          Scheme.Hom.comp_apply]
        rfl
      calc
        _ = Algebra.FormallyEtale.equivPiOfIsSepClosed Ω Γ(X.left, ⊤)
            (af (cY.symm x)) (X.left.isoSpec.schemeIsoToHomeo s) := by
          have hEval :=
            Equiv.piCongrLeft_apply_eq_cast
              (P := fun _ : X.left ↦ Ω)
              (e := X.left.isoSpec.schemeIsoToHomeo.toEquiv.symm)
              (Algebra.FormallyEtale.equivPiOfIsSepClosed Ω Γ(X.left, ⊤)
                (af (cY.symm x)))
              s
          have hs : X.left.isoSpec.schemeIsoToHomeo.toEquiv s =
              X.left.isoSpec.schemeIsoToHomeo s := rfl
          rw [← hs]
          simpa only [cast_eq, Equiv.symm_symm_apply] using hEval
        _ = Algebra.FormallyEtale.equivPiOfIsSepClosed Ω Γ(Y.left, ⊤)
            (cY.symm x) ((X.left.isoSpec.schemeIsoToHomeo s).comap af) := by
          exact (Algebra.FormallyEtale.equivPiOfIsSepClosed_comap af
            (cY.symm x) (X.left.isoSpec.schemeIsoToHomeo s)).symm
        _ = Algebra.FormallyEtale.equivPiOfIsSepClosed Ω Γ(Y.left, ⊤)
            (cY.symm x) (Y.left.isoSpec.schemeIsoToHomeo (f.left.base s)) := by
          rw [hp]
        _ = (Equiv.piCongrLeft (fun _ : Y.left ↦ Ω)
              Y.left.isoSpec.schemeIsoToHomeo.toEquiv.symm)
            (Algebra.FormallyEtale.equivPiOfIsSepClosed Ω Γ(Y.left, ⊤)
              (cY.symm x)) (f.left.base s) := by
          symm
          have hEval :=
            Equiv.piCongrLeft_apply_eq_cast
              (P := fun _ : Y.left ↦ Ω)
              (e := Y.left.isoSpec.schemeIsoToHomeo.toEquiv.symm)
              (Algebra.FormallyEtale.equivPiOfIsSepClosed Ω Γ(Y.left, ⊤)
                (cY.symm x))
              (f.left.base s)
          have hs : Y.left.isoSpec.schemeIsoToHomeo.toEquiv (f.left.base s) =
              Y.left.isoSpec.schemeIsoToHomeo (f.left.base s) := rfl
          rw [← hs]
          simpa only [cast_eq, Equiv.symm_symm_apply] using hEval
        _ = cY (cY.symm x) (f.left.base s) := rfl
        _ = x (f.left.base s) :=
          congrFun (cY.apply_symm_apply x) (f.left.base s)
        _ = φ x s := rfl

/-- The equivalence between finite etale schemes over a separably closed field and finite sets. -/
def equivFintypeCat [IsSepClosed Ω] : FiniteEtale (Spec <| .of Ω) ≌ FintypeCat.{u} :=
  CategoryTheory.Equivalence.mk (forgetScheme Ω) (inventScheme Ω)
    (forgetInventIso Ω) (inventForgetIso Ω)

instance [IsSepClosed Ω] : (forgetScheme Ω).IsEquivalence :=
  (equivFintypeCat Ω).isEquivalence_functor

variable {Ω : Type u} [Field Ω] (ξ : Spec (.of Ω) ⟶ X)
variable {X}

/-- The open subset corresponding to one component when the scheme has finitely many connected
components. -/
def _root_.AlgebraicGeometry.Scheme.connCompOpen {X : Scheme.{u}}
    [Finite (_root_.ConnectedComponents X)]
    (i : _root_.ConnectedComponents X) : X.Opens :=
  ⟨ConnectedComponents.mk ⁻¹' {i}, by
    rw [ConnectedComponents.isQuotientMap_coe.isOpen_preimage]
    exact isOpen_discrete {i}⟩

/-- The open cover by connected components of a scheme with finitely many connected components. -/
def _root_.AlgebraicGeometry.Scheme.connectedComponents (X : Scheme.{u})
      [Finite (_root_.ConnectedComponents X)] :
    X.OpenCover where
  I₀ := _root_.ConnectedComponents X
  X c := X.connCompOpen c
  f c := (X.connCompOpen c).ι
  mem₀ := by
    rw [Scheme.ofArrows_mem_precoverage_iff]
    refine ⟨?_, ?_⟩
    · intro x
      refine ⟨.mk x, ?_⟩
      exact ⟨⟨x, rfl⟩, rfl⟩
    · infer_instance

instance {X : Scheme.{u}} [Finite (_root_.ConnectedComponents X)]
    (i : _root_.ConnectedComponents X) :
    ConnectedSpace (X.connectedComponents.X i) := by
  apply isConnected_iff_connectedSpace.mp
  simp only [Scheme.connCompOpen, TopologicalSpace.Opens.coe_mk]
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe i
  rw [connectedComponents_preimage_singleton]
  exact isConnected_connectedComponent

instance {X : Scheme.{u}} [Finite (_root_.ConnectedComponents X)]
    (i : _root_.ConnectedComponents X) :
    IsClosedImmersion (X.connectedComponents.f i) := by
  change IsClosedImmersion (X.connCompOpen i).ι
  apply IsClosedImmersion.of_isPreimmersion
  rw [Scheme.Opens.range_ι]
  change IsClosed (ConnectedComponents.mk ⁻¹' {i})
  rw [ConnectedComponents.isQuotientMap_coe.isClosed_preimage]
  exact isClosed_discrete {i}

lemma _root_.AlgebraicGeometry.IsFiniteEtale.isIso_of_isIso_snd {X Y Z : Scheme.{u}} (f : X ⟶ Z)
    (g : Y ⟶ Z) [IsFiniteEtale f] [PreconnectedSpace Z] [Nonempty Y]
    [IsIso (pullback.snd f g)] : IsIso f := by
  rw [f.isIso_iff_finrank_eq]
  obtain ⟨y⟩ := ‹Nonempty Y›
  ext z
  rw [finrank_eq_const_of_preconnectedSpace f z (g.base y), ← Scheme.Hom.finrank_pullback_snd,
    Scheme.Hom.finrank_eq_one_of_isIso, Pi.one_apply, Pi.one_apply]

instance {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) [IsFiniteEtale g] :
    IsFiniteEtale (pullback.fst f g) := by
  have hFiniteBC : MorphismProperty.IsStableUnderBaseChange
      (@IsFinite : MorphismProperty Scheme.{u}) := inferInstance
  have hEtaleBC : MorphismProperty.IsStableUnderBaseChange
      (@Etale : MorphismProperty Scheme.{u}) := Etale.etale_isStableUnderBaseChange
  exact @IsFiniteEtale.mk _ _ _
    (hFiniteBC.of_isPullback (IsPullback.of_hasPullback f g).flip
      (show IsFinite g from inferInstance))
    (hEtaleBC.of_isPullback (IsPullback.of_hasPullback f g).flip
      (show Etale g from inferInstance))

instance {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) [IsFiniteEtale f] :
    IsFiniteEtale (pullback.snd f g) := by
  have hFiniteBC : MorphismProperty.IsStableUnderBaseChange
      (@IsFinite : MorphismProperty Scheme.{u}) := inferInstance
  have hEtaleBC : MorphismProperty.IsStableUnderBaseChange
      (@Etale : MorphismProperty Scheme.{u}) := Etale.etale_isStableUnderBaseChange
  exact @IsFiniteEtale.mk _ _ _
    (hFiniteBC.of_isPullback (IsPullback.of_hasPullback f g)
      (show IsFinite f from inferInstance))
    (hEtaleBC.of_isPullback (IsPullback.of_hasPullback f g)
      (show Etale f from inferInstance))

instance _root_.AlgebraicGeometry.IsFiniteEtale.surjective {X Y : Scheme.{u}} (f : X ⟶ Y)
    [PreconnectedSpace Y] [Nonempty X] [IsFiniteEtale f] :
    Surjective f := by
  rw [← Scheme.Hom.one_le_finrank_iff_surjective]
  obtain ⟨x⟩ := ‹Nonempty X›
  intro y
  rw [finrank_eq_const_of_preconnectedSpace _ _ (f.base x)]
  apply Scheme.Hom.one_le_finrank_map

lemma _root_.AlgebraicGeometry.IsFiniteEtale.isIso_of_isIso_snd' {X Y Z : Scheme.{u}} (f : X ⟶ Z)
    (g : Y ⟶ Z) [IsFiniteEtale f]
    [Finite (_root_.ConnectedComponents Z)]
    [∀ i : _root_.ConnectedComponents Z, Nonempty ↑(Limits.pullback g
      (Z.connectedComponents.f i))]
    [IsIso (pullback.snd f g)] : IsIso f := by
  change MorphismProperty.isomorphisms _ _
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := MorphismProperty.isomorphisms Scheme.{u})
    Z.connectedComponents]
  intro i
  change IsIso (Z.connectedComponents.pullbackHom f i)
  dsimp only [Scheme.Cover.pullbackHom]
  let c : Z.connectedComponents.X i ⟶ Z := Z.connectedComponents.f i
  let f' : Limits.pullback f c ⟶ Z.connectedComponents.X i := pullback.snd f c
  let g' : Limits.pullback g c ⟶ Z.connectedComponents.X i := pullback.snd g c
  have hFiniteBC : MorphismProperty.IsStableUnderBaseChange
      (@IsFinite : MorphismProperty Scheme.{u}) := inferInstance
  have hEtaleBC : MorphismProperty.IsStableUnderBaseChange
      (@Etale : MorphismProperty Scheme.{u}) := Etale.etale_isStableUnderBaseChange
  let _ : IsFiniteEtale f' := @IsFiniteEtale.mk _ _ _
    (hFiniteBC.of_isPullback (IsPullback.of_hasPullback f c)
      (show IsFinite f from inferInstance))
    (hEtaleBC.of_isPullback (IsPullback.of_hasPullback f c)
      (show Etale f from inferInstance))
  let a : Limits.pullback f' g' ⟶ Limits.pullback f (g' ≫ c) :=
    (pullbackLeftPullbackSndIso f c g').hom
  let b : Limits.pullback f (g' ≫ c) ⟶
      Limits.pullback f (pullback.fst g c ≫ g) :=
    (pullback.congrHom rfl pullback.condition.symm).hom
  let d : Limits.pullback f (pullback.fst g c ≫ g) ⟶
      Limits.pullback (pullback.snd f g ≫ g) c :=
    (pullbackAssoc f g g c).inv
  let m : Limits.pullback (pullback.snd f g ≫ g) c ⟶ Limits.pullback g c :=
    pullback.map (pullback.snd f g ≫ g) c g c
      (pullback.snd f g) (𝟙 _) (𝟙 _) rfl rfl
  let _ : IsIso a := (pullbackLeftPullbackSndIso f c g').isIso_hom
  let _ : IsIso b := (pullback.congrHom rfl pullback.condition.symm).isIso_hom
  let _ : IsIso d := (pullbackAssoc f g g c).isIso_inv
  let _ : IsIso m := by
    dsimp only [m]
    exact pullback.map_isIso (pullback.snd f g ≫ g) c g c
      (pullback.snd f g) (𝟙 _) (𝟙 _) rfl rfl
  have heq : pullback.snd f' g' = a ≫ b ≫ d ≫ m := by
    dsimp only [a, b, d, m, c, f', g']
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.map, pullback.lift_fst,
        pullbackAssoc_inv_fst_snd, pullback.congrHom_hom,
        pullback.lift_snd_assoc, pullbackLeftPullbackSndIso_hom_snd_assoc,
        Category.comp_id]
    · simp only [Category.assoc, pullback.map, pullback.lift_snd,
        pullback.lift_snd_assoc, Category.comp_id, pullbackAssoc_inv_snd,
        pullback.congrHom_hom, pullbackLeftPullbackSndIso_hom_snd_assoc]
  let _ : IsIso (pullback.snd f' g') := by
    rw [heq]
    infer_instance
  change IsIso f'
  have hConnected : ConnectedSpace (Z.connectedComponents.X i) := by
    change ConnectedSpace (Z.connCompOpen i)
    apply isConnected_iff_connectedSpace.mp
    simp only [Scheme.connCompOpen, TopologicalSpace.Opens.coe_mk]
    obtain ⟨z, rfl⟩ := ConnectedComponents.surjective_coe i
    rw [connectedComponents_preimage_singleton]
    exact isConnected_connectedComponent
  let _ : PreconnectedSpace (Z.connectedComponents.X i) :=
    hConnected.toPreconnectedSpace
  have hNonemptyAll : ∀ j : _root_.ConnectedComponents Z,
      Nonempty ↑(Limits.pullback (C := Scheme.{u}) g
        (Z.connectedComponents.f j)) := by
    assumption
  let _ : Nonempty ↑(Limits.pullback g c) := by
    change Nonempty ↑(Limits.pullback g (Z.connectedComponents.f i))
    exact hNonemptyAll i
  exact IsFiniteEtale.isIso_of_isIso_snd f' g'

lemma isIso_of_isIso_left {A B : FiniteEtale X} (f : A ⟶ B) [IsIso f.left] : IsIso f := by
  have : IsIso ((forget X ⋙ Over.forget X).map f) := ‹_›
  exact isIso_of_reflects_iso f (forget X ⋙ Over.forget X)

instance [ConnectedSpace X] (Y : FiniteEtale X) :
    Finite (_root_.ConnectedComponents Y.left) := by
  have : ConnectedSpace ↑↑((Functor.fromPUnit X).obj Y.right).toPresheafedSpace := by
    exact inferInstanceAs (ConnectedSpace X)
  exact Y.hom.isOpenMap.finite_connectedComponents_of_finite_preimage_singleton Y.hom.isClosedMap
    Y.hom.continuous (fun y ↦ Scheme.Hom.finite_preimage_singleton _ y)

open MorphismProperty

instance {Y : Scheme.{u}} [Nonempty Y] (g : Y ⟶ X) [ConnectedSpace X] :
    (pullback g).ReflectsIsomorphisms := by
  constructor
  intro A B f hf
  let q : (pullback g).obj A ⟶ (pullback g).obj B := (pullback g).map f
  let _ : IsIso q := hf
  let qScheme : Limits.pullback A.hom g ⟶ Limits.pullback B.hom g :=
    (FiniteEtale.forget Y ⋙ _root_.CategoryTheory.Over.forget Y).map q
  have hqScheme : IsIso qScheme := by
    change IsIso ((FiniteEtale.forget Y ⋙ _root_.CategoryTheory.Over.forget Y).map q)
    infer_instance
  have hfW : f.left ≫ B.hom = A.hom := by
    change (Functor.id Scheme).map f.left ≫ B.hom = A.hom
    exact MorphismProperty.Over.w f
  let qLeft : Limits.pullback A.hom g ⟶ Limits.pullback B.hom g :=
    pullback.lift (pullback.fst A.hom g ≫ f.left) (pullback.snd A.hom g) (by
      calc
        (pullback.fst A.hom g ≫ f.left) ≫ B.hom =
            pullback.fst A.hom g ≫ (f.left ≫ B.hom) := Category.assoc _ _ _
        _ = pullback.fst A.hom g ≫ A.hom :=
          congrArg (fun k ↦ pullback.fst A.hom g ≫ k) hfW
        _ = pullback.snd A.hom g ≫ g := pullback.condition)
  have hqLeft_eq : qScheme = qLeft := rfl
  have hqLeft : IsIso qLeft := hqLeft_eq ▸ hqScheme
  let : IsIso f.left := by
    let e := pullbackRightPullbackFstIso B.hom g f.left
    have heq : e.inv ≫
        pullback.snd f.left (pullback.fst B.hom g) =
          (pullback.congrHom
            hfW rfl).hom ≫ qLeft := by
      change
        (pullbackRightPullbackFstIso B.hom g f.left).inv ≫
            pullback.snd f.left (pullback.fst B.hom g) =
          (pullback.congrHom
            hfW rfl).hom ≫
            pullback.lift
              (pullback.fst A.hom g ≫ f.left)
              (pullback.snd A.hom g) _
      apply pullback.hom_ext
      · simp only [Category.assoc,
          pullbackRightPullbackFstIso_inv_snd_fst,
          pullback.congrHom_hom, pullback.lift_fst_assoc,
          pullback.lift_fst, Category.comp_id]
      · simp only [Category.assoc,
          pullbackRightPullbackFstIso_inv_snd_snd,
          pullback.congrHom_hom,
          pullback.lift_snd, Category.comp_id]
    let : IsIso (e.inv ≫ pullback.snd f.left (pullback.fst B.hom g)) := by
      rw [heq]
      exact (pullback.congrHom
        hfW rfl ≪≫
          @asIso _ _ _ _ qLeft hqLeft).isIso_hom
    have : IsIso (pullback.snd f.left (pullback.fst B.hom g)) :=
      IsIso.of_isIso_comp_left e.inv _
    let hB : IsFiniteEtale B.hom := B.2
    let hpb : ∀ i : _root_.ConnectedComponents B.left,
        Nonempty ↑(Limits.pullback (pullback.fst B.hom g)
          (B.left.connectedComponents.f i)) := fun i ↦ by
      let e := pullbackRightPullbackFstIso B.hom g (B.left.connectedComponents.f i)
      let hnonempty : Nonempty ↑(Limits.pullback
          (B.left.connectedComponents.f i ≫ B.hom) g) := by
        obtain ⟨y⟩ := ‹Nonempty Y›
        let : IsFiniteEtale (B.left.connectedComponents.f i ≫ B.hom) := by
          let _ : IsOpenImmersion (B.left.connectedComponents.f i) := by
            dsimp only [Scheme.connectedComponents]
            infer_instance
          have hComponent : IsFiniteEtale (B.left.connectedComponents.f i) :=
            @IsFiniteEtale.mk _ _ _ inferInstance inferInstance
          exact MorphismProperty.comp_mem
            (@IsFiniteEtale : MorphismProperty Scheme.{u}) _ _ hComponent hB
        let : Nonempty (B.left.connectedComponents.X i) := inferInstance
        let : Surjective (B.left.connectedComponents.f i ≫ B.hom) := by
          have : PreconnectedSpace ↑((Functor.fromPUnit X).obj B.right) :=
            inferInstanceAs (PreconnectedSpace X)
          convert IsFiniteEtale.surjective _
          · infer_instance
          · infer_instance
          · infer_instance
        obtain ⟨z, hz⟩ := (B.left.connectedComponents.f i ≫ B.hom).surjective (g.base y)
        obtain ⟨o, _⟩ := Scheme.Pullback.exists_preimage_pullback _ _ hz
        use o
      exact hnonempty.map (((pullbackSymmetry _ _).hom ≫ e.hom).homeomorph.symm)
    exact @IsFiniteEtale.isIso_of_isIso_snd' _ _ _ f.left
      (pullback.fst B.hom g) inferInstance inferInstance hpb inferInstance
  apply isIso_of_isIso_left


end AlgebraicGeometry.FiniteEtale
