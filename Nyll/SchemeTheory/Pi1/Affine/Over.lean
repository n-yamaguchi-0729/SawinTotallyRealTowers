/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/

/-
Adapted from the pinned pi1 source:
https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/FundamentalGroup/AffineColimits.lean
-/

/-
This is a Nyll-maintained port, not an unmodified upstream file.
Local changes adapt imports, proofs and API compatibility to the pinned Nyll toolchain.
Upstream notices above apply to the upstream-derived code; they are not replaced by
Nyll authorship. Revision, file hashes and modification provenance are recorded in
Nyll/EtaleFundamentalGroups/Pi1/UPSTREAM.json and ATTRIBUTION.md.

Local proof adaptations and compatibility additions:
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Authors of local modifications: Naganori Yamaguchi (assisted by OpenAI Codex).
-/

module

public import Mathlib.AlgebraicGeometry.ColimitsOver
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Category of schemes affine over an affine base

-/


@[expose] public section

universe w t u

noncomputable section

open CategoryTheory Limits Opposite TensorProduct

section

namespace CategoryTheory

variable {C : Type*} [Category C] (P Q : MorphismProperty C) [Q.IsMultiplicative]
  [P.IsStableUnderBaseChange] [Q.IsStableUnderBaseChange]

/-- Pullback along the identity is naturally isomorphic to the identity on the relative category. -/
def MorphismProperty.Over.pullbackId [HasPullbacks C] (X : C) :
    MorphismProperty.Over.pullback P Q (𝟙 X) ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun A ↦ MorphismProperty.Over.isoMk
      (Comma.leftIso (CategoryTheory.Over.pullbackId.app <| A.toComma))
      (CategoryTheory.Over.w
        (CategoryTheory.Over.pullbackId.hom.app A.toComma)))
    (by
      intro A B f
      ext
      exact congrArg CommaMorphism.left
        (CategoryTheory.Over.pullbackId.hom.naturality f.hom))

/-- Transport the relative category along an isomorphism of base objects. -/
def MorphismProperty.Over.pullbackIso [HasPullbacks C] {X Y : C} (e : X ≅ Y) :
    P.Over Q X ≌ P.Over Q Y :=
  Equivalence.mk
    (MorphismProperty.Over.pullback P Q e.inv)
    (MorphismProperty.Over.pullback P Q e.hom)
    ((MorphismProperty.Over.pullbackId P Q _).symm ≪≫
      MorphismProperty.Over.pullbackCongr e.hom_inv_id.symm ≪≫
      MorphismProperty.Over.pullbackComp e.hom e.inv)
    ((MorphismProperty.Over.pullbackComp e.inv e.hom).symm ≪≫
      MorphismProperty.Over.pullbackCongr e.inv_hom_id ≪≫
      (MorphismProperty.Over.pullbackId P Q _))

end CategoryTheory

end

section

variable {C : Type*} [Category C]

instance MorphismProperty.top_isStableUnderBaseChange :
    (⊤ : MorphismProperty C).IsStableUnderBaseChange where
  of_isPullback _ _ := trivial

instance (P : MorphismProperty C) : (⊤ : MorphismProperty C).HasOfPostcompProperty P where
  of_postcomp _ _ _ _ := trivial

end

namespace AlgebraicGeometry

section

variable {P Q : MorphismProperty Scheme.{u}} [Q.IsMultiplicative] [P.IsStableUnderBaseChange]
  [Q.IsStableUnderBaseChange] [P.IsMultiplicative]
variable {S : Scheme.{u}} {J : Type t} [Category J] (D : J ⥤ P.Over ⊤ S)
  {𝒰 : Scheme.OpenCover.{w} S} [Small.{u} 𝒰.I₀] [Category 𝒰.I₀] [Quiver.IsThin 𝒰.I₀]
  [𝒰.LocallyDirected]
variable (d : 𝒰.ColimitGluingData D)
--variable [∀ {i j : d.ι} (hij : d.ℬ i ≤ d.ℬ j),
--  PreservesColimitsOfShape J (MorphismProperty.Over.map Q (d.hPhom hij))]
variable [∀ (i j : 𝒰.I₀) (hij : i ⟶ j),
  PreservesColimitsOfShape J (MorphismProperty.Over.pullback P ⊤ (𝒰.trans hij))]
variable [IsZariskiLocalAtTarget P]

@[reassoc (attr := simp)]
lemma Scheme.Cover.ColimitGluingData.pullbackGluedIso_hom (i : 𝒰.I₀) :
    (d.pullbackGluedIso i).hom.left ≫ colimit.ι d.relativeGluingData.functor i =
      pullback.fst _ _ := by
  let e :
      ((MorphismProperty.Over.pullback P ⊤ (𝒰.f i)).obj d.glued).left ≅
        (d.cocone i).pt.left :=
    (MorphismProperty.Over.forget P ⊤ _ ⋙ Over.forget _).mapIso
      (d.pullbackGluedIso i)
  change e.hom ≫ colimit.ι d.relativeGluingData.functor i =
    pullback.fst d.glued.hom (𝒰.f i)
  rw [← d.pullbackGluedIso_inv_fst i]
  exact e.hom_inv_id_assoc (pullback.fst d.glued.hom (𝒰.f i))

/-- Identify the pullback of the glued cocone with the cocone on an individual cover chart. -/
def Scheme.Cover.ColimitGluingData.mapCoconePullback (i : 𝒰.I₀) :
    (MorphismProperty.Over.pullback P ⊤ (𝒰.f i)).mapCocone
      d.gluedCocone ≅ d.cocone i := by
  refine Cocone.ext (d.pullbackGluedIso i) ?_
  intro j
  ext : 1
  let q : (D.obj j).left ⟶ S := (D.obj j).hom
  let u : (D.obj j).left ⟶ d.glued.left :=
    (d.gluedCocone.ι.app j).left
  let a : pullback q (𝒰.f i) ⟶ pullback d.glued.hom (𝒰.f i) :=
    (((MorphismProperty.Over.pullback P ⊤ (𝒰.f i)).mapCocone
      d.gluedCocone).ι.app j).left
  let b : pullback q (𝒰.f i) ⟶ (d.cocone i).pt.left :=
    ((d.cocone i).ι.app j).left
  change a ≫ (d.pullbackGluedIso i).hom.left = b
  let k := colimit.ι d.relativeGluingData.functor i
  let p : pullback d.glued.hom (𝒰.f i) ⟶ d.glued.left :=
    pullback.fst d.glued.hom (𝒰.f i)
  let qfst : pullback q (𝒰.f i) ⟶ (D.obj j).left :=
    pullback.fst q (𝒰.f i)
  have ha : a ≫ p = qfst ≫ u := by
    change (pullback.lift (pullback.fst q (𝒰.f i) ≫ u)
      (pullback.snd q (𝒰.f i)) _) ≫
        pullback.fst d.glued.hom (𝒰.f i) =
      pullback.fst q (𝒰.f i) ≫ u
    exact pullback.lift_fst _ _ _
  have hk : (d.pullbackGluedIso i).hom.left ≫ k = p :=
    Scheme.Cover.ColimitGluingData.pullbackGluedIso_hom
      (D := D) (𝒰 := 𝒰) d i
  have hglue : qfst ≫ u = b ≫ k :=
    d.fst_gluedCocone_ι j i
  have hab : a ≫ p = b ≫ k := ha.trans hglue
  apply (cancel_mono k).1
  exact (Category.assoc a (d.pullbackGluedIso i).hom.left k).trans
    ((congrArg (fun z ↦ a ≫ z) hk).trans hab)

end

section

variable {X Y S : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine S] {f : X ⟶ S} {g : Y ⟶ S}

lemma Γ_isPushout {P : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y} (h : IsPullback fst snd f g) :
    IsPushout (f.app ⊤) (g.app ⊤) (fst.app ⊤) (snd.app ⊤) := by
  have : IsAffine (pullback f g) := inferInstance
  let iso : P ≅ pullback f g := h.isoPullback
  have : IsAffine P := .of_isIso iso.hom
  let h' : IsPullback (AffineScheme.ofHom fst) (AffineScheme.ofHom snd)
      (AffineScheme.ofHom f) (AffineScheme.ofHom g) := by
    apply IsPullback.of_map (F := AffineScheme.forgetToScheme.{u}) (ObjectProperty.hom_ext _ h.w)
    exact h
  have h'' := AffineScheme.Γ.rightOp.map_isPullback h'
  have h2 := h''.unop
  exact h2.flip

variable (f g)

/-- Global sections identify a pullback of affine schemes with the pushout of their section
rings. -/
def ΓpullbackIsoPushout : Γ(pullback f g, ⊤) ≅ pushout f.appTop g.appTop :=
  IsPushout.isoPushout (Γ_isPushout (f := f) (g := g) <| IsPullback.of_hasPullback f g)

@[reassoc (attr := simp)]
lemma inl_ΓpullbackIsoPushout_inv :
    pushout.inl f.appTop g.appTop ≫ (ΓpullbackIsoPushout f g).inv = (pullback.fst f g).appTop := by
  exact (Γ_isPushout (f := f) (g := g) <| IsPullback.of_hasPullback f g).inl_isoPushout_inv

@[reassoc (attr := simp)]
lemma inr_ΓpullbackIsoPushout_inv :
    pushout.inr f.appTop g.appTop ≫ (ΓpullbackIsoPushout f g).inv = (pullback.snd f g).appTop := by
  exact (Γ_isPushout (f := f) (g := g) <| IsPullback.of_hasPullback f g).inr_isoPushout_inv

@[reassoc (attr := simp)]
lemma app_fst_ΓpullbackIsoPushout_hom :
     (pullback.fst f g).appTop ≫ (ΓpullbackIsoPushout f g).hom =
        pushout.inl f.appTop g.appTop := by
  exact (Γ_isPushout (f := f) (g := g) <| IsPullback.of_hasPullback f g).inl_isoPushout_hom

@[reassoc (attr := simp)]
lemma app_snd_ΓpullbackIsoPushout_hom :
     (pullback.snd f g).appTop ≫ (ΓpullbackIsoPushout f g).hom =
        pushout.inr f.appTop g.appTop := by
  exact (Γ_isPushout (f := f) (g := g) <| IsPullback.of_hasPullback f g).inr_isoPushout_hom

end

variable (S : Scheme.{u})

section General

variable (A : CommRingCat.{u})

/-- Apply the spectrum functor to objects over the opposite of a commutative ring. -/
def Over.Spec : Over (op A) ⥤ Over (Spec A) :=
  Over.post Scheme.Spec

/-- Send a scheme over the base to its global sections under the section ring of the base. -/
def Over.Γ : (Over S)ᵒᵖ ⥤ Under Γ(S, ⊤) :=
  (Under.opEquivOpOver S).inverse ⋙ Under.post Scheme.Γ

end General

/-- The category of affine morphisms with target `S`. -/
def Affine : Type _ := MorphismProperty.Over @IsAffineHom ⊤ S

variable {S} in
/-- View an affine morphism as an object of the category of affine morphisms over its target. -/
abbrev Affine.mk {X : Scheme.{u}} (f : X ⟶ S) [IsAffineHom f] : Affine S :=
  MorphismProperty.Over.mk ⊤ f inferInstance

instance : Category (Affine S) := by
  unfold Affine
  exact MorphismProperty.Comma.instCategory
    (Functor.id Scheme) (Functor.fromPUnit S) @IsAffineHom ⊤ ⊤

instance (X : Affine S) : IsAffineHom X.hom := X.prop

namespace Affine

local instance affineHomOverCategory (S : Scheme.{u}) :
    Category (MorphismProperty.Over
      (@IsAffineHom : MorphismProperty Scheme.{u})
      (⊤ : MorphismProperty Scheme.{u}) S) :=
  instCategoryAffine S

local instance affineHomHasPullbacksAlong {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.HasPullbacksAlong
      (@IsAffineHom : MorphismProperty Scheme.{u}) f :=
  ⟨fun _ _ ↦ inferInstance⟩

local instance affineHomIsStableUnderBaseChangeAlong
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.IsStableUnderBaseChangeAlong
      (@IsAffineHom : MorphismProperty Scheme.{u}) f :=
  ⟨fun h hf ↦ isAffineHom_isStableUnderBaseChange.of_isPullback h hf⟩

local instance affineHomIsStableUnderComposition :
    MorphismProperty.IsStableUnderComposition
      (@IsAffineHom : MorphismProperty Scheme.{u}) :=
  ⟨fun _ _ hf hg ↦ by
    let _ := hf
    let _ := hg
    infer_instance⟩

local instance affineHomHasAffineProperty :
    HasAffineProperty
      (@IsAffineHom : MorphismProperty Scheme.{u})
      (fun X _ _ _ ↦ IsAffine X) :=
  AlgebraicGeometry.instHasAffinePropertyIsAffineHomIsAffine

local instance affineHomIsZariskiLocalAtTarget :
    IsZariskiLocalAtTarget
      (@IsAffineHom : MorphismProperty Scheme.{u}) :=
  (HasAffineProperty.iff.mp affineHomHasAffineProperty).1

section

variable {S} {T : Scheme.{u}}

/-- Base change affine morphisms along a morphism of schemes. -/
abbrev pullback (f : T ⟶ S) : Affine S ⥤ Affine T := by
  unfold AlgebraicGeometry.Affine
  exact MorphismProperty.Over.pullback
    (P := (@IsAffineHom : MorphismProperty Scheme.{u}))
    (Q := (⊤ : MorphismProperty Scheme.{u})) (f := f)

variable (f : T ⟶ S)

/-- Compose affine morphisms with the given affine morphism of bases. -/
abbrev map [IsAffineHom f] : Affine T ⥤ Affine S := by
  unfold AlgebraicGeometry.Affine
  exact MorphismProperty.Over.map
    (P := (@IsAffineHom : MorphismProperty Scheme.{u}))
    (f := f) (⊤ : MorphismProperty Scheme.{u})
    (show IsAffineHom f from inferInstance)

/-- Composition with an affine base morphism is left adjoint to base change. -/
abbrev mapPullbackAdjunction [IsAffineHom f] :
    map (f := f) ⊣ Affine.pullback f := by
  unfold AlgebraicGeometry.Affine
  exact MorphismProperty.Over.mapPullbackAdj
    (P := (@IsAffineHom : MorphismProperty Scheme.{u}))
    (Q := (⊤ : MorphismProperty Scheme.{u})) (f := f)
    (show IsAffineHom f from inferInstance) trivial

instance [IsAffineHom f] : (map (f := f)).IsLeftAdjoint :=
  ⟨Affine.pullback f, ⟨mapPullbackAdjunction (f := f)⟩⟩

instance [IsAffineHom f] : (Affine.pullback f).IsRightAdjoint :=
  ⟨map (f := f), ⟨mapPullbackAdjunction (f := f)⟩⟩

end

section AffineBase

variable [IsAffine S]

instance (X : Affine S) : IsAffine ((Functor.fromPUnit S).obj X.right) := ‹IsAffine S›

instance (X : Affine S) : IsAffine X.left := by
  exact @isAffine_of_isAffineHom X.left S X.hom X.prop ‹IsAffine S›

instance (X : Affine S) : IsAffine ((𝟭 Scheme).obj X.left) := inferInstanceAs <| IsAffine X.left

/-- View affine morphisms over an affine base in the over category of affine schemes. -/
def toAffine : Affine S ⥤ Over (AffineScheme.mk S inferInstance) :=
  { obj := fun X ↦ Over.mk (AffineScheme.ofHom X.hom)
    map := fun {X Y} f ↦ Over.homMk (AffineScheme.ofHom f.left) <| by
      apply ObjectProperty.hom_ext
      exact CategoryTheory.Over.w f.1 }

/-- Forget the affine-scheme packaging of an object over an affine base. -/
noncomputable
def fromAffine : Over (AffineScheme.mk S inferInstance) ⥤ Affine S :=
  { obj := fun X ↦
      let hHom : IsAffineHom X.hom.hom :=
        @isAffineHom_of_isAffine X.left.obj S X.hom.hom
          (isAffine_affineScheme X.left) ‹IsAffine S›
      MorphismProperty.Over.mk (⊤ : MorphismProperty Scheme.{u}) X.hom.hom hHom
    map := fun {X Y} f ↦ MorphismProperty.Over.homMk f.left.hom <| by
      exact congrArg
        (fun k : X.left ⟶ AffineScheme.mk S inferInstance ↦ k.hom)
        (CategoryTheory.Over.w f) }

lemma toAffine_fromAffine : toAffine S ⋙ fromAffine S = 𝟭 _ := rfl
lemma fromAffine_toAffine : fromAffine S ⋙ toAffine S = 𝟭 _ := rfl

/-- If `S` is affine, the category of affine morphisms with target `S` is equivalent
to the over category of `S` viewed as affine scheme. -/
def toAffineEquiv : Affine S ≌ Over (AffineScheme.mk S inferInstance) :=
  CategoryTheory.Equivalence.mk (toAffine S) (fromAffine S)
    (eqToIso (toAffine_fromAffine S).symm)
    (eqToIso (fromAffine_toAffine S))

instance : (toAffine S).IsEquivalence := (toAffineEquiv S).isEquivalence_functor
instance : (fromAffine S).IsEquivalence := (toAffineEquiv S).isEquivalence_inverse

/-- Apply global sections to affine schemes over the base, with values in the opposite under
category. -/
def Over.AffineΓ : Over (AffineScheme.mk S inferInstance) ⥤ (Under Γ(S, ⊤))ᵒᵖ :=
  Over.post AffineScheme.Γ.rightOp ⋙ (Over.opEquivOpUnder _).functor

instance : (Over.AffineΓ S).IsEquivalence := inferInstanceAs <|
  (Over.post AffineScheme.Γ.rightOp ⋙ (Over.opEquivOpUnder _).functor).IsEquivalence

/-- The global-sections equivalence from affine morphisms over an affine base to rings under its
section ring. -/
def Γ : (Affine S)ᵒᵖ ⥤ Under Γ(S, ⊤) :=
  (toAffine S ⋙ Over.AffineΓ S).leftOp

instance : (Γ S).IsEquivalence :=
  inferInstanceAs <| (toAffine S ⋙ Over.AffineΓ S).leftOp.IsEquivalence

section

variable {T : Scheme.{u}} (f : T ⟶ S) [IsAffine T]

variable {S}

/-- Identify the section ring of an affine base change with the corresponding pushout under the
new base. -/
@[simps! hom_right]
def pullbackIsoPushout (X : (Affine S)ᵒᵖ) :
    (Γ T).obj (op ((Affine.pullback f).obj X.unop)) ≅
      Under.mk (pushout.inr ((Γ S).obj X).hom (f.app ⊤)) :=
  have hXHom : IsAffineHom X.unop.hom := X.unop.prop
  have hX : IsAffine X.unop.left :=
    @isAffine_of_isAffineHom X.unop.left S X.unop.hom hXHom inferInstance
  have : IsAffine ((Functor.id Scheme).obj X.unop.left) := hX
  have : IsAffine ((Functor.fromPUnit S).obj X.unop.right) :=
    inferInstanceAs (IsAffine S)
  Under.isoMk
    (ΓpullbackIsoPushout (X := X.unop.left) (Y := T) (S := S)
      (X.unop.hom : X.unop.left ⟶ S) f) <| by
        change (Limits.pullback.snd X.unop.hom f).appTop ≫
          (ΓpullbackIsoPushout X.unop.hom f).hom =
            pushout.inr X.unop.hom.appTop f.appTop
        exact app_snd_ΓpullbackIsoPushout_hom X.unop.hom f

/-- Global sections turn affine base change into the pushout functor on section rings. -/
def pullbackΓIso : (Affine.pullback f).op ⋙ Γ T ≅
    Γ S ⋙ Under.pushout (f.app ⊤) :=
  NatIso.ofComponents (pullbackIsoPushout f) <| by
    intro X Y g
    ext : 1
    have hXHom : IsAffineHom X.unop.hom := X.unop.prop
    have hYHom : IsAffineHom Y.unop.hom := Y.unop.prop
    have hX : IsAffine X.unop.left :=
      @isAffine_of_isAffineHom X.unop.left S X.unop.hom hXHom inferInstance
    have hY : IsAffine Y.unop.left :=
      @isAffine_of_isAffineHom Y.unop.left S Y.unop.hom hYHom inferInstance
    have : IsAffine ((Functor.id Scheme).obj X.unop.left) := hX
    have : IsAffine ((Functor.id Scheme).obj Y.unop.left) := hY
    have : IsAffine ((Functor.fromPUnit S).obj X.unop.right) :=
      inferInstanceAs (IsAffine S)
    have : IsAffine ((Functor.fromPUnit S).obj Y.unop.right) :=
      inferInstanceAs (IsAffine S)
    let eX : Γ(((Affine.pullback f).obj X.unop).left, ⊤) ≅
        pushout X.unop.hom.appTop f.appTop :=
      ΓpullbackIsoPushout X.unop.hom f
    let eY : Γ(((Affine.pullback f).obj Y.unop).left, ⊤) ≅
        pushout Y.unop.hom.appTop f.appTop :=
      ΓpullbackIsoPushout Y.unop.hom f
    let m : ((Affine.pullback f).obj Y.unop).left ⟶
        ((Affine.pullback f).obj X.unop).left :=
      ((Affine.pullback f).map g.unop).left
    let gm : Y.unop.left ⟶ X.unop.left := g.unop.left
    let pX : ((Affine.pullback f).obj X.unop).left ⟶ X.unop.left :=
      Limits.pullback.fst X.unop.hom f
    let pY : ((Affine.pullback f).obj Y.unop).left ⟶ Y.unop.left :=
      Limits.pullback.fst Y.unop.hom f
    let sX : ((Affine.pullback f).obj X.unop).left ⟶ T :=
      Limits.pullback.snd X.unop.hom f
    let sY : ((Affine.pullback f).obj Y.unop).left ⟶ T :=
      Limits.pullback.snd Y.unop.hom f
    have hgm : gm ≫ X.unop.hom = Y.unop.hom :=
      CategoryTheory.Over.w g.unop.hom
    have hpY : pY ≫ Y.unop.hom = sY ≫ f :=
      Limits.pullback.condition
    let l : ((Affine.pullback f).obj Y.unop).left ⟶
        ((Affine.pullback f).obj X.unop).left :=
      Limits.pullback.lift (pY ≫ gm) sY <| by
        exact (congrArg (fun z ↦ pY ≫ z) hgm).trans hpY
    have hm : m = l := rfl
    have hl_fst : l ≫ pX = pY ≫ gm :=
      Limits.pullback.lift_fst _ _ _
    have hl_snd : l ≫ sX = sY :=
      Limits.pullback.lift_snd _ _ _
    have hm_fst : m ≫ pX = pY ≫ gm :=
      (congrArg (fun z ↦ z ≫ pX) hm).trans hl_fst
    have hm_snd : m ≫ sX = sY :=
      (congrArg (fun z ↦ z ≫ sX) hm).trans hl_snd
    let mΓ := m.appTop
    let gmΓ := gm.appTop
    let pXΓ := pX.appTop
    let pYΓ := pY.appTop
    let sXΓ := sX.appTop
    let sYΓ := sY.appTop
    let iX := pushout.inl X.unop.hom.appTop f.appTop
    let iY := pushout.inl Y.unop.hom.appTop f.appTop
    let rX := pushout.inr X.unop.hom.appTop f.appTop
    let rY := pushout.inr Y.unop.hom.appTop f.appTop
    have hm_fstΓ : pXΓ ≫ mΓ = gmΓ ≫ pYΓ :=
      congrArg Scheme.Hom.appTop hm_fst
    have hm_sndΓ : sXΓ ≫ mΓ = sYΓ :=
      congrArg Scheme.Hom.appTop hm_snd
    have hgmΓ :
        X.unop.hom.appTop ≫ gmΓ = Y.unop.hom.appTop :=
      congrArg Scheme.Hom.appTop hgm
    have hinlX :
        iX ≫ eX.inv = pXΓ :=
      inl_ΓpullbackIsoPushout_inv X.unop.hom f
    have hinrX :
        rX ≫ eX.inv = sXΓ :=
      inr_ΓpullbackIsoPushout_inv X.unop.hom f
    have hfstY :
        pYΓ ≫ eY.hom = iY :=
      app_fst_ΓpullbackIsoPushout_hom Y.unop.hom f
    have hsndY :
        sYΓ ≫ eY.hom = rY :=
      app_snd_ΓpullbackIsoPushout_hom Y.unop.hom f
    have hcompat :
        X.unop.hom.appTop ≫ (gmΓ ≫ iY) = f.appTop ≫ rY := by
      calc
        X.unop.hom.appTop ≫ (gmΓ ≫ iY) =
            (X.unop.hom.appTop ≫ gmΓ) ≫ iY :=
          (Category.assoc _ _ _).symm
        _ = Y.unop.hom.appTop ≫ iY :=
          congrArg (fun z ↦ z ≫ iY) hgmΓ
        _ = f.appTop ≫ rY := pushout.condition
    have hinlDesc :
        iX ≫ pushout.desc (gmΓ ≫ iY) rY hcompat = gmΓ ≫ iY :=
      pushout.inl_desc _ _ _
    have hinrDesc :
        rX ≫ pushout.desc (gmΓ ≫ iY) rY hcompat = rY :=
      pushout.inr_desc _ _ _
    change mΓ ≫ eY.hom =
      eX.hom ≫
        pushout.desc (gmΓ ≫ iY) rY hcompat
    apply (cancel_epi eX.inv).1
    rw [eX.inv_hom_id_assoc]
    apply pushout.hom_ext
    · exact calc
        iX ≫ eX.inv ≫ mΓ ≫ eY.hom =
            (iX ≫ eX.inv) ≫ (mΓ ≫ eY.hom) :=
          (Category.assoc _ _ _).symm
        _ = pXΓ ≫ (mΓ ≫ eY.hom) :=
          congrArg (fun z ↦ z ≫ (mΓ ≫ eY.hom)) hinlX
        _ = (pXΓ ≫ mΓ) ≫ eY.hom :=
          (Category.assoc _ _ _).symm
        _ = (gmΓ ≫ pYΓ) ≫ eY.hom :=
          congrArg (fun z ↦ z ≫ eY.hom) hm_fstΓ
        _ = gmΓ ≫ (pYΓ ≫ eY.hom) :=
          Category.assoc _ _ _
        _ = gmΓ ≫ iY :=
          congrArg (fun z ↦ gmΓ ≫ z) hfstY
        _ = iX ≫ pushout.desc (gmΓ ≫ iY) rY hcompat :=
          hinlDesc.symm
    · exact calc
        rX ≫ eX.inv ≫ mΓ ≫ eY.hom =
            (rX ≫ eX.inv) ≫ (mΓ ≫ eY.hom) :=
          (Category.assoc _ _ _).symm
        _ = sXΓ ≫ (mΓ ≫ eY.hom) :=
          congrArg (fun z ↦ z ≫ (mΓ ≫ eY.hom)) hinrX
        _ = (sXΓ ≫ mΓ) ≫ eY.hom :=
          (Category.assoc _ _ _).symm
        _ = sYΓ ≫ eY.hom :=
          congrArg (fun z ↦ z ≫ eY.hom) hm_sndΓ
        _ = rY := hsndY
        _ = rX ≫ pushout.desc (gmΓ ≫ iY) rY hcompat :=
          hinrDesc.symm

end

variable {J : Type t} [Category J] [UnivLE.{t, u}]

instance : HasLimitsOfShape J (Affine S)ᵒᵖ :=
  Adjunction.hasLimitsOfShape_of_equivalence (Γ S)

instance hasColimitsOfShape_of_isAffine : HasColimitsOfShape J (Affine S) :=
  Limits.hasColimitsOfShape_of_hasLimitsOfShape_op

instance : HasColimitsOfShape J (MorphismProperty.Over @IsAffineHom ⊤ S) :=
  hasColimitsOfShape_of_isAffine _

variable (T : Scheme.{u}) [IsAffine T] (f : T ⟶ S)

instance [Flat f] : PreservesFiniteLimits (Under.pushout (f.app ⊤)) := by
  apply CommRingCat.Under.preservesFiniteLimits_of_flat (Scheme.Hom.app f ⊤)
  apply HasRingHomProperty.appTop (P := @Flat)
  infer_instance

instance preservesColimitsOfShapePullback
    [hpush : PreservesLimitsOfShape Jᵒᵖ (Under.pushout (f.app ⊤))] :
    PreservesColimitsOfShape J (Affine.pullback f) := by
  have hcomp : PreservesLimitsOfShape Jᵒᵖ (Γ S ⋙ Under.pushout (f.app ⊤)) :=
    CategoryTheory.Limits.comp_preservesLimitsOfShape (Γ S) (Under.pushout (f.app ⊤))
  let : PreservesLimitsOfShape Jᵒᵖ ((Affine.pullback f).op ⋙ Γ T) :=
    (preservesLimitsOfShape_iff_of_natIso (J := Jᵒᵖ) (pullbackΓIso f).symm).mp hcomp
  let : PreservesLimitsOfShape Jᵒᵖ (Affine.pullback f).op :=
    preservesLimitsOfShape_of_reflects_of_preserves _ (Γ T)
  exact preservesColimitsOfShape_of_op J (Affine.pullback f)

instance [Flat f] : PreservesFiniteColimits (Affine.pullback f) where
  preservesFiniteColimits _ := inferInstance

instance [Flat f] :
    PreservesFiniteColimits (MorphismProperty.Over.pullback @IsAffineHom ⊤ f) :=
  inferInstanceAs <| PreservesFiniteColimits (Affine.pullback f)

end AffineBase

section

variable {J : Type t} [UnivLE.{t, u}] [SmallCategory J] [FinCategory J] (D : J ⥤ Affine S)

instance (i) : IsAffine (S.directedAffineCover.X i) :=
  i.2

variable {S} in
/-- The local colimit cocones for a finite diagram of affine morphisms on the directed affine
cover. -/
def colimitGluingData : S.directedAffineCover.ColimitGluingData D where
  cocone _ := colimit.cocone _
  isColimit _ := colimit.isColimit _
  prop_trans := by
    intro i j hij
    have hhom : (homOfLE (leOfHom hij) : i ⟶ j) = hij :=
      homOfLE_leOfHom hij
    have h₁ :
        Scheme.Cover.trans S.directedAffineCover hij =
          Scheme.Cover.trans S.directedAffineCover
            (homOfLE (leOfHom hij) : i ⟶ j) :=
      congrArg
        (fun k : i ⟶ j ↦ Scheme.Cover.trans S.directedAffineCover k)
        hhom.symm
    have h₂ :
        Scheme.Cover.trans S.directedAffineCover
            (homOfLE (leOfHom hij) : i ⟶ j) =
          S.homOfLE (leOfHom hij) :=
      Scheme.directedAffineCover_trans (X := S) (leOfHom hij)
    have htrans :
        Scheme.Cover.trans S.directedAffineCover hij =
          S.homOfLE (leOfHom hij) :=
      Eq.trans h₁ h₂
    have hi : IsAffine (S.directedAffineCover.X i) := i.2
    have hj : IsAffine (S.directedAffineCover.X j) := j.2
    have hAffine : IsAffineHom (S.homOfLE (leOfHom hij)) :=
      @isAffineHom_of_isAffine
        (S.directedAffineCover.X i) (S.directedAffineCover.X j)
        (S.homOfLE (leOfHom hij)) hi hj
    exact htrans.symm ▸ hAffine

instance : HasColimit D where
  exists_colimit := by
    have hmap {U V : S.affineOpens} (hUV : U.1 ≤ V.1) :
        PreservesColimitsOfShape J (map (S.homOfLE hUV)) :=
      inferInstance
    have hpb {U V : S.affineOpens} (hUV : U.1 ≤ V.1) :
        PreservesColimitsOfShape J (Affine.pullback (S.homOfLE hUV)) :=
      inferInstance
    let _ : ∀ {i j : S.directedAffineCover.I₀} (hij : i ⟶ j),
        PreservesColimitsOfShape J
          (MorphismProperty.Over.pullback
            (@IsAffineHom : MorphismProperty Scheme.{u}) ⊤
            (S.directedAffineCover.trans hij)) :=
      fun {i j} hij ↦ by
        have hhom : (homOfLE (leOfHom hij) : i ⟶ j) = hij :=
          homOfLE_leOfHom hij
        have h₁ :
            Scheme.Cover.trans S.directedAffineCover hij =
              Scheme.Cover.trans S.directedAffineCover
                (homOfLE (leOfHom hij) : i ⟶ j) :=
          congrArg
            (fun k : i ⟶ j ↦ Scheme.Cover.trans S.directedAffineCover k)
            hhom.symm
        have h₂ :
            Scheme.Cover.trans S.directedAffineCover
                (homOfLE (leOfHom hij) : i ⟶ j) =
              S.homOfLE (leOfHom hij) :=
          Scheme.directedAffineCover_trans (X := S) (leOfHom hij)
        have htrans :
            Scheme.Cover.trans S.directedAffineCover hij =
              S.homOfLE (leOfHom hij) :=
          Eq.trans h₁ h₂
        have hraw : PreservesColimitsOfShape J
            (MorphismProperty.Over.pullback
              (@IsAffineHom : MorphismProperty Scheme.{u}) ⊤
              (S.homOfLE (leOfHom hij))) :=
          hpb (leOfHom hij)
        exact htrans.symm ▸ hraw
    use (colimitGluingData D).gluedCocone
    exact (colimitGluingData D).isColimitGluedCocone

end

instance : HasFiniteColimits (Affine S) where
  out J _ _ := { }

instance {U : Scheme.{u}} (f : U ⟶ S) [IsOpenImmersion f] [IsAffine U] :
    PreservesFiniteColimits (Affine.pullback f) := by
  wlog h : ∃ (V : S.Opens) (h : U = V), IsAffineOpen V ∧ h ▸ f = V.ι
  · let V : S.Opens := f.opensRange
    have _ : IsAffineOpen V := isAffineOpen_opensRange f
    let e : U ≅ V := f.isoOpensRange
    have heq : f = e.hom ≫ V.ι := by simp [e, V]
    rw [heq]
    let iso := MorphismProperty.Over.pullbackComp
      (P := @IsAffineHom)
      (Q := ⊤) e.hom V.ι
    constructor
    intro J _ _
    let eq : Affine U ≌ Affine V := MorphismProperty.Over.pullbackIso _ _ e
    have heq : Affine.pullback e.hom = eq.inverse := rfl
    let recurse := this
    let : PreservesColimitsOfShape J (Affine.pullback e.hom) := by
      rw [heq]
      infer_instance
    let : IsAffine V := ‹_›
    let : PreservesFiniteColimits (Affine.pullback V.ι) :=
      recurse _ _ ⟨_, rfl, isAffineOpen_opensRange f, rfl⟩
    let : PreservesColimitsOfShape J (Affine.pullback V.ι) := inferInstance
    have hcomp : PreservesColimitsOfShape J
        (Affine.pullback V.ι ⋙ Affine.pullback e.hom) :=
      CategoryTheory.Limits.comp_preservesColimitsOfShape
        (Affine.pullback V.ι) (Affine.pullback e.hom)
    exact (preservesColimitsOfShape_iff_of_natIso iso.symm).mp hcomp
  obtain ⟨V, rfl, hV, rfl⟩ := h
  constructor
  intro J _ _
  constructor
  intro D
  have hmap {U V : S.affineOpens} (hUV : U.1 ≤ V.1) :
      PreservesColimitsOfShape J (map (S.homOfLE hUV)) :=
    inferInstance
  have hpb {U V : S.affineOpens} (hUV : U.1 ≤ V.1) :
      PreservesColimitsOfShape J (Affine.pullback (S.homOfLE hUV)) :=
    inferInstance
  let _ : ∀ {i j : S.directedAffineCover.I₀} (hij : i ⟶ j),
      PreservesColimitsOfShape J
        (MorphismProperty.Over.pullback
          (@IsAffineHom : MorphismProperty Scheme.{u}) ⊤
          (S.directedAffineCover.trans hij)) :=
    fun {i j} hij ↦ by
      have hhom : (homOfLE (leOfHom hij) : i ⟶ j) = hij :=
        homOfLE_leOfHom hij
      have h₁ :
          Scheme.Cover.trans S.directedAffineCover hij =
            Scheme.Cover.trans S.directedAffineCover
              (homOfLE (leOfHom hij) : i ⟶ j) :=
        congrArg
          (fun k : i ⟶ j ↦ Scheme.Cover.trans S.directedAffineCover k)
          hhom.symm
      have h₂ :
          Scheme.Cover.trans S.directedAffineCover
              (homOfLE (leOfHom hij) : i ⟶ j) =
            S.homOfLE (leOfHom hij) :=
        Scheme.directedAffineCover_trans (X := S) (leOfHom hij)
      have htrans :
          Scheme.Cover.trans S.directedAffineCover hij =
            S.homOfLE (leOfHom hij) :=
        Eq.trans h₁ h₂
      have hraw : PreservesColimitsOfShape J
          (MorphismProperty.Over.pullback
            (@IsAffineHom : MorphismProperty Scheme.{u}) ⊤
            (S.homOfLE (leOfHom hij))) :=
        hpb (leOfHom hij)
      exact htrans.symm ▸ hraw
  change PreservesColimit D
    (MorphismProperty.Over.pullback
      (@IsAffineHom : MorphismProperty Scheme.{u}) ⊤ V.ι)
  have hc := (colimitGluingData D).isColimitGluedCocone
  apply CategoryTheory.Limits.preservesColimit_of_preserves_colimit_cocone hc
  let iso := (colimitGluingData D).mapCoconePullback D ⟨V, hV⟩
  have hsource :
      @IsColimit J _
        (MorphismProperty.Over (@IsAffineHom : MorphismProperty Scheme.{u}) ⊤
          (S.directedAffineCover.X ⟨V, hV⟩))
        (MorphismProperty.Comma.instCategory
          (Functor.id Scheme) (Functor.fromPUnit (S.directedAffineCover.X ⟨V, hV⟩))
          (@IsAffineHom : MorphismProperty Scheme.{u}) ⊤ ⊤)
        (D ⋙ MorphismProperty.Over.pullback
          (@IsAffineHom : MorphismProperty Scheme.{u}) ⊤
          (S.directedAffineCover.f ⟨V, hV⟩))
        ((MorphismProperty.Over.pullback
          (@IsAffineHom : MorphismProperty Scheme.{u}) ⊤
          (S.directedAffineCover.f ⟨V, hV⟩)).mapCocone
            (colimitGluingData D).gluedCocone) :=
    ((colimitGluingData D).isColimit ⟨V, hV⟩).ofIsoColimit iso.symm
  have hX :
      S.directedAffineCover.X ⟨V, hV⟩ = (V : Scheme) :=
    Scheme.directedAffineCover_X (X := S) ⟨V, hV⟩
  cases hX
  have hf :
      S.directedAffineCover.f ⟨V, hV⟩ = V.ι :=
    Scheme.directedAffineCover_f (X := S) ⟨V, hV⟩
  cases hf
  exact hsource

end Affine

end AlgebraicGeometry
