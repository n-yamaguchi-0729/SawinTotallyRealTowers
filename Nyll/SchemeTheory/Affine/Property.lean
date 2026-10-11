/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/

/-
Based on pi1 source (comparison revision; exact copied commit unverified):
https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/FundamentalGroup/AffineAnd.lean
-/

module

public import Mathlib.Algebra.Category.Ring.Under.Property
public import Mathlib.AlgebraicGeometry.Morphisms.AffineAnd
public import Nyll.SchemeTheory.Affine.Over

/-!
# Limit properties of subcategories of `P.Over ⊤ X` for `P = affineAnd`
-/


@[expose] public section

universe u

open CategoryTheory Limits

namespace CategoryTheory.MorphismProperty

variable {A : Type*} [Category A]
  {B : Type*} [Category B] {T : Type*} [Category T] {L L₁ L₂ L₃ : A ⥤ T} {P : MorphismProperty T}
  {Q : MorphismProperty A} {W : MorphismProperty B} [Q.IsMultiplicative] [W.IsMultiplicative]
  {R R₁ R₂ R₃ : B ⥤ T}

variable (L)

variable {L} (R)

variable {C : Type*} [Category C] (P Q : MorphismProperty C) [Q.IsMultiplicative]

/-- Pushout in relative under categories commutes with a compatible change of objects by
isomorphisms. -/
noncomputable
def Under.congrPushoutIso [HasPushouts C] [P.IsStableUnderCobaseChange]
    [Q.IsStableUnderCobaseChange] [Q.RespectsIso]
    {X X' Y Y' : C} (f : X ⟶ Y) (f' : X' ⟶ Y') (eX : X ≅ X') (eY : Y ≅ Y')
    (h : f ≫ eY.hom = eX.hom ≫ f') :
    (Comma.mapLeftIso _ (Discrete.natIso fun _ ↦ eX)).functor ⋙ Under.pushout P Q f' ≅
      Under.pushout P Q f ⋙
        (Comma.mapLeftIso _ (Discrete.natIso fun _ ↦ eY)).functor :=
  have h_inv : f' ≫ eY.inv = eX.inv ≫ f := by
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
    exact h.symm
  have h_id (A : P.Under Q X) :
      (eX.inv ≫ A.hom) ≫ (Iso.refl ((𝟭 C).obj A.right)).hom =
        eX.inv ≫ A.hom := by
    simp only [Iso.refl_hom, Category.comp_id]
  NatIso.ofComponents
    (fun A ↦
      haveI : IsIso (Iso.refl ((𝟭 C).obj A.right)).hom := inferInstance
      haveI : IsIso eY.inv := inferInstance
      haveI : IsIso eX.inv := inferInstance
      let k := pushout.map (eX.inv ≫ A.hom) f' A.hom f
        (Iso.refl ((𝟭 C).obj A.right)).hom eY.inv eX.inv (h_id A) h_inv
      have hk : IsIso k := by
        dsimp only [k]
        exact CategoryTheory.Limits.pushout.map_isIso (eX.inv ≫ A.hom) f' A.hom f
          (Iso.refl ((𝟭 C).obj A.right)).hom eY.inv eX.inv (h_id A) h_inv
      Under.isoMk
      (@asIso C _ _ _ k hk)
      (by
        change pushout.inr (eX.inv ≫ A.hom) f' ≫ k =
          eY.inv ≫ pushout.inr A.hom f
        dsimp only [k, pushout.map]
        apply pushout.inr_desc)) <|
    fun {A B} g ↦ by
      ext
      let a : X ⟶ A.right := A.hom
      let b : X ⟶ B.right := B.hom
      let gr : A.right ⟶ B.right := g.right
      have hgr : a ≫ gr = b := by
        change A.hom ≫ g.right = B.hom
        exact Under.w g
      have ha_id :
          (eX.inv ≫ a) ≫ (Iso.refl ((𝟭 C).obj A.right)).hom =
            eX.inv ≫ a := by
        change
          (eX.inv ≫ A.hom) ≫ (Iso.refl ((𝟭 C).obj A.right)).hom =
            eX.inv ≫ A.hom
        exact h_id A
      have hb_id :
          (eX.inv ≫ b) ≫ (Iso.refl ((𝟭 C).obj B.right)).hom =
            eX.inv ≫ b := by
        change
          (eX.inv ≫ B.hom) ≫ (Iso.refl ((𝟭 C).obj B.right)).hom =
            eX.inv ≫ B.hom
        exact h_id B
      let s : Limits.pushout (eX.inv ≫ a) f' ⟶
          Limits.pushout (eX.inv ≫ b) f' :=
        pushout.desc
          (gr ≫ pushout.inl (eX.inv ≫ b) f')
          (pushout.inr (eX.inv ≫ b) f') (by
            calc
              (eX.inv ≫ a) ≫
                  (gr ≫ pushout.inl (eX.inv ≫ b) f') =
                  (eX.inv ≫ (a ≫ gr)) ≫
                    pushout.inl (eX.inv ≫ b) f' := by
                simp only [Category.assoc]
              _ = (eX.inv ≫ b) ≫
                    pushout.inl (eX.inv ≫ b) f' := by
                rw [hgr]
              _ = f' ≫ pushout.inr (eX.inv ≫ b) f' :=
                pushout.condition)
      let t : Limits.pushout a f ⟶ Limits.pushout b f :=
        pushout.desc
          (gr ≫ pushout.inl b f)
          (pushout.inr b f) (by
            calc
              a ≫ (gr ≫ pushout.inl b f) =
                  (a ≫ gr) ≫ pushout.inl b f := by
                simp only [Category.assoc]
              _ = b ≫ pushout.inl b f := by rw [hgr]
              _ = f ≫ pushout.inr b f := pushout.condition)
      let kA : Limits.pushout (eX.inv ≫ a) f' ⟶ Limits.pushout a f :=
        pushout.map (eX.inv ≫ a) f' a f
          (Iso.refl ((𝟭 C).obj A.right)).hom eY.inv eX.inv
          ha_id h_inv
      let kB : Limits.pushout (eX.inv ≫ b) f' ⟶ Limits.pushout b f :=
        pushout.map (eX.inv ≫ b) f' b f
          (Iso.refl ((𝟭 C).obj B.right)).hom eY.inv eX.inv
          hb_id h_inv
      change s ≫ kB = kA ≫ t
      have hs_inl :
          pushout.inl (eX.inv ≫ a) f' ≫ s =
            gr ≫ pushout.inl (eX.inv ≫ b) f' := by
        exact pushout.inl_desc _ _ _
      have hs_inr :
          pushout.inr (eX.inv ≫ a) f' ≫ s =
            pushout.inr (eX.inv ≫ b) f' := by
        exact pushout.inr_desc _ _ _
      have ht_inl :
          pushout.inl a f ≫ t =
            gr ≫ pushout.inl b f := by
        exact pushout.inl_desc _ _ _
      have ht_inr :
          pushout.inr a f ≫ t =
            pushout.inr b f := by
        exact pushout.inr_desc _ _ _
      have hkA_inl :
          pushout.inl (eX.inv ≫ a) f' ≫ kA =
            (Iso.refl ((𝟭 C).obj A.right)).hom ≫
              pushout.inl a f := by
        exact pushout.inl_desc _ _ _
      have hkA_inr :
          pushout.inr (eX.inv ≫ a) f' ≫ kA =
            eY.inv ≫ pushout.inr a f := by
        exact pushout.inr_desc _ _ _
      have hkB_inl :
          pushout.inl (eX.inv ≫ b) f' ≫ kB =
            (Iso.refl ((𝟭 C).obj B.right)).hom ≫
              pushout.inl b f := by
        exact pushout.inl_desc _ _ _
      have hkB_inr :
          pushout.inr (eX.inv ≫ b) f' ≫ kB =
            eY.inv ≫ pushout.inr b f := by
        exact pushout.inr_desc _ _ _
      have hkA_inl' :
          pushout.inl (eX.inv ≫ a) f' ≫ kA =
            pushout.inl a f := by
        simpa only [Iso.refl_hom, Category.id_comp] using hkA_inl
      have hkB_inl' :
          pushout.inl (eX.inv ≫ b) f' ≫ kB =
            pushout.inl b f := by
        simpa only [Iso.refl_hom, Category.id_comp] using hkB_inl
      apply pushout.hom_ext
      · calc
          pushout.inl (eX.inv ≫ a) f' ≫ (s ≫ kB) =
              (pushout.inl (eX.inv ≫ a) f' ≫ s) ≫ kB :=
            (Category.assoc _ _ _).symm
          _ = (gr ≫ pushout.inl (eX.inv ≫ b) f') ≫ kB := by
            rw [hs_inl]
          _ = gr ≫
              (pushout.inl (eX.inv ≫ b) f' ≫ kB) :=
            Category.assoc _ _ _
          _ = gr ≫ pushout.inl b f := by rw [hkB_inl']
          _ = pushout.inl a f ≫ t := ht_inl.symm
          _ = (pushout.inl (eX.inv ≫ a) f' ≫ kA) ≫ t := by
            rw [hkA_inl']
          _ = pushout.inl (eX.inv ≫ a) f' ≫ (kA ≫ t) :=
            Category.assoc _ _ _
      · calc
          pushout.inr (eX.inv ≫ a) f' ≫ (s ≫ kB) =
              (pushout.inr (eX.inv ≫ a) f' ≫ s) ≫ kB :=
            (Category.assoc _ _ _).symm
          _ = pushout.inr (eX.inv ≫ b) f' ≫ kB := by
            rw [hs_inr]
          _ = eY.inv ≫ pushout.inr b f := hkB_inr
          _ = eY.inv ≫ (pushout.inr a f ≫ t) := by
            rw [ht_inr]
          _ = (eY.inv ≫ pushout.inr a f) ≫ t :=
            (Category.assoc _ _ _).symm
          _ = (pushout.inr (eX.inv ≫ a) f' ≫ kA) ≫ t := by
            rw [hkA_inr]
          _ = pushout.inr (eX.inv ≫ a) f' ≫ (kA ≫ t) :=
            Category.assoc _ _ _

end CategoryTheory.MorphismProperty

namespace AlgebraicGeometry

variable {Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
variable (P : MorphismProperty Scheme.{u}) [HasAffineProperty P (affineAnd Q)]

namespace AffineAnd

open MorphismProperty

variable {X : Scheme.{u}}

local instance affineHomOverCategory (S : Scheme.{u}) :
    Category (MorphismProperty.Over
      (@IsAffineHom : MorphismProperty Scheme.{u})
      (⊤ : MorphismProperty Scheme.{u}) S) :=
  instCategoryAffine S

instance (f : P.Over ⊤ X) : IsAffineHom f.hom :=
  HasAffineProperty.affineAnd_le_isAffineHom P inferInstance _ f.2

/-- Forget the additional affine morphism property while retaining the morphism over the base. -/
def toAffine (X : Scheme.{u}) : P.Over ⊤ X ⥤ Affine X where
  obj f := ⟨f.toComma, inferInstance⟩
  map f := ⟨f.toCommaMorphism, trivial, trivial⟩

/-- The forgetful functor from affine morphisms with the given property is fully faithful. -/
def toAffineFullyFaithful (X : Scheme.{u}) : (toAffine P X).FullyFaithful where
  preimage f := ⟨f.toCommaMorphism, trivial, trivial⟩

instance : (toAffine P X).Faithful := (toAffineFullyFaithful P X).faithful
instance : (toAffine P X).Full := (toAffineFullyFaithful P X).full

variable [hPbc : P.IsStableUnderBaseChange]

variable (J : Type) [SmallCategory J] [FinCategory J]

lemma _root_.CommRingCat.Under.property_limit_of_hasFiniteProducts_of_hasEqualizers
    (hQi : RingHom.RespectsIso Q) (hQp : RingHom.HasFiniteProducts Q)
    (hQe : RingHom.HasEqualizers Q)
    {R : CommRingCat.{u}} (D : J ⥤ Under R) (h : ∀ j, Q (D.obj j).hom.hom) :
    Q (limit D).hom.hom := by
  have := CommRingCat.Under.hasFiniteLimits hQi hQp hQe
  let D' : J ⥤ (RingHom.toMorphismProperty Q).Under ⊤ R :=
    MorphismProperty.Comma.lift D h (by simp) (by simp)
  let A := limit D'
  have : CreatesFiniteLimits (Under.forget (RingHom.toMorphismProperty Q) ⊤ R) :=
    CommRingCat.Under.createsFiniteLimitsForget hQi hQp hQe R
  let e : (Under.forget _ _ R).obj A ≅ limit D :=
    preservesLimitIso (Under.forget (RingHom.toMorphismProperty Q) ⊤ R) D'
  have := CategoryTheory.Under.w e.hom
  let _ : IsIso e.hom.right := by
    change IsIso ((CategoryTheory.Under.forget R).map e.hom)
    exact Functor.map_isIso (CategoryTheory.Under.forget R) e.hom
  rw [← this, CommRingCat.hom_comp, hQi.cancel_right_isIso]
  exact A.prop

/-- The forgetful functor creates finite colimits when the ring-hom property is stable under the
required finite limits. -/
@[implicit_reducible]
noncomputable
def createsFiniteColimits (hQi : RingHom.RespectsIso Q) (hQp : RingHom.HasFiniteProducts Q)
    (hQe : RingHom.HasEqualizers Q) :
    CreatesFiniteColimits (toAffine P X) := by
  constructor
  intro J _ _
  constructor
  intro D
  let D' : J ⥤ Affine X := D ⋙ toAffine P X
  letI hD' : HasColimit D' := inferInstance
  let A : Affine X := colimit D'
  have hA : P A.hom := by
    rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := P) _ (iSup_affineOpens_eq_top _)]
    dsimp
    intro U
    simp only [morphismRestrict]
    rw [P.cancel_left_of_respectsIso]
    change P <| ((Affine.pullback U.1.ι).obj A).hom
    let i : (Affine.pullback U.1.ι).obj A ≅
        colimit (D' ⋙ Affine.pullback U.1.ι) :=
      preservesColimitIso (Affine.pullback U.1.ι) D'
    let forgetAffine : Affine (U.1 : Scheme) ⥤
        CategoryTheory.Over (U.1 : Scheme) :=
      { obj := fun B ↦ CategoryTheory.Over.mk B.hom
        map := fun g ↦ CategoryTheory.Over.homMk g.left
          (MorphismProperty.Over.w g)
        map_id := by
          intro B
          ext
          rfl
        map_comp := by
          intro B C E g k
          ext
          rfl }
    let iOver : forgetAffine.obj ((Affine.pullback U.1.ι).obj A) ≅
        forgetAffine.obj (colimit (D' ⋙ Affine.pullback U.1.ι)) :=
      forgetAffine.mapIso i
    erw [P.over_iso_iff iOver]
    let i₂ : (Affine.Γ U.1).rightOp.obj (colimit (D' ⋙ Affine.pullback U.1.ι)) ≅
        colimit (D' ⋙ Affine.pullback U.1.ι ⋙ (Affine.Γ U.1).rightOp) :=
      preservesColimitIso (Affine.Γ U.1).rightOp (D' ⋙ Affine.pullback U.1.ι)
    let i₃ : ((Affine.Γ U.1).rightOp.obj (colimit (D' ⋙ Affine.pullback U.1.ι))).unop ≅
        (colimit (D' ⋙ Affine.pullback U.1.ι ⋙ (Affine.Γ U.1).rightOp)).unop :=
      i₂.symm.unop
    let i₄ : ((Affine.Γ U.1).rightOp.obj (colimit (D' ⋙ Affine.pullback U.1.ι))).unop ≅
        limit (D' ⋙ Affine.pullback U.1.ι ⋙ (Affine.Γ U.1).rightOp).leftOp :=
      i₃ ≪≫ (limitLeftOpIsoUnopColimit
        (D' ⋙ Affine.pullback U.1.ι ⋙ (Affine.Γ ↑↑U).rightOp)).symm
    let _ : IsIso i₄.inv.right := by
      change IsIso ((CategoryTheory.Under.forget _).map i₄.inv)
      exact Functor.map_isIso _ i₄.inv
    rw [HasAffineProperty.iff_of_isAffine (P := P)]
    simp only [affineAnd_apply]
    constructor
    · change IsAffine (colimit (D' ⋙ Affine.pullback U.1.ι)).left
      exact @isAffine_of_isAffineHom
        (colimit (D' ⋙ Affine.pullback U.1.ι)).left (U.1 : Scheme)
        (colimit (D' ⋙ Affine.pullback U.1.ι)).hom
        (colimit (D' ⋙ Affine.pullback U.1.ι)).prop inferInstance
    have heq : (colimit (D' ⋙ Affine.pullback U.1.ι)).hom.appTop =
        ((Affine.Γ U.1).rightOp.obj (colimit (D' ⋙ Affine.pullback U.1.ι))).unop.hom := rfl
    change Q ((colimit (D' ⋙ Affine.pullback U.1.ι)).hom.appTop).hom
    have hlimit :
        Q (limit (D' ⋙ Affine.pullback U.1.ι ⋙
          (Affine.Γ U.1).rightOp).leftOp).hom.hom := by
      apply _root_.CommRingCat.Under.property_limit_of_hasFiniteProducts_of_hasEqualizers
      · exact hQi
      · exact hQp
      · exact hQe
      · intro ⟨j⟩
        have h :
            P (pullback.snd (D'.obj j).hom U.1.ι) :=
          P.pullback_snd _ _ (D.obj j).prop
        rw [HasAffineProperty.iff_of_isAffine (P := P)] at h
        exact h.2
    have hcomp :
        Q (i₄.inv.right.hom.comp
          (limit (D' ⋙ Affine.pullback U.1.ι ⋙
            (Affine.Γ U.1).rightOp).leftOp).hom.hom) :=
      (hQi.cancel_right_isIso
        (limit (D' ⋙ Affine.pullback U.1.ι ⋙
          (Affine.Γ U.1).rightOp).leftOp).hom i₄.inv.right).2 hlimit
    have hi₄w :
        ((Affine.Γ U.1).rightOp.obj
          (colimit (D' ⋙ Affine.pullback U.1.ι))).unop.hom.hom =
          i₄.inv.right.hom.comp
            (limit (D' ⋙ Affine.pullback U.1.ι ⋙
              (Affine.Γ U.1).rightOp).leftOp).hom.hom := by
      rw [← CommRingCat.hom_comp]
      exact congrArg (fun k ↦ k.hom) (CategoryTheory.Under.w i₄.inv).symm
    have htarget :
        ((colimit (D' ⋙ Affine.pullback U.1.ι)).hom.appTop).hom =
          i₄.inv.right.hom.comp
            (limit (D' ⋙ Affine.pullback U.1.ι ⋙
              (Affine.Γ U.1).rightOp).leftOp).hom.hom :=
      (congrArg (fun k ↦ k.hom) heq).trans hi₄w
    rw [htarget]
    exact hcomp
  exact CategoryTheory.createsColimitOfFullyFaithfulOfIso
    ⟨A.toComma, hA⟩ (eqToIso rfl)

include hPbc in
lemma hasFiniteColimits (hQi : RingHom.RespectsIso Q) (hQp : RingHom.HasFiniteProducts Q)
    (hQe : RingHom.HasEqualizers Q) :
    HasFiniteColimits (P.Over ⊤ X) := by
  let _ : P.IsStableUnderBaseChange := hPbc
  constructor
  intro J _ _
  constructor
  intro D
  have := createsFiniteColimits (X := X) P hQi hQp hQe
  apply CategoryTheory.hasColimit_of_created D (toAffine P X)

include hPbc in
lemma preservesFiniteColimits_toAffine (hQi : RingHom.RespectsIso Q)
    (hQp : RingHom.HasFiniteProducts Q) (hQe : RingHom.HasEqualizers Q) :
    PreservesFiniteColimits (toAffine P X) := by
  have := hasFiniteColimits (X := X) P hQi hQp hQe
  have := createsFiniteColimits (X := X) P hQi hQp hQe
  infer_instance

theorem preservesFiniteLimits_pullback
    [P.IsStableUnderComposition] [P.ContainsIdentities]
    [P.HasOfPostcompProperty P] {Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits (MorphismProperty.Over.pullback P ⊤ f) := by
  let _ : P.IsMultiplicative := {}
  infer_instance

/-- Global sections of affine morphisms with the given property lie in the corresponding
relative under category of rings. -/
@[simps! obj_hom]
def ΓProp (hQi : RingHom.RespectsIso Q) (S : Scheme.{u}) [IsAffine S] :
    (P.Over ⊤ S)ᵒᵖ ⥤ (RingHom.toMorphismProperty Q).Under ⊤ Γ(S, ⊤) :=
  MorphismProperty.Comma.lift
    ((MorphismProperty.Over.forget P ⊤ S).op ⋙ AlgebraicGeometry.Over.Γ S)
    (fun X ↦ by
      change Q (X.unop.hom.appTop).hom
      have hX : targetAffineLocally (affineAnd Q) X.unop.hom := by
        rw [← HasAffineProperty.eq_targetAffineLocally P]
        exact X.unop.prop
      rw [targetAffineLocally_affineAnd_iff hQi] at hX
      exact (hX ⊤ (isAffineOpen_top S)).2)
    (fun _ ↦ trivial) (fun _ ↦ trivial)

omit [P.IsStableUnderBaseChange] in
-- `simps` generates this with `appLE` on the RHS
@[simp]
lemma ΓProp_map_right (hQi : RingHom.RespectsIso Q) (S : Scheme.{u}) [IsAffine S]
    {X Y : (P.Over ⊤ S)ᵒᵖ} (f : X ⟶ Y) :
    ((ΓProp P hQi S).map f).right = f.unop.left.appTop := rfl

lemma _root_.AlgebraicGeometry.Scheme.Hom.appTop_bijective_of_isAffine
      {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] :
    Function.Bijective (fun (f : X ⟶ Y) ↦ f.appTop) := by
  refine ⟨fun f g (hfg : f.appTop = g.appTop) ↦ ?_, fun f ↦ ?_⟩
  · have (f : X ⟶ Y) : f = X.isoSpec.hom ≫ Spec.map f.appTop ≫ Y.isoSpec.inv := by
      simp [Scheme.isoSpec_hom_naturality_assoc]
    rw [this f, this g, hfg]
  · let g : X ⟶ Spec Γ(Y, ⊤) :=
      (ΓSpec.adjunction.homEquiv X (Opposite.op Γ(Y, ⊤))) f.op
    use g ≫ Y.isoSpec.inv
    have hg : g.appTop = (Scheme.ΓSpecIso Γ(Y, ⊤)).hom ≫ f :=
      ΓSpec_adjunction_homEquiv_eq f
    have hY :
        Y.isoSpec.inv.appTop ≫ (Scheme.ΓSpecIso Γ(Y, ⊤)).hom = 𝟙 _ := by
      rw [← Scheme.toSpecΓ_appTop, ← Scheme.Hom.comp_appTop]
      simp
    calc
      (g ≫ Y.isoSpec.inv).appTop = Y.isoSpec.inv.appTop ≫ g.appTop :=
        Scheme.Hom.comp_appTop _ _
      _ = Y.isoSpec.inv.appTop ≫
          ((Scheme.ΓSpecIso Γ(Y, ⊤)).hom ≫ f) :=
        congrArg (fun k ↦ Y.isoSpec.inv.appTop ≫ k) hg
      _ = (Y.isoSpec.inv.appTop ≫
          (Scheme.ΓSpecIso Γ(Y, ⊤)).hom) ≫ f :=
        (Category.assoc _ _ _).symm
      _ = 𝟙 _ ≫ f := congrArg (fun k ↦ k ≫ f) hY
      _ = f := Category.id_comp _

omit [P.IsStableUnderBaseChange] in
lemma faithful_ΓProp (hQi : RingHom.RespectsIso Q) {S : Scheme.{u}} [IsAffine S] :
    (ΓProp P hQi S).Faithful where
  map_injective := by
    intro ⟨X⟩ ⟨Y⟩ ⟨f⟩ ⟨g⟩ hfg
    let hXHom : IsAffineHom X.hom :=
      HasAffineProperty.affineAnd_le_isAffineHom P inferInstance _ X.prop
    let hYHom : IsAffineHom Y.hom :=
      HasAffineProperty.affineAnd_le_isAffineHom P inferInstance _ Y.prop
    let _ : IsAffine X.left :=
      @isAffine_of_isAffineHom X.left S X.hom hXHom inferInstance
    let _ : IsAffine Y.left :=
      @isAffine_of_isAffineHom Y.left S Y.hom hYHom inferInstance
    have : f = g := by
      ext : 1
      apply AlgebraicGeometry.Scheme.Hom.appTop_bijective_of_isAffine.injective
      change ((ΓProp P hQi S).map (Opposite.op f)).right =
        ((ΓProp P hQi S).map (Opposite.op g)).right
      exact congrArg (fun k ↦ k.right) hfg
    rw [this]

omit [P.IsStableUnderBaseChange] in
lemma full_ΓProp (hQi : RingHom.RespectsIso Q) {S : Scheme.{u}} [IsAffine S] :
    (ΓProp P hQi S).Full where
  map_surjective := by
    intro ⟨X⟩ ⟨Y⟩ f
    let hXHom : IsAffineHom X.hom :=
      HasAffineProperty.affineAnd_le_isAffineHom P inferInstance _ X.prop
    let hYHom : IsAffineHom Y.hom :=
      HasAffineProperty.affineAnd_le_isAffineHom P inferInstance _ Y.prop
    let _ : IsAffine X.left :=
      @isAffine_of_isAffineHom X.left S X.hom hXHom inferInstance
    let _ : IsAffine Y.left :=
      @isAffine_of_isAffineHom Y.left S Y.hom hYHom inferInstance
    let _ : IsAffine ((Functor.fromPUnit S).obj X.right) :=
      inferInstanceAs (IsAffine S)
    let _ : IsAffine ((Functor.fromPUnit S).obj Y.right) :=
      inferInstanceAs (IsAffine S)
    let φ : Γ(X.left, ⊤) ⟶ Γ(Y.left, ⊤) := f.right
    obtain ⟨f', h⟩ :=
      AlgebraicGeometry.Scheme.Hom.appTop_bijective_of_isAffine.surjective φ
    have hw : X.hom.appTop ≫ φ = Y.hom.appTop := by
      change X.hom.appTop ≫ f.right = Y.hom.appTop
      ext s
      exact ConcreteCategory.congr_hom (MorphismProperty.Under.w f) s
    let g : Y ⟶ X := MorphismProperty.Over.homMk f' <| by
      apply AlgebraicGeometry.Scheme.Hom.appTop_bijective_of_isAffine.injective
      calc
        (f' ≫ X.hom).appTop = X.hom.appTop ≫ f'.appTop :=
          Scheme.Hom.comp_appTop _ _
        _ = X.hom.appTop ≫ φ :=
          congrArg (fun k ↦ X.hom.appTop ≫ k) h
        _ = Y.hom.appTop := hw
    use g.op
    ext : 1
    change f'.appTop = φ
    exact h

omit [P.IsStableUnderBaseChange] in
lemma essSurj_ΓProp (hQi : RingHom.RespectsIso Q) {S : Scheme.{u}} [IsAffine S] :
    (ΓProp P hQi S).EssSurj where
  mem_essImage R := by
    let X : P.Over ⊤ S := MorphismProperty.Over.mk ⊤ (Spec.map R.hom ≫ S.isoSpec.inv) <| by
      rw [P.cancel_right_of_respectsIso, HasAffineProperty.SpecMap_iff_of_affineAnd (P := P) _ hQi]
      · exact R.prop
      · infer_instance
    refine ⟨⟨X⟩, ⟨Under.isoMk (Scheme.ΓSpecIso _) ?_⟩⟩
    change (Spec.map R.hom ≫ S.isoSpec.inv).appTop ≫ (Scheme.ΓSpecIso R.right).hom =
      R.hom
    let a : Γ(S, ⊤) ⟶ Γ(Spec Γ(S, ⊤), ⊤) :=
      S.isoSpec.inv.appTop
    let b : Γ(Spec Γ(S, ⊤), ⊤) ⟶ Γ(Spec R.right, ⊤) :=
      (Spec.map R.hom).appTop
    let c : Γ(Spec R.right, ⊤) ⟶ R.right :=
      (Scheme.ΓSpecIso R.right).hom
    let d : Γ(Spec Γ(S, ⊤), ⊤) ⟶ Γ(S, ⊤) :=
      (Scheme.ΓSpecIso Γ(S, ⊤)).hom
    let r : Γ(S, ⊤) ⟶ R.right := R.hom
    have hS : a ≫ d = 𝟙 _ := by
      change S.isoSpec.inv.appTop ≫ (Scheme.ΓSpecIso Γ(S, ⊤)).hom = 𝟙 _
      rw [← Scheme.toSpecΓ_appTop, ← Scheme.Hom.comp_appTop]
      simp
    have hcomp :
        (Spec.map R.hom ≫ S.isoSpec.inv).appTop = a ≫ b :=
      Scheme.Hom.comp_appTop _ _
    have hnat : b ≫ c = d ≫ r :=
      Scheme.ΓSpecIso_naturality R.hom
    calc
      (Spec.map R.hom ≫ S.isoSpec.inv).appTop ≫ c =
          (a ≫ b) ≫ c :=
        congrArg (fun k ↦ k ≫ c) hcomp
      _ = a ≫ (b ≫ c) :=
        Category.assoc _ _ _
      _ = a ≫ (d ≫ r) :=
        congrArg (fun k ↦ a ≫ k) hnat
      _ = (a ≫ d) ≫ r :=
        (Category.assoc _ _ _).symm
      _ = 𝟙 _ ≫ r :=
        congrArg (fun k ↦ k ≫ r) hS
      _ = r := Category.id_comp _

omit [P.IsStableUnderBaseChange] in
lemma isEquivalence_ΓProp (hQi : RingHom.RespectsIso Q) {S : Scheme.{u}} [IsAffine S] :
    (ΓProp P hQi S).IsEquivalence where
  faithful := faithful_ΓProp ..
  full := full_ΓProp ..
  essSurj := essSurj_ΓProp ..

/-- Identify global sections after base change with pushout in the ring category carrying the
given property. -/
noncomputable
def pullbackΓPropIso [(RingHom.toMorphismProperty Q).IsStableUnderCobaseChange]
    (hQi : RingHom.RespectsIso Q) {S T : Scheme.{u}} [IsAffine S]
    [IsAffine T] (f : S ⟶ T) :
    (Over.pullback P ⊤ f).op ⋙ ΓProp P hQi S ≅
      ΓProp P hQi T ⋙ Under.pushout _ ⊤ f.appTop :=
  NatIso.ofComponents
    (fun X ↦
      haveI hXHom : IsAffineHom X.unop.hom :=
        HasAffineProperty.affineAnd_le_isAffineHom P inferInstance _ X.unop.prop
      haveI hX : IsAffine X.unop.left :=
        @isAffine_of_isAffineHom X.unop.left T X.unop.hom hXHom inferInstance
      haveI : IsAffine ((Functor.id Scheme).obj X.unop.left) := hX
      haveI : IsAffine ((Functor.fromPUnit T).obj X.unop.right) :=
        inferInstanceAs (IsAffine T)
      Under.isoMk (ΓpullbackIsoPushout (X := X.unop.left) (Y := S) (S := T)
        (X.unop.hom : X.unop.left ⟶ T) f) <| by
          change (pullback.snd X.unop.hom f).appTop ≫
            (ΓpullbackIsoPushout X.unop.hom f).hom =
              pushout.inr X.unop.hom.appTop f.appTop
          exact app_snd_ΓpullbackIsoPushout_hom X.unop.hom f) <| fun {X Y} g ↦ by
    ext : 1
    let hXHom : IsAffineHom X.unop.hom :=
      HasAffineProperty.affineAnd_le_isAffineHom P inferInstance _ X.unop.prop
    let hYHom : IsAffineHom Y.unop.hom :=
      HasAffineProperty.affineAnd_le_isAffineHom P inferInstance _ Y.unop.prop
    let hX : IsAffine X.unop.left :=
      @isAffine_of_isAffineHom X.unop.left T X.unop.hom hXHom inferInstance
    let hY : IsAffine Y.unop.left :=
      @isAffine_of_isAffineHom Y.unop.left T Y.unop.hom hYHom inferInstance
    let _ : IsAffine ((Functor.id Scheme).obj X.unop.left) := hX
    let _ : IsAffine ((Functor.id Scheme).obj Y.unop.left) := hY
    let _ : IsAffine ((Functor.fromPUnit T).obj X.unop.right) :=
      inferInstanceAs (IsAffine T)
    let _ : IsAffine ((Functor.fromPUnit T).obj Y.unop.right) :=
      inferInstanceAs (IsAffine T)
    let eX : Γ(((Over.pullback P ⊤ f).obj X.unop).left, ⊤) ≅
        pushout X.unop.hom.appTop f.appTop :=
      ΓpullbackIsoPushout X.unop.hom f
    let eY : Γ(((Over.pullback P ⊤ f).obj Y.unop).left, ⊤) ≅
        pushout Y.unop.hom.appTop f.appTop :=
      ΓpullbackIsoPushout Y.unop.hom f
    let m : ((Over.pullback P ⊤ f).obj Y.unop).left ⟶
        ((Over.pullback P ⊤ f).obj X.unop).left :=
      ((Over.pullback P ⊤ f).map g.unop).left
    let gm : Y.unop.left ⟶ X.unop.left := g.unop.left
    let pX : ((Over.pullback P ⊤ f).obj X.unop).left ⟶ X.unop.left :=
      pullback.fst X.unop.hom f
    let pY : ((Over.pullback P ⊤ f).obj Y.unop).left ⟶ Y.unop.left :=
      pullback.fst Y.unop.hom f
    let sX : ((Over.pullback P ⊤ f).obj X.unop).left ⟶ S :=
      pullback.snd X.unop.hom f
    let sY : ((Over.pullback P ⊤ f).obj Y.unop).left ⟶ S :=
      pullback.snd Y.unop.hom f
    have hgm : gm ≫ X.unop.hom = Y.unop.hom :=
      CategoryTheory.Over.w g.unop.hom
    have hpY : pY ≫ Y.unop.hom = sY ≫ f :=
      pullback.condition
    let l : ((Over.pullback P ⊤ f).obj Y.unop).left ⟶
        ((Over.pullback P ⊤ f).obj X.unop).left :=
      pullback.lift (pY ≫ gm) sY <| by
        exact (congrArg (fun z ↦ pY ≫ z) hgm).trans hpY
    have hm : m = l := rfl
    have hl_fst : l ≫ pX = pY ≫ gm :=
      pullback.lift_fst _ _ _
    have hl_snd : l ≫ sX = sY :=
      pullback.lift_snd _ _ _
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
    have hinlX : iX ≫ eX.inv = pXΓ :=
      inl_ΓpullbackIsoPushout_inv X.unop.hom f
    have hinrX : rX ≫ eX.inv = sXΓ :=
      inr_ΓpullbackIsoPushout_inv X.unop.hom f
    have hfstY : pYΓ ≫ eY.hom = iY :=
      app_fst_ΓpullbackIsoPushout_hom Y.unop.hom f
    have hsndY : sYΓ ≫ eY.hom = rY :=
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
      eX.hom ≫ pushout.desc (gmΓ ≫ iY) rY hcompat
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

/-- The equivalence between affine morphisms with the given property over a spectrum and the
corresponding rings under the base ring. -/
@[simps!]
noncomputable
def overSpecEquivUnder (hQi : RingHom.RespectsIso Q) (R : CommRingCat.{u}) :
    (P.Over ⊤ (Spec R))ᵒᵖ ≌ (RingHom.toMorphismProperty Q).Under ⊤ R :=
  have : (RingHom.toMorphismProperty Q).RespectsIso :=
    RingHom.toMorphismProperty_respectsIso_iff.mp hQi
  have : (ΓProp P hQi (Spec R)).IsEquivalence :=
    isEquivalence_ΓProp P hQi
  (ΓProp P hQi (Spec R)).asEquivalence.trans <|
    Comma.mapLeftIso _ (Discrete.natIso fun _ ↦ Scheme.ΓSpecIso R)

/-- The spectrum-under-category equivalence identifies pushout of rings with pullback of schemes. -/
noncomputable
def overSpecEquivUnderCompPushoutIso (hQi : RingHom.RespectsIso Q) {R S : CommRingCat.{u}}
    (f : R ⟶ S)
    [(RingHom.toMorphismProperty Q).IsStableUnderCobaseChange] :
    (overSpecEquivUnder P hQi R).functor ⋙
      (MorphismProperty.Under.pushout (RingHom.toMorphismProperty Q) ⊤ f) ≅
      (Over.pullback P ⊤ (Spec.map f)).op ⋙ (overSpecEquivUnder P hQi S).functor :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Under.congrPushoutIso _ ⊤
      (Spec.map f).appTop f (Scheme.ΓSpecIso R) (Scheme.ΓSpecIso S) (by simp)) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (pullbackΓPropIso P hQi _).symm _ ≪≫
      Functor.associator _ _ _

lemma preservesColimitsOfShape_pullback_iff_preservesLimitsOfShape (hQi : RingHom.RespectsIso Q)
    {R S : CommRingCat.{u}} (f : R ⟶ S) {J : Type*} [Category J]
    [(RingHom.toMorphismProperty Q).IsStableUnderCobaseChange] :
    PreservesColimitsOfShape J (Over.pullback P ⊤ (Spec.map f)) ↔
      PreservesLimitsOfShape Jᵒᵖ
        (MorphismProperty.Under.pushout (RingHom.toMorphismProperty Q) ⊤ f) := by
  let iso : (overSpecEquivUnder P hQi R).functor ⋙
      (Under.pushout (RingHom.toMorphismProperty Q) ⊤ f) ⋙
      (overSpecEquivUnder P hQi S).inverse ≅ (Over.pullback P ⊤ (Spec.map f)).op :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (overSpecEquivUnderCompPushoutIso P hQi f) _ ≪≫
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (overSpecEquivUnder P hQi S).unitIso.symm ≪≫
      Functor.rightUnitor _
  let iso' : ((overSpecEquivUnder P hQi R).functor.rightOp ⋙
      (Under.pushout (RingHom.toMorphismProperty Q) ⊤ f).op ⋙
      (overSpecEquivUnder P hQi S).inverse.leftOp).op ≅ (Over.pullback P ⊤ (Spec.map f)).op :=
    iso
  let foo := NatIso.removeOp iso'
  let e' : _ ≅ (overSpecEquivUnder P (Q := Q) hQi R).inverse.leftOp ⋙
      (overSpecEquivUnder P (Q := Q) hQi R).functor.rightOp :=
   (NatIso.op <| (overSpecEquivUnder P (Q := Q) hQi R).counitIso)
  let e'' : _ ≅ (overSpecEquivUnder P hQi S).inverse.leftOp ⋙
      (overSpecEquivUnder P hQi S).functor.rightOp :=
   (NatIso.op <| (overSpecEquivUnder P hQi S).counitIso)
  let iso2 : (Under.pushout (RingHom.toMorphismProperty Q) ⊤ f).op ≅
      (overSpecEquivUnder P hQi R).inverse.leftOp ⋙ Over.pullback P ⊤ (Spec.map f) ⋙
      (overSpecEquivUnder P hQi S).functor.rightOp :=
    (Functor.rightUnitor _).symm ≪≫
      Functor.isoWhiskerLeft _ e'' ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Functor.leftUnitor _).symm _ ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerRight e' _) _ ≪≫
      Functor.isoWhiskerRight (Functor.associator _ _ _) _ ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerLeft _ foo.symm) _ ≪≫ Functor.associator _ _ _
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · convert preservesLimitsOfShape_of_op _ _
    convert preservesColimitsOfShape_of_natIso iso2.symm
    exact preservesColimitsOfShape_of_equiv (opOpEquivalence J).symm _
  · convert preservesColimitsOfShape_of_op _ _
    exact preservesLimitsOfShape_of_natIso iso

instance preservesColimitsOfShape_pullback_of_toAffine {J : Type*} [Category J]
      {Y : Scheme.{u}} (f : X ⟶ Y)
      [PreservesColimitsOfShape J (toAffine P Y)]
      [PreservesColimitsOfShape J (Affine.pullback f)] :
    PreservesColimitsOfShape J (Over.pullback P ⊤ f) := by
  have heq : MorphismProperty.Over.pullback P ⊤ f ⋙ toAffine P X =
      toAffine P Y ⋙ Affine.pullback f :=
    rfl
  have : PreservesColimitsOfShape J (MorphismProperty.Over.pullback P ⊤ f ⋙ toAffine P X) := by
    rw [heq]
    infer_instance
  apply preservesColimitsOfShape_of_reflects_of_preserves
    (MorphismProperty.Over.pullback P ⊤ f) (toAffine P X)

section

/-- If `F` is naturally isomorphic to `F'` they induce isomorphic `colimit.post` maps. -/
noncomputable
def _root_.CategoryTheory.Limits.colimit.arrowMkPostIsoOfIso {J C D : Type*} [Category J]
    [Category C] [Category D] (K : J ⥤ C) (F F' : C ⥤ D)
    (e : F ≅ F') [HasColimit K] [HasColimit (K ⋙ F)] [HasColimit (K ⋙ F')] :
    CategoryTheory.Arrow.mk (colimit.post K F) ≅ CategoryTheory.Arrow.mk (colimit.post K F') :=
  Arrow.isoMk (HasColimit.isoOfNatIso <| Functor.isoWhiskerLeft K e) (e.app _)
    (by
      change (HasColimit.isoOfNatIso (Functor.isoWhiskerLeft K e)).hom ≫
        colimit.post K F' = colimit.post K F ≫ e.hom.app (colimit K)
      apply colimit.hom_ext
      intro j
      rw [← Category.assoc, HasColimit.ι_isoOfNatIso_hom]
      rw [Category.assoc, colimit.ι_post]
      rw [colimit.ι_post_assoc]
      exact (e.hom.naturality (colimit.ι K j)).symm)

end

section

variable (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]

lemma _root_.AlgebraicGeometry.IsLocalAtTarget.iff_of_openCover_of_over
    {X Y S : Scheme.{u}} [X.Over S] [Y.Over S]
    (f : X ⟶ Y) [f.IsOver S] (𝒰 : S.OpenCover) :
    P f ↔ ∀ i : 𝒰.I₀,
      P (pullback.map (X ↘ S) (𝒰.f i) (Y ↘ S) (𝒰.f i) f (𝟙 _) (𝟙 _) (by simp) (by simp)) := by
  let s : X ⟶ S := X ↘ S
  let t : Y ⟶ S := Y ↘ S
  have hover : f ≫ t = s := HomIsOver.comp_over
  let a (i : 𝒰.I₀) :
      pullback f (pullback.fst t (𝒰.f i)) ≅ pullback (f ≫ t) (𝒰.f i) :=
    pullbackRightPullbackFstIso t (𝒰.f i) f
  let c (i : 𝒰.I₀) : pullback (f ≫ t) (𝒰.f i) ≅ pullback s (𝒰.f i) :=
    pullback.congrHom hover rfl
  let m (i : 𝒰.I₀) : pullback s (𝒰.f i) ⟶ pullback t (𝒰.f i) :=
    pullback.map s (𝒰.f i) t (𝒰.f i) f (𝟙 _) (𝟙 _)
      (by simpa only [Category.comp_id] using hover.symm) (by simp)
  have heq (i : 𝒰.I₀) :
      pullback.snd f (pullback.fst t (𝒰.f i)) =
        (a i).hom ≫ (c i).hom ≫ m i := by
    let u : 𝒰.X i ⟶ S := 𝒰.f i
    change pullback.snd f (pullback.fst t u) =
      (a i).hom ≫ (c i).hom ≫ m i
    have hm_fst : m i ≫ pullback.fst t u = pullback.fst s u ≫ f := by
      dsimp only [m, pullback.map, u]
      rw [pullback.lift_fst]
    have hm_snd : m i ≫ pullback.snd t u = pullback.snd s u := by
      dsimp only [m, pullback.map, u]
      rw [pullback.lift_snd, Category.comp_id]
    have hc_fst : (c i).hom ≫ pullback.fst s u = pullback.fst (f ≫ t) u := by
      dsimp only [c, pullback.congrHom, pullback.map, u]
      rw [asIso_hom, pullback.lift_fst, Category.comp_id]
    have hc_snd : (c i).hom ≫ pullback.snd s u = pullback.snd (f ≫ t) u := by
      dsimp only [c, pullback.congrHom, pullback.map, u]
      rw [asIso_hom, pullback.lift_snd, Category.comp_id]
    have ha_fst : (a i).hom ≫ pullback.fst (f ≫ t) u =
        pullback.fst f (pullback.fst t u) :=
      pullbackRightPullbackFstIso_hom_fst t u f
    have ha_snd : (a i).hom ≫ pullback.snd (f ≫ t) u =
        pullback.snd f (pullback.fst t u) ≫ pullback.snd t u :=
      pullbackRightPullbackFstIso_hom_snd t u f
    apply pullback.hom_ext
    · calc
        pullback.snd f (pullback.fst t u) ≫ pullback.fst t u =
            pullback.fst f (pullback.fst t u) ≫ f :=
          pullback.condition.symm
        _ = ((a i).hom ≫ pullback.fst (f ≫ t) u) ≫ f :=
          congrArg (fun k ↦ k ≫ f) ha_fst.symm
        _ = (a i).hom ≫ (pullback.fst (f ≫ t) u ≫ f) :=
          Category.assoc _ _ _
        _ = (a i).hom ≫ (((c i).hom ≫ pullback.fst s u) ≫ f) :=
          congrArg (fun k ↦ (a i).hom ≫ (k ≫ f)) hc_fst.symm
        _ = (a i).hom ≫ ((c i).hom ≫ (pullback.fst s u ≫ f)) :=
          congrArg (fun k ↦ (a i).hom ≫ k) (Category.assoc _ _ _)
        _ = (a i).hom ≫ ((c i).hom ≫ (m i ≫ pullback.fst t u)) :=
          congrArg (fun k ↦ (a i).hom ≫ ((c i).hom ≫ k)) hm_fst.symm
        _ = ((a i).hom ≫ (c i).hom ≫ m i) ≫ pullback.fst t u := by
          simp only [Category.assoc]
    · calc
        pullback.snd f (pullback.fst t u) ≫ pullback.snd t u =
            (a i).hom ≫ pullback.snd (f ≫ t) u :=
          ha_snd.symm
        _ = (a i).hom ≫ ((c i).hom ≫ pullback.snd s u) :=
          congrArg (fun k ↦ (a i).hom ≫ k) hc_snd.symm
        _ = (a i).hom ≫ ((c i).hom ≫ (m i ≫ pullback.snd t u)) :=
          congrArg (fun k ↦ (a i).hom ≫ ((c i).hom ≫ k)) hm_snd.symm
        _ = ((a i).hom ≫ (c i).hom ≫ m i) ≫ pullback.snd t u := by
          simp only [Category.assoc]
  refine ⟨fun hf i ↦ ?_, fun H ↦ ?_⟩
  · let _ : IsOpenImmersion (pullback.fst t (𝒰.f i)) :=
      MorphismProperty.pullback_fst t (𝒰.f i) (𝒰.map_prop i)
    have hpb : P (pullback.snd f (pullback.fst t (𝒰.f i))) :=
      IsZariskiLocalAtTarget.of_isPullback (.of_hasPullback _ _) hf
    rw [heq i] at hpb
    let ha : IsIso (a i).hom := (a i).isIso_hom
    let hc : IsIso (c i).hom := (c i).isIso_hom
    exact (P.cancel_left_of_respectsIso (c i).hom (m i)).mp
      ((P.cancel_left_of_respectsIso (a i).hom ((c i).hom ≫ m i)).mp hpb)
  · rw [IsZariskiLocalAtTarget.iff_of_openCover (P := P) (𝒰.pullback₁ (Y ↘ S))]
    have hdirect : ∀ i : 𝒰.I₀,
        P (pullback.snd f (pullback.fst t (𝒰.f i))) := by
      intro i
      let ha : IsIso (a i).hom := (a i).isIso_hom
      let hc : IsIso (c i).hom := (c i).isIso_hom
      have hm : P (m i) := by
        simpa only [m] using H i
      have hcomp : P ((a i).hom ≫ (c i).hom ≫ m i) :=
        (P.cancel_left_of_respectsIso (a i).hom ((c i).hom ≫ m i)).2
          ((P.cancel_left_of_respectsIso (c i).hom (m i)).2 hm)
      rw [heq i]
      exact hcomp
    simpa only [Scheme.Cover.pullbackHom,
      Precoverage.ZeroHypercover.pullback₁, PreZeroHypercover.pullback₁, t] using hdirect

variable {W Q : MorphismProperty Scheme.{u}} [Q.IsMultiplicative]
variable [W.IsStableUnderBaseChange] [Q.IsStableUnderBaseChange]

variable {P} in
lemma _root_.AlgebraicGeometry.IsLocalAtTarget.left_iff_of_openCover
    {S : Scheme.{u}} {X Y : W.Over Q S} {f : X ⟶ Y} (𝒰 : S.OpenCover) :
    P f.left ↔ ∀ i : 𝒰.I₀,
      P ((MorphismProperty.Over.pullback W Q (𝒰.f i)).map f).left :=
  by
    let _ : Scheme.Hom.IsOver f.left S := ⟨by
      change f.left ≫ Y.hom = X.hom
      exact MorphismProperty.Over.w f⟩
    exact AlgebraicGeometry.IsLocalAtTarget.iff_of_openCover_of_over
      (P := P) (X := X.left) (Y := Y.left) (S := S) f.left 𝒰

end

nonrec theorem preservesFiniteColimits_pullback (hQi : RingHom.RespectsIso Q)
    (hQp : RingHom.HasFiniteProducts Q) (hQe : RingHom.HasEqualizers Q)
    [(RingHom.toMorphismProperty Q).IsStableUnderCobaseChange]
    [∀ (R S : CommRingCat.{u}) (f : R ⟶ S), PreservesFiniteLimits
      (Under.pushout (RingHom.toMorphismProperty Q) ⊤ f)]
    {Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteColimits (Over.pullback P ⊤ f) := by
  have (S : Scheme.{u}) : HasFiniteColimits (P.Over ⊤ S) := hasFiniteColimits P hQi hQp hQe
  constructor
  intro J _ _
  constructor
  intro D
  suffices h : IsIso (colimit.post D (MorphismProperty.Over.pullback P ⊤ f)).left by
    have : IsIso (colimit.post D (MorphismProperty.Over.pullback P ⊤ f)) := by
      convert isIso_of_reflects_iso _ (Over.forget P ⊤ X ⋙ Over.forget X)
      exact h
    apply preservesColimit_of_isIso_post
  change isomorphisms Scheme.{u} _
  wlog H : (∃ R, Y = Spec R) ∧ ∃ S, X = Spec S generalizing X Y D f
  · let 𝒰X : X.OpenCover :=
      (Scheme.OpenCover.affineRefinement (Y.affineCover.pullback₁ f)).openCover
    rw [IsLocalAtTarget.left_iff_of_openCover (P := isomorphisms Scheme) 𝒰X]
    intro i
    let uᵢ : Y.affineCover.X i.1 ⟶ Y := Y.affineCover.f i.1
    let _ : IsAffine (𝒰X.X i) := by
      dsimp only [𝒰X]
      exact Scheme.isAffine_affineOpenCover X
        (Scheme.OpenCover.affineRefinement (Y.affineCover.pullback₁ f)) i
    let _ : IsOpenImmersion (𝒰X.f i) := 𝒰X.map_prop i
    let _ : IsAffine (Y.affineCover.X i.1) :=
      Scheme.isAffine_affineCover Y i.1
    let _ : IsOpenImmersion uᵢ := by
      dsimp only [uᵢ]
      exact Y.affineCover.map_prop i.1
    let _ : PreservesFiniteColimits (toAffine P X) :=
      preservesFiniteColimits_toAffine P hQi hQp hQe
    let _ : PreservesFiniteColimits (toAffine P Y) :=
      preservesFiniteColimits_toAffine P hQi hQp hQe
    let _ : PreservesColimitsOfShape J (toAffine P X) := inferInstance
    let _ : PreservesColimitsOfShape J (toAffine P Y) := inferInstance
    let _ : PreservesFiniteColimits (Affine.pullback (𝒰X.f i)) := inferInstance
    let _ : PreservesColimitsOfShape J (Affine.pullback (𝒰X.f i)) := inferInstance
    let _ : PreservesColimitsOfShape J (Over.pullback P ⊤ (𝒰X.f i)) :=
      preservesColimitsOfShape_pullback_of_toAffine P (𝒰X.f i)
    let _ : PreservesFiniteColimits (Affine.pullback uᵢ) := inferInstance
    let _ : PreservesColimitsOfShape J (Affine.pullback uᵢ) := inferInstance
    let _ : PreservesColimitsOfShape J (Over.pullback P ⊤ uᵢ) :=
      preservesColimitsOfShape_pullback_of_toAffine P uᵢ
    let r : 𝒰X.X i ⟶ pullback f uᵢ :=
      (Scheme.OpenCover.fromAffineRefinement
        (Y.affineCover.pullback₁ f)).h₀ i
    let q₀ := colimit.post (D ⋙ Over.pullback P ⊤ f)
      (Over.pullback P ⊤ (𝒰X.f i))
    let _ : IsIso q₀ := by
      dsimp only [q₀]
      infer_instance
    let _ : IsIso q₀.left := by
      change IsIso ((Over.forget P ⊤ _ ⋙ Over.forget _).map q₀)
      exact Functor.map_isIso _ q₀
    rw [← MorphismProperty.cancel_left_of_respectsIso
      (MorphismProperty.isomorphisms Scheme) q₀.left]
    dsimp only [q₀]
    erw [← MorphismProperty.Comma.comp_left]
    simp only [colimit.post_post]
    have heq : 𝒰X.f i = r ≫ pullback.fst f uᵢ := by
      change 𝒰X.f i = r ≫ (Y.affineCover.pullback₁ f).f i.fst
      exact (Scheme.OpenCover.fromAffineRefinement (Y.affineCover.pullback₁ f)).w₀ i |>.symm
    let aux : 𝒰X.X i ⟶ Y.affineCover.X i.fst :=
      r ≫ pullback.snd f uᵢ
    have hpb : pullback.fst f uᵢ ≫ f = pullback.snd f uᵢ ≫ uᵢ :=
      pullback.condition
    have hbase : 𝒰X.f i ≫ f = aux ≫ uᵢ := by
      calc
        𝒰X.f i ≫ f =
            (r ≫ pullback.fst f uᵢ) ≫ f :=
          congrArg (fun k ↦ k ≫ f) heq
        _ = r ≫ (pullback.fst f uᵢ ≫ f) :=
          Category.assoc _ _ _
        _ = r ≫ (pullback.snd f uᵢ ≫ uᵢ) :=
          congrArg (fun k ↦ r ≫ k) hpb
        _ = (r ≫ pullback.snd f uᵢ) ≫ uᵢ :=
          (Category.assoc _ _ _).symm
        _ = aux ≫ uᵢ := rfl
    let natiso :
        Over.pullback P ⊤ f ⋙ Over.pullback P ⊤ (𝒰X.f i) ≅
          Over.pullback P ⊤ uᵢ ⋙
            MorphismProperty.Over.pullback P ⊤
              aux :=
              -- ((Scheme.OpenCover.fromAffineRefinement _).h₀ i ≫ pullback.snd f uᵢ) :=
      (MorphismProperty.Over.pullbackComp _ _).symm ≪≫
        MorphismProperty.Over.pullbackCongr hbase ≪≫
        (MorphismProperty.Over.pullbackComp _ _)
    let e := colimit.arrowMkPostIsoOfIso D _ _ natiso
    let p := colimit.post D
      (Over.pullback P ⊤ f ⋙ MorphismProperty.Over.pullback P ⊤ (𝒰X.f i))
    have hp : IsIso p := by
      let F := Over.pullback P ⊤ uᵢ
      let G := Over.pullback P ⊤ aux
      let q₁ := colimit.post (D ⋙ F) G
      let q₂ := G.map (colimit.post D F)
      let q := colimit.post D (F ⋙ G)
      have hq₁Left : isomorphisms Scheme q₁.left := by
        dsimp only [q₁, F, G]
        exact this _ ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩
      let _ :
          IsIso ((Over.forget P ⊤ _ ⋙ Over.forget _).map q₁) := by
        change IsIso q₁.left
        simpa only [isomorphisms.iff] using hq₁Left
      let hq₁ : IsIso q₁ := by
        exact isIso_of_reflects_iso q₁ (Over.forget P ⊤ _ ⋙ Over.forget _)
      let _ : IsIso (colimit.post D F) := by
        dsimp only [F]
        infer_instance
      let hq₂ : IsIso q₂ := by
        dsimp only [q₂]
        infer_instance
      have hq : q₁ ≫ q₂ = q := by
        exact colimit.post_post D F G
      have hqComp : IsIso (q₁ ≫ q₂) :=
        @IsIso.comp_isIso _ _ _ _ _ q₁ q₂ hq₁ hq₂
      let hqIso : IsIso q := hq ▸ hqComp
      change isomorphisms _ _
      apply ((isomorphisms _).arrow_mk_iso_iff e).2
      simp only [isomorphisms.iff]
      change IsIso q
      exact hqIso
    simp only [isomorphisms.iff]
    let forget := Over.forget P ⊤ (𝒰X.X i) ⋙ Over.forget (𝒰X.X i)
    let _ : IsIso p := hp
    change IsIso (forget.map p)
    exact Functor.map_isIso forget p
  obtain ⟨⟨R, rfl⟩, ⟨S, rfl⟩⟩ := H
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  have : PreservesColimitsOfShape J (MorphismProperty.Over.pullback P ⊤ (Spec.map φ)) := by
    rw [preservesColimitsOfShape_pullback_iff_preservesLimitsOfShape _ hQi]
    infer_instance
  simp only [isomorphisms.iff]
  infer_instance

end AffineAnd

end AlgebraicGeometry
