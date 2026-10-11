/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RingTheory.Etale.Finite
public import Mathlib.CategoryTheory.Opposites
public import Nyll.SchemeTheory.FiniteEtale.Basic

/-!
# Finite étale covers of an affine scheme

This file identifies finite étale covers of an affine scheme with finite étale algebras.
Under this identification, the contravariance of `Spec` accounts for the opposite category
on the scheme side.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory
open scoped TensorProduct

namespace CommAlgCat.FiniteEtale

/-- Finite étale algebras over `R` are the same as finite étale ring homomorphisms under
`R`. -/
def equivUnder (R : CommRingCat.{u}) :
    CommAlgCat.FiniteEtale.{u} R ≌
      CategoryTheory.MorphismProperty.Under
        (RingHom.toMorphismProperty RingHom.FiniteEtale) ⊤ R where
  functor.obj A :=
    ⟨(commAlgCatEquivUnder R).functor.obj A.obj, by
      change RingHom.FiniteEtale (algebraMap R A.obj)
      rw [RingHom.finiteEtale_algebraMap_iff]
      let : Module.Finite R A.obj := A.property.left
      let : Algebra.Etale R A.obj := A.property.right
      constructor⟩
  functor.map {A B} f :=
    ⟨(commAlgCatEquivUnder R).functor.map f.hom, trivial, trivial⟩
  inverse.obj A :=
    ⟨CommAlgCat.of R A.right, by
      let := A.hom.hom.toAlgebra
      let h : Algebra.FiniteEtale R A.right := A.2
      change Module.Finite R A.right ∧ Algebra.Etale R A.right
      exact ⟨h.toFinite, h.toEtale⟩⟩
  inverse.map {A B} f :=
    ObjectProperty.homMk (CommAlgCat.ofHom (CommRingCat.toAlgHom f.hom))
  unitIso := NatIso.ofComponents fun A ↦
    ObjectProperty.isoMk _
      (CommAlgCat.isoMk { toRingEquiv := .refl A.obj, commutes' _ := rfl })
  counitIso := .refl _

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- Under `equivUnder`, tensor-product base change is pushout of finite étale ring
homomorphisms. -/
def equivUnderInverseCompBaseChangeIso :
    (equivUnder (.of R)).inverse ⋙ CommAlgCat.FiniteEtale.baseChange R S ≅
      CategoryTheory.MorphismProperty.Under.pushout
          (RingHom.toMorphismProperty RingHom.FiniteEtale) ⊤
          (CommRingCat.ofHom (algebraMap R S)) ⋙
        (equivUnder (.of S)).inverse :=
  NatIso.ofComponents
    (fun A ↦ by
      letI : Algebra R A.right := A.hom.hom.toAlgebra
      let pushout := CategoryTheory.MorphismProperty.Under.pushout
        (RingHom.toMorphismProperty RingHom.FiniteEtale) ⊤
        (CommRingCat.ofHom (algebraMap R S))
      letI : Algebra S (pushout.obj A).right := (pushout.obj A).hom.hom.toAlgebra
      let e := CommRingCat.tensorProdObjIsoPushoutObj (.of S) A.toComma
      let eAlg : (S ⊗[R] A.right) ≃ₐ[S]
          (pushout.obj A).right := {
        __ := CommRingCat.toAlgHom e.hom
        toFun := e.hom.right
        invFun := e.inv.right
        left_inv x := by
          have hright : e.hom.right ≫ e.inv.right = 𝟙 _ := by
            change (e.hom ≫ e.inv).right = 𝟙 _
            rw [e.hom_inv_id]
            rfl
          exact ConcreteCategory.congr_hom hright x
        right_inv x := by
          have hright : e.inv.right ≫ e.hom.right = 𝟙 _ := by
            change (e.inv ≫ e.hom).right = 𝟙 _
            rw [e.inv_hom_id]
            rfl
          exact ConcreteCategory.congr_hom hright x
      }
      exact ObjectProperty.isoMk _ (CommAlgCat.isoMk eAlg)) <|
    fun {A B} f ↦ by
      apply ObjectProperty.hom_ext
      apply CommAlgCat.hom_ext
      apply AlgHom.ext
      intro x
      have h := congrArg (fun g ↦ g.right)
        ((CommRingCat.tensorProdIsoPushout (.of R) (.of S)).hom.naturality f.hom)
      exact ConcreteCategory.congr_hom h x

end CommAlgCat.FiniteEtale

namespace AlgebraicGeometry.FiniteEtale

local instance finiteEtaleOverCategoryAffine (X : Scheme.{u}) :
    Category (MorphismProperty.Over
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) ⊤ X) :=
  FiniteEtale.instCategory X

/-- Finite étale covers of `Spec R`, with arrows reversed, are equivalent to finite étale
`R`-algebras. -/
def affineEquivalence (R : CommRingCat.{u}) :
    (AlgebraicGeometry.FiniteEtale (AlgebraicGeometry.Spec R))ᵒᵖ ≌
      CommAlgCat.FiniteEtale.{u} R :=
  (AlgebraicGeometry.AffineAnd.overSpecEquivUnder (@AlgebraicGeometry.IsFiniteEtale :
      MorphismProperty AlgebraicGeometry.Scheme.{u})
      RingHom.FiniteEtale.respectsIso R).trans
    (CommAlgCat.FiniteEtale.equivUnder R).symm

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- Pulling back finite étale covers along `Spec S ⟶ Spec R` corresponds to tensor-product
base change of finite étale algebras. -/
def affineEquivalenceCompBaseChangeIso :
    (affineEquivalence (.of R)).functor ⋙
        CommAlgCat.FiniteEtale.baseChange R S ≅
      (AlgebraicGeometry.FiniteEtale.pullback
          (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R S)))).op ⋙
        (affineEquivalence (.of S)).functor :=
  let overR := AlgebraicGeometry.AffineAnd.overSpecEquivUnder
    (@AlgebraicGeometry.IsFiniteEtale :
      MorphismProperty AlgebraicGeometry.Scheme.{u}) RingHom.FiniteEtale.respectsIso (.of R)
  let overS := AlgebraicGeometry.AffineAnd.overSpecEquivUnder
    (@AlgebraicGeometry.IsFiniteEtale :
      MorphismProperty AlgebraicGeometry.Scheme.{u}) RingHom.FiniteEtale.respectsIso (.of S)
  let pushout := CategoryTheory.MorphismProperty.Under.pushout
    (RingHom.toMorphismProperty RingHom.FiniteEtale) ⊤
    (CommRingCat.ofHom (algebraMap R S))
  let pullback := (AlgebraicGeometry.FiniteEtale.pullback
    (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R S)))).op
  (Functor.associator overR.functor
      (CommAlgCat.FiniteEtale.equivUnder (.of R)).inverse
      (CommAlgCat.FiniteEtale.baseChange R S)) ≪≫
    Functor.isoWhiskerLeft overR.functor
      (CommAlgCat.FiniteEtale.equivUnderInverseCompBaseChangeIso R S) ≪≫
    (Functor.associator overR.functor pushout
      (CommAlgCat.FiniteEtale.equivUnder (.of S)).inverse).symm ≪≫
    Functor.isoWhiskerRight
      (AlgebraicGeometry.AffineAnd.overSpecEquivUnderCompPushoutIso
        (@AlgebraicGeometry.IsFiniteEtale :
          MorphismProperty AlgebraicGeometry.Scheme.{u}) RingHom.FiniteEtale.respectsIso
        (CommRingCat.ofHom (algebraMap R S)))
      (CommAlgCat.FiniteEtale.equivUnder (.of S)).inverse ≪≫
    Functor.associator pullback overS.functor
      (CommAlgCat.FiniteEtale.equivUnder (.of S)).inverse

local instance finiteEtaleInfStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange
      ((@IsFinite : MorphismProperty Scheme.{u}) ⊓
        (@Etale : MorphismProperty Scheme.{u})) :=
  MorphismProperty.IsStableUnderBaseChange.inf

/-- The canonical pullback on finite étale covers of affine schemes is an
equivalence exactly when tensor-product base change of finite étale algebras is
an equivalence. This also identifies the legacy finite-étale property with the
intersection of the finite and étale morphism properties. -/
theorem pullback_specMap_isEquivalence_iff :
    (MorphismProperty.Over.pullback
      ((@IsFinite : MorphismProperty Scheme.{u}) ⊓
        (@Etale : MorphismProperty Scheme.{u})) ⊤
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))).IsEquivalence ↔
    (CommAlgCat.FiniteEtale.baseChange R S : CommAlgCat.FiniteEtale.{u} R ⥤
      CommAlgCat.FiniteEtale.{u} S).IsEquivalence := by
  let P : MorphismProperty Scheme.{u} :=
    (@IsFinite : MorphismProperty Scheme.{u}) ⊓
      (@Etale : MorphismProperty Scheme.{u})
  change (MorphismProperty.Over.pullback P ⊤
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))).IsEquivalence ↔ _
  have hP : P = (@IsFiniteEtale : MorphismProperty Scheme.{u}) :=
    IsFiniteEtale.eq_inf.symm
  have htransport (Q : MorphismProperty Scheme.{u})
      [Q.IsStableUnderBaseChange]
      (hQ : Q = (@IsFiniteEtale : MorphismProperty Scheme.{u})) :
      (MorphismProperty.Over.pullback Q ⊤
        (Spec.map (CommRingCat.ofHom (algebraMap R S)))).IsEquivalence ↔
      (CommAlgCat.FiniteEtale.baseChange R S : CommAlgCat.FiniteEtale.{u} R ⥤
        CommAlgCat.FiniteEtale.{u} S).IsEquivalence := by
    subst Q
    let F := FiniteEtale.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))
    constructor
    · intro h
      let : F.IsEquivalence := h
      let : F.op.IsEquivalence := F.asEquivalence.op.isEquivalence_functor
      let : ((affineEquivalence (.of R)).functor ⋙
          CommAlgCat.FiniteEtale.baseChange R S).IsEquivalence :=
        Functor.isEquivalence_of_iso (affineEquivalenceCompBaseChangeIso R S).symm
      exact Functor.isEquivalence_of_comp_left (affineEquivalence (.of R)).functor
        (CommAlgCat.FiniteEtale.baseChange R S)
    · intro h
      let : (CommAlgCat.FiniteEtale.baseChange R S).IsEquivalence := h
      let : (F.op ⋙ (affineEquivalence (.of S)).functor).IsEquivalence :=
        Functor.isEquivalence_of_iso (affineEquivalenceCompBaseChangeIso R S)
      let : F.op.IsEquivalence := Functor.isEquivalence_of_comp_right
        F.op (affineEquivalence (.of S)).functor
      let : F.op.unop.IsEquivalence := F.op.asEquivalence.unop.isEquivalence_functor
      have hF : F.IsEquivalence := Functor.isEquivalence_of_iso F.opUnopIso
      exact hF
  exact htransport P hP

end AlgebraicGeometry.FiniteEtale
