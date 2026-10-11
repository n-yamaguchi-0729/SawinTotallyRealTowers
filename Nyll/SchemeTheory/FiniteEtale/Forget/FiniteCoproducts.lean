/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.FiniteEtale.Forget.FiniteLimits
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts

/-!
# Finite coproducts of finite étale schemes

This file proves the finite-coproduct part of Stacks Project, Tag `0BNA`,
directly for the canonical forgetful functor from finite étale schemes.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory Limits

namespace AlgebraicGeometry.FiniteEtale

variable (X : Scheme.{u})

private instance : IsZariskiLocalAtSource
    (@Etale : MorphismProperty Scheme.{u}) :=
  HasRingHomProperty.instIsZariskiLocalAtSource

private instance : MorphismProperty.RespectsIso
    (@IsFiniteEtale : MorphismProperty Scheme.{u}) := by
  apply MorphismProperty.RespectsIso.mk
  · intro U V W e f hf
    let : IsFinite f := hf.toIsFinite
    let : Etale f := hf.toEtale
    exact IsFiniteEtale.mk
  · intro U V W e f hf
    let : IsFinite f := hf.toIsFinite
    let : Etale f := hf.toEtale
    exact IsFiniteEtale.mk

private lemma isFiniteEtale_sigmaDesc_walkingPair {T : Scheme.{u}}
    (Y : WalkingPair → Scheme.{u})
    (f : ∀ i, Y i ⟶ T) (hf : ∀ i, IsFiniteEtale (f i)) :
    IsFiniteEtale (Sigma.desc f) := by
  let b : Cofan Y := Cofan.mk (Y .left ⨿ Y .right) fun
    | .left => coprod.inl
    | .right => coprod.inr
  let hb : IsColimit b := Cofan.IsColimit.mk b
    (fun t => coprod.desc (t.inj .left) (t.inj .right))
    (by
      intro t j
      cases j
      · exact coprod.inl_desc _ _
      · exact coprod.inr_desc _ _)
    (by
      intro t m hm
      apply coprod.hom_ext
      · rw [coprod.inl_desc]
        exact hm .left
      · rw [coprod.inr_desc]
        exact hm .right)
  let hSigma : IsColimit (Sigma.cocone (Discrete.functor Y)) :=
    coproductIsCoproduct' (Discrete.functor Y)
  let e : (∐ Y) ≅ Y .left ⨿ Y .right :=
    hSigma.coconePointUniqueUpToIso hb
  have he_fac (j : WalkingPair) : Sigma.ι Y j ≫ e.hom = b.inj j := by
    dsimp only [e]
    exact IsColimit.comp_coconePointUniqueUpToIso_hom hSigma hb ⟨j⟩
  have heq : Sigma.desc f = e.hom ≫ coprod.desc (f .left) (f .right) := by
    apply Sigma.hom_ext
    intro j
    cases j
    · rw [Sigma.ι_comp_desc]
      rw [← Category.assoc, he_fac]
      change f .left = coprod.inl ≫ coprod.desc (f .left) (f .right)
      exact (coprod.inl_desc _ _).symm
    · rw [Sigma.ι_comp_desc]
      rw [← Category.assoc, he_fac]
      change f .right = coprod.inr ≫ coprod.desc (f .left) (f .right)
      exact (coprod.inr_desc _ _).symm
  let : IsFiniteEtale (f .left) := hf .left
  let : IsFiniteEtale (f .right) := hf .right
  let : IsFinite (Sigma.desc f) := by
    rw [heq]
    infer_instance
  let : Etale (Sigma.desc f) :=
    IsZariskiLocalAtSource.sigmaDesc fun i => by
      let : IsFiniteEtale (f i) := hf i
      infer_instance
  exact .mk

private lemma isFiniteEtale_sigmaDesc_empty {T : Scheme.{u}}
    (Y : PEmpty.{v + 1} → Scheme.{u}) [Small.{u} PEmpty.{v + 1}]
    (f : ∀ i, Y i ⟶ T) :
    IsFiniteEtale (Sigma.desc f) := by
  let b : Cofan Y := Cofan.mk (∅ : Scheme.{u}) fun i => i.elim
  let hb : IsColimit b :=
    (isColimitEquivIsInitialOfIsEmpty Scheme b).symm emptyIsInitial
  let hSigma : IsColimit (Sigma.cocone (Discrete.functor Y)) :=
    coproductIsCoproduct' (Discrete.functor Y)
  let e : (∐ Y) ≅ (∅ : Scheme.{u}) :=
    hSigma.coconePointUniqueUpToIso hb
  have heq : Sigma.desc f = e.hom ≫ Scheme.emptyTo T := by
    apply Sigma.hom_ext
    intro i
    exact i.elim
  let : IsFinite (Sigma.desc f) := by
    rw [heq]
    infer_instance
  let : Etale (Sigma.desc f) :=
    IsZariskiLocalAtSource.sigmaDesc fun i => i.elim
  exact .mk

private instance isClosedUnderBinaryCoproducts (X : Scheme.{u}) :
    ObjectProperty.IsClosedUnderColimitsOfShape
      (MorphismProperty.costructuredArrowObj
        (𝟭 Scheme.{u}) (X := X) (@IsFiniteEtale))
      (Discrete WalkingPair) :=
  CostructuredArrow.isClosedUnderColimitsOfShape
    (T := Scheme.{u}) (A := Scheme.{u}) (L := 𝟭 Scheme.{u})
    (P := @IsFiniteEtale) (J := Discrete WalkingPair) _
    (fun _ => coproductIsCoproduct' _)
    (fun D _ _ s h =>
      isFiniteEtale_sigmaDesc_walkingPair
        (fun i => D.obj ⟨i⟩) (fun i => s.app ⟨i⟩) (fun i => h ⟨i⟩)) X

private instance isClosedUnderInitial (X : Scheme.{u}) :
    ObjectProperty.IsClosedUnderColimitsOfShape
      (MorphismProperty.costructuredArrowObj
        (𝟭 Scheme.{u}) (X := X) (@IsFiniteEtale))
      (Discrete PEmpty.{1}) :=
  CostructuredArrow.isClosedUnderColimitsOfShape
    (T := Scheme.{u}) (A := Scheme.{u}) (L := 𝟭 Scheme.{u})
    (P := @IsFiniteEtale) (J := Discrete PEmpty.{1}) _
    (fun _ => coproductIsCoproduct' _)
    (fun D _ _ s _ =>
      isFiniteEtale_sigmaDesc_empty
        (fun i => D.obj ⟨i⟩) (fun i => s.app ⟨i⟩)) X

private instance isClosedUnderBinaryCoproductsComma (X : Scheme.{u}) :
    ObjectProperty.IsClosedUnderColimitsOfShape
      (MorphismProperty.commaObj (𝟭 Scheme.{u}) (Functor.fromPUnit.{0} X)
        (@IsFiniteEtale))
      (Discrete WalkingPair) := by
  change ObjectProperty.IsClosedUnderColimitsOfShape
    (MorphismProperty.costructuredArrowObj
      (𝟭 Scheme.{u}) (X := X) (@IsFiniteEtale))
    (Discrete WalkingPair)
  infer_instance

private instance isClosedUnderInitialComma (X : Scheme.{u}) :
    ObjectProperty.IsClosedUnderColimitsOfShape
      (MorphismProperty.commaObj (𝟭 Scheme.{u}) (Functor.fromPUnit.{0} X)
        (@IsFiniteEtale))
      (Discrete PEmpty.{1}) := by
  change ObjectProperty.IsClosedUnderColimitsOfShape
    (MorphismProperty.costructuredArrowObj
      (𝟭 Scheme.{u}) (X := X) (@IsFiniteEtale))
    (Discrete PEmpty.{1})
  infer_instance

private noncomputable instance forgetCreatesBinaryCoproducts :
    CreatesColimitsOfShape (Discrete WalkingPair) (forget X) := by
  letI : Category (MorphismProperty.Over
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) ⊤ X) :=
    finiteEtaleOverCategory X
  change CreatesColimitsOfShape (Discrete WalkingPair)
    (MorphismProperty.Over.forget (@IsFiniteEtale) ⊤ X)
  exact MorphismProperty.Comma.forgetCreatesColimitsOfShapeOfClosed
    (@IsFiniteEtale) (Discrete WalkingPair)

private noncomputable instance forgetCreatesInitial :
    CreatesColimitsOfShape (Discrete PEmpty.{1}) (forget X) := by
  letI : Category (MorphismProperty.Over
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) ⊤ X) :=
    finiteEtaleOverCategory X
  change CreatesColimitsOfShape (Discrete PEmpty.{1})
    (MorphismProperty.Over.forget (@IsFiniteEtale) ⊤ X)
  exact MorphismProperty.Comma.forgetCreatesColimitsOfShapeOfClosed
    (@IsFiniteEtale) (Discrete PEmpty.{1})

private instance forgetPreservesBinaryCoproducts :
    PreservesColimitsOfShape (Discrete WalkingPair) (forget X) := by
  infer_instance

private instance forgetPreservesInitial :
    PreservesColimitsOfShape (Discrete PEmpty.{1}) (forget X) := by
  infer_instance

/-- The canonical forgetful functor from finite étale schemes over `X` to
schemes over `X` preserves finite coproducts. -/
instance forgetPreservesFiniteCoproducts :
    PreservesFiniteCoproducts (forget X) where
  preserves n := PreservesFiniteCoproducts.of_preserves_binary_and_initial (forget X) (Fin n)

/-- Forgetting a finite étale scheme all the way to schemes preserves finite
coproducts. -/
instance forgetCompOverForgetPreservesFiniteCoproducts :
    PreservesFiniteCoproducts (forget X ⋙ CategoryTheory.Over.forget X) :=
  inferInstance

end AlgebraicGeometry.FiniteEtale
