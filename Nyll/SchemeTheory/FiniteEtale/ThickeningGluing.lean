/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.FiniteEtale.AffineThickening
public import Nyll.SchemeTheory.FiniteEtale.Basic
public import Nyll.SchemeTheory.FiniteEtale.PullbackRepresentable
public import Nyll.SchemeTheory.FiniteEtale.ThickeningFullyFaithful
public import Nyll.SchemeTheory.WeilRestriction.GluedRepresentable
public import Nyll.SchemeTheory.WeilRestriction.GluingData
public import Mathlib.AlgebraicGeometry.Cover.Directed
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Sites.BigZariski
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver

/-!
# Gluing finite étale lifts across a thickening

Local finite étale lifts represent the same presheaf of maps after pullback.
Their universal elements therefore supply compatible transition maps and
cartesian squares on the directed affine cover. Gluing these local representers
produces a finite étale lift over the whole target.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open SchemeTheory.WeilRestriction

noncomputable section

universe u

namespace AlgebraicGeometry.FiniteEtale

local instance finiteEtaleInfStableUnderBaseChangeThickeningGluing :
    MorphismProperty.IsStableUnderBaseChange
      ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) :=
  MorphismProperty.IsStableUnderBaseChange.inf

variable {X Y U : Scheme.{u}}

private def pullbackMapLeftIso (i : X ⟶ Y) (u : U ⟶ Y) (T : Over U) :
    Limits.pullback T.hom (Limits.pullback.snd i u) ≅ Limits.pullback (T.hom ≫ u) i :=
  (pullbackSymmetry T.hom (Limits.pullback.snd i u)).trans <|
    (pullbackLeftPullbackSndIso i u T.hom).trans
      (pullbackSymmetry i (T.hom ≫ u))

@[reassoc]
private lemma pullbackMapLeftIso_hom_fst (i : X ⟶ Y) (u : U ⟶ Y) (T : Over U) :
    (pullbackMapLeftIso i u T).hom ≫ Limits.pullback.fst (T.hom ≫ u) i =
      Limits.pullback.fst T.hom (Limits.pullback.snd i u) := by
  simp only [pullbackMapLeftIso, Iso.trans_hom, Category.assoc,
    pullbackSymmetry_hom_comp_fst, pullbackLeftPullbackSndIso_hom_snd,
    pullbackSymmetry_hom_comp_snd]

@[reassoc]
private lemma pullbackMapLeftIso_hom_snd (i : X ⟶ Y) (u : U ⟶ Y) (T : Over U) :
    (pullbackMapLeftIso i u T).hom ≫ Limits.pullback.snd (T.hom ≫ u) i =
      Limits.pullback.snd T.hom (Limits.pullback.snd i u) ≫ Limits.pullback.fst i u := by
  simp only [pullbackMapLeftIso, Iso.trans_hom, Category.assoc,
    pullbackSymmetry_hom_comp_snd, pullbackLeftPullbackSndIso_hom_fst,
    pullbackSymmetry_hom_comp_fst_assoc]

private def pullbackMapIso (i : X ⟶ Y) (u : U ⟶ Y) :
    Over.pullback (Limits.pullback.snd i u) ⋙ Over.map (Limits.pullback.fst i u) ≅
      Over.map u ⋙ Over.pullback i :=
  NatIso.ofComponents
    (fun T ↦ Over.isoMk (pullbackMapLeftIso i u T)
      (pullbackMapLeftIso_hom_snd i u T))
    (fun {T T'} f ↦ by
      apply Over.OverMorphism.ext
      have hQ :
          (Limits.pullback.fst T.hom (Limits.pullback.snd i u) ≫ f.left) ≫ T'.hom =
            Limits.pullback.snd T.hom (Limits.pullback.snd i u) ≫ Limits.pullback.snd i u := by
        rw [Category.assoc, Over.w f, Limits.pullback.condition]
      have hP :
          (Limits.pullback.fst (T.hom ≫ u) i ≫ f.left) ≫ (T'.hom ≫ u) =
            Limits.pullback.snd (T.hom ≫ u) i ≫ i := by
        rw [Category.assoc, ← Category.assoc f.left T'.hom u, Over.w f,
          Limits.pullback.condition]
      change
        (Limits.pullback.lift (Limits.pullback.fst T.hom (Limits.pullback.snd i u) ≫ f.left)
          (Limits.pullback.snd T.hom (Limits.pullback.snd i u)) hQ) ≫
            (pullbackMapLeftIso i u T').hom =
          (pullbackMapLeftIso i u T).hom ≫
            (Limits.pullback.lift (Limits.pullback.fst (T.hom ≫ u) i ≫ f.left)
              (Limits.pullback.snd (T.hom ≫ u) i) hP)
      apply Limits.pullback.hom_ext
      · simp only [Category.assoc, pullbackMapLeftIso_hom_fst,
          Limits.pullback.lift_fst, pullbackMapLeftIso_hom_fst_assoc]
      · simp only [Category.assoc, pullbackMapLeftIso_hom_snd,
          Limits.pullback.lift_snd, Limits.pullback.lift_snd_assoc])

private def restrictionPullbackHomIso (i : X ⟶ Y) (u : U ⟶ Y) (V : Over X) :
    (Over.map u).op ⋙ ((Over.pullback i).op ⋙ yoneda.obj V) ≅
      (Over.pullback (Limits.pullback.snd i u)).op ⋙
        yoneda.obj ((Over.pullback (Limits.pullback.fst i u)).obj V) :=
  (Functor.associator (Over.map u).op (Over.pullback i).op (yoneda.obj V)).symm.trans <|
    (Functor.isoWhiskerRight (NatIso.op (pullbackMapIso i u)) (yoneda.obj V)).trans <|
      (Functor.associator (Over.pullback (Limits.pullback.snd i u)).op
        (Over.map (Limits.pullback.fst i u)).op (yoneda.obj V)).trans <|
        Functor.isoWhiskerLeft (Over.pullback (Limits.pullback.snd i u)).op
          ((Over.mapPullbackAdj (Limits.pullback.fst i u)).representableBy V).toIso.symm

private lemma pullbackHom_isSheaf (i : X ⟶ Y) (V : Over X) :
    Presheaf.IsSheaf (Scheme.zariskiTopology.over Y)
      ((Over.pullback i).op ⋙ yoneda.obj V) := by
  exact Functor.op_comp_isSheaf_of_isSheaf
    (F := Over.pullback i) (J := Scheme.zariskiTopology.over Y)
    (K := Scheme.zariskiTopology.over X) (yoneda.obj V)
    (by
      rw [isSheaf_iff_isSheaf_of_type]
      exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
        (J := Scheme.zariskiTopology.over X) (yoneda.obj V))

private def pullbackHomRepresentable
    (i : X ⟶ Y) [IsClosedImmersion i] [Surjective i]
    (W : Over Y) [IsFinite W.hom] [Etale W.hom] :
    ((Over.pullback i).op ⋙ yoneda.obj ((Over.pullback i).obj W)).RepresentableBy W where
  homEquiv {T} := Equiv.ofBijective ((Over.pullback i).map (X := T) (Y := W))
    (pullback_map_bijective_to_finiteEtale i T W)
  homEquiv_comp f g := (Over.pullback i).map_comp f g

private theorem exists_localRepresenter
    (i : X ⟶ Y) [IsClosedImmersion i] [Surjective i]
    (u : U ⟶ Y) [IsAffine U]
    (V : MorphismProperty.Over
      ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ X) :
    ∃ W : Over U, IsFiniteEtale W.hom ∧
      Nonempty (((Over.map u).op ⋙
        ((Over.pullback i).op ⋙ yoneda.obj V.toComma)).RepresentableBy W) := by
  let P : MorphismProperty Scheme.{u} := @IsFinite ⊓ @Etale
  let G : P.Over ⊤ U ⥤ P.Over ⊤ (Limits.pullback i u) :=
    MorphismProperty.Over.pullback P ⊤ (Limits.pullback.snd i u)
  let B : P.Over ⊤ (Limits.pullback i u) :=
    (MorphismProperty.Over.pullback P ⊤ (Limits.pullback.fst i u)).obj V
  let : G.IsEquivalence :=
    pullback_isEquivalence_of_isAffine_of_surjective_closedImmersion
      (Limits.pullback.snd i u)
  let W : P.Over ⊤ U := G.objPreimage B
  let e : (Over.pullback (Limits.pullback.snd i u)).obj W.toComma ≅
      (Over.pullback (Limits.pullback.fst i u)).obj V.toComma :=
    (MorphismProperty.Over.forget P ⊤ (Limits.pullback i u)).mapIso
      (G.objObjPreimageIso B)
  let : IsFinite W.hom := W.prop.1
  let : Etale W.hom := W.prop.2
  have hFiniteEtale : IsFiniteEtale W.hom := ⟨⟩
  let h : ((Over.pullback (Limits.pullback.snd i u)).op ⋙
      yoneda.obj ((Over.pullback (Limits.pullback.fst i u)).obj V.toComma)).RepresentableBy
        W.toComma :=
    (pullbackHomRepresentable (Limits.pullback.snd i u) W.toComma).ofIso
      (Functor.isoWhiskerLeft (Over.pullback (Limits.pullback.snd i u)).op
        (yoneda.mapIso e))
  exact ⟨W.toComma, hFiniteEtale,
    ⟨h.ofIso (restrictionPullbackHomIso i u V.toComma).symm⟩⟩

/-- Finite étale covers lift across an arbitrary surjective closed immersion.
The lifts on the directed affine cover glue using their actual representing
equivalences, so compatibility on overlaps is part of the construction. -/
theorem pullback_essSurj_of_surjective_closedImmersion
    (i : X ⟶ Y) [IsClosedImmersion i] [Surjective i] :
    (MorphismProperty.Over.pullback
      ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ i).EssSurj := by
  let P : MorphismProperty Scheme.{u} := @IsFinite ⊓ @Etale
  constructor
  intro V
  let F : (Over Y)ᵒᵖ ⥤ Type u := (Over.pullback i).op ⋙ yoneda.obj V.toComma
  let 𝒰 : Y.OpenCover := Y.directedAffineCover
  have hlocal : ∀ j : 𝒰.I₀, ∃ W : Over (𝒰.X j), IsFiniteEtale W.hom ∧
      Nonempty (((Over.map (𝒰.f j)).op ⋙ F).RepresentableBy W) := by
    intro j
    let : IsAffine (𝒰.X j) := j.2
    exact exists_localRepresenter i (𝒰.f j) V
  choose W hFinite hRepresentable using hlocal
  let h : ∀ j : 𝒰.I₀, ((Over.map (𝒰.f j)).op ⋙ F).RepresentableBy (W j) :=
    fun j ↦ Classical.choice (hRepresentable j)
  let T : Over Y := gluedLocalRepresenter F 𝒰 W h
  have hT : IsFiniteEtale T.hom :=
    gluedLocalRepresenter_isFiniteEtale F 𝒰 W h hFinite
  let hRep : F.RepresentableBy T :=
    gluedLocalRepresentable F 𝒰 W h (pullbackHom_isSheaf i V.toComma)
  let B : P.Over ⊤ Y := MorphismProperty.Over.mk ⊤ T.hom
    ⟨hT.toIsFinite, hT.toEtale⟩
  refine ⟨B, ⟨?_⟩⟩
  exact (MorphismProperty.Comma.forgetFullyFaithful
    (Functor.id Scheme.{u}) (Functor.fromPUnit X) P).preimageIso
      (pullbackIsoOfRepresentable i V.toComma T hRep)

end AlgebraicGeometry.FiniteEtale
