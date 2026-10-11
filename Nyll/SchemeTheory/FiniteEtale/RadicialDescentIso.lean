/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.FiniteEtale.ThickeningFullyFaithful
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-!
# Canonical comparison for finite étale covers along a radicial morphism

The diagonal of a separated universally injective morphism is a surjective
closed immersion. Its fully faithful pullback therefore lifts the canonical
comparison between the two iterated pullbacks to a unique natural isomorphism.
The comparison is normalized by the common pullback along the identity.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.FiniteEtale

/- The intersection is used throughout the comparison. Giving it a name avoids
relying on notation expansion inside qualified names such as `P.Over`. -/
/-- The morphism property of being both finite and etale. -/
abbrev finiteEtaleProperty : MorphismProperty Scheme.{u} :=
  (@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale

local instance finiteEtalePropertyStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange (finiteEtaleProperty : MorphismProperty Scheme.{u}) :=
  MorphismProperty.IsStableUnderBaseChange.inf

variable {X Y : Scheme.{u}}

/-- Pullback along the first projection followed by the diagonal is canonically
pullback along the identity. -/
def radicialDiagonalFstIso (f : X ⟶ Y) :
    MorphismProperty.Over.pullback finiteEtaleProperty ⊤ (𝟙 X) ≅
      MorphismProperty.Over.pullback finiteEtaleProperty ⊤ (Limits.pullback.fst f f) ⋙
        MorphismProperty.Over.pullback finiteEtaleProperty ⊤ (Limits.pullback.diagonal f) :=
  MorphismProperty.Over.pullbackComp (P := finiteEtaleProperty) (Q := ⊤)
    (Limits.pullback.diagonal f) (Limits.pullback.fst f f) (𝟙 X)
    (Limits.pullback.diagonal_fst f).symm

/-- Pullback along the second projection followed by the diagonal is canonically
pullback along the identity. -/
def radicialDiagonalSndIso (f : X ⟶ Y) :
    MorphismProperty.Over.pullback finiteEtaleProperty ⊤ (𝟙 X) ≅
      MorphismProperty.Over.pullback finiteEtaleProperty ⊤ (Limits.pullback.snd f f) ⋙
        MorphismProperty.Over.pullback finiteEtaleProperty ⊤ (Limits.pullback.diagonal f) :=
  MorphismProperty.Over.pullbackComp (P := finiteEtaleProperty) (Q := ⊤)
    (Limits.pullback.diagonal f) (Limits.pullback.snd f f) (𝟙 X)
    (Limits.pullback.diagonal_snd f).symm

/-- The two pullbacks of a finite étale cover along a separated universally
injective morphism are canonically isomorphic, naturally in the cover. -/
def radicialDescentIso (f : X ⟶ Y) [IsSeparated f] [UniversallyInjective f] :
    MorphismProperty.Over.pullback finiteEtaleProperty ⊤ (Limits.pullback.fst f f) ≅
      MorphismProperty.Over.pullback finiteEtaleProperty ⊤ (Limits.pullback.snd f f) := by
  letI : Surjective (Limits.pullback.diagonal f) :=
    (UniversallyInjective.iff_diagonal f).mp inferInstance
  letI := pullback_full_of_surjective_closedImmersion (Limits.pullback.diagonal f)
  letI := pullback_faithful_of_surjective_closedImmersion (Limits.pullback.diagonal f)
  exact Functor.fullyFaithfulCancelRight
    (MorphismProperty.Over.pullback finiteEtaleProperty ⊤ (Limits.pullback.diagonal f))
    ((radicialDiagonalFstIso f).symm ≪≫ radicialDiagonalSndIso f)

/-- Pulling the canonical comparison back to the diagonal gives precisely the
comparison through the common identity pullback. -/
@[simp]
theorem radicialDescentIso_map_hom_app
    (f : X ⟶ Y) [IsSeparated f] [UniversallyInjective f] (V : finiteEtaleProperty.Over ⊤ X) :
    (MorphismProperty.Over.pullback finiteEtaleProperty ⊤ (Limits.pullback.diagonal f)).map
        ((radicialDescentIso f).hom.app V) =
      (radicialDiagonalFstIso f).inv.app V ≫ (radicialDiagonalSndIso f).hom.app V := by
  let : Surjective (Limits.pullback.diagonal f) :=
    (UniversallyInjective.iff_diagonal f).mp inferInstance
  let := pullback_full_of_surjective_closedImmersion (Limits.pullback.diagonal f)
  let := pullback_faithful_of_surjective_closedImmersion (Limits.pullback.diagonal f)
  simp only [radicialDescentIso, Functor.fullyFaithfulCancelRight_hom_app,
    Functor.map_preimage, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]

/-- The isomorphism form of the diagonal comparison formula. -/
theorem radicialDescentIso_mapIso
    (f : X ⟶ Y) [IsSeparated f] [UniversallyInjective f] (V : finiteEtaleProperty.Over ⊤ X) :
    (MorphismProperty.Over.pullback finiteEtaleProperty ⊤ (Limits.pullback.diagonal f)).mapIso
        ((radicialDescentIso f).app V) =
      ((radicialDiagonalFstIso f).app V).symm ≪≫ (radicialDiagonalSndIso f).app V := by
  apply Iso.ext
  exact radicialDescentIso_map_hom_app f V

/-- With the canonical identifications on both sides, the diagonal restriction
of the comparison is the identity. -/
@[simp]
theorem radicialDescentIso_diagonal
    (f : X ⟶ Y) [IsSeparated f] [UniversallyInjective f] (V : finiteEtaleProperty.Over ⊤ X) :
    (radicialDiagonalFstIso f).hom.app V ≫
        (MorphismProperty.Over.pullback finiteEtaleProperty ⊤ (Limits.pullback.diagonal f)).map
          ((radicialDescentIso f).hom.app V) ≫
        (radicialDiagonalSndIso f).inv.app V =
      𝟙 ((MorphismProperty.Over.pullback finiteEtaleProperty ⊤ (𝟙 X)).obj V) := by
  rw [radicialDescentIso_map_hom_app]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app]

/-- Diagonal normalization characterizes the comparison on every finite étale
cover; no choice of a preimage changes it. -/
theorem radicialDescentIso_hom_app_unique
    (f : X ⟶ Y) [IsSeparated f] [UniversallyInjective f] (V : finiteEtaleProperty.Over ⊤ X)
    (a : (MorphismProperty.Over.pullback finiteEtaleProperty ⊤ (Limits.pullback.fst f f)).obj V ⟶
      (MorphismProperty.Over.pullback finiteEtaleProperty ⊤ (Limits.pullback.snd f f)).obj V)
    (ha : (radicialDiagonalFstIso f).hom.app V ≫
        (MorphismProperty.Over.pullback finiteEtaleProperty ⊤ (Limits.pullback.diagonal f)).map a ≫
        (radicialDiagonalSndIso f).inv.app V =
      𝟙 ((MorphismProperty.Over.pullback finiteEtaleProperty ⊤ (𝟙 X)).obj V)) :
    a = (radicialDescentIso f).hom.app V := by
  let : Surjective (Limits.pullback.diagonal f) :=
    (UniversallyInjective.iff_diagonal f).mp inferInstance
  let := pullback_faithful_of_surjective_closedImmersion (Limits.pullback.diagonal f)
  apply (MorphismProperty.Over.pullback
    finiteEtaleProperty ⊤ (Limits.pullback.diagonal f)).map_injective
  apply (cancel_mono ((radicialDiagonalSndIso f).inv.app V)).mp
  apply (cancel_epi ((radicialDiagonalFstIso f).hom.app V)).mp
  exact ha.trans (radicialDescentIso_diagonal f V).symm

/-- The diagonal section of the first pullback. -/
def radicialDiagonalFstSection (f : X ⟶ Y) (V : finiteEtaleProperty.Over ⊤ X) :
    V.left ⟶ Limits.pullback V.hom (Limits.pullback.fst f f) :=
  Limits.pullback.lift (𝟙 V.left) (V.hom ≫ Limits.pullback.diagonal f)
    (by simp only [Category.assoc, Limits.pullback.diagonal_fst,
      Category.comp_id, Category.id_comp])

/-- The diagonal section of the second pullback. -/
def radicialDiagonalSndSection (f : X ⟶ Y) (V : finiteEtaleProperty.Over ⊤ X) :
    V.left ⟶ Limits.pullback V.hom (Limits.pullback.snd f f) :=
  Limits.pullback.lift (𝟙 V.left) (V.hom ≫ Limits.pullback.diagonal f)
    (by simp only [Category.assoc, Limits.pullback.diagonal_snd,
      Category.comp_id, Category.id_comp])

private theorem pullbackComp_identitySection
    {A B : Scheme.{u}} (j : A ⟶ B) (q : B ⟶ A) (hj : j ≫ q = 𝟙 A)
    (V : finiteEtaleProperty.Over ⊤ A) :
    Limits.pullback.lift (𝟙 V.left) V.hom (by simp) ≫
        ((MorphismProperty.Over.pullbackComp
          (P := finiteEtaleProperty) (Q := ⊤) j q (𝟙 A) hj.symm).hom.app V).left ≫
        Limits.pullback.fst (Limits.pullback.snd V.hom q) j =
      Limits.pullback.lift (𝟙 V.left) (V.hom ≫ j)
        (by simp [Category.assoc, hj]) := by
  change Limits.pullback.lift (𝟙 V.left) V.hom _ ≫
      ((Limits.pullback.congrHom (f₁ := V.hom) rfl hj.symm).hom ≫
        (pullbackLeftPullbackSndIso V.hom q j).inv) ≫
          Limits.pullback.fst (Limits.pullback.snd V.hom q) j = _
  apply Limits.pullback.hom_ext
  · simp only [Category.assoc, pullbackLeftPullbackSndIso_inv_fst,
      Limits.pullback.congrHom_hom,
      Category.comp_id, Limits.pullback.lift_fst]
  · simp only [Category.assoc, pullbackLeftPullbackSndIso_inv_fst_snd,
      Limits.pullback.congrHom_hom,
      Category.id_comp, Limits.pullback.lift_snd_assoc, Limits.pullback.lift_snd]

/-- On the actual diagonal sections, the canonical comparison is the identity
on the original finite étale cover. -/
theorem radicialDescentIso_diagonal_section
    (f : X ⟶ Y) [IsSeparated f] [UniversallyInjective f] (V : finiteEtaleProperty.Over ⊤ X) :
    radicialDiagonalFstSection f V ≫ ((radicialDescentIso f).hom.app V).left =
      radicialDiagonalSndSection f V := by
  have h : (radicialDiagonalFstIso f).hom.app V ≫
        (MorphismProperty.Over.pullback finiteEtaleProperty ⊤ (Limits.pullback.diagonal f)).map
          ((radicialDescentIso f).hom.app V) =
      (radicialDiagonalSndIso f).hom.app V := by
    rw [radicialDescentIso_map_hom_app]
    simp only [Iso.hom_inv_id_app_assoc]
  let e : V.left ⟶ Limits.pullback V.hom (𝟙 X) :=
    Limits.pullback.lift (𝟙 V.left) V.hom
      (by simp only [Category.id_comp, Category.comp_id])
  have h' := congrArg
    (fun a : (MorphismProperty.Over.pullback finiteEtaleProperty ⊤ (𝟙 X)).obj V ⟶
        (MorphismProperty.Over.pullback finiteEtaleProperty ⊤ (Limits.pullback.diagonal f)).obj
          ((MorphismProperty.Over.pullback finiteEtaleProperty ⊤ (Limits.pullback.snd f f)).obj V) ↦
      e ≫ a.left ≫ Limits.pullback.fst
          (Limits.pullback.snd V.hom (Limits.pullback.snd f f)) (Limits.pullback.diagonal f)) h
  have h₁ : e ≫ ((radicialDiagonalFstIso f).hom.app V).left ≫
        Limits.pullback.fst (Limits.pullback.snd V.hom (Limits.pullback.fst f f))
          (Limits.pullback.diagonal f) = radicialDiagonalFstSection f V :=
    pullbackComp_identitySection (Limits.pullback.diagonal f)
      (Limits.pullback.fst f f) (Limits.pullback.diagonal_fst f) V
  have h₂ : e ≫ ((radicialDiagonalSndIso f).hom.app V).left ≫
        Limits.pullback.fst (Limits.pullback.snd V.hom (Limits.pullback.snd f f))
          (Limits.pullback.diagonal f) = radicialDiagonalSndSection f V :=
    pullbackComp_identitySection (Limits.pullback.diagonal f)
      (Limits.pullback.snd f f) (Limits.pullback.diagonal_snd f) V
  have hmap' :
      ((MorphismProperty.Over.pullback finiteEtaleProperty ⊤ (Limits.pullback.diagonal f)).map
        ((radicialDescentIso f).hom.app V)).left ≫
        Limits.pullback.fst (Limits.pullback.snd V.hom (Limits.pullback.snd f f))
          (Limits.pullback.diagonal f) =
      Limits.pullback.fst (Limits.pullback.snd V.hom (Limits.pullback.fst f f))
        (Limits.pullback.diagonal f) ≫ ((radicialDescentIso f).hom.app V).left := by
    exact Limits.pullback.lift_fst _ _ _
  have hcomp : (e ≫ ((radicialDiagonalFstIso f).hom.app V).left ≫
        Limits.pullback.fst (Limits.pullback.snd V.hom (Limits.pullback.fst f f))
          (Limits.pullback.diagonal f)) ≫ ((radicialDescentIso f).hom.app V).left =
      e ≫ ((radicialDiagonalSndIso f).hom.app V).left ≫
        Limits.pullback.fst (Limits.pullback.snd V.hom (Limits.pullback.snd f f))
          (Limits.pullback.diagonal f) := by
    change e ≫ (((radicialDiagonalFstIso f).hom.app V).left ≫
      ((MorphismProperty.Over.pullback finiteEtaleProperty ⊤ (Limits.pullback.diagonal f)).map
        ((radicialDescentIso f).hom.app V)).left) ≫
        Limits.pullback.fst (Limits.pullback.snd V.hom (Limits.pullback.snd f f))
          (Limits.pullback.diagonal f) = _ at h'
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun k ↦ e ≫ k)
        ((Category.assoc _ _ _).trans
          ((congrArg (fun k ↦ ((radicialDiagonalFstIso f).hom.app V).left ≫ k)
            hmap').trans (Category.assoc _ _ _).symm))).symm.trans h')
  rw [h₁, h₂] at hcomp
  exact hcomp

end AlgebraicGeometry.FiniteEtale
