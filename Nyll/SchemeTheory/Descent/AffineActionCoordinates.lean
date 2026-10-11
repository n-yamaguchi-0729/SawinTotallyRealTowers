/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Descent.ActionOverlap
import Nyll.SchemeTheory.Descent.AffineAlgebraCoaction
import Nyll.SchemeTheory.Descent.AffineCocycle
import Nyll.SchemeTheory.Descent.AlgebraCoaction
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Tensor coordinates for genuine descent actions

We transport an action across the equality between a composite structure map
and its affine coordinate map. The resulting overlap isomorphism, its two base
coordinates, and its diagonal restriction are expressed in tensor coordinates.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace AlgebraicGeometry

variable {X Y Z : Scheme.{u}} (f : Y ⟶ X) (p : Z ⟶ Y) (g : Z ⟶ X)
  (e : p ≫ f = g) (a : pullback f (p ≫ f) ⟶ Z)

/-- Express an action using an equal composite structure map. -/
def pullbackActionCongr : pullback f g ⟶ Z :=
  (pullback.congrHom rfl e).inv ≫ a

/-- Invariance of a morphism under the action is unchanged by the coordinate transport. -/
lemma pullbackActionCongr_invariant_iff {T : Scheme.{u}} (q : Z ⟶ T) :
    pullbackActionCongr f p g e a ≫ q = pullback.snd f g ≫ q ↔
      a ≫ q = pullback.snd f (p ≫ f) ≫ q := by
  subst g
  simp only [pullbackActionCongr, pullback.congrHom_inv, pullback.map_id,
    Category.id_comp]

variable (ha : a ≫ p = pullback.fst f (p ≫ f))

include ha in
lemma pullbackActionCongr_over : pullbackActionCongr f p g e a ≫ p = pullback.fst f g := by
  subst g
  simpa only [pullbackActionCongr, pullback.congrHom_inv, pullback.map_id,
    Category.id_comp] using ha

include ha in
lemma pullbackActionCongr_base : pullbackActionCongr f p g e a ≫ g = pullback.fst f g ≫ f := by
  calc
    _ = pullbackActionCongr f p g e a ≫ (p ≫ f) := congrArg (_ ≫ ·) e.symm
    _ = _ := by rw [← Category.assoc, pullbackActionCongr_over f p g e a ha]

variable
  (hunit : pullback.lift (f := f) (g := p ≫ f) p (𝟙 Z)
    (Category.id_comp (p ≫ f)).symm ≫ a = 𝟙 Z)
  (hassoc : pullbackActionStep f (p ≫ f) a (by rw [← Category.assoc, ha]) ≫ a =
    pullbackSkipMiddle f (p ≫ f) ≫ a)

/-- The geometric overlap isomorphism in the changed pullback coordinates. -/
def pullbackActionOverlapCongrIso : pullback f g ≅ pullback g f :=
  (pullback.congrHom rfl e).symm ≪≫ pullbackActionOverlapIso f p a ha hunit hassoc ≪≫
    pullback.congrHom e rfl

lemma pullbackActionOverlapCongrIso_fst :
    (pullbackActionOverlapCongrIso f p g e a ha hunit hassoc).hom ≫ pullback.fst g f =
      pullbackActionCongr f p g e a := by
  subst g
  simpa only [pullbackActionOverlapCongrIso, Iso.trans_hom, Iso.symm_hom,
    pullback.congrHom_hom, pullback.congrHom_inv, pullback.map_id,
    Category.id_comp, Category.comp_id, pullbackActionCongr] using
      pullbackActionOverlapIso_hom_fst f p a ha hunit hassoc

lemma pullbackActionOverlapCongrIso_snd :
    (pullbackActionOverlapCongrIso f p g e a ha hunit hassoc).hom ≫ pullback.snd g f =
      pullback.snd f g ≫ p := by
  subst g
  simpa only [pullbackActionOverlapCongrIso, Iso.trans_hom, Iso.symm_hom,
    pullback.congrHom_hom, pullback.congrHom_inv, pullback.map_id,
    Category.id_comp, Category.comp_id] using
      pullbackActionOverlapIso_hom_snd f p a ha hunit hassoc

lemma pullbackActionOverlapCongrIso_diagonal :
    pullback.lift (f := f) (g := g) p (𝟙 Z) (by rw [Category.id_comp, e]) ≫
        (pullbackActionOverlapCongrIso f p g e a ha hunit hassoc).hom =
      pullback.lift (f := g) (g := f) (𝟙 Z) p (by rw [Category.id_comp, e]) := by
  subst g
  simpa only [pullbackActionOverlapCongrIso, Iso.trans_hom, Iso.symm_hom,
    pullback.congrHom_hom, pullback.congrHom_inv, pullback.map_id,
    Category.id_comp, Category.comp_id] using
      pullbackActionOverlapIso_diagonal f p a ha hunit hassoc

include hassoc in
lemma pullbackActionCongr_assoc :
    pullbackActionStep f g (pullbackActionCongr f p g e a)
        (pullbackActionCongr_base f p g e a ha) ≫ pullbackActionCongr f p g e a =
      pullbackSkipMiddle f g ≫ pullbackActionCongr f p g e a := by
  subst g
  simpa only [pullbackActionCongr, pullback.congrHom_inv, pullback.map_id,
    Category.id_comp] using hassoc

end AlgebraicGeometry

namespace Algebra.Descent

variable (R B C : Type u) [CommRing R] [CommRing B] [CommRing C]
variable [Algebra R B] [Algebra R C] [Algebra B C] [IsScalarTower R B C]

/-- The algebra tower identifies the two actual maps to the affine base. -/
lemma specMap_tower :
    Spec.map (CommRingCat.ofHom (algebraMap B C)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R B)) =
      Spec.map (CommRingCat.ofHom (algebraMap R C)) := by
  rw [← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext (IsScalarTower.algebraMap_eq R B C).symm)

/-- Tensor coordinates of an actual geometric overlap isomorphism. -/
def affinePullbackOverlapIso
    (β : pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))
        (Spec.map (CommRingCat.ofHom (algebraMap R C))) ≅
      pullback (Spec.map (CommRingCat.ofHom (algebraMap R C)))
        (Spec.map (CommRingCat.ofHom (algebraMap R B)))) :
    Spec (.of (B ⊗[R] C)) ≅ Spec (.of (C ⊗[R] B)) :=
  (pullbackSpecIso R B C).symm ≪≫ β ≪≫ pullbackSpecIso R C B

omit [Algebra B C] [IsScalarTower R B C] in
lemma affinePullbackOverlapIso_action
    (β : pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))
        (Spec.map (CommRingCat.ofHom (algebraMap R C))) ≅
      pullback (Spec.map (CommRingCat.ofHom (algebraMap R C)))
        (Spec.map (CommRingCat.ofHom (algebraMap R B)))) :
    affineOverlapAction R B C (affinePullbackOverlapIso R B C β) =
      β.hom ≫ pullback.fst _ _ := by
  simp only [affineOverlapAction, affinePullbackOverlapIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.hom_inv_id_assoc]
  exact congrArg (β.hom ≫ ·) (pullbackSpecIso_hom_fst R C B)

private lemma affineSourceBase_fst :
    Spec.map (CommRingCat.ofHom (affineOverlapSourceBase R B C).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
          B →+* B ⊗[R] B)) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
        C →+* C ⊗[R] B)) ≫ Spec.map (CommRingCat.ofHom (algebraMap B C)) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1

private lemma affineSourceBase_snd :
    Spec.map (CommRingCat.ofHom (affineOverlapSourceBase R B C).toRingHom) ≫
        Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.includeRight :
          B →ₐ[R] B ⊗[R] B) : B →+* B ⊗[R] B)) =
      Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.includeRight :
        B →ₐ[R] C ⊗[R] B) : B →+* C ⊗[R] B)) := by
  rw [← Spec.map_comp]
  congr 1
  ext b
  change affineOverlapSourceBase R B C (1 ⊗ₜ[R] b) = 1 ⊗ₜ[R] b
  simp only [affineOverlapSourceBase, Algebra.TensorProduct.map_tmul, map_one,
    AlgHom.id_apply]

private lemma affineTargetBase_fst :
    Spec.map (CommRingCat.ofHom (affineOverlapTargetBase R B C).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
          B →+* B ⊗[R] B)) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
        B →+* B ⊗[R] C)) := by
  rw [← Spec.map_comp]
  congr 1
  ext b
  change affineOverlapTargetBase R B C (b ⊗ₜ[R] 1) = b ⊗ₜ[R] 1
  simp only [affineOverlapTargetBase, Algebra.TensorProduct.map_tmul, map_one,
    AlgHom.id_apply]

private lemma affineTargetBase_snd :
    Spec.map (CommRingCat.ofHom (affineOverlapTargetBase R B C).toRingHom) ≫
        Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.includeRight :
          B →ₐ[R] B ⊗[R] B) : B →+* B ⊗[R] B)) =
      Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.includeRight :
        C →ₐ[R] B ⊗[R] C) : C →+* B ⊗[R] C)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap B C)) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1

variable (β : pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))
    (Spec.map (CommRingCat.ofHom (algebraMap R C))) ≅
  pullback (Spec.map (CommRingCat.ofHom (algebraMap R C)))
    (Spec.map (CommRingCat.ofHom (algebraMap R B))))

/-- Preservation of the two geometric cover coordinates gives the full
tensor-square base compatibility, including its second coordinate. -/
lemma affinePullbackOverlapIso_base
    (hfst : β.hom ≫ pullback.fst _ _ ≫ Spec.map (CommRingCat.ofHom (algebraMap B C)) =
      pullback.fst _ _)
    (hsnd : β.hom ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (algebraMap B C))) :
    (affinePullbackOverlapIso R B C β).hom ≫
        Spec.map (CommRingCat.ofHom (affineOverlapSourceBase R B C).toRingHom) =
      Spec.map (CommRingCat.ofHom (affineOverlapTargetBase R B C).toRingHom) := by
  apply (cancel_epi (pullbackSpecIso R B C).hom).mp
  simp only [affinePullbackOverlapIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_assoc]
  apply (cancel_mono (pullbackSpecIso R B B).inv).mp
  apply pullback.hom_ext
  · simp only [Category.assoc, pullbackSpecIso_inv_fst, affineSourceBase_fst,
      affineTargetBase_fst, pullbackSpecIso_hom_fst, pullbackSpecIso_hom_fst_assoc]
    exact hfst
  · simp only [Category.assoc, pullbackSpecIso_inv_snd, affineSourceBase_snd,
      affineTargetBase_snd, pullbackSpecIso_hom_snd, pullbackSpecIso_hom_snd_assoc]
    exact hsnd

private lemma affineTargetDiagonal_chart :
    Spec.map (CommRingCat.ofHom (tensorTargetDiagonal R B C).toRingHom) ≫
        (pullbackSpecIso R B C).inv =
      pullback.lift (f := Spec.map (CommRingCat.ofHom (algebraMap R B)))
        (g := Spec.map (CommRingCat.ofHom (algebraMap R C)))
        (Spec.map (CommRingCat.ofHom (algebraMap B C))) (𝟙 _) (by
          rw [Category.id_comp, specMap_tower R B C]) := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackSpecIso_inv_fst, pullback.lift_fst, ← Spec.map_comp]
    congr 1
    ext b
    change tensorTargetDiagonal R B C (b ⊗ₜ[R] 1) = algebraMap B C b
    simp only [tensorTargetDiagonal, Algebra.TensorProduct.lift_tmul,
      Algebra.ofId_apply, AlgHom.id_apply, mul_one]
  · rw [Category.assoc, pullbackSpecIso_inv_snd, pullback.lift_snd,
      ← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext c
    change tensorTargetDiagonal R B C (1 ⊗ₜ[R] c) = c
    simp only [tensorTargetDiagonal, Algebra.TensorProduct.lift_tmul,
      map_one, AlgHom.id_apply, one_mul]

private lemma affineSourceDiagonal_chart :
    Spec.map (CommRingCat.ofHom (tensorSourceDiagonal R B C).toRingHom) ≫
        (pullbackSpecIso R C B).inv =
      pullback.lift (f := Spec.map (CommRingCat.ofHom (algebraMap R C)))
        (g := Spec.map (CommRingCat.ofHom (algebraMap R B)))
        (𝟙 _) (Spec.map (CommRingCat.ofHom (algebraMap B C))) (by
          rw [Category.id_comp, specMap_tower R B C]) := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackSpecIso_inv_fst, pullback.lift_fst,
      ← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext c
    change tensorSourceDiagonal R B C (c ⊗ₜ[R] 1) = c
    simp only [tensorSourceDiagonal, Algebra.TensorProduct.lift_tmul,
      map_one, AlgHom.id_apply, mul_one]
  · rw [Category.assoc, pullbackSpecIso_inv_snd, pullback.lift_snd, ← Spec.map_comp]
    congr 1
    ext b
    change tensorSourceDiagonal R B C (1 ⊗ₜ[R] b) = algebraMap B C b
    simp only [tensorSourceDiagonal, Algebra.TensorProduct.lift_tmul,
      map_one, IsScalarTower.toAlgHom_apply, one_mul]

/-- The ordinary geometric diagonal equality gives the literal tensor diagonal
equality used by affine algebra descent. -/
lemma affinePullbackOverlapIso_diagonal
    (hdiag :
      pullback.lift (f := Spec.map (CommRingCat.ofHom (algebraMap R B)))
        (g := Spec.map (CommRingCat.ofHom (algebraMap R C)))
        (Spec.map (CommRingCat.ofHom (algebraMap B C))) (𝟙 _) (by
          rw [Category.id_comp, specMap_tower R B C]) ≫ β.hom =
      pullback.lift (f := Spec.map (CommRingCat.ofHom (algebraMap R C)))
        (g := Spec.map (CommRingCat.ofHom (algebraMap R B)))
        (𝟙 _) (Spec.map (CommRingCat.ofHom (algebraMap B C))) (by
          rw [Category.id_comp, specMap_tower R B C])) :
    Spec.map (CommRingCat.ofHom (tensorTargetDiagonal R B C).toRingHom) ≫
        (affinePullbackOverlapIso R B C β).hom =
      Spec.map (CommRingCat.ofHom (tensorSourceDiagonal R B C).toRingHom) := by
  apply (cancel_mono (pullbackSpecIso R C B).inv).mp
  simp only [affinePullbackOverlapIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]
  rw [← Category.assoc, affineTargetDiagonal_chart, affineSourceDiagonal_chart]
  exact hdiag

end Algebra.Descent
