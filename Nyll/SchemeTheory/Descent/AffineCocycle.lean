/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Descent.AffineAlgebraCoaction
public import Nyll.SchemeTheory.Descent.AlgebraCoaction
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# The affine cocycle from geometric descent actions

The geometric action law is an equality of maps from an actual iterated
pullback. Tensor-product coordinates identify it with coassociativity.
Together with the overlap square over the tensor-square base, this supplies
the full tensor cocycle used for faithfully flat algebra descent.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

variable {S Y Z : Scheme.{u}} (f : Y ⟶ S) (g : Z ⟶ S)

/-- Apply an action on the last two coordinates of a genuine triple fiber product. -/
def pullbackActionStep (a : pullback f g ⟶ Z)
    (ha : a ≫ g = pullback.fst f g ≫ f) :
    pullback f (pullback.fst f g ≫ f) ⟶ pullback f g :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ a) (by
    rw [Category.assoc, ha]
    exact pullback.condition)

/-- Forget the middle coordinate of a genuine triple fiber product. -/
def pullbackSkipMiddle : pullback f (pullback.fst f g ≫ f) ⟶ pullback f g :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ pullback.snd f g) (by
    rw [Category.assoc, ← pullback.condition]
    exact pullback.condition)

end AlgebraicGeometry

namespace Algebra.Descent

variable (R B C : Type u) [CommRing R] [CommRing B] [CommRing C]
variable [Algebra R B] [Algebra R C] [Algebra B C] [IsScalarTower R B C]

/-- Compatibility with both overlap-base coordinates promotes coassociativity
of the extracted coaction to the full triple-overlap cocycle. -/
theorem tensorCocycle_eq_of_coaction_coassoc
    (θ : C ⊗[R] B ≃ₐ[B] B ⊗[R] C)
    (hbase : θ.toAlgHom.comp (affineOverlapSourceBase R B C) =
      affineOverlapTargetBase R B C)
    (hcoassoc : ∀ c : C,
      Algebra.TensorProduct.map (.id R B) ((tensorCoaction R B C θ).restrictScalars R)
          (tensorCoaction R B C θ c) =
        Algebra.TensorProduct.map (.id R B)
          (Algebra.TensorProduct.includeRight : C →ₐ[R] B ⊗[R] C)
          (tensorCoaction R B C θ c)) :
    tensorCocycleLeft R B C θ = tensorCocycleRight R B C θ := by
  have hright (b : B) : θ ((1 : C) ⊗ₜ[R] b) =
      (1 : B) ⊗ₜ[R] algebraMap B C b := by
    have h := AlgHom.congr_fun hbase ((1 : B) ⊗ₜ[R] b)
    simpa only [AlgHom.comp_apply, affineOverlapSourceBase, affineOverlapTargetBase,
      Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply,
      IsScalarTower.toAlgHom_apply, AlgEquiv.toAlgHom_apply] using h
  have hleft (b : B) : θ (algebraMap B C b ⊗ₜ[R] (1 : B)) =
      b ⊗ₜ[R] (1 : C) := θ.commutes b
  apply Algebra.TensorProduct.ext
  · apply AlgHom.ext
    intro c
    change tensorCocycleLeft R B C θ (c ⊗ₜ[R] ((1 : B) ⊗ₜ[R] (1 : B))) =
      tensorCocycleRight R B C θ (c ⊗ₜ[R] ((1 : B) ⊗ₜ[R] (1 : B)))
    simp only [tensorCocycleLeft, tensorCocycleRight, tensorFirstTransition,
      AlgHom.comp_apply, AlgEquiv.toAlgHom_apply,
      Algebra.TensorProduct.assoc_symm_tmul, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply, Algebra.TensorProduct.comm_tmul]
    change Algebra.TensorProduct.map (.id R B) (θ.restrictScalars R).toAlgHom
        (Algebra.TensorProduct.assoc R R R B C B
          (tensorCoaction R B C θ c ⊗ₜ[R] (1 : B))) =
      Algebra.TensorProduct.map (.id R B) (Algebra.TensorProduct.comm R C B).toAlgHom
        (Algebra.TensorProduct.assoc R R R B C B
          (tensorCoaction R B C θ c ⊗ₜ[R] (1 : B)))
    have h (z : B ⊗[R] C) :
        Algebra.TensorProduct.map (.id R B) (θ.restrictScalars R).toAlgHom
            (Algebra.TensorProduct.assoc R R R B C B (z ⊗ₜ[R] (1 : B))) =
          Algebra.TensorProduct.map (.id R B)
            ((tensorCoaction R B C θ).restrictScalars R) z := by
      induction z using TensorProduct.inductionOn with
      | tmul b c => rfl
      | add z w hz hw => simp only [TensorProduct.add_tmul, map_add, hz, hw]
    have h' (z : B ⊗[R] C) :
        Algebra.TensorProduct.map (.id R B) (Algebra.TensorProduct.comm R C B).toAlgHom
            (Algebra.TensorProduct.assoc R R R B C B (z ⊗ₜ[R] (1 : B))) =
          Algebra.TensorProduct.map (.id R B)
            (Algebra.TensorProduct.includeRight : C →ₐ[R] B ⊗[R] C) z := by
      induction z using TensorProduct.inductionOn with
      | tmul b c => rfl
      | add z w hz hw => simp only [TensorProduct.add_tmul, map_add, hz, hw]
    rw [h, h']
    exact hcoassoc c
  · apply Algebra.TensorProduct.ext
    · apply AlgHom.ext
      intro b
      change tensorCocycleLeft R B C θ ((1 : C) ⊗ₜ[R] (b ⊗ₜ[R] (1 : B))) =
        tensorCocycleRight R B C θ ((1 : C) ⊗ₜ[R] (b ⊗ₜ[R] (1 : B)))
      simp only [tensorCocycleLeft, tensorCocycleRight, tensorFirstTransition,
        AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, AlgEquiv.restrictScalars_apply,
        Algebra.TensorProduct.assoc_symm_tmul, Algebra.TensorProduct.assoc_tmul,
        Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        Algebra.TensorProduct.comm_tmul, hright, hleft, map_one]
    · apply AlgHom.ext
      intro b
      change tensorCocycleLeft R B C θ ((1 : C) ⊗ₜ[R] ((1 : B) ⊗ₜ[R] b)) =
        tensorCocycleRight R B C θ ((1 : C) ⊗ₜ[R] ((1 : B) ⊗ₜ[R] b))
      simp only [tensorCocycleLeft, tensorCocycleRight, tensorFirstTransition,
        AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, AlgEquiv.restrictScalars_apply,
        Algebra.TensorProduct.assoc_symm_tmul, Algebra.TensorProduct.assoc_tmul,
        Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        Algebra.TensorProduct.comm_tmul, hright, map_one]


section Coaction

omit [Algebra B C] [IsScalarTower R B C]

/-- The map on actual affine pullbacks represented by an algebra coaction. -/
def affineCoactionAction (ρ : C →ₐ[R] B ⊗[R] C) :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))
      (Spec.map (CommRingCat.ofHom (algebraMap R C))) ⟶ Spec (.of C) :=
  (pullbackSpecIso R B C).hom ≫ Spec.map (CommRingCat.ofHom ρ.toRingHom)

theorem affineCoactionAction_base (ρ : C →ₐ[R] B ⊗[R] C) :
    affineCoactionAction R B C ρ ≫ Spec.map (CommRingCat.ofHom (algebraMap R C)) =
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R B)))
        (Spec.map (CommRingCat.ofHom (algebraMap R C))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
  rw [affineCoactionAction, Category.assoc, ← Spec.map_comp]
  change (pullbackSpecIso R B C).hom ≫
    Spec.map (CommRingCat.ofHom (ρ.toRingHom.comp (algebraMap R C))) = _
  have hρ : ρ.toRingHom.comp (algebraMap R C) = algebraMap R (B ⊗[R] C) :=
    RingHom.ext ρ.commutes
  rw [hρ]
  exact pullbackSpecIso_hom_base R B C

private def affineTripleChart :
    Spec (.of (B ⊗[R] (B ⊗[R] C))) ⟶
      pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))
        (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R B)))
          (Spec.map (CommRingCat.ofHom (algebraMap R C))) ≫
            Spec.map (CommRingCat.ofHom (algebraMap R B))) :=
  (pullbackSpecIso R B (B ⊗[R] C)).inv ≫
    pullback.map _ _ _ _ (𝟙 _) (pullbackSpecIso R B C).inv (𝟙 _)
      (by rw [Category.id_comp, Category.comp_id])
      (by rw [Category.comp_id, ← pullbackSpecIso_hom_base R B C, Iso.inv_hom_id_assoc])

private theorem affineTripleChart_fst :
    affineTripleChart R B C ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft :
        B →ₐ[R] B ⊗[R] (B ⊗[R] C)).toRingHom) := by
  rw [affineTripleChart, Category.assoc, pullback.lift_fst, Category.comp_id]
  exact pullbackSpecIso_inv_fst R B (B ⊗[R] C)

private theorem affineTripleChart_snd :
    affineTripleChart R B C ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        B ⊗[R] C →ₐ[R] B ⊗[R] (B ⊗[R] C)).toRingHom) ≫
          (pullbackSpecIso R B C).inv := by
  rw [affineTripleChart, Category.assoc, pullback.lift_snd,
    pullbackSpecIso_inv_snd_assoc]
  rfl

private theorem affineTripleChart_actionStep (ρ : C →ₐ[R] B ⊗[R] C) :
    affineTripleChart R B C ≫
        pullbackActionStep (Spec.map (CommRingCat.ofHom (algebraMap R B)))
          (Spec.map (CommRingCat.ofHom (algebraMap R C))) (affineCoactionAction R B C ρ)
          (affineCoactionAction_base R B C ρ) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (.id R B) ρ).toRingHom) ≫
        (pullbackSpecIso R B C).inv := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackActionStep, pullback.lift_fst,
      affineTripleChart_fst, Category.assoc, pullbackSpecIso_inv_fst,
      ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro b
    change b ⊗ₜ[R] (1 : B ⊗[R] C) =
      Algebra.TensorProduct.map (.id R B) ρ (b ⊗ₜ[R] (1 : C))
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]
  · rw [Category.assoc, pullbackActionStep, pullback.lift_snd,
      ← Category.assoc, affineTripleChart_snd, affineCoactionAction,
      Category.assoc, Iso.inv_hom_id_assoc,
      Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp, ← Spec.map_comp]
    rfl

private theorem affineTripleChart_skipMiddle :
    affineTripleChart R B C ≫
        pullbackSkipMiddle (Spec.map (CommRingCat.ofHom (algebraMap R B)))
          (Spec.map (CommRingCat.ofHom (algebraMap R C))) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (.id R B)
        (Algebra.TensorProduct.includeRight : C →ₐ[R] B ⊗[R] C)).toRingHom) ≫
          (pullbackSpecIso R B C).inv := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackSkipMiddle, pullback.lift_fst,
      affineTripleChart_fst, Category.assoc, pullbackSpecIso_inv_fst,
      ← Spec.map_comp]
    rfl
  · rw [Category.assoc, pullbackSkipMiddle, pullback.lift_snd,
      ← Category.assoc, affineTripleChart_snd, Category.assoc,
      pullbackSpecIso_inv_snd, Category.assoc, pullbackSpecIso_inv_snd,
      ← Spec.map_comp, ← Spec.map_comp]
    rfl

/-- The ordinary associativity law on the actual triple fiber product gives
coassociativity on the coordinate ring. -/
theorem affineCoaction_coassoc_of_actionLaw (ρ : C →ₐ[R] B ⊗[R] C)
    (htrans :
      pullbackActionStep (Spec.map (CommRingCat.ofHom (algebraMap R B)))
          (Spec.map (CommRingCat.ofHom (algebraMap R C))) (affineCoactionAction R B C ρ)
          (affineCoactionAction_base R B C ρ) ≫ affineCoactionAction R B C ρ =
        pullbackSkipMiddle (Spec.map (CommRingCat.ofHom (algebraMap R B)))
          (Spec.map (CommRingCat.ofHom (algebraMap R C))) ≫ affineCoactionAction R B C ρ)
    (c : C) :
    Algebra.TensorProduct.map (.id R B) ρ (ρ c) =
      Algebra.TensorProduct.map (.id R B)
        (Algebra.TensorProduct.includeRight : C →ₐ[R] B ⊗[R] C) (ρ c) := by
  have h := congrArg (fun k => affineTripleChart R B C ≫ k) htrans
  rw [← Category.assoc, affineTripleChart_actionStep,
    ← Category.assoc, affineTripleChart_skipMiddle,
    affineCoactionAction, Category.assoc, Iso.inv_hom_id_assoc,
    Category.assoc, Iso.inv_hom_id_assoc, ← Spec.map_comp, ← Spec.map_comp] at h
  have h' := Spec.map_injective h
  exact congrArg (fun k : CommRingCat.of C ⟶
    CommRingCat.of (B ⊗[R] (B ⊗[R] C)) => k.hom c) h'

/-- The actual action on the affine pullback extracted from an overlap isomorphism. -/
def affineOverlapAction
    (α : Spec (.of (B ⊗[R] C)) ≅ Spec (.of (C ⊗[R] B))) :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))
      (Spec.map (CommRingCat.ofHom (algebraMap R C))) ⟶ Spec (.of C) :=
  (pullbackSpecIso R B C).hom ≫ α.hom ≫
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft :
      C →ₐ[R] C ⊗[R] B).toRingHom)

end Coaction

/-- Its coordinate-ring map is the coaction extracted from the overlap algebra equivalence. -/
theorem affineOverlapAction_eq_coaction
    (α : Spec (.of (B ⊗[R] C)) ≅ Spec (.of (C ⊗[R] B)))
    (hα : α.hom ≫ Spec.map (CommRingCat.ofHom (affineOverlapSourceBase R B C).toRingHom) =
      Spec.map (CommRingCat.ofHom (affineOverlapTargetBase R B C).toRingHom)) :
    affineOverlapAction R B C α =
      affineCoactionAction R B C
        ((tensorCoaction R B C (affineOverlapAlgEquiv R B C α hα)).restrictScalars R) := by
  rw [affineOverlapAction, affineCoactionAction]
  congr 1
  rw [← affineOverlapAlgEquiv_spec R B C α hα, ← Spec.map_comp]
  rfl

/-- The extracted geometric action is a morphism over the original base. -/
theorem affineOverlapAction_base
    (α : Spec (.of (B ⊗[R] C)) ≅ Spec (.of (C ⊗[R] B)))
    (hα : α.hom ≫ Spec.map (CommRingCat.ofHom (affineOverlapSourceBase R B C).toRingHom) =
      Spec.map (CommRingCat.ofHom (affineOverlapTargetBase R B C).toRingHom)) :
    affineOverlapAction R B C α ≫ Spec.map (CommRingCat.ofHom (algebraMap R C)) =
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R B)))
        (Spec.map (CommRingCat.ofHom (algebraMap R C))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
  rw [affineOverlapAction_eq_coaction R B C α hα]
  exact affineCoactionAction_base R B C _

/-- The action lands over the first coordinate of the cover, as required by
the usual geometric descent-action interface. -/
theorem affineOverlapAction_coverBase
    (α : Spec (.of (B ⊗[R] C)) ≅ Spec (.of (C ⊗[R] B)))
    (hα : α.hom ≫ Spec.map (CommRingCat.ofHom (affineOverlapSourceBase R B C).toRingHom) =
      Spec.map (CommRingCat.ofHom (affineOverlapTargetBase R B C).toRingHom)) :
    affineOverlapAction R B C α ≫ Spec.map (CommRingCat.ofHom (algebraMap B C)) =
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R B)))
        (Spec.map (CommRingCat.ofHom (algebraMap R C))) := by
  rw [affineOverlapAction_eq_coaction R B C α hα, affineCoactionAction,
    Category.assoc, ← Spec.map_comp]
  have hρ :
      ((tensorCoaction R B C (affineOverlapAlgEquiv R B C α hα)).restrictScalars R).toRingHom.comp
          (algebraMap B C) = algebraMap B (B ⊗[R] C) :=
    RingHom.ext (tensorCoaction R B C (affineOverlapAlgEquiv R B C α hα)).commutes
  change (pullbackSpecIso R B C).hom ≫ Spec.map (CommRingCat.ofHom
    (((tensorCoaction R B C (affineOverlapAlgEquiv R B C α hα)).restrictScalars R).toRingHom.comp
      (algebraMap B C))) = _
  rw [hρ]
  exact pullbackSpecIso_hom_fst' R B C

/-- A genuine geometric action law on the triple pullback supplies the full
algebra cocycle required for effective faithfully flat descent. -/
theorem affineOverlapAlgEquiv_cocycle_of_actionLaw
    (α : Spec (.of (B ⊗[R] C)) ≅ Spec (.of (C ⊗[R] B)))
    (hα : α.hom ≫ Spec.map (CommRingCat.ofHom (affineOverlapSourceBase R B C).toRingHom) =
      Spec.map (CommRingCat.ofHom (affineOverlapTargetBase R B C).toRingHom))
    (htrans :
      pullbackActionStep (Spec.map (CommRingCat.ofHom (algebraMap R B)))
          (Spec.map (CommRingCat.ofHom (algebraMap R C))) (affineOverlapAction R B C α)
          (affineOverlapAction_base R B C α hα) ≫ affineOverlapAction R B C α =
        pullbackSkipMiddle (Spec.map (CommRingCat.ofHom (algebraMap R B)))
          (Spec.map (CommRingCat.ofHom (algebraMap R C))) ≫ affineOverlapAction R B C α) :
    tensorCocycleLeft R B C (affineOverlapAlgEquiv R B C α hα) =
      tensorCocycleRight R B C (affineOverlapAlgEquiv R B C α hα) := by
  apply tensorCocycle_eq_of_coaction_coassoc R B C _
    (affineOverlapAlgEquiv_base R B C α hα)
  intro c
  apply affineCoaction_coassoc_of_actionLaw R B C
    ((tensorCoaction R B C (affineOverlapAlgEquiv R B C α hα)).restrictScalars R) _ c
  simpa only [affineOverlapAction_eq_coaction R B C α hα] using htrans

end Algebra.Descent
