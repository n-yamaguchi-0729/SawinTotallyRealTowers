/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# Actual pullback comparisons for a cone in an over category

The comparison is built from the chosen scheme pullbacks.  Its components
preserve both projections, and their naturality is proved by those projections.
No limiting or cofilteredness hypothesis is needed.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AffineTransitionHom

variable {I : Type u} [Category.{u} I] {S : Scheme.{u}}
variable (D : I ⥤ Over S) (c : Cone D)

/-- The actual map from a pulled-back model at the cone point to its original
stage pullback, preserving the model coordinate and the cone leg. -/
def overInverseLimitTransition (A : Over S) (i : I) :
    pullback A.hom c.pt.hom ⟶ pullback A.hom (D.obj i).hom :=
  pullback.lift (pullback.fst A.hom c.pt.hom)
    (pullback.snd A.hom c.pt.hom ≫ (c.π.app i).left)
    (by
      rw [Category.assoc, Over.w (c.π.app i)]
      exact pullback.condition)

/-- The transition preserves the original model projection. -/
theorem overInverseLimitTransition_fst (A : Over S) (i : I) :
    overInverseLimitTransition D c A i ≫ pullback.fst A.hom (D.obj i).hom =
      pullback.fst A.hom c.pt.hom :=
  pullback.lift_fst _ _ _

/-- The transition's coefficient projection is the original cone leg. -/
theorem overInverseLimitTransition_snd (A : Over S) (i : I) :
    overInverseLimitTransition D c A i ≫ pullback.snd A.hom (D.obj i).hom =
      pullback.snd A.hom c.pt.hom ≫ (c.π.app i).left :=
  pullback.lift_snd _ _ _

private def overInverseLimitComponent (A : Over S) (i : I) :
    pullback A.hom c.pt.hom ≅
      pullback (pullback.snd A.hom (D.obj i).hom) (c.π.app i).left :=
  pullback.congrHom (rfl : A.hom = A.hom) (Over.w (c.π.app i)).symm ≪≫
    (pullbackLeftPullbackSndIso A.hom (D.obj i).hom (c.π.app i).left).symm

private theorem overInverseLimitComponent_hom_fst_fst (A : Over S) (i : I) :
    (overInverseLimitComponent D c A i).hom ≫
        pullback.fst (pullback.snd A.hom (D.obj i).hom) (c.π.app i).left ≫
        pullback.fst A.hom (D.obj i).hom = pullback.fst A.hom c.pt.hom := by
  rw [overInverseLimitComponent, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    pullbackLeftPullbackSndIso_inv_fst, pullback.congrHom_hom,
    pullback.lift_fst, Category.comp_id]
  rfl

private theorem overInverseLimitComponent_hom_snd (A : Over S) (i : I) :
    (overInverseLimitComponent D c A i).hom ≫
        pullback.snd (pullback.snd A.hom (D.obj i).hom) (c.π.app i).left =
      pullback.snd A.hom c.pt.hom := by
  rw [overInverseLimitComponent, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    pullbackLeftPullbackSndIso_inv_snd_snd, pullback.congrHom_hom,
    pullback.lift_snd, Category.comp_id]
  rfl

private theorem overInverseLimitComponent_hom_fst (A : Over S) (i : I) :
    (overInverseLimitComponent D c A i).hom ≫
        pullback.fst (pullback.snd A.hom (D.obj i).hom) (c.π.app i).left =
      overInverseLimitTransition D c A i := by
  apply pullback.hom_ext
  · rw [Category.assoc, overInverseLimitComponent_hom_fst_fst,
      overInverseLimitTransition_fst]
  · rw [Category.assoc, pullback.condition, ← Category.assoc,
      overInverseLimitComponent_hom_snd, overInverseLimitTransition_snd]

private theorem overInverseLimitTransition_naturality
    {A B : Over S} (f : A ⟶ B) (i : I) :
    ((Over.pullback c.pt.hom).map f).left ≫ overInverseLimitTransition D c B i =
      overInverseLimitTransition D c A i ≫ ((Over.pullback (D.obj i).hom).map f).left := by
  apply pullback.hom_ext
  · simp only [Category.assoc, overInverseLimitTransition_fst, Over.pullback_map_left,
      pullback.lift_fst]
    rw [← Category.assoc, overInverseLimitTransition_fst]
  · simp only [Category.assoc, overInverseLimitTransition_snd, Over.pullback_map_left,
      pullback.lift_snd]
    rw [← Category.assoc, pullback.lift_snd]

/-- The native comparison between pulling back directly to the cone point
and pulling back through an original stage. -/
def overInverseLimitPullbackComparison (i : I) :
    Over.pullback c.pt.hom ≅
      Over.pullback (D.obj i).hom ⋙ Over.pullback (c.π.app i).left :=
  NatIso.ofComponents
    (fun A ↦ Over.isoMk (overInverseLimitComponent D c A i)
      (overInverseLimitComponent_hom_snd D c A i))
    (fun {A B} f ↦ by
      apply Over.OverMorphism.ext
      change ((Over.pullback c.pt.hom).map f).left ≫
          (overInverseLimitComponent D c B i).hom =
        (overInverseLimitComponent D c A i).hom ≫
          ((Over.pullback (c.π.app i).left).map
            ((Over.pullback (D.obj i).hom).map f)).left
      have hfst : ((Over.pullback (c.π.app i).left).map
          ((Over.pullback (D.obj i).hom).map f)).left ≫
          pullback.fst (pullback.snd B.hom (D.obj i).hom) (c.π.app i).left =
        pullback.fst (pullback.snd A.hom (D.obj i).hom) (c.π.app i).left ≫
          ((Over.pullback (D.obj i).hom).map f).left := pullback.lift_fst _ _ _
      have hsnd : ((Over.pullback (c.π.app i).left).map
          ((Over.pullback (D.obj i).hom).map f)).left ≫
          pullback.snd (pullback.snd B.hom (D.obj i).hom) (c.π.app i).left =
        pullback.snd (pullback.snd A.hom (D.obj i).hom) (c.π.app i).left :=
        Over.w ((Over.pullback (c.π.app i).left).map
          ((Over.pullback (D.obj i).hom).map f))
      apply pullback.hom_ext
      · rw [Category.assoc, overInverseLimitComponent_hom_fst,
          Category.assoc, hfst, ← Category.assoc, overInverseLimitComponent_hom_fst]
        exact overInverseLimitTransition_naturality D c f i
      · rw [Category.assoc, overInverseLimitComponent_hom_snd,
          Category.assoc, hsnd, overInverseLimitComponent_hom_snd]
        exact Over.w ((Over.pullback c.pt.hom).map f))

/-- The forward comparison's first projection is the actual scheme
transition used in raw model recovery. -/
theorem overInverseLimitPullbackComparison_hom_fst (A : Over S) (i : I) :
    ((overInverseLimitPullbackComparison D c i).hom.app A).left ≫
        pullback.fst (pullback.snd A.hom (D.obj i).hom) (c.π.app i).left =
      overInverseLimitTransition D c A i :=
  overInverseLimitComponent_hom_fst D c A i

/-- The forward comparison preserves the projection to the cone point. -/
theorem overInverseLimitPullbackComparison_hom_snd (A : Over S) (i : I) :
    ((overInverseLimitPullbackComparison D c i).hom.app A).left ≫
        pullback.snd (pullback.snd A.hom (D.obj i).hom) (c.π.app i).left =
      pullback.snd A.hom c.pt.hom :=
  overInverseLimitComponent_hom_snd D c A i

/-- The inverse comparison preserves the original model coordinate. -/
theorem overInverseLimitPullbackComparison_inv_fst (A : Over S) (i : I) :
    ((overInverseLimitPullbackComparison D c i).inv.app A).left ≫
        pullback.fst A.hom c.pt.hom =
      pullback.fst (pullback.snd A.hom (D.obj i).hom) (c.π.app i).left ≫
        pullback.fst A.hom (D.obj i).hom := by
  let e := overInverseLimitComponent D c A i
  change e.inv ≫ pullback.fst A.hom c.pt.hom = _
  apply (cancel_epi e.hom).1
  rw [Iso.hom_inv_id_assoc]
  exact (overInverseLimitComponent_hom_fst_fst D c A i).symm

/-- The inverse comparison preserves the coefficient coordinate. -/
theorem overInverseLimitPullbackComparison_inv_snd (A : Over S) (i : I) :
    ((overInverseLimitPullbackComparison D c i).inv.app A).left ≫
        pullback.snd A.hom c.pt.hom =
      pullback.snd (pullback.snd A.hom (D.obj i).hom) (c.π.app i).left := by
  let e := overInverseLimitComponent D c A i
  change e.inv ≫ pullback.snd A.hom c.pt.hom = _
  apply (cancel_epi e.hom).1
  rw [Iso.hom_inv_id_assoc]
  exact (overInverseLimitComponent_hom_snd D c A i).symm

end AlgebraicGeometry.AffineTransitionHom
