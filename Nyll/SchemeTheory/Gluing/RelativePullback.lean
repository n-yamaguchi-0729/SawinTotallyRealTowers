/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Gluing.RelativeOverlap
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
# Scheme gluing after actual pullback equations

Once the diagonal and triple relations have been proved after a base
change, the transported cartesian overlap maps form actual scheme gluing
data. The triple comparison construction adapts `GlueData.mapGlueData`:
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/CategoryTheory/GlueData.lean

The inverse-limit consumer supplies both relations using actual eventual
equality, with no equality-reflection assumption on the limit projection.
-/

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Cover

/-- The native pullback of a morphism over the base is cartesian over its
original underlying morphism. -/
theorem relativePullback_map_isPullback
    {B B' : Scheme.{u}} (ψ : B' ⟶ B) {A C : Over B} (m : A ⟶ C) :
    IsPullback ((Over.pullback ψ).map m).left (pullback.fst A.hom ψ)
      (pullback.fst C.hom ψ) m.left := by
  refine IsPullback.of_right ?_ ?_ (IsPullback.of_hasPullback C.hom ψ).flip
  · have h₁ : ((Over.pullback ψ).map m).left ≫ pullback.snd C.hom ψ =
        pullback.snd A.hom ψ := ((Over.pullback ψ).map m).w
    have h₂ : m.left ≫ C.hom = A.hom := m.w
    rw [h₁, h₂]
    exact (IsPullback.of_hasPullback A.hom ψ).flip
  · exact pullback.lift_fst _ _ _

variable {B S B' : Scheme.{u}} (𝒰 : S.OpenCover)
variable (A : 𝒰.I₀ → Over B) (V : 𝒰.I₀ × 𝒰.I₀ → Over B)
variable (d : ∀ i j : 𝒰.I₀, V (i, j) ⟶ A i)
variable (y : ∀ i : 𝒰.I₀, (A i).left ⟶ 𝒰.X i)
variable (ℓ : ∀ i j : 𝒰.I₀, (V (i, j)).left ⟶ 𝒰.X j)
variable (hV : ∀ i j : 𝒰.I₀, IsPullback (d i j).left (ℓ i j) (y i ≫ 𝒰.f i) (𝒰.f j))
variable (t : ∀ i j : 𝒰.I₀, V (i, j) ⟶ V (j, i))
variable (ht : ∀ i j : 𝒰.I₀, (t i j).left ≫ (d j i).left ≫ y j = ℓ i j)
variable (ψ : B' ⟶ B)
variable (hdiag : ∀ i : 𝒰.I₀,
  (Over.pullback ψ).map (t i i) = 𝟙 ((Over.pullback ψ).obj (V (i, i))))
variable (hcycle : ∀ i j k : 𝒰.I₀,
  (Over.pullback ψ).map
      (relativeTripleTransition 𝒰 A V d y ℓ hV t ht i j k ≫
        relativeTripleTransition 𝒰 A V d y ℓ hV t ht j k i ≫
          relativeTripleTransition 𝒰 A V d y ℓ hV t ht k i j) =
    𝟙 ((Over.pullback ψ).obj (relativeTriple 𝒰 A V d i j k)))

/-- Actual relative gluing data after the diagonal and triple equations
have been established by pullback. -/
def relativeGlueDataOfPullbackEquations : Scheme.GlueData.{u} := by
  let F : Over B ⥤ Scheme.{u} := relativeRecoveryFunctor ψ
  have : ∀ i j : 𝒰.I₀, Mono (d i j) :=
    relativeOverlapInclusion_mono 𝒰 A V d y ℓ hV
  have : ∀ i : 𝒰.I₀, IsIso (d i i) :=
    relativeOverlapInclusion_isIso 𝒰 A V d y ℓ hV
  have hopen (i j : 𝒰.I₀) : IsOpenImmersion (F.map (d i j)) := by
    have : IsOpenImmersion (d i j).left :=
      relativeOverlapInclusion_isOpenImmersion 𝒰 A V d y ℓ hV i j
    exact MorphismProperty.of_isPullback (P := @IsOpenImmersion)
      (relativePullback_map_isPullback ψ (d i j)).flip inferInstance
  have hd (i : 𝒰.I₀) : F.map (t i i) = 𝟙 (F.obj (V (i, i))) :=
    congrArg (fun m ↦ (Over.forget B').map m) (hdiag i)
  have hc (i j k : 𝒰.I₀) :
      F.map (relativeTripleTransition 𝒰 A V d y ℓ hV t ht i j k ≫
        relativeTripleTransition 𝒰 A V d y ℓ hV t ht j k i ≫
          relativeTripleTransition 𝒰 A V d y ℓ hV t ht k i j) =
        𝟙 (F.obj (relativeTriple 𝒰 A V d i j k)) :=
    congrArg (fun m ↦ (Over.forget B').map m) (hcycle i j k)
  exact
    { J := 𝒰.I₀
      U := fun i ↦ F.obj (A i)
      V := fun ij ↦ F.obj (V ij)
      f := fun i j ↦ F.map (d i j)
      f_mono := fun i j ↦ preserves_mono_of_preservesLimit F (d i j)
      f_id := fun i ↦ inferInstanceAs (IsIso (F.map (d i i)))
      t := fun i j ↦ F.map (t i j)
      t_id := hd
      t' := fun i j k ↦
        (PreservesPullback.iso F (d i j) (d i k)).inv ≫
          F.map (relativeTripleTransition 𝒰 A V d y ℓ hV t ht i j k) ≫
            (PreservesPullback.iso F (d j k) (d j i)).hom
      t_fac := by
        intro i j k
        rw [Category.assoc, Category.assoc, PreservesPullback.iso_hom_snd,
          ← F.map_comp, relativeTripleTransition_fac, F.map_comp,
          ← Category.assoc, PreservesPullback.iso_inv_fst]
      cocycle := by
        intro i j k
        simp only [Category.assoc, Iso.hom_inv_id_assoc,
          ← CategoryTheory.Functor.map_comp_assoc, hc, Category.id_comp, Iso.inv_hom_id]
      f_open := hopen }

/-- The glued charts are the actual pullbacks of the original local models. -/
theorem relativeGlueDataOfPullbackEquations_U (i : 𝒰.I₀) :
    (relativeGlueDataOfPullbackEquations 𝒰 A V d y ℓ hV t ht ψ hdiag hcycle).U i =
      (relativeRecoveryFunctor ψ).obj (A i) := rfl

/-- The glued overlap inclusions are the actual pulled-back inclusions. -/
theorem relativeGlueDataOfPullbackEquations_f (i j : 𝒰.I₀) :
    (relativeGlueDataOfPullbackEquations 𝒰 A V d y ℓ hV t ht ψ hdiag hcycle).f i j =
      (relativeRecoveryFunctor ψ).map (d i j) := rfl

/-- The glued transition maps are the actual pulled-back transitions. -/
theorem relativeGlueDataOfPullbackEquations_t (i j : 𝒰.I₀) :
    (relativeGlueDataOfPullbackEquations 𝒰 A V d y ℓ hV t ht ψ hdiag hcycle).t i j =
      (relativeRecoveryFunctor ψ).map (t i j) := rfl

end AlgebraicGeometry.Scheme.Cover
