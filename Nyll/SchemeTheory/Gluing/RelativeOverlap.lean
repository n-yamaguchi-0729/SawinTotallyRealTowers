/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.AlgebraicGeometry.Cover.Open

/-!
# Recovered relative-overlap equations

Actual cartesian pairwise overlaps produce triple transition maps. After
an arbitrary base change, monic recovered chart maps prove the diagonal
and triple equations. No faithfulness or surjectivity of the base change
is used: these equations can subsequently be descended to a later stage.
-/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Cover

variable {B S : Scheme.{u}} (𝒰 : S.OpenCover)
variable (A : 𝒰.I₀ → Over B) (V : 𝒰.I₀ × 𝒰.I₀ → Over B)
variable (d : ∀ i j : 𝒰.I₀, V (i, j) ⟶ A i)
variable (y : ∀ i : 𝒰.I₀, (A i).left ⟶ 𝒰.X i)
variable (ℓ : ∀ i j : 𝒰.I₀, (V (i, j)).left ⟶ 𝒰.X j)
variable (hV : ∀ i j : 𝒰.I₀, IsPullback (d i j).left (ℓ i j) (y i ≫ 𝒰.f i) (𝒰.f j))

include hV in
theorem relativeOverlapInclusion_isOpenImmersion (i j : 𝒰.I₀) : IsOpenImmersion (d i j).left :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) (hV i j).flip inferInstance

include hV in
theorem relativeOverlapInclusion_mono (i j : 𝒰.I₀) : Mono (d i j) := by
  have : IsOpenImmersion (d i j).left := relativeOverlapInclusion_isOpenImmersion 𝒰 A V d y ℓ hV i j
  apply (Over.forget B).mono_of_mono_map
  exact inferInstanceAs (Mono (d i j).left)

include hV in
theorem relativeOverlapInclusion_isIso (i : 𝒰.I₀) : IsIso (d i i) := by
  have : IsIso ((Over.forget B).map (d i i)) := by
    change IsIso (d i i).left
    rw [← (hV i i).isoPullback_hom_fst]
    infer_instance
  exact isIso_of_reflects_iso (d i i) (Over.forget B)

variable (t : ∀ i j : 𝒰.I₀, V (i, j) ⟶ V (j, i))
variable (ht : ∀ i j : 𝒰.I₀, (t i j).left ≫ (d j i).left ≫ y j = ℓ i j)

include hV in
/-- Preservation of the base gives the other chart structure equation. -/
theorem relativeOverlapTransition_structure
    (hS : ∀ i j : 𝒰.I₀, (t i j).left ≫ (d j i).left ≫ y j ≫ 𝒰.f j =
      (d i j).left ≫ y i ≫ 𝒰.f i) (i j : 𝒰.I₀) :
    (t i j).left ≫ (d j i).left ≫ y j = ℓ i j := by
  apply (cancel_mono (𝒰.f j)).mp
  rw [Category.assoc, Category.assoc, hS]
  exact (hV i j).w

/-- The actual intersection of two overlap objects inside their first chart. -/
abbrev relativeTriple (i j k : 𝒰.I₀) : Over B :=
  pullback (d i j) (d i k)

/-- The map from a triple intersection to the next pairwise overlap. -/
def relativeTripleToOverlap (i j k : 𝒰.I₀) :
    relativeTriple 𝒰 A V d i j k ⟶ V (j, k) := by
  let r := (pullback.fst (d i j) (d i k)).left
  let s := (pullback.snd (d i j) (d i k)).left
  have hrs : r ≫ (d i j).left = s ≫ (d i k).left :=
    congrArg (fun q => (Over.forget B).map q) pullback.condition
  let g : (relativeTriple 𝒰 A V d i j k).left ⟶ (V (j, k)).left :=
    (hV j k).lift (r ≫ (t i j).left ≫ (d j i).left) (s ≫ ℓ i k)
      (by
        calc
          (r ≫ (t i j).left ≫ (d j i).left) ≫ (y j ≫ 𝒰.f j) =
              r ≫ ℓ i j ≫ 𝒰.f j := by
            simpa only [Category.assoc] using
              congrArg (fun q => r ≫ q ≫ 𝒰.f j) (ht i j)
          _ = (r ≫ (d i j).left) ≫ (y i ≫ 𝒰.f i) := by
            rw [Category.assoc, (hV i j).w]
          _ = (s ≫ (d i k).left) ≫ (y i ≫ 𝒰.f i) :=
            congrArg (fun q => q ≫ (y i ≫ 𝒰.f i)) hrs
          _ = (s ≫ ℓ i k) ≫ 𝒰.f k := by
            rw [Category.assoc, (hV i k).w, Category.assoc])
  refine Over.homMk g ?_
  rw [← Over.w (d j k), ← Category.assoc]
  dsimp only [g]
  rw [(hV j k).lift_fst]
  simp only [Category.assoc, Over.w]
  exact Over.w (pullback.fst (d i j) (d i k))

/-- The cyclic transition between actual triple intersection objects. -/
def relativeTripleTransition (i j k : 𝒰.I₀) :
    relativeTriple 𝒰 A V d i j k ⟶ relativeTriple 𝒰 A V d j k i :=
  pullback.lift
    (relativeTripleToOverlap 𝒰 A V d y ℓ hV t ht i j k)
    (pullback.fst _ _ ≫ t i j)
    (by
      apply Over.OverMorphism.ext
      exact (hV j k).lift_fst _ _ _)

theorem relativeTripleTransition_fac (i j k : 𝒰.I₀) :
    relativeTripleTransition 𝒰 A V d y ℓ hV t ht i j k ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ t i j :=
  pullback.lift_snd _ _ _

variable {B' Z : Scheme.{u}} (ψ : B' ⟶ B)

/-- Base change followed by forgetting the structure morphism. -/
abbrev relativeRecoveryFunctor : Over B ⥤ Scheme.{u} :=
  Over.pullback ψ ⋙ Over.forget B'

variable (h : ∀ i : 𝒰.I₀, (relativeRecoveryFunctor ψ).obj (A i) ⟶ Z)
variable [∀ i : 𝒰.I₀, Mono (h i)]
variable (hrec : ∀ i j : 𝒰.I₀,
  (relativeRecoveryFunctor ψ).map (t i j) ≫
      (relativeRecoveryFunctor ψ).map (d j i) ≫ h j =
    (relativeRecoveryFunctor ψ).map (d i j) ≫ h i)

include hV hrec in
/-- The diagonal transition is the identity after the actual recovering
base change. No equality-reflection hypothesis is needed. -/
theorem relativeRecoveredTransition_id (i : 𝒰.I₀) :
    (relativeRecoveryFunctor ψ).map (t i i) =
      (relativeRecoveryFunctor ψ).map (𝟙 (V (i, i))) := by
  have : IsIso (d i i) := relativeOverlapInclusion_isIso 𝒰 A V d y ℓ hV i
  apply (cancel_mono ((relativeRecoveryFunctor ψ).map (d i i) ≫ h i)).mp
  rw [(relativeRecoveryFunctor ψ).map_id, Category.id_comp]
  exact hrec i i

omit [∀ i : 𝒰.I₀, Mono (h i)] in
include hrec in
/-- The recovered triple transition preserves its actual chart map. -/
theorem relativeRecoveredTripleTransition_chartMap (i j k : 𝒰.I₀) :
    (relativeRecoveryFunctor ψ).map (relativeTripleTransition 𝒰 A V d y ℓ hV t ht i j k) ≫
      (relativeRecoveryFunctor ψ).map (pullback.fst _ _) ≫
        (relativeRecoveryFunctor ψ).map (d j k) ≫ h j =
    (relativeRecoveryFunctor ψ).map (pullback.fst _ _) ≫
      (relativeRecoveryFunctor ψ).map (d i j) ≫ h i := by
  let K := relativeRecoveryFunctor ψ
  have hw : K.map (pullback.fst (d j k) (d j i)) ≫ K.map (d j k) =
      K.map (pullback.snd (d j k) (d j i)) ≫ K.map (d j i) := by
    rw [← K.map_comp, ← K.map_comp, pullback.condition]
  change K.map _ ≫ K.map _ ≫ K.map _ ≫ h j = K.map _ ≫ K.map _ ≫ h i
  rw [reassoc_of% hw, ← Category.assoc
      (K.map (relativeTripleTransition 𝒰 A V d y ℓ hV t ht i j k)),
    ← K.map_comp, relativeTripleTransition_fac, K.map_comp, Category.assoc, hrec]

include hV hrec in
/-- The actual triple cocycle holds after recovering the local charts.
This is the equation to descend eventually, not an assumption of faithful
pullback at the current stage. -/
theorem relativeRecoveredTripleTransition_cocycle (i j k : 𝒰.I₀) :
    (relativeRecoveryFunctor ψ).map
        (relativeTripleTransition 𝒰 A V d y ℓ hV t ht i j k ≫
          relativeTripleTransition 𝒰 A V d y ℓ hV t ht j k i ≫
            relativeTripleTransition 𝒰 A V d y ℓ hV t ht k i j) =
      (relativeRecoveryFunctor ψ).map (𝟙 (relativeTriple 𝒰 A V d i j k)) := by
  have : Mono (d i j) := relativeOverlapInclusion_mono 𝒰 A V d y ℓ hV i j
  have : Mono (d i k) := relativeOverlapInclusion_mono 𝒰 A V d y ℓ hV i k
  let K := relativeRecoveryFunctor ψ
  apply (cancel_mono (K.map (pullback.fst (d i j) (d i k)) ≫ K.map (d i j) ≫ h i)).mp
  simp only [Functor.map_comp, Category.assoc]
  rw [relativeRecoveredTripleTransition_chartMap 𝒰 A V d y ℓ hV t ht ψ h hrec k i j,
    relativeRecoveredTripleTransition_chartMap 𝒰 A V d y ℓ hV t ht ψ h hrec j k i,
    relativeRecoveredTripleTransition_chartMap 𝒰 A V d y ℓ hV t ht ψ h hrec i j k,
    K.map_id, Category.id_comp]

end AlgebraicGeometry.Scheme.Cover
