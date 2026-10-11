/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Gluing.RelativeOverlap
import Nyll.SchemeTheory.Descent.AffineTransitionOverEquality

/-!
# Actual gluing relations at a common inverse-system stage

Recovered chart maps prove the diagonal and triple equations after the
actual limit projection. Eventual equality then proves all of these
relations at one common original stage. Limit projections need not be
faithful, flat, or surjective.
-/

noncomputable section

universe u

open CategoryTheory Limits
open AlgebraicGeometry.Scheme.Cover

namespace AlgebraicGeometry.FiniteEtale

/-- All diagonal and triple gluing relations descend together from actual
recovered local charts to one later stage. -/
theorem exists_inverse_limit_stage_gluing_relations
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (h : i ⟶ j), IsAffineHom (D.map h)]
    [∀ i : I, CompactSpace (D.obj i)]
    (i : I) (𝒰 : (D.obj i).OpenCover) [Finite 𝒰.I₀]
    (A : 𝒰.I₀ → Over (D.obj i)) (V : 𝒰.I₀ × 𝒰.I₀ → Over (D.obj i))
    (d : ∀ a b : 𝒰.I₀, V (a, b) ⟶ A a)
    (y : ∀ a : 𝒰.I₀, (A a).left ⟶ 𝒰.X a)
    (ℓ : ∀ a b : 𝒰.I₀, (V (a, b)).left ⟶ 𝒰.X b)
    (hV : ∀ a b : 𝒰.I₀,
      IsPullback (d a b).left (ℓ a b) (y a ≫ 𝒰.f a) (𝒰.f b))
    (t : ∀ a b : 𝒰.I₀, V (a, b) ⟶ V (b, a))
    (ht : ∀ a b : 𝒰.I₀, (t a b).left ≫ (d b a).left ≫ y b = ℓ a b)
    [∀ a : 𝒰.I₀, QuasiCompact (V (a, a)).hom]
    [∀ a : 𝒰.I₀, LocallyOfFiniteType (V (a, a)).hom]
    [∀ a b d' : 𝒰.I₀, QuasiCompact (relativeTriple 𝒰 A V d a b d').hom]
    [∀ a b d' : 𝒰.I₀, LocallyOfFiniteType (relativeTriple 𝒰 A V d a b d').hom]
    (Z : Scheme.{u})
    (h : ∀ a : 𝒰.I₀, (relativeRecoveryFunctor (c.π.app i)).obj (A a) ⟶ Z)
    [hmono : ∀ a : 𝒰.I₀, Mono (h a)]
    (hrec : ∀ a b : 𝒰.I₀,
      (relativeRecoveryFunctor (c.π.app i)).map (t a b) ≫
          (relativeRecoveryFunctor (c.π.app i)).map (d b a) ≫ h b =
        (relativeRecoveryFunctor (c.π.app i)).map (d a b) ≫ h a) :
    ∃ (j : I) (hji : j ⟶ i),
      (∀ a : 𝒰.I₀, (Over.pullback (D.map hji)).map (t a a) =
        𝟙 ((Over.pullback (D.map hji)).obj (V (a, a)))) ∧
      (∀ a b d' : 𝒰.I₀,
        (Over.pullback (D.map hji)).map
            (relativeTripleTransition 𝒰 A V d y ℓ hV t ht a b d' ≫
              relativeTripleTransition 𝒰 A V d y ℓ hV t ht b d' a ≫
                relativeTripleTransition 𝒰 A V d y ℓ hV t ht d' a b) =
          𝟙 ((Over.pullback (D.map hji)).obj (relativeTriple 𝒰 A V d a b d'))) := by
  let K := Sum 𝒰.I₀ (𝒰.I₀ × 𝒰.I₀ × 𝒰.I₀)
  let E : K → Over (D.obj i)
    | Sum.inl a => V (a, a)
    | Sum.inr (a, b, d') => relativeTriple 𝒰 A V d a b d'
  let m : ∀ k : K, E k ⟶ E k
    | Sum.inl a => t a a
    | Sum.inr (a, b, d') =>
      relativeTripleTransition 𝒰 A V d y ℓ hV t ht a b d' ≫
        relativeTripleTransition 𝒰 A V d y ℓ hV t ht b d' a ≫
          relativeTripleTransition 𝒰 A V d y ℓ hV t ht d' a b
  have : ∀ k : K, QuasiCompact (E k).hom := by
    intro k
    cases k with
    | inl a => exact inferInstanceAs (QuasiCompact (V (a, a)).hom)
    | inr q => exact inferInstanceAs
        (QuasiCompact (relativeTriple 𝒰 A V d q.1 q.2.1 q.2.2).hom)
  have : ∀ k : K, LocallyOfFiniteType (E k).hom := by
    intro k
    cases k with
    | inl a => exact inferInstanceAs (LocallyOfFiniteType (V (a, a)).hom)
    | inr q => exact inferInstanceAs
        (LocallyOfFiniteType (relativeTriple 𝒰 A V d q.1 q.2.1 q.2.2).hom)
  have hm : ∀ k : K, (Over.pullback (c.π.app i)).map (m k) =
      (Over.pullback (c.π.app i)).map (𝟙 (E k)) := by
    intro k
    apply Over.OverMorphism.ext
    cases k with
    | inl a =>
      exact relativeRecoveredTransition_id 𝒰 A V d y ℓ hV t (c.π.app i) h hrec a
    | inr q =>
      exact relativeRecoveredTripleTransition_cocycle
        𝒰 A V d y ℓ hV t ht (c.π.app i) h hrec q.1 q.2.1 q.2.2
  obtain ⟨j, hji, hj⟩ := AffineTransitionHom.exists_over_map_eq_later_stage_family
    D c hc i E E m (fun k ↦ 𝟙 (E k)) hm
  refine ⟨j, hji, ?_, ?_⟩
  · intro a
    exact (hj (Sum.inl a)).trans ((Over.pullback (D.map hji)).map_id (V (a, a)))
  · intro a b d'
    exact (hj (Sum.inr (a, b, d'))).trans
      ((Over.pullback (D.map hji)).map_id (relativeTriple 𝒰 A V d a b d'))

end AlgebraicGeometry.FiniteEtale
