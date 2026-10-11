/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.Sites.BigZariski
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Over

/-!
# Detecting sheaf isomorphisms on an open cover of the base

A morphism of sheaves on schemes over `S` is an isomorphism if its components
are bijective on every scheme over a member of an open cover of `S`.
Pulling that cover back to each test scheme supplies the covering sieves
needed for local injectivity and local surjectivity.
-/


@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

universe u v w

namespace SchemeTheory.WeilRestriction

variable {S : Scheme.{u}} (𝒰 : Scheme.OpenCover.{v} S)

/-- A member of the pullback cover, viewed as a scheme over the original base. -/
def baseCoverPullbackObject (T : Over S) (i : 𝒰.I₀) : Over S :=
  (Over.map (𝒰.f i)).obj (Over.mk (pullback.snd T.hom (𝒰.f i)))

/-- The projection from a member of the pullback cover to the test scheme. -/
def baseCoverPullbackMap (T : Over S) (i : 𝒰.I₀) :
    baseCoverPullbackObject 𝒰 T i ⟶ T :=
  Over.homMk (pullback.fst T.hom (𝒰.f i)) pullback.condition

/-- The pullback cover is covering for the induced Zariski topology on `Over S`. -/
lemma baseCoverPullbackSieve_mem (T : Over S) :
    Sieve.ofArrows (baseCoverPullbackObject 𝒰 T) (baseCoverPullbackMap 𝒰 T) ∈
      (Scheme.zariskiTopology.over S) T := by
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  exact Scheme.Cover.mem_grothendieckTopology
    (P := (@IsOpenImmersion : MorphismProperty Scheme.{u})) (𝒰.pullback₁ T.hom)

/-- Bijectivity after restricting to every member of a base cover detects
isomorphisms between sheaves on the relative big Zariski site. -/
lemma isIso_of_bijective_on_openCover
    {F G : Sheaf (Scheme.zariskiTopology.over S) (Type w)} (η : F ⟶ G)
    (h : ∀ (i : 𝒰.I₀) (T : Over (𝒰.X i)),
      Function.Bijective (η.hom.app (op ((Over.map (𝒰.f i)).obj T)))) :
    IsIso η := by
  have hInjective : Presheaf.IsLocallyInjective (Scheme.zariskiTopology.over S) η.hom := by
    refine ⟨?_⟩
    intro T x y hxy
    apply (Scheme.zariskiTopology.over S).superset_covering ?_
      (baseCoverPullbackSieve_mem 𝒰 T.unop)
    rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    intro i
    change F.obj.map (baseCoverPullbackMap 𝒰 T.unop i).op x =
      F.obj.map (baseCoverPullbackMap 𝒰 T.unop i).op y
    apply (h i (Over.mk (pullback.snd T.unop.hom (𝒰.f i)))).injective
    change η.hom.app (op (baseCoverPullbackObject 𝒰 T.unop i))
        (F.obj.map (baseCoverPullbackMap 𝒰 T.unop i).op x) =
      η.hom.app (op (baseCoverPullbackObject 𝒰 T.unop i))
        (F.obj.map (baseCoverPullbackMap 𝒰 T.unop i).op y)
    rw [η.hom.naturality_apply, η.hom.naturality_apply, hxy]
  have hSurjective : Presheaf.IsLocallySurjective (Scheme.zariskiTopology.over S) η.hom := by
    refine ⟨?_⟩
    intro T s
    apply (Scheme.zariskiTopology.over S).superset_covering ?_
      (baseCoverPullbackSieve_mem 𝒰 T)
    rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    intro i
    exact (h i (Over.mk (pullback.snd T.hom (𝒰.f i)))).surjective
      (G.obj.map (baseCoverPullbackMap 𝒰 T i).op s)
  exact (Sheaf.isLocallyBijective_iff_isIso η).mp ⟨hInjective, hSurjective⟩

end SchemeTheory.WeilRestriction
