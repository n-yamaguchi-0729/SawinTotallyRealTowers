/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.AlgebraicGeometry.Cover.Directed
public import Mathlib.AlgebraicGeometry.Sites.BigZariski
public import Mathlib.CategoryTheory.Sites.Hypercover.One
public import Mathlib.CategoryTheory.Sites.Over

/-!
# A relative hypercover from a locally directed open cover

The common lower indices of a locally directed open cover give a cover of
each pairwise intersection. They therefore define a `1`-hypercover, also
in the category of schemes over a fixed base.

The relative construction accepts chosen structure maps on the cover
components. Thus its objects can agree definitionally with local objects
already in use. The zero indices are universe-lifted so that no smallness
assumption on the category of cover indices is required.
-/


@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u v w

namespace SchemeTheory.WeilRestriction

variable {X S : Scheme.{u}} (𝒰 : Scheme.OpenCover.{w} X)
  [Category.{v} 𝒰.I₀] [𝒰.LocallyDirected]

/-- The pre-hypercover of a locally directed open cover with common lower indices as overlaps. -/
def locallyDirectedCoverPreHypercover : PreOneHypercover.{max v w} X where
  I₀ := ULift.{v} 𝒰.I₀
  X i := 𝒰.X i.down
  f i := 𝒰.f i.down
  I₁ i j := Σ k : 𝒰.I₀, (k ⟶ i.down) × (k ⟶ j.down)
  Y {_ _} k := 𝒰.X k.1
  p₁ {_ _} k := 𝒰.trans k.2.1
  p₂ {_ _} k := 𝒰.trans k.2.2
  w {_ _} k := by rw [Scheme.Cover.trans_map, Scheme.Cover.trans_map]

lemma locallyDirectedCoverPreHypercover_mem₀ :
    (locallyDirectedCoverPreHypercover 𝒰).sieve₀ ∈ Scheme.zariskiTopology X := by
  have h : (locallyDirectedCoverPreHypercover 𝒰).presieve₀ = 𝒰.presieve₀ :=
    Presieve.ofArrows_comp_eq_of_surjective 𝒰.f
      (a := fun i : ULift.{v} 𝒰.I₀ => i.down)
      (fun i => ⟨ULift.up i, rfl⟩)
  change Sieve.generate (locallyDirectedCoverPreHypercover 𝒰).presieve₀ ∈
    Scheme.zariskiTopology X
  rw [h]
  exact 𝒰.mem_grothendieckTopology

/-- The hypercover whose overlap components are indexed by common lower indices. -/
def locallyDirectedCoverHypercover :
    GrothendieckTopology.OneHypercover.{max v w} Scheme.zariskiTopology X :=
  GrothendieckTopology.OneHypercover.mk'
    (locallyDirectedCoverPreHypercover 𝒰)
    (locallyDirectedCoverPreHypercover_mem₀ 𝒰)
    (fun i j => (𝒰.intersectionOfLocallyDirected i.down j.down).mem_grothendieckTopology)

variable (f : X ⟶ S) (g : ∀ i : 𝒰.I₀, 𝒰.X i ⟶ S)
  (hg : ∀ i : 𝒰.I₀, 𝒰.f i ≫ f = g i)

/-- The pre-hypercover in the slice over the chosen base, retaining the specified component
structure maps. -/
def locallyDirectedCoverPreHypercoverOver :
    PreOneHypercover.{max v w} (Over.mk f) where
  I₀ := ULift.{v} 𝒰.I₀
  X i := Over.mk (g i.down)
  f i := Over.homMk (𝒰.f i.down) (hg i.down)
  I₁ i j := Σ k : 𝒰.I₀, (k ⟶ i.down) × (k ⟶ j.down)
  Y {_ _} k := Over.mk (g k.1)
  p₁ {i j} k := Over.homMk (𝒰.trans k.2.1) (by
    change 𝒰.trans k.2.1 ≫ g i.down = g k.1
    rw [← hg i.down, ← Category.assoc, Scheme.Cover.trans_map, hg k.1])
  p₂ {i j} k := Over.homMk (𝒰.trans k.2.2) (by
    change 𝒰.trans k.2.2 ≫ g j.down = g k.1
    rw [← hg j.down, ← Category.assoc, Scheme.Cover.trans_map, hg k.1])
  w {i j} k := by
    apply (Over.forget S).map_injective
    change 𝒰.trans k.2.1 ≫ 𝒰.f i.down = 𝒰.trans k.2.2 ≫ 𝒰.f j.down
    rw [Scheme.Cover.trans_map, Scheme.Cover.trans_map]

/-- A locally directed open cover gives a `1`-hypercover over `S`.

The specified equations `hg` let the components retain the chosen structure
maps `g`, instead of replacing them by their composites through `X`.
-/
def locallyDirectedCoverHypercoverOver :
    GrothendieckTopology.OneHypercover.{max v w}
      (Scheme.zariskiTopology.over S) (Over.mk f) where
  __ := locallyDirectedCoverPreHypercoverOver (𝒰 := 𝒰) f g hg
  mem₀ := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    exact (locallyDirectedCoverHypercover 𝒰).mem₀
  mem₁ i j T p₁ p₂ h := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_preOneHypercover_sieve₁]
    exact (locallyDirectedCoverHypercover 𝒰).mem₁ i j p₁.left p₂.left
      (congrArg (fun k : T ⟶ Over.mk f => k.left) h)

/-- The zero component has exactly the chosen structure map. -/
lemma locallyDirectedCoverHypercoverOver_X (i : ULift.{v} 𝒰.I₀) :
    (locallyDirectedCoverHypercoverOver (𝒰 := 𝒰) f g hg).X i =
      Over.mk (g i.down) := rfl

/-- The covering arrow is the original covering arrow on underlying schemes. -/
lemma locallyDirectedCoverHypercoverOver_f_left (i : ULift.{v} 𝒰.I₀) :
    ((locallyDirectedCoverHypercoverOver (𝒰 := 𝒰) f g hg).f i).left = 𝒰.f i.down := rfl

/-- A common lower index contributes the corresponding chosen relative object. -/
lemma locallyDirectedCoverHypercoverOver_Y
    {i j : ULift.{v} 𝒰.I₀} (k : Σ l : 𝒰.I₀, (l ⟶ i.down) × (l ⟶ j.down)) :
    (locallyDirectedCoverHypercoverOver (𝒰 := 𝒰) f g hg).Y (i₁ := i) (i₂ := j) k =
      Over.mk (g k.1) := rfl

/-- The first overlap projection is the first transition of the original cover. -/
lemma locallyDirectedCoverHypercoverOver_p₁_left
    {i j : ULift.{v} 𝒰.I₀} (k : Σ l : 𝒰.I₀, (l ⟶ i.down) × (l ⟶ j.down)) :
    ((locallyDirectedCoverHypercoverOver (𝒰 := 𝒰) f g hg).p₁ (i₁ := i) (i₂ := j) k).left =
      𝒰.trans k.2.1 := rfl

/-- The second overlap projection is the second transition of the original cover. -/
lemma locallyDirectedCoverHypercoverOver_p₂_left
    {i j : ULift.{v} 𝒰.I₀} (k : Σ l : 𝒰.I₀, (l ⟶ i.down) × (l ⟶ j.down)) :
    ((locallyDirectedCoverHypercoverOver (𝒰 := 𝒰) f g hg).p₂ (i₁ := i) (i₂ := j) k).left =
      𝒰.trans k.2.2 := rfl

end SchemeTheory.WeilRestriction
