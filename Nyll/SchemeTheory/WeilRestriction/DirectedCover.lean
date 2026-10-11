/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.AlgebraicGeometry.Cover.Directed
public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Topology.Sets.Opens

/-!
# A locally directed refinement of an open cover

Given an open cover of a scheme, consider every open subset contained in
the image of some member of that cover. These open subsets form a basis,
and their inclusion ordering makes the associated open cover locally
directed. A chosen containing member supplies a refinement map to the
original cover.
-/


@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u v

namespace SchemeTheory.WeilRestriction

variable {X : Scheme.{u}} (𝒰 : Scheme.OpenCover.{v} X)

/-- The open cover consisting of all open subsets contained in the image
of a member of `𝒰`. -/
def subordinateOpenCover : Scheme.OpenCover.{u} X where
  I₀ := {V : X.Opens // ∃ i : 𝒰.I₀, V ≤ (𝒰.f i).opensRange}
  X V := V.1
  f V := V.1.ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, ?_⟩
    · intro x
      refine ⟨⟨(𝒰.f (𝒰.idx x)).opensRange, ⟨𝒰.idx x, le_rfl⟩⟩, ?_⟩
      change x ∈ Set.range (𝒰.f (𝒰.idx x)).opensRange.ι
      rw [Scheme.Opens.range_ι]
      exact 𝒰.covers x
    · intro V
      exact inferInstanceAs (IsOpenImmersion V.1.ι)

instance subordinateOpenCoverPreorder : Preorder (subordinateOpenCover 𝒰).I₀ :=
  inferInstanceAs (Preorder {V : X.Opens // ∃ i : 𝒰.I₀, V ≤ (𝒰.f i).opensRange})

/-- The members of the subordinate cover form a basis for the topology. -/
lemma subordinateOpenCover_isBasis :
    TopologicalSpace.Opens.IsBasis
      (Set.range fun i : (subordinateOpenCover 𝒰).I₀ ↦
        ((subordinateOpenCover 𝒰).f i).opensRange) := by
  rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
  intro V x hx
  let W : X.Opens := V ⊓ (𝒰.f (𝒰.idx x)).opensRange
  let j : (subordinateOpenCover 𝒰).I₀ := ⟨W, ⟨𝒰.idx x, inf_le_right⟩⟩
  refine ⟨W, ⟨j, ?_⟩, ?_, inf_le_left⟩
  · exact Scheme.Opens.opensRange_ι W
  · exact ⟨hx, 𝒰.covers x⟩

instance subordinateOpenCoverLocallyDirected :
    (subordinateOpenCover 𝒰).LocallyDirected := by
  refine Scheme.Cover.LocallyDirected.ofIsBasisOpensRange ?_
    (subordinateOpenCover_isBasis 𝒰)
  intro i j
  change i.1 ≤ j.1 ↔ i.1.ι.opensRange ≤ j.1.ι.opensRange
  rw [Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι]

/-- Choose a member of `𝒰` containing a given subordinate open subset. -/
def subordinateOpenCoverRefinementIndex (i : (subordinateOpenCover 𝒰).I₀) : 𝒰.I₀ :=
  i.2.choose

/-- The map from a subordinate open subset to its chosen containing member
of the original cover. -/
def subordinateOpenCoverRefinementMap (i : (subordinateOpenCover 𝒰).I₀) :
    (subordinateOpenCover 𝒰).X i ⟶ 𝒰.X (subordinateOpenCoverRefinementIndex 𝒰 i) :=
  IsOpenImmersion.lift
    (𝒰.f (subordinateOpenCoverRefinementIndex 𝒰 i))
    ((subordinateOpenCover 𝒰).f i) (by
      change Set.range i.1.ι ⊆ Set.range (𝒰.f (subordinateOpenCoverRefinementIndex 𝒰 i))
      rw [Scheme.Opens.range_ι]
      exact i.2.choose_spec)

/-- The refinement maps commute with the structure maps to the base. -/
@[reassoc]
lemma subordinateOpenCoverRefinementMap_comp (i : (subordinateOpenCover 𝒰).I₀) :
    subordinateOpenCoverRefinementMap 𝒰 i ≫
        𝒰.f (subordinateOpenCoverRefinementIndex 𝒰 i) =
      (subordinateOpenCover 𝒰).f i :=
  IsOpenImmersion.lift_fac
    (𝒰.f (subordinateOpenCoverRefinementIndex 𝒰 i))
    ((subordinateOpenCover 𝒰).f i) (by
      change Set.range i.1.ι ⊆ Set.range (𝒰.f (subordinateOpenCoverRefinementIndex 𝒰 i))
      rw [Scheme.Opens.range_ι]
      exact i.2.choose_spec)

end SchemeTheory.WeilRestriction
