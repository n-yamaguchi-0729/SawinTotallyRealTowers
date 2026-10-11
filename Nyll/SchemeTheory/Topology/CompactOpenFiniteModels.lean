/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Topology.Category.TopCat.OpenNhds
import Mathlib.Topology.Order.UpperLowerSetTopology
import Mathlib.Topology.QuasiSeparated
import Mathlib.Topology.Sets.Compacts
import Mathlib.Topology.Sheaves.Alexandrov
import Mathlib.Topology.Spectral.Hom
import Mathlib.Topology.Spectral.Prespectral

/-!
# Coherent finite models of compact-open families

For a finite set `S` of compact opens, the space `Space S` consists of the
membership patterns actually realized by points of `X`. It has the
upper-set topology for inclusion of patterns. Forgetting coordinates
gives continuous refinement maps with exact identity, composition, and
quotient compatibility laws.

Principal opens pull back to finite intersections of compact opens.
The resulting neighborhoods shrink under refinement and are cofinal
among all open neighborhoods on a prespectral space. These are actual
finite models for sheaf approximation; no sheaf descent is assumed.
The Lean proof is original.
-/

noncomputable section

universe u

open CategoryTheory TopologicalSpace Topology

namespace SchemeTheory.CompactOpenFiniteModel

variable {X : TopCat.{u}}

/-- The compact opens in `S` that contain a point. -/
def pattern (S : Finset (CompactOpens X)) (x : X) : Set S :=
  {U | x ∈ (U.1 : Set X)}

/-- The finite space of realized membership patterns, ordered by inclusion. -/
abbrev Space (S : Finset (CompactOpens X)) : TopCat.{u} :=
  TopCat.of (WithUpperSet (Set.range (pattern S)))

instance finite_space (S : Finset (CompactOpens X)) : Finite (Space S) :=
  Finite.of_equiv (Set.range (pattern S)) WithUpperSet.toUpperSet

private def quotientFn (S : Finset (CompactOpens X)) (x : X) : Space S :=
  WithUpperSet.toUpperSet ⟨pattern S x, ⟨x, rfl⟩⟩

/-- The open intersection specified by a realized pattern. -/
def principalPreimage (S : Finset (CompactOpens X)) (p : Space S) : Opens X :=
  ⟨⋂ U ∈ (WithUpperSet.ofUpperSet p).1, (U.1 : Set X),
    (Set.toFinite (WithUpperSet.ofUpperSet p).1).isOpen_biInter
      (fun U _ => U.1.isOpen)⟩

theorem mem_principalPreimage (S : Finset (CompactOpens X)) (p : Space S) (x : X) :
    x ∈ principalPreimage S p ↔
      ∀ U : S, U ∈ (WithUpperSet.ofUpperSet p).1 → x ∈ (U.1 : Set X) :=
  Set.mem_iInter₂

private theorem quotientFn_preimage (S : Finset (CompactOpens X))
    (W : Set (Space S)) (hW : IsOpen W) :
    quotientFn S ⁻¹' W = ⋃ p ∈ W, (principalPreimage S p : Set X) := by
  have hu : IsUpperSet W := Topology.IsUpperSet.isOpen_iff_isUpperSet.mp hW
  ext x
  constructor
  · intro hx
    refine Set.mem_iUnion₂.mpr ⟨quotientFn S x, hx, ?_⟩
    exact (mem_principalPreimage S (quotientFn S x) x).mpr (fun _ hU => hU)
  · intro hx
    obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp hx
    have hle : p ≤ quotientFn S x := (mem_principalPreimage S p x).mp hxp
    exact hu hle hp

/-- The actual continuous quotient map recording the finite family. -/
def quotient (S : Finset (CompactOpens X)) : X ⟶ Space S :=
  TopCat.ofHom ⟨quotientFn S, by
    apply continuous_def.mpr
    intro W hW
    rw [quotientFn_preimage S W hW]
    exact isOpen_iUnion (fun p => isOpen_iUnion (fun _ => (principalPreimage S p).isOpen))⟩

theorem quotient_apply (S : Finset (CompactOpens X)) (x : X) :
    quotient S x = WithUpperSet.toUpperSet ⟨pattern S x, ⟨x, rfl⟩⟩ := rfl

theorem quotient_surjective (S : Finset (CompactOpens X)) :
    Function.Surjective (quotient S) := by
  intro p
  obtain ⟨x, hx⟩ := (WithUpperSet.ofUpperSet p).2
  refine ⟨x, ?_⟩
  apply WithUpperSet.ofUpperSet.injective
  exact Subtype.ext hx

theorem principal_preimage (S : Finset (CompactOpens X)) (p : Space S) :
    (Opens.map (quotient S)).obj (Alexandrov.principalOpen p) =
      principalPreimage S p := by
  apply Opens.ext
  ext x
  exact (mem_principalPreimage S p x).symm

theorem principalPreimage_isCompact [CompactSpace X] [QuasiSeparatedSpace X]
    (S : Finset (CompactOpens X)) (p : Space S) :
    IsCompact (principalPreimage S p : Set X) := by
  let C : Set (Set X) :=
    (fun U : S => (U.1 : Set X)) '' (WithUpperSet.ofUpperSet p).1
  have hC : C.Finite :=
    (Set.toFinite (WithUpperSet.ofUpperSet p).1).image (fun U : S => (U.1 : Set X))
  have heq : (principalPreimage S p : Set X) = ⋂₀ C := by
    ext x
    constructor
    · intro hx V hV
      obtain ⟨U, hU, rfl⟩ := hV
      exact (mem_principalPreimage S p x).mp hx U hU
    · intro hx
      exact (mem_principalPreimage S p x).mpr
        (fun U hU => hx (U.1 : Set X) ⟨U, hU, rfl⟩)
  rw [heq]
  refine QuasiSeparatedSpace.isCompact_sInter hC ?_ ?_
  · rintro V ⟨U, _, rfl⟩
    exact Or.inl U.1.isOpen
  · rintro V ⟨U, _, rfl⟩
    exact U.1.isCompact

theorem quotient_isSpectralMap [CompactSpace X] [QuasiSeparatedSpace X]
    (S : Finset (CompactOpens X)) : IsSpectralMap (quotient S) := by
  refine ⟨(quotient S).hom.continuous, ?_⟩
  intro W hW _
  change IsCompact (quotientFn S ⁻¹' W)
  rw [quotientFn_preimage S W hW]
  exact (Set.toFinite W).isCompact_biUnion
    (fun p _ => principalPreimage_isCompact S p)

private def restrictPattern {S T : Finset (CompactOpens X)} (h : S ⊆ T) :
    Set.range (pattern T) →o Set.range (pattern S) where
  toFun p := ⟨(fun U : S => (⟨U.1, h U.2⟩ : T)) ⁻¹' p.1, by
    obtain ⟨x, hx⟩ := p.2
    refine ⟨x, ?_⟩
    rw [← hx]
    rfl⟩
  monotone' := fun _ _ hp _ hU => hp hU

/-- Forgetting extra compact-open coordinates defines a refinement map. -/
def refinement {S T : Finset (CompactOpens X)} (h : S ⊆ T) : Space T ⟶ Space S :=
  TopCat.ofHom (WithUpperSet.map (restrictPattern h))

theorem quotient_comp {S T : Finset (CompactOpens X)} (h : S ⊆ T) :
    quotient T ≫ refinement h = quotient S := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  apply WithUpperSet.ofUpperSet.injective
  apply Subtype.ext
  rfl

theorem refinement_refl (S : Finset (CompactOpens X)) :
    refinement (Finset.Subset.refl S) = 𝟙 (Space S) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  apply WithUpperSet.ofUpperSet.injective
  apply Subtype.ext
  rfl

theorem refinement_comp {S T R : Finset (CompactOpens X)}
    (hST : S ⊆ T) (hTR : T ⊆ R) :
    refinement hTR ≫ refinement hST = refinement (hST.trans hTR) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  apply WithUpperSet.ofUpperSet.injective
  apply Subtype.ext
  rfl

/-- The inverse image of the smallest finite-model neighborhood of `x`. -/
def neighborhood (S : Finset (CompactOpens X)) (x : X) : Opens X :=
  principalPreimage S (quotient S x)

theorem mem_neighborhood (S : Finset (CompactOpens X)) (x y : X) :
    y ∈ neighborhood S x ↔ ∀ U ∈ S, x ∈ (U : Set X) → y ∈ (U : Set X) := by
  rw [neighborhood, mem_principalPreimage]
  constructor
  · intro h U hU hx
    exact h ⟨U, hU⟩ hx
  · intro h U hx
    exact h U.1 U.2 hx

theorem self_mem_neighborhood (S : Finset (CompactOpens X)) (x : X) :
    x ∈ neighborhood S x :=
  (mem_neighborhood S x x).mpr (fun _ _ hx => hx)

theorem neighborhood_preimage (S : Finset (CompactOpens X)) (x : X) :
    (Opens.map (quotient S)).obj (Alexandrov.principalOpen (quotient S x)) =
      neighborhood S x :=
  principal_preimage S (quotient S x)

theorem neighborhood_isCompact [CompactSpace X] [QuasiSeparatedSpace X]
    (S : Finset (CompactOpens X)) (x : X) : IsCompact (neighborhood S x : Set X) :=
  principalPreimage_isCompact S (quotient S x)

theorem neighborhood_antitone {S T : Finset (CompactOpens X)}
    (h : S ⊆ T) (x : X) : neighborhood T x ≤ neighborhood S x := by
  intro y hy
  exact (mem_neighborhood S x y).mpr
    (fun U hU hx => (mem_neighborhood T x y).mp hy U (h hU) hx)

/-- On a prespectral space the principal preimages are cofinal among
open neighborhoods: one compact-open coordinate already suffices. -/
theorem exists_neighborhood_le [PrespectralSpace X] (x : X)
    (V : Opens X) (hx : x ∈ V) :
    ∃ S : Finset (CompactOpens X), neighborhood S x ≤ V := by
  classical
  obtain ⟨U, hU, hxU, hUV⟩ :=
    (Opens.isBasis_iff_nbhd.mp (PrespectralSpace.isBasis_opens X)) hx
  let W : CompactOpens X := ⟨⟨U, hU⟩, U.isOpen⟩
  refine ⟨{W}, ?_⟩
  intro y hy
  exact hUV ((mem_neighborhood {W} x y).mp hy W (Finset.mem_singleton_self W) hxU)

end SchemeTheory.CompactOpenFiniteModel
