/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.QuasiSeparated
import Mathlib.Topology.Sober
import Mathlib.Topology.Spectral.Basic
import Nyll.SchemeTheory.Topology.SpectralClosedRestriction

/-!
# The closed-support reduction for spectral restriction

Closed subspaces of spectral spaces are spectral. The connected
point-closure intersection condition restricts to each closed subspace,
because the closure of any point of that subspace remains in it. Thus
the locally constant extension theorem applies on every closed support,
as required in Stacks Project, tag 09ZG.

Reference: https://stacks.math.columbia.edu/tag/09ZG.
The Lean proofs are original.
-/

noncomputable section

universe u

open Set TopologicalSpace Topology

namespace SchemeTheory

variable {X : Type u} [TopologicalSpace X]

/-- A closed subspace of a spectral space is spectral. Its compact-open
basis is obtained by intersecting ambient compact opens with the subspace. -/
theorem spectralSpace_closedSubtype [SpectralSpace X] {C : Set X} (hC : IsClosed C) :
    SpectralSpace C := by
  let f : C → X := Subtype.val
  have hf : IsClosedEmbedding f := hC.isClosedEmbedding_subtypeVal
  let I := {U : Set X // IsOpen U ∧ IsCompact U}
  let B : I → Set C := fun U => f ⁻¹' U.1
  have hB : Set.range B = Set.preimage f '' {U : Set X | IsOpen U ∧ IsCompact U} := by
    ext V
    constructor
    · rintro ⟨U, rfl⟩
      exact ⟨U.1, U.2, rfl⟩
    · rintro ⟨U, hU, rfl⟩
      exact ⟨⟨U, hU⟩, rfl⟩
  have hBasis : IsTopologicalBasis (Set.range B) :=
    hB.symm ▸ hf.isInducing.isTopologicalBasis PrespectralSpace.isTopologicalBasis
  have hQS : QuasiSeparatedSpace C :=
    QuasiSeparatedSpace.of_isTopologicalBasis hBasis (fun U V => by
      change IsCompact ((f ⁻¹' U.1) ∩ (f ⁻¹' V.1))
      rw [← Set.preimage_inter]
      exact hf.isProperMap.isCompact_preimage
        (U.2.2.inter_of_isOpen V.2.2 U.2.1 V.2.1))
  exact
    { __ := hf.isEmbedding.t0Space
      __ := isCompact_iff_compactSpace.mp hC.isCompact
      __ := hf.quasiSober
      __ := hQS
      __ := PrespectralSpace.of_isClosedEmbedding f hf }

/-- The original connected, nonempty point-closure condition holds on
every closed support, with no additional geometric assumption. -/
theorem connected_closed_intersections_on_closedSubset {Z C : Set X} (hC : IsClosed C)
    (hconnected : ∀ x : X, IsConnected (Z ∩ closure ({x} : Set X))) (x : C) :
    IsConnected ((Subtype.val ⁻¹' Z : Set C) ∩ closure ({x} : Set C)) := by
  let A : Set C := (Subtype.val ⁻¹' Z : Set C) ∩ closure ({x} : Set C)
  have hImage : (Subtype.val : C → X) '' A = Z ∩ closure ({x.1} : Set X) := by
    ext y
    constructor
    · rintro ⟨z, ⟨hzZ, hxz⟩, rfl⟩
      exact ⟨hzZ, ((subtype_specializes_iff x z).mp
        (specializes_iff_mem_closure.mpr hxz)).mem_closure⟩
    · intro hy
      have hyC : y ∈ C :=
        (specializes_iff_mem_closure.mpr hy.2).mem_closed hC x.2
      refine ⟨⟨y, hyC⟩, ⟨hy.1, ?_⟩, rfl⟩
      exact ((subtype_specializes_iff x ⟨y, hyC⟩).mpr
        (specializes_iff_mem_closure.mpr hy.2)).mem_closure
  have hA : IsConnected ((Subtype.val : C → X) '' A) :=
    hImage.symm ▸ hconnected x.1
  exact ⟨Set.image_nonempty.mp hA.nonempty,
    IsInducing.subtypeVal.isPreconnected_image.mp hA.isPreconnected⟩

/-- Locally constant functions on the intersection of two closed subsets
extend uniquely over the closed support under the original hypotheses. -/
theorem locallyConstant_closedSupport_restriction_bijective [SpectralSpace X]
    {Z C : Set X} (hZ : IsClosed Z) (hC : IsClosed C)
    (hconnected : ∀ x : X, IsConnected (Z ∩ closure ({x} : Set X))) (A : Type*) :
    Function.Bijective (LocallyConstant.comap
      (⟨Subtype.val, continuous_subtype_val⟩ : C((Subtype.val ⁻¹' Z : Set C), C)) :
        LocallyConstant C A → LocallyConstant (Subtype.val ⁻¹' Z : Set C) A) := by
  have hSpectral : SpectralSpace C := spectralSpace_closedSubtype hC
  exact locallyConstant_restriction_bijective (hZ.preimage continuous_subtype_val)
    (connected_closed_intersections_on_closedSubset hC hconnected) A

end SchemeTheory
