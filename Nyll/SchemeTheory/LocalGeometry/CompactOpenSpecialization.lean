/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Topology.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Inseparable
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Spectral.Basic
import Mathlib.Topology.Spectral.ConstructibleTopology
import Mathlib.Topology.Spectral.Prespectral
import Mathlib.Topology.WithTopology

/-!
# Avoiding a compact open set by a neighborhood

The proof takes a finite constructible-open cover of the compact open set
by complements of compact open neighborhoods of the specified point.
-/

open TopologicalSpace Topology

universe u

/-- A compact open set in a spectral space can be avoided by an open
neighborhood of a point if none of its points specializes to that point. -/
theorem exists_open_nhds_disjoint_of_forall_not_specializes
    {X : Type u} [TopologicalSpace X] [SpectralSpace X]
    (K : Set X) (hKopen : IsOpen K) (hKcompact : IsCompact K)
    (x : X) (havoid : ∀ y ∈ K, ¬ y ⤳ x) :
    ∃ V : Opens X, x ∈ V ∧ Disjoint (V : Set X) K := by
  classical
  let C : Type u := WithConstructibleTopology X
  let f : C → X := WithTopology.ofTopology
  let I : Type u := {V : Set X // IsOpen V ∧ IsCompact V ∧ x ∈ V}
  let U : I → Set C := fun i ↦ f ⁻¹' i.valᶜ
  have hKclosed : IsClosed (f ⁻¹' K) := by
    apply (WithConstructibleTopology.isClosed_iff (X := X)).mpr
    exact hKcompact.isClosed_constructibleTopology_of_isOpen hKopen
  have hKpatch : IsCompact (f ⁻¹' K) := hKclosed.isCompact
  have hU : ∀ i : I, IsOpen (U i) := by
    intro i
    have hi : IsClosed (f ⁻¹' i.val) := by
      apply (WithConstructibleTopology.isClosed_iff (X := X)).mpr
      exact i.property.2.1.isClosed_constructibleTopology_of_isOpen i.property.1
    exact hi.isOpen_compl
  have hcover : f ⁻¹' K ⊆ ⋃ i : I, U i := by
    intro y hy
    obtain ⟨W, hWopen, hxW, hyW⟩ :=
      not_specializes_iff_exists_open.mp (havoid (f y) hy)
    obtain ⟨V, hV, hxV, hVW⟩ :=
      (PrespectralSpace.isTopologicalBasis (X := X)).exists_subset_of_mem_open hxW hWopen
    refine Set.mem_iUnion.mpr ⟨⟨V, hV.1, hV.2, hxV⟩, ?_⟩
    exact fun hyV ↦ hyW (hVW hyV)
  obtain ⟨s, hs⟩ := hKpatch.elim_finite_subcover U hU hcover
  refine ⟨⟨⋂ i ∈ s, i.val,
    isOpen_biInter_finset (fun i _hi ↦ i.property.1)⟩, ?_, ?_⟩
  · exact Set.mem_iInter₂.mpr (fun i _hi ↦ i.property.2.2)
  · apply Set.disjoint_left.mpr
    intro y hyV hyK
    have hyPatch : WithTopology.toTopology (constructibleTopology X) y ∈ f ⁻¹' K := hyK
    have hyCover : WithTopology.toTopology (constructibleTopology X) y ∈ ⋃ i ∈ s, U i :=
      hs hyPatch
    obtain ⟨i, his, hyi⟩ := Set.mem_iUnion₂.mp hyCover
    exact hyi (Set.mem_iInter₂.mp hyV i his)
