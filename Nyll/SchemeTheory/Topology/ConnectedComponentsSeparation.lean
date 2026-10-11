/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Topology.ConnectedComponents
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Hausdorff connected-component spaces

The connected-component quotient of a compact quasi-separated prespectral space is
Hausdorff, even when the original space is not Hausdorff.
-/

@[expose] public section

universe u

open Set TopologicalSpace

namespace SchemeTheory

/-- Clopen neighbourhoods separate distinct connected components of a compact
quasi-separated prespectral space. -/
theorem t2Space_connectedComponents_of_prespectral {X : Type u} [TopologicalSpace X]
    [CompactSpace X] [PrespectralSpace X] [QuasiSeparatedSpace X] :
    T2Space (ConnectedComponents X) := by
  classical
  refine ⟨ConnectedComponents.surjective_coe.forall₂.2 fun a b hab => ?_⟩
  have ha : a ∉ connectedComponent b := by
    intro h
    exact hab (ConnectedComponents.coe_eq_coe'.mpr h)
  rw [connectedComponent_eq_iInter_isClopen_of_prespectral b] at ha
  simp only [Set.mem_iInter, not_forall] at ha
  obtain ⟨U, haU⟩ := ha
  let V : Set (ConnectedComponents X) := (↑) '' (U : Set X)
  have hpre : (↑) ⁻¹' V = (U : Set X) :=
    (connectedComponents_preimage_image (U : Set X)).trans
      U.2.1.biUnion_connectedComponent_eq
  have hV : IsClopen V := by
    apply ConnectedComponents.isQuotientMap_coe.isClopen_preimage.mp
    rw [hpre]
    exact U.2.1
  refine ⟨Vᶜ, V, hV.compl.isOpen, hV.isOpen, ?_, ⟨b, U.2.2, rfl⟩,
    disjoint_compl_left⟩
  change a ∉ (↑) ⁻¹' V
  rwa [hpre]

end SchemeTheory
