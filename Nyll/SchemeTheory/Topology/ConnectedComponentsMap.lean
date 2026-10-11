/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Topology.ConnectedComponentsSeparation
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Sets.Closeds

/-!
# Connected components detected by clopen inverse images

For compact prespectral quasi-separated spaces, a continuous map inducing a
bijection on clopen subsets induces a homeomorphism on connected components.
Surjectivity is proved by the finite intersection property in the source;
injectivity follows from the description of a component by clopen neighborhoods.
-/

@[expose] public section

open Set TopologicalSpace

universe u v

namespace SchemeTheory

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

private lemma clopen_mem_iff_of_component_eq {x y : X}
    (h : ConnectedComponents.mk x = ConnectedComponents.mk y) (U : Clopens X) :
    x ∈ U ↔ y ∈ U := by
  constructor
  · intro hx
    exact U.isClopen.connectedComponent_subset hx
      (ConnectedComponents.coe_eq_coe'.mp h.symm)
  · intro hy
    exact U.isClopen.connectedComponent_subset hy
      (ConnectedComponents.coe_eq_coe'.mp h)

/-- A bijection on clopen inverse images also detects connectedness. -/
theorem connectedSpace_iff_of_clopen_preimage {f : X → Y}
    (hf : Continuous f)
    (hclopen : Function.Bijective (fun U : Clopens Y ↦
      (⟨f ⁻¹' (U : Set Y), U.isClopen.preimage hf⟩ : Clopens X))) :
    ConnectedSpace X ↔ ConnectedSpace Y := by
  classical
  constructor
  · intro hX
    let : ConnectedSpace X := hX
    apply connectedSpace_iff_clopen.mpr
    refine ⟨Nonempty.map f inferInstance, ?_⟩
    intro s hs
    rcases isClopen_iff.mp (hs.preimage hf) with hempty | hfull
    · have he : (⟨s, hs⟩ : Clopens Y) = ⊥ :=
        hclopen.injective (Clopens.ext hempty)
      exact Or.inl (congrArg (fun U : Clopens Y ↦ (U : Set Y)) he)
    · have he : (⟨s, hs⟩ : Clopens Y) = ⊤ :=
        hclopen.injective (Clopens.ext hfull)
      exact Or.inr (congrArg (fun U : Clopens Y ↦ (U : Set Y)) he)
  · intro hY
    let : ConnectedSpace Y := hY
    apply connectedSpace_iff_clopen.mpr
    constructor
    · by_contra h
      have he : f ⁻¹' (Set.univ : Set Y) = ∅ :=
        Set.eq_empty_iff_forall_notMem.mpr (fun x _ ↦ h ⟨x⟩)
      have ht : (⊤ : Clopens Y) = ⊥ := hclopen.injective (Clopens.ext he)
      let y : Y := Classical.choice (inferInstance : Nonempty Y)
      have hy : y ∈ (⊥ : Clopens Y) := ht ▸ (show y ∈ (⊤ : Clopens Y) from trivial)
      exact hy
    · intro s hs
      obtain ⟨V, hV⟩ := hclopen.surjective (⟨s, hs⟩ : Clopens X)
      have he : f ⁻¹' (V : Set Y) = s :=
        congrArg (fun U : Clopens X ↦ (U : Set X)) hV
      rcases isClopen_iff.mp V.isClopen with hempty | hfull
      · left
        rw [← he, hempty, Set.preimage_empty]
      · right
        rw [← he, hfull, Set.preimage_univ]

variable [CompactSpace X] [PrespectralSpace X] [QuasiSeparatedSpace X]
  [CompactSpace Y] [PrespectralSpace Y] [QuasiSeparatedSpace Y]

/-- A bijection on clopen inverse images detects exactly the connected components. -/
theorem connectedComponentsMap_bijective_of_clopen_preimage {f : X → Y}
    (hf : Continuous f)
    (hclopen : Function.Bijective (fun U : Clopens Y ↦
      (⟨f ⁻¹' (U : Set Y), U.isClopen.preimage hf⟩ : Clopens X))) :
    Function.Bijective hf.connectedComponentsMap := by
  classical
  constructor
  · intro a b hab
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe a
    obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe b
    change ConnectedComponents.mk (f x) = ConnectedComponents.mk (f y) at hab
    apply ConnectedComponents.coe_eq_coe'.mpr
    rw [connectedComponent_eq_iInter_isClopen_of_prespectral y]
    apply Set.mem_iInter.mpr
    intro U
    obtain ⟨V, hV⟩ := hclopen.surjective (⟨U.1, U.2.1⟩ : Clopens X)
    have hpre : f ⁻¹' (V : Set Y) = U.1 :=
      congrArg (fun W : Clopens X ↦ (W : Set X)) hV
    have hy : f y ∈ V := by
      change y ∈ f ⁻¹' (V : Set Y)
      rw [hpre]
      exact U.2.2
    have hx : f x ∈ V := (clopen_mem_iff_of_component_eq hab V).mpr hy
    rw [← hpre]
    exact hx
  · intro a
    obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe a
    have hnonempty (V : Clopens Y) (hy : y ∈ V) :
        (f ⁻¹' (V : Set Y)).Nonempty := by
      by_contra h
      have he : f ⁻¹' (V : Set Y) = ∅ := Set.not_nonempty_iff_eq_empty.mp h
      have hV : V = ⊥ := hclopen.injective (Clopens.ext he)
      have : y ∈ (⊥ : Clopens Y) := hV ▸ hy
      exact this
    let I := {V : Clopens Y // y ∈ V}
    have hfinite (s : Finset I) :
        (⋂ V ∈ s, f ⁻¹' ((V.1 : Clopens Y) : Set Y)).Nonempty := by
      let W : Clopens Y :=
        ⟨⋂ V ∈ s, ((V.1 : Clopens Y) : Set Y),
          isClopen_biInter_finset (fun V _ ↦ V.1.isClopen)⟩
      have hyW : y ∈ W := Set.mem_iInter₂.mpr (fun V _ ↦ V.2)
      obtain ⟨x, hx⟩ := hnonempty W hyW
      refine ⟨x, Set.mem_iInter₂.mpr (fun V hV ↦ ?_)⟩
      exact Set.mem_iInter₂.mp hx V hV
    obtain ⟨x, hx⟩ := CompactSpace.iInter_nonempty
      (fun V : I ↦ V.1.isClosed.preimage hf) hfinite
    refine ⟨ConnectedComponents.mk x, ?_⟩
    change ConnectedComponents.mk (f x) = ConnectedComponents.mk y
    apply ConnectedComponents.coe_eq_coe'.mpr
    rw [connectedComponent_eq_iInter_isClopen_of_prespectral y]
    apply Set.mem_iInter.mpr
    intro V
    exact Set.mem_iInter.mp hx ⟨⟨V.1, V.2.1⟩, V.2.2⟩

/-- A continuous map inducing a bijection on clopen subsets induces a homeomorphism
on connected components of compact prespectral quasi-separated spaces. -/
theorem connectedComponentsMap_isHomeomorph_of_clopen_preimage {f : X → Y}
    (hf : Continuous f)
    (hclopen : Function.Bijective (fun U : Clopens Y ↦
      (⟨f ⁻¹' (U : Set Y), U.isClopen.preimage hf⟩ : Clopens X))) :
    IsHomeomorph hf.connectedComponentsMap := by
  let : T2Space (ConnectedComponents Y) := t2Space_connectedComponents_of_prespectral
  exact isHomeomorph_iff_continuous_bijective.mpr
    ⟨hf.connectedComponentsMap_continuous,
      connectedComponentsMap_bijective_of_clopen_preimage hf hclopen⟩

end SchemeTheory
