/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Sets.Closeds
import Mathlib.Topology.Spectral.Basic
import Mathlib.Topology.Spectral.ConstructibleTopology

/-!
# Clopen restriction along a closed subset of a spectral space

If every point closure meets a closed subset in a connected nonempty set,
every clopen partition of the closed subset extends uniquely to the whole
space. This proves the topological partition step of Stacks Project, tag
0CAM, used in the sheaf restriction theorem 09ZG.

The proof constructs the generalization closures of the two parts. They
are closed in the constructible topology by compactness, and the connected
intersection hypothesis makes them stable under specialization.

References: https://stacks.math.columbia.edu/tag/0CAM and
https://stacks.math.columbia.edu/tag/09ZG. The Lean proofs are original.
-/

noncomputable section

universe u

open Set TopologicalSpace Topology

namespace SchemeTheory

variable {X : Type u} [TopologicalSpace X]

private lemma generizations_eq_iInter_compactOpens [PrespectralSpace X]
    {A : Set X} (hA : IsCompact A) :
    {x : X | ∃ z ∈ A, x ⤳ z} =
      ⋂ U : {U : Set X // IsOpen U ∧ IsCompact U ∧ A ⊆ U}, (U : Set X) := by
  classical
  ext x
  constructor
  · rintro ⟨z, hz, hxz⟩
    exact mem_iInter.mpr (fun U => hxz.mem_open U.2.1 (U.2.2.2 hz))
  · intro hx
    by_contra hn
    have hAc : A ⊆ (closure ({x} : Set X))ᶜ := by
      intro z hz hzx
      exact hn ⟨z, hz, specializes_iff_mem_closure.mpr hzx⟩
    obtain ⟨U, hUc, hUo, hAU, hUx⟩ :=
      PrespectralSpace.exists_isCompact_and_isOpen_between
        hA isClosed_closure.isOpen_compl hAc
    exact hUx (mem_iInter.mp hx ⟨U, hUo, hUc, hAU⟩)
      (subset_closure (mem_singleton x))

private lemma isClosed_constructible_generizations [PrespectralSpace X]
    {A : Set X} (hA : IsCompact A) :
    IsClosed ((WithTopology.ofTopology : WithConstructibleTopology X → X) ⁻¹'
      {x : X | ∃ z ∈ A, x ⤳ z}) := by
  rw [generizations_eq_iInter_compactOpens hA, preimage_iInter]
  apply isClosed_iInter
  intro U
  exact WithConstructibleTopology.isClosed_iff.mpr
    (U.2.2.1.isClosed_constructibleTopology_of_isOpen U.2.1)

/-- A point in the closure of a constructibly closed subset specializes
from a point of that subset. The compactness used here is compactness of
the constructible topology of the actual spectral space. -/
private lemma exists_specializes_of_mem_closure [SpectralSpace X]
    {A : Set X}
    (hA : IsClosed ((WithTopology.ofTopology : WithConstructibleTopology X → X) ⁻¹' A))
    {x : X} (hx : x ∈ closure A) : ∃ a ∈ A, a ⤳ x := by
  classical
  let I := {U : Set X // IsOpen U ∧ IsCompact U ∧ x ∈ U}
  let P : Set (WithConstructibleTopology X) := WithTopology.ofTopology ⁻¹' A
  let N (U : I) : Set (WithConstructibleTopology X) :=
    WithTopology.ofTopology ⁻¹' (U : Set X)
  have hN (U : I) : IsClosed (N U) :=
    WithConstructibleTopology.isClosed_iff.mpr
      (U.2.2.1.isClosed_constructibleTopology_of_isOpen U.2.1)
  have hfinite (s : Finset I) : (P ∩ ⋂ U ∈ s, N U).Nonempty := by
    have hopen : IsOpen (⋂ U ∈ s, (U : Set X)) :=
      isOpen_biInter_finset (fun U _ => U.2.1)
    have hxU : x ∈ ⋂ U ∈ s, (U : Set X) :=
      mem_iInter₂.mpr (fun U _ => U.2.2.2)
    obtain ⟨a, haU, haA⟩ := mem_closure_iff.mp hx _ hopen hxU
    refine ⟨WithTopology.toTopology (constructibleTopology X) a, haA, ?_⟩
    exact mem_iInter₂.mpr (fun U hU => mem_iInter₂.mp haU U hU)
  obtain ⟨a, haA, haN⟩ := hA.isCompact.inter_iInter_nonempty N hN hfinite
  refine ⟨WithTopology.ofTopology a, haA, specializes_iff_forall_open.mpr ?_⟩
  intro U hU hxU
  obtain ⟨V, hV, hxV, hVU⟩ :=
    PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open hxU hU
  exact hVU (mem_iInter.mp haN ⟨V, hV.1, hV.2, hxV⟩)

private lemma isClosed_of_constructible_closed_specialization [SpectralSpace X]
    {A : Set X}
    (hA : IsClosed ((WithTopology.ofTopology : WithConstructibleTopology X → X) ⁻¹' A))
    (hstable : ∀ ⦃x y : X⦄, x ∈ A → x ⤳ y → y ∈ A) : IsClosed A := by
  have hclosure : closure A ⊆ A := by
    intro x hx
    obtain ⟨a, ha, hax⟩ := exists_specializes_of_mem_closure hA hx
    exact hstable ha hax
  exact (closure_eq_iff_isClosed).mp (subset_antisymm hclosure subset_closure)

/-- A closed partition extends along a closed subset meeting every point
closure in a connected nonempty set. -/
@[stacks 0CAM]
theorem exists_clopen_partition_of_connected_closed_intersections [SpectralSpace X]
    {Z A B : Set X} (hA : IsClosed A) (hB : IsClosed B)
    (hAB : A ∪ B = Z) (hdisjoint : Disjoint A B)
    (hconnected : ∀ x : X, IsConnected (Z ∩ closure ({x} : Set X))) :
    ∃ W : Set X, IsClopen W ∧ W ∩ Z = A ∧ Wᶜ ∩ Z = B := by
  classical
  let WA : Set X := {x | ∃ z ∈ A, x ⤳ z}
  let WB : Set X := {x | ∃ z ∈ B, x ⤳ z}
  have hpart (x : X) : Z ∩ closure ({x} : Set X) ⊆ A ∨
      Z ∩ closure ({x} : Set X) ⊆ B := by
    apply (isPreconnected_iff_subset_of_disjoint_closed.mp
      (hconnected x).isPreconnected) A B hA hB
    · rw [hAB]
      exact inter_subset_left
    · rw [hdisjoint.inter_eq, inter_empty]
  have hcover (x : X) : x ∈ WA ∨ x ∈ WB := by
    obtain ⟨z, hzZ, hzx⟩ := (hconnected x).nonempty
    have hzAB : z ∈ A ∪ B := hAB.symm ▸ hzZ
    rcases hzAB with hzA | hzB
    · exact Or.inl ⟨z, hzA, specializes_iff_mem_closure.mpr hzx⟩
    · exact Or.inr ⟨z, hzB, specializes_iff_mem_closure.mpr hzx⟩
  have hdis : Disjoint WA WB := by
    apply Set.disjoint_left.mpr
    rintro x ⟨a, haA, hxa⟩ ⟨b, hbB, hxb⟩
    rcases hpart x with hpA | hpB
    · exact Set.disjoint_left.mp hdisjoint
        (hpA ⟨hAB ▸ Or.inr hbB, hxb.mem_closure⟩) hbB
    · exact Set.disjoint_left.mp hdisjoint haA
        (hpB ⟨hAB ▸ Or.inl haA, hxa.mem_closure⟩)
  have hWA : IsClosed WA := by
    apply isClosed_of_constructible_closed_specialization
      (isClosed_constructible_generizations hA.isCompact)
    intro x y hx hxy
    rcases hcover y with hyA | hyB
    · exact hyA
    · obtain ⟨b, hb, hyb⟩ := hyB
      exact (Set.disjoint_left.mp hdis hx ⟨b, hb, hxy.trans hyb⟩).elim
  have hWB : IsClosed WB := by
    apply isClosed_of_constructible_closed_specialization
      (isClosed_constructible_generizations hB.isCompact)
    intro x y hx hxy
    rcases hcover y with hyA | hyB
    · obtain ⟨a, ha, hya⟩ := hyA
      exact (Set.disjoint_left.mp hdis ⟨a, ha, hxy.trans hya⟩ hx).elim
    · exact hyB
  have hcompl : WAᶜ = WB := by
    ext x
    constructor
    · intro hx
      exact (hcover x).resolve_left hx
    · intro hxB hxA
      exact Set.disjoint_left.mp hdis hxA hxB
  refine ⟨WA, ⟨hWA, ?_⟩, ?_, ?_⟩
  · rw [← isClosed_compl_iff, hcompl]
    exact hWB
  · apply subset_antisymm
    · rintro z ⟨⟨a, ha, hza⟩, hzZ⟩
      rcases (show z ∈ A ∪ B from hAB.symm ▸ hzZ) with hzA | hzB
      · exact hzA
      · exact (Set.disjoint_left.mp hdisjoint ha (hza.mem_closed hB hzB)).elim
    · intro a ha
      exact ⟨⟨a, ha, specializes_refl a⟩, hAB ▸ Or.inl ha⟩
  · rw [hcompl]
    apply subset_antisymm
    · rintro z ⟨⟨b, hb, hzb⟩, hzZ⟩
      rcases (show z ∈ A ∪ B from hAB.symm ▸ hzZ) with hzA | hzB
      · exact (Set.disjoint_left.mp hdisjoint (hzb.mem_closed hA hzA) hb).elim
      · exact hzB
    · intro b hb
      exact ⟨⟨b, hb, specializes_refl b⟩, hAB ▸ Or.inr hb⟩

/-- Restriction gives a bijection on actual clopen subsets. -/
theorem clopen_restriction_bijective [SpectralSpace X] {Z : Set X}
    (hZ : IsClosed Z)
    (hconnected : ∀ x : X, IsConnected (Z ∩ closure ({x} : Set X))) :
    Function.Bijective (fun W : Clopens X =>
      (⟨Subtype.val ⁻¹' (W : Set X),
        W.isClopen.preimage continuous_subtype_val⟩ : Clopens Z)) := by
  classical
  constructor
  · intro U V hUV
    apply Clopens.ext
    ext x
    obtain ⟨z, hzZ, hxz⟩ := (hconnected x).nonempty
    have hspec : x ⤳ z := specializes_iff_mem_closure.mpr hxz
    have hzUV : z ∈ U ↔ z ∈ V :=
      Iff.of_eq (congrArg (fun W : Clopens Z => (⟨z, hzZ⟩ : Z) ∈ W) hUV)
    constructor
    · intro hxU
      exact hspec.mem_open V.isOpen (hzUV.mp (hspec.mem_closed U.isClosed hxU))
    · intro hxV
      exact hspec.mem_open U.isOpen (hzUV.mpr (hspec.mem_closed V.isClosed hxV))
  · intro U
    let A : Set X := Subtype.val '' (U : Set Z)
    let B : Set X := Subtype.val '' (U : Set Z)ᶜ
    have hA : IsClosed A := hZ.isClosedMap_subtype_val _ U.isClosed
    have hB : IsClosed B := hZ.isClosedMap_subtype_val _ U.isOpen.isClosed_compl
    have hAB : A ∪ B = Z := by
      ext x
      constructor
      · rintro (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩) <;> exact z.2
      · intro hx
        by_cases hxU : (⟨x, hx⟩ : Z) ∈ U
        · exact Or.inl ⟨⟨x, hx⟩, hxU, rfl⟩
        · exact Or.inr ⟨⟨x, hx⟩, hxU, rfl⟩
    have hdis : Disjoint A B := by
      apply Set.disjoint_left.mpr
      rintro x ⟨a, ha, hax⟩ ⟨b, hb, hbx⟩
      have hab : a = b := Subtype.ext (hax.trans hbx.symm)
      exact hb (hab ▸ ha)
    obtain ⟨W, hW, hWA, hWB⟩ :=
      exists_clopen_partition_of_connected_closed_intersections
        hA hB hAB hdis hconnected
    refine ⟨⟨W, hW⟩, Clopens.ext ?_⟩
    ext z
    change z.1 ∈ W ↔ z ∈ U
    constructor
    · intro hzW
      have hzA : z.1 ∈ A := hWA ▸ ⟨hzW, z.2⟩
      obtain ⟨a, ha, haz⟩ := hzA
      exact (Subtype.ext haz : a = z) ▸ ha
    · intro hzU
      have hzA : z.1 ∈ A := ⟨z, hzU, rfl⟩
      exact (show z.1 ∈ W ∩ Z from hWA.symm ▸ hzA).1

/-- Every locally constant function on the closed subset extends uniquely.
This is the constant-sheaf case needed in Stacks 09ZG; the value type need
not be finite. -/
theorem locallyConstant_restriction_bijective [SpectralSpace X] {Z : Set X}
    (hZ : IsClosed Z)
    (hconnected : ∀ x : X, IsConnected (Z ∩ closure ({x} : Set X)))
    (S : Type*) :
    Function.Bijective (LocallyConstant.comap
      (⟨Subtype.val, continuous_subtype_val⟩ : C(Z, X)) :
        LocallyConstant X S → LocallyConstant Z S) := by
  classical
  have hs (x : X) : ∃ z : Z, x ⤳ z.1 := by
    obtain ⟨z, hzZ, hxz⟩ := (hconnected x).nonempty
    exact ⟨⟨z, hzZ⟩, specializes_iff_mem_closure.mpr hxz⟩
  choose z hz using hs
  constructor
  · intro f g hfg
    apply LocallyConstant.ext
    intro x
    have hf : f x = f (z x).1 :=
      (hz x).mem_open (f.isLocallyConstant.isOpen_fiber (f (z x).1)) rfl
    have hg : g x = g (z x).1 :=
      (hz x).mem_open (g.isLocallyConstant.isOpen_fiber (g (z x).1)) rfl
    exact hf.trans ((congrArg (fun k : LocallyConstant Z S => k (z x)) hfg).trans hg.symm)
  · intro f
    let g : X → S := fun x => f (z x)
    have hfiber (a : S) : ∃ W : Clopens X, ∀ x : X, g x = a ↔ x ∈ W := by
      let U : Clopens Z := ⟨{z | f z = a}, f.isLocallyConstant.isClopen_fiber a⟩
      obtain ⟨W, hW⟩ := (clopen_restriction_bijective hZ hconnected).surjective U
      have hWmem (y : Z) : y.1 ∈ W ↔ f y = a :=
        Iff.of_eq (congrArg (fun V : Clopens Z => y ∈ V) hW)
      refine ⟨W, fun x => ?_⟩
      constructor
      · intro hx
        exact (hz x).mem_open W.isOpen ((hWmem (z x)).mpr hx)
      · intro hx
        exact (hWmem (z x)).mp ((hz x).mem_closed W.isClosed hx)
    have hg : IsLocallyConstant g := by
      apply IsLocallyConstant.iff_isOpen_fiber.mpr
      intro a
      obtain ⟨W, hW⟩ := hfiber a
      have heq : g ⁻¹' {a} = (W : Set X) := Set.ext hW
      rw [heq]
      exact W.isOpen
    refine ⟨⟨g, hg⟩, LocallyConstant.ext ?_⟩
    intro y
    have hsub : y ⤳ z y.1 := (subtype_specializes_iff y (z y.1)).mpr (hz y.1)
    exact hsub.mem_closed (f.isLocallyConstant.isClosed_fiber (f y)) rfl

end SchemeTheory
