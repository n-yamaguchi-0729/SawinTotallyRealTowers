import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Finiteness.Cardinality
import ProCGroups.FiniteGeneration.Basic

set_option autoImplicit false
/-!
# Generator bounds for finite elementary abelian groups

This file compares bounded topological generation of a finite discrete
commutative group with the dimension of a supplied `ZMod p`-module structure
on its additive copy.  It creates no group or module instance: the canonical
structure for a power--commutator quotient is installed only in the importing
pro-`p` leaf.
-/

open Set

namespace ClassFieldTower.ProP

universe u

open ProCGroups.Generation
open ProCGroups.FiniteGeneration

/-- A finite topological generating set of a discrete `ZMod p`-module bounds its dimension. -/
theorem finrank_le_of_topologicallyGeneratedByAtMost_zmod
    {p : ℕ} {Q : Type u} [Fact (Nat.Prime p)]
    [TopologicalSpace Q] [CommGroup Q] [IsTopologicalGroup Q] [DiscreteTopology Q]
    [Module (ZMod p) (Additive Q)] {d : ℕ}
    (hgen : TopologicallyGeneratedByAtMost d Q) :
    Module.finrank (ZMod p) (Additive Q) ≤ d := by
  classical
  rcases hgen with ⟨s, hs_card, hs_gen⟩
  have hs_closure : Subgroup.closure (s : Set Q) = ⊤ :=
    (topologicallyGenerates_iff_subgroupClosure_eq_top_of_discrete).mp hs_gen
  let v : {q : Q // q ∈ s} → Additive Q := fun q => Additive.ofMul q.1
  let V : Submodule (ZMod p) (Additive Q) :=
    Submodule.span (ZMod p) (Set.range v)
  have hspan : Submodule.span (ZMod p) (Set.range v) = ⊤ := by
    change V = ⊤
    apply eq_top_iff.2
    intro x _
    let K : Subgroup Q :=
      { carrier := {q : Q | Additive.ofMul q ∈ V}
        one_mem' := by
          show Additive.ofMul (1 : Q) ∈ V
          change (0 : Additive Q) ∈ V
          exact V.zero_mem
        mul_mem' := by
          intro a b ha hb
          show Additive.ofMul (a * b) ∈ V
          change Additive.ofMul a + Additive.ofMul b ∈ V
          exact V.add_mem ha hb
        inv_mem' := by
          intro a ha
          show Additive.ofMul a⁻¹ ∈ V
          change -Additive.ofMul a ∈ V
          exact V.neg_mem ha }
    have hs_le : Subgroup.closure (s : Set Q) ≤ K := by
      exact (Subgroup.closure_le K).2 (by
        intro q hq
        change Additive.ofMul q ∈ V
        exact Submodule.subset_span (R := ZMod p) (s := Set.range v)
          ⟨⟨q, hq⟩, rfl⟩)
    have hxK : Additive.toMul x ∈ K := by
      have hxTop : Additive.toMul x ∈ (⊤ : Subgroup Q) := Subgroup.mem_top _
      rw [← hs_closure] at hxTop
      exact hs_le hxTop
    change x ∈ V
    simpa [K] using hxK
  have hfin :
      Module.finrank (ZMod p) (Additive Q) ≤ Fintype.card {q : Q // q ∈ s} :=
    finrank_le_of_span_eq_top hspan
  have hcard : Fintype.card {q : Q // q ∈ s} = s.card := Fintype.card_coe s
  rw [hcard] at hfin
  exact hfin.trans hs_card

/-- A basis of a finite `ZMod p`-module gives a minimal-size topological generating set. -/
theorem topologicallyGeneratedByAtMost_finrank_zmod
    {p : ℕ} {Q : Type u} [Fact (Nat.Prime p)]
    [TopologicalSpace Q] [CommGroup Q] [IsTopologicalGroup Q] [DiscreteTopology Q]
    [Finite Q] [Module (ZMod p) (Additive Q)] :
    TopologicallyGeneratedByAtMost (Module.finrank (ZMod p) (Additive Q)) Q := by
  classical
  let _ : Module.Finite (ZMod p) (Additive Q) := Module.Finite.of_finite
  let ι := Module.Free.ChooseBasisIndex (ZMod p) (Additive Q)
  let b := Module.Free.chooseBasis (ZMod p) (Additive Q)
  let s : Finset Q := Finset.univ.image (fun i : ι => Additive.toMul (b i))
  refine ⟨s, ?_, ?_⟩
  · have hcard_le : s.card ≤ Fintype.card ι := Finset.card_image_le
    have hfinrank :
        Module.finrank (ZMod p) (Additive Q) = Fintype.card ι :=
      Module.finrank_eq_card_chooseBasisIndex (ZMod p) (Additive Q)
    rw [hfinrank]
    exact hcard_le
  · apply topologicallyGenerates_iff_subgroupClosure_eq_top_of_discrete.mpr
    let H : Subgroup Q := Subgroup.closure (s : Set Q)
    let A : AddSubgroup (Additive Q) :=
      { carrier := {x : Additive Q | Additive.toMul x ∈ H}
        zero_mem' := by
          change (1 : Q) ∈ H
          exact H.one_mem
        add_mem' := by
          intro x y hx hy
          change Additive.toMul x * Additive.toMul y ∈ H
          exact H.mul_mem hx hy
        neg_mem' := by
          intro x hx
          change (Additive.toMul x)⁻¹ ∈ H
          exact H.inv_mem hx }
    have hspan_le :
        Submodule.span (ZMod p) (Set.range b) ≤ AddSubgroup.toZModSubmodule p A := by
      apply Submodule.span_le.2
      intro x hx
      rcases hx with ⟨i, rfl⟩
      show b i ∈ AddSubgroup.toZModSubmodule p A
      change b i ∈ A
      change Additive.toMul (b i) ∈ H
      exact Subgroup.subset_closure (by
        show Additive.toMul (b i) ∈ (s : Set Q)
        exact Finset.mem_coe.2
          (Finset.mem_image.2 ⟨i, Finset.mem_univ i, rfl⟩))
    have hA_top : A = ⊤ := by
      apply eq_top_iff.2
      intro x _
      have hx_span : x ∈ Submodule.span (ZMod p) (Set.range b) := by
        rw [Module.Basis.span_eq b]
        exact Submodule.mem_top
      have hx_sub : x ∈ AddSubgroup.toZModSubmodule p A := hspan_le hx_span
      change x ∈ A at hx_sub
      exact hx_sub
    apply eq_top_iff.2
    intro q _
    have hqA : Additive.ofMul q ∈ A := by
      rw [hA_top]
      exact AddSubgroup.mem_top _
    simpa [A, H] using hqA

end ClassFieldTower.ProP
