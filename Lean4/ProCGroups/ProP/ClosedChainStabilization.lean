import ProCGroups.ProP.GeneratorRank
import ProCGroups.ProP.BurnsideBasis
import ProCGroups.ProP.FrattiniQuotient
import ProCGroups.ProP.FrattiniPowers
import ProCGroups.FiniteGeneration.Basic
import ProCGroups.Generation.Basic
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Topology.Algebra.Group.Basic

set_option autoImplicit false

/-!
# Closed increasing subgroup chains in a finitely generated pro-p group

The finite power-commutator quotient detects generation. Consequently a
monotone sequence of closed subgroups with dense union already reaches the
whole group. This is the finite-witness step for a hypothetically finite
quotient by countably many relators.
-/

namespace ClassFieldTower.ProP

open ProCGroups.Generation ProCGroups.FiniteGeneration

universe u

/-- A dense increasing union of closed subgroups of a finitely generated
pro-p group reaches the whole group at a finite stage. -/
theorem exists_eq_top_of_monotone_closedSubgroups
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hpro : ProCGroups.ProC.HasPGroupOpenNormalBasis p G)
    (hfg : TopologicallyFinitelyGenerated G)
    (H : ℕ → Subgroup G) (hmono : Monotone H)
    (hclosed : ∀ n, IsClosed (H n : Set G))
    (hdense : (⨆ n, H n).topologicalClosure = ⊤) :
    ∃ n, H n = ⊤ := by
  classical
  let : (closedPowerCommutator p G).Normal := closedPowerCommutator_normal p G
  let : IsClosed (closedPowerCommutator p G : Set G) :=
    isClosed_closedPowerCommutator p G
  let Q := powerCommutatorQuotient p G
  let : Finite Q := powerCommutatorQuotient_finite_of_topologicallyFinitelyGenerated hfg
  let : Fintype Q := Fintype.ofFinite Q
  let q : G →ₜ* Q := powerCommutatorQuotientMk p G
  have hmapDense : ((⨆ n, H n).map q.toMonoidHom).topologicalClosure = ⊤ :=
    DenseRange.topologicalClosure_map_subgroup q.continuous_toFun
      (powerCommutatorQuotientMk_surjective p G).denseRange hdense
  have hmapTop : (⨆ n, H n).map q.toMonoidHom = ⊤ := by
    simpa using hmapDense
  have hdir : Directed (· ≤ ·) (fun n ↦ (H n).map q.toMonoidHom) := by
    intro i j
    exact ⟨max i j, Subgroup.map_mono (hmono (le_max_left i j)),
      Subgroup.map_mono (hmono (le_max_right i j))⟩
  have hcovers : ∀ x : Q, ∃ n, x ∈ (H n).map q.toMonoidHom := by
    intro x
    apply (Subgroup.mem_iSup_of_directed hdir).mp
    rw [← Subgroup.map_iSup, hmapTop]
    exact Subgroup.mem_top x
  let stage : Q → ℕ := fun x ↦ Classical.choose (hcovers x)
  let N : ℕ := Finset.univ.sup stage
  have hN : (H N).map q.toMonoidHom = ⊤ := by
    apply top_unique
    intro x _
    have hx : x ∈ (H (stage x)).map q.toMonoidHom := Classical.choose_spec (hcovers x)
    have hxN : stage x ≤ N := Finset.le_sup (Finset.mem_univ x)
    exact Subgroup.map_mono (hmono hxN) hx
  have hqgen : TopologicallyGenerates (G := Q) (q '' (H N : Set G)) := by
    change TopologicallyGenerates (q.toMonoidHom '' (H N : Set G))
    rw [← Subgroup.coe_map q.toMonoidHom (H N), hN]
    simp [TopologicallyGenerates]
  have hgen : TopologicallyGenerates (G := G) (H N : Set G) :=
    (topologicallyGenerates_iff_powerCommutatorQuotient_image hpro).mpr hqgen
  refine ⟨N, ?_⟩
  have hc : (H N).topologicalClosure = ⊤ := by
    simpa [TopologicallyGenerates] using hgen
  apply le_antisymm le_top
  rw [← hc]
  exact Subgroup.topologicalClosure_minimal _ le_rfl (hclosed N)

end ClassFieldTower.ProP
