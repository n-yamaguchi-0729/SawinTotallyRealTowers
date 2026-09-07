import ProCGroups.FiniteGeneration.OpenSubgroups
import ProCGroups.ProP.Zassenhaus.DegreeTwo
import ProCGroups.ProP.Zassenhaus.Laws
import ProCGroups.ProP.Zassenhaus.Depth
import ProCGroups.ProC.OpenNormalSubgroups.Basic
import ProCGroups.Topologies.ContinuousMonoidHom
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Constructions

set_option autoImplicit false

/-!
# Deep finite open quotients and lifts

Iterating the open power--commutator core produces open normal subgroups
inside arbitrary closed augmentation degrees. Applying an actual compact
surjective homomorphism to such a source subgroup gives a target open
normal subgroup whose elements have source lifts of the required depth.
-/

open scoped commutatorElement

namespace ClassFieldTower.ProP

open ProCGroups ProCGroups.ProC ProCGroups.FiniteGeneration

noncomputable section

universe u v

variable (p : ℕ) [Fact p.Prime]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

private theorem closedPowerCommutator_map_le_zassenhaus_double
    (H : Subgroup G) (n : ℕ) (hH : H ≤ zassenhausSubgroup p G n) :
    (closedPowerCommutator p H).map H.subtype ≤ zassenhausSubgroup p G (2 * n) := by
  rw [Subgroup.map_le_iff_le_comap]
  apply Subgroup.topologicalClosure_minimal
  · apply sup_le
    · rw [powerSubgroup, Subgroup.closure_le]
      rintro _ ⟨x, rfl⟩
      change (x : G) ^ p ∈ zassenhausSubgroup p G (2 * n)
      exact zassenhausSubgroup_antitone p G
        (Nat.mul_le_mul_right n (Fact.out : Nat.Prime p).two_le)
        (pow_mem_zassenhausSubgroup_mul p G (hH x.property))
    · rw [commutator_def, Subgroup.commutator_le]
      intro x _ y _
      change ⁅(x : G), (y : G)⁆ ∈ zassenhausSubgroup p G (2 * n)
      simpa only [two_mul] using
        commutator_mem_zassenhausSubgroup_add p G (hH x.property) (hH y.property)
  · change IsClosed ((Subtype.val : H → G) ⁻¹'
      (zassenhausSubgroup p G (2 * n) : Set G))
    exact (isClosed_zassenhausSubgroup p G (2 * n)).preimage continuous_subtype_val

/-- Every prescribed augmentation depth contains an actual open normal subgroup. -/
theorem exists_openNormal_le_zassenhausSubgroup
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hfg : TopologicallyFinitelyGenerated G) (n : ℕ) :
    ∃ U : OpenNormalSubgroup G, (U : Subgroup G) ≤ zassenhausSubgroup p G n := by
  have hsucc : ∀ m : ℕ, ∃ U : OpenNormalSubgroup G,
      (U : Subgroup G) ≤ zassenhausSubgroup p G (m + 1) := by
    intro m
    induction m with
    | zero =>
        refine ⟨⊤, ?_⟩
        simp only [Nat.zero_add, zassenhausSubgroup_one]
        exact le_rfl
    | succ m ih =>
        obtain ⟨U, hU⟩ := ih
        have hfgU : TopologicallyFinitelyGenerated (U : Subgroup G) :=
          topologicallyFinitelyGenerated_openSubgroup hfg U.toOpenSubgroup
        let W : OpenNormalSubgroup (U : Subgroup G) :=
          closedPowerCommutatorOpenNormal p hfgU
        let H : Subgroup G := (W : Subgroup (U : Subgroup G)).map (U : Subgroup G).subtype
        have hHopen : IsOpen (H : Set G) := by
          change IsOpen ((Subtype.val : ↥(U : Subgroup G) → G) ''
            (W : Set (U : Subgroup G)))
          exact U.toOpenSubgroup.isOpen.isOpenMap_subtype_val _ W.toOpenSubgroup.isOpen
        obtain ⟨V, hV⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
          hHopen H.one_mem
        have hHdepth : H ≤ zassenhausSubgroup p G (2 * (m + 1)) :=
          closedPowerCommutator_map_le_zassenhaus_double p (U : Subgroup G) (m + 1) hU
        refine ⟨V, fun g hg ↦ ?_⟩
        exact zassenhausSubgroup_antitone p G (by omega : m + 1 + 1 ≤ 2 * (m + 1))
          (hHdepth (hV hg))
  obtain ⟨U, hU⟩ := hsucc n
  exact ⟨U, hU.trans (zassenhausSubgroup_antitone p G (Nat.le_succ n))⟩

/-- The closed augmentation filtration is open at every finite degree for
a finitely generated profinite group. -/
theorem isOpen_zassenhausSubgroup
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hfg : TopologicallyFinitelyGenerated G) (n : ℕ) :
    IsOpen (zassenhausSubgroup p G n : Set G) := by
  obtain ⟨U, hU⟩ := exists_openNormal_le_zassenhausSubgroup p hfg n
  exact Subgroup.isOpen_mono hU U.toOpenSubgroup.isOpen

/-- Selecting a finite quotient through the image of a deep source subgroup
provides actual source lifts with the same lower depth bound. -/
theorem exists_openNormal_with_zassenhaus_lifts
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    (hfg : TopologicallyFinitelyGenerated G) (q : G →ₜ* H)
    (hq : Function.Surjective q) (n : ℕ) :
    ∃ U : OpenNormalSubgroup H, ∀ g : H, g ∈ U →
      ∃ f : G, q f = g ∧ ZassenhausDepthAtLeast p n f := by
  obtain ⟨V, hV⟩ := exists_openNormal_le_zassenhausSubgroup p hfg n
  let U : OpenNormalSubgroup H := OpenNormalSubgroup.map q
    (ContinuousMonoidHom.isOpenMap_of_surjective_compact_t2 q hq) hq V
  refine ⟨U, ?_⟩
  intro g hg
  change g ∈ (V : Subgroup G).map q.toMonoidHom at hg
  obtain ⟨f, hf, rfl⟩ := hg
  exact ⟨f, rfl, hV hf⟩

end

end ClassFieldTower.ProP
