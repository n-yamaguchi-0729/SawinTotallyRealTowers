import ProCGroups.FiniteGeneration.Basic
import ProCGroups.Generation.Basic
import ProCGroups.ReidemeisterSchreier.Profinite.OpenSubgroups.RankBound
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.SetTheory.Cardinal.ToNat

set_option autoImplicit false

/-!
# Finite generation of open subgroups

The existing Schreier bound makes the least generating cardinal of an open
subgroup finite. A generating set attaining that cardinal then gives an
actual finite generating set, without a new finite-generation hypothesis.
-/

namespace ProCGroups.FiniteGeneration

open ProCGroups.Generation

universe u

/-- An open subgroup of a finitely generated profinite group has an actual
finite topological generating set. -/
theorem topologicallyFinitelyGenerated_openSubgroup
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hfg : TopologicallyFinitelyGenerated G) (U : OpenSubgroup G) :
    TopologicallyFinitelyGenerated (U : Subgroup G) := by
  classical
  obtain ⟨s, hs⟩ := hfg
  have hfinite : topologicalRank G < Cardinal.aleph0 :=
    (topologicalRank_le_mk_of_topologicallyGenerates hs).trans_lt (Cardinal.lt_aleph0_iff_finite.mpr inferInstance)
  have hrank : topologicalRank G = (topologicalRank G).toNat :=
    (Cardinal.cast_toNat_of_lt_aleph0 hfinite).symm
  have hbound :=
    ReidemeisterSchreier.Profinite.topologicalRank_openSubgroup_le_rankTransform_of_topologicalRank_eq_nat
      hrank U
  obtain ⟨X, hX, hXcard⟩ :=
    exists_topologicallyGenerates_card_eq_topologicalRank (G := (U : Subgroup G))
  have hXfinite : Cardinal.mk X < Cardinal.aleph0 :=
    (hXcard.trans_le hbound).trans_lt Cardinal.natCast_lt_aleph0
  let : Finite X := Cardinal.lt_aleph0_iff_finite.mp hXfinite
  refine ⟨(Set.toFinite X).toFinset, ?_⟩
  simpa only [Set.Finite.coe_toFinset] using hX

end ProCGroups.FiniteGeneration
