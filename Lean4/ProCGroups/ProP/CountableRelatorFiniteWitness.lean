import ProCGroups.ProP.ClosedChainStabilization
import ProCGroups.FiniteGeneration.OpenSubgroups
import ProCGroups.Presentations.Profinite
import ProCGroups.ProC.Subgroups.Closed
import ProCGroups.FiniteGroups.StandardClasses
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.GroupTheory.Index
import Mathlib.Topology.Algebra.Group.ClosedSubgroup

set_option autoImplicit false

/-!
# A finite witness for a finite quotient by countably many relations

If a finitely generated pro-p group modulo a closed normal relator closure
is finite, its open kernel is finitely generated. The finite Frattini
quotient of that kernel then supplies a finite prefix with the same closed
normal closure. No finite presentation of the countable quotient is an input.
-/

namespace ClassFieldTower.ProP

open ProCGroups ProCGroups.Presentations ProCGroups.FiniteGeneration

universe u

section Closure

variable {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]

private theorem prefix_closedNormalClosure_mono (R₀ : Set F) (f : ℕ → F) :
    Monotone (fun n ↦ closedNormalClosure (R₀ ∪ f '' (Finset.range n : Set ℕ))) := by
  intro m n hmn
  apply closedNormalClosure_le_closed_normal (closedNormalClosure_isClosed _)
  apply Set.Subset.trans _ (subset_closedNormalClosure _)
  exact Set.union_subset_union_right R₀
    (Set.image_mono (by exact_mod_cast Finset.range_mono hmn))

private theorem prefix_closedNormalClosure_le (R₀ : Set F) (f : ℕ → F) (n : ℕ) :
    closedNormalClosure (R₀ ∪ f '' (Finset.range n : Set ℕ)) ≤
      closedNormalClosure (R₀ ∪ Set.range f) := by
  apply closedNormalClosure_le_closed_normal (closedNormalClosure_isClosed _)
  apply Set.Subset.trans _ (subset_closedNormalClosure _)
  exact Set.union_subset_union_right R₀ (Set.image_subset_range _ _)

/-- The closed normal closure of countably many new relators is the
closure of the increasing supremum of the finite-prefix normal closures. -/
theorem closedNormalClosure_countable_eq_closure_iSup (R₀ : Set F) (f : ℕ → F) :
    closedNormalClosure (R₀ ∪ Set.range f) =
      (⨆ n, closedNormalClosure (R₀ ∪ f '' (Finset.range n : Set ℕ))).topologicalClosure := by
  let H : ℕ → Subgroup F := fun n ↦
    closedNormalClosure (R₀ ∪ f '' (Finset.range n : Set ℕ))
  change closedNormalClosure (R₀ ∪ Set.range f) = (⨆ n, H n).topologicalClosure
  apply le_antisymm
  · let : ∀ n, (H n).Normal := fun _ ↦ inferInstance
    let : (⨆ n, H n).Normal := Subgroup.iSup_normal H
    let : ((⨆ n, H n).topologicalClosure).Normal :=
      Subgroup.is_normal_topologicalClosure _
    apply closedNormalClosure_le_closed_normal (Subgroup.isClosed_topologicalClosure _)
    intro x hx
    apply Subgroup.le_topologicalClosure _
    rcases hx with hx | ⟨n, rfl⟩
    · exact (le_iSup H 0) (subset_closedNormalClosure _ (Or.inl hx))
    · apply le_iSup H (n + 1)
      apply subset_closedNormalClosure _
      exact Or.inr ⟨n, by simp, rfl⟩
  · apply Subgroup.topologicalClosure_minimal _ _ (closedNormalClosure_isClosed _)
    exact iSup_le (prefix_closedNormalClosure_le R₀ f)

end Closure

private theorem exists_stage_eq_of_closed_sup
    {p : ℕ} [Fact p.Prime]
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
    (hpro : ProC.HasPGroupOpenNormalBasis p F)
    (R : Subgroup F) (hRclosed : IsClosed (R : Set F))
    (hRfg : TopologicallyFinitelyGenerated R)
    (H : ℕ → Subgroup F) (hmono : Monotone H)
    (hclosed : ∀ n, IsClosed (H n : Set F))
    (hle : ∀ n, H n ≤ R)
    (hclosure : (⨆ n, H n).topologicalClosure = R) :
    ∃ n, H n = R := by
  let : CompactSpace R := hRclosed.isClosedEmbedding_subtypeVal.compactSpace
  have hRpro : ProC.HasPGroupOpenNormalBasis p R :=
    ProC.HasOpenNormalBasisInClass.of_isClosed_subgroup
      (FiniteGroupClass.pGroup_formation p).isomClosed
      (FiniteGroupClass.pGroup_subgroupClosed p) hpro R hRclosed
  let K : ℕ → Subgroup R := fun n ↦ (H n).subgroupOf R
  have hKmono : Monotone K := by
    intro m n hmn
    exact Subgroup.comap_mono (hmono hmn)
  have hKclosed : ∀ n, IsClosed (K n : Set R) := by
    intro n
    exact (hclosed n).preimage continuous_subtype_val
  have hmap : (⨆ n, K n).map R.subtype = ⨆ n, H n := by
    rw [Subgroup.map_iSup]
    congr 1
    funext n
    exact Subgroup.map_subgroupOf_eq_of_le (hle n)
  have hKdense : (⨆ n, K n).topologicalClosure = ⊤ := by
    apply SetLike.coe_injective
    rw [Subgroup.topologicalClosure_coe, Subgroup.coe_top, ← dense_iff_closure_eq]
    apply Subtype.dense_iff.mpr
    have hImage : R.subtype '' (⨆ n, K n : Subgroup R) =
        (⨆ n, H n : Subgroup F) := by
      rw [← Subgroup.coe_map, hmap]
    change (R : Set F) ⊆ closure (R.subtype '' (⨆ n, K n : Subgroup R))
    rw [hImage, ← Subgroup.topologicalClosure_coe, hclosure]
  obtain ⟨n, hn⟩ := exists_eq_top_of_monotone_closedSubgroups
    hRpro hRfg K hKmono hKclosed hKdense
  refine ⟨n, ?_⟩
  calc
    H n = (K n).map R.subtype := (Subgroup.map_subgroupOf_eq_of_le (hle n)).symm
    _ = R := by rw [hn, ← MonoidHom.range_eq_map, R.range_subtype]

/-- A finite quotient by a countable closed normal relator closure already
has the same kernel after a finite prefix of the added relations. -/
theorem exists_finitePrefix_eq_closedNormalClosure_of_finite_quotient
    {p : ℕ} [Fact p.Prime]
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
    (hpro : ProC.HasPGroupOpenNormalBasis p F)
    (hfg : TopologicallyFinitelyGenerated F)
    (R₀ : Set F) (f : ℕ → F)
    [Finite (F ⧸ closedNormalClosure (R₀ ∪ Set.range f))] :
    ∃ n, closedNormalClosure (R₀ ∪ f '' (Finset.range n : Set ℕ)) =
      closedNormalClosure (R₀ ∪ Set.range f) := by
  let R : Subgroup F := closedNormalClosure (R₀ ∪ Set.range f)
  have hRclosed : IsClosed (R : Set F) := closedNormalClosure_isClosed _
  let : R.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hRopen : IsOpen (R : Set F) := R.isOpen_of_isClosed_of_finiteIndex hRclosed
  let U : OpenSubgroup F := ⟨R, hRopen⟩
  have hRfg : TopologicallyFinitelyGenerated R :=
    topologicallyFinitelyGenerated_openSubgroup hfg U
  apply exists_stage_eq_of_closed_sup hpro R hRclosed hRfg
    (fun n ↦ closedNormalClosure (R₀ ∪ f '' (Finset.range n : Set ℕ)))
    (prefix_closedNormalClosure_mono R₀ f)
    (fun _ ↦ closedNormalClosure_isClosed _)
    (prefix_closedNormalClosure_le R₀ f)
  exact (closedNormalClosure_countable_eq_closure_iSup R₀ f).symm

end ClassFieldTower.ProP
