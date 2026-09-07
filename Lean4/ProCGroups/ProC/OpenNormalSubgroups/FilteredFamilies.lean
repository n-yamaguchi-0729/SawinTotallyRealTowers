import ProCGroups.ProC.OpenNormalSubgroups.BasisAtOne
import ProCGroups.ProC.OpenNormalSubgroups.ClosedAndCosets

set_option autoImplicit false

/-!
# Filtered families of open subgroups

This file proves compactness and intersection lemmas for directed families of closed and open
subgroups. These results produce finite-intersection neighborhood bases and control images of
intersections under continuous surjections.
-/

namespace ProCGroups.ProC

open Set
open scoped Topology Pointwise

universe u v w

section

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/--
A nonempty finite subfamily of a directed family of sets has a common lower bound for the
reverse-inclusion order.
-/
theorem directed_finset_has_lower_bound {α : Type*} {ι : Type*} {U : ι → Set α}
    (hdir : Directed (· ⊇ ·) U) :
    ∀ s : Finset ι, s.Nonempty → ∃ k : ι, ∀ i ∈ s, U k ⊆ U i := by
  classical
  intro s
  refine Finset.induction_on s ?_ ?_
  · intro hs
    rcases hs with ⟨i, hi⟩
    simp only [Finset.notMem_empty] at hi
  · intro a s ha ih hs
    by_cases hs' : s.Nonempty
    · rcases ih hs' with ⟨j, hj⟩
      rcases hdir a j with ⟨k, hka, hkj⟩
      refine ⟨k, ?_⟩
      intro i hi
      rw [Finset.mem_insert] at hi
      rcases hi with rfl | hi
      · exact hka
      · exact hkj.trans (hj i hi)
    · have hs_singleton : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs'
      refine ⟨a, ?_⟩
      intro i hi
      have : i = a := by
        simpa [hs_singleton] using hi
      subst this
      exact Subset.rfl

/--
For a closed subgroup of a profinite group, multiplication by the intersection of a filtered
family of closed sets is the intersection of the products.
-/
theorem closedSubgroup_mul_iInter_eq_iInter_mul [CompactSpace G]
    (H : ClosedSubgroup G) {ι : Type v} (U : ι → Set G)
    (hclosed : ∀ i, IsClosed (U i))
    (hdir : Directed (· ⊇ ·) U) :
    ((H : Set G) * ⋂ i, U i) = ⋂ i, ((H : Set G) * U i) := by
  classical
  ext x
  constructor
  · intro hx
    rcases hx with ⟨h, hhH, u, hu, rfl⟩
    refine Set.mem_iInter.2 ?_
    intro i
    exact ⟨h, hhH, u, Set.mem_iInter.1 hu i, rfl⟩
  · intro hx
    by_cases hι : Nonempty ι
    · let A : ι → Set H := fun i => {h : H | ((h : G)⁻¹ * x) ∈ U i}
      have hAclosed : ∀ i, IsClosed (A i) := by
        intro i
        change IsClosed (((fun h : H => ((h : G)⁻¹ * x)) ⁻¹' U i))
        exact (hclosed i).preimage (continuous_subtype_val.inv.mul continuous_const)
      have hAfin : ∀ s : Finset ι, (⋂ i ∈ s, A i).Nonempty := by
        intro s
        by_cases hs : s.Nonempty
        · rcases directed_finset_has_lower_bound hdir s hs with ⟨k, hk⟩
          rcases Set.mem_iInter.1 hx k with ⟨h, hhH, u, huK, hmul⟩
          refine ⟨⟨h, hhH⟩, ?_⟩
          refine Set.mem_iInter₂.2 ?_
          intro i hi
          change h⁻¹ * x ∈ U i
          rw [← hmul]
          simpa [mul_assoc] using hk i hi huK
        · refine ⟨1, ?_⟩
          simp only [Finset.not_nonempty_iff_eq_empty.mp hs, Finset.notMem_empty,
              iInter_of_empty, iInter_univ,
  mem_univ]
      have hA : (⋂ i, A i).Nonempty := by
        simpa using
          (isCompact_univ : IsCompact (Set.univ : Set H)).inter_iInter_nonempty A hAclosed
            (fun s => by
              simpa [Set.inter_univ] using hAfin s)
      rcases hA with ⟨h, hh⟩
      have hhU : ∀ i, ((h : G)⁻¹ * x) ∈ U i := by
        intro i
        exact Set.mem_iInter.1 hh i
      refine ⟨(h : G), h.2, ((h : G)⁻¹ * x), Set.mem_iInter.2 hhU, by simp only
          [mul_inv_cancel_left]⟩
    · have : IsEmpty ι := not_nonempty_iff.mp hι
      have hxuniv : x ∈ ((H : Set G) * (Set.univ : Set G)) := by
        exact ⟨1, H.one_mem, x, Set.mem_univ x, one_mul x⟩
      rw [Set.iInter_of_empty]
      exact hxuniv

/--
Continuous surjections commute with the intersection of a filtered family of closed sets in a
compact domain.
-/
theorem continuous_surjective_image_iInter_eq_iInter_image {X : Type u}
    [TopologicalSpace X] [CompactSpace X] {R : Type v} [TopologicalSpace R] [T2Space R]
    (φ : X → R) (hφ : Continuous φ) (hsurj : Function.Surjective φ)
    {ι : Type w} (U : ι → Set X)
    (hclosed : ∀ i, IsClosed (U i))
    (hdir : Directed (· ⊇ ·) U) :
    φ '' ⋂ i, U i = ⋂ i, φ '' U i := by
  classical
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine Set.mem_iInter.2 ?_
    intro i
    exact ⟨x, Set.mem_iInter.1 hx i, rfl⟩
  · intro hy
    by_cases hι : Nonempty ι
    · let A : ι → Set X := fun i => U i ∩ φ ⁻¹' ({y} : Set R)
      have hAclosed : ∀ i, IsClosed (A i) := by
        intro i
        exact (hclosed i).inter ((isClosed_singleton.preimage hφ))
      have hAfin : ∀ s : Finset ι, (⋂ i ∈ s, A i).Nonempty := by
        intro s
        by_cases hs : s.Nonempty
        · rcases directed_finset_has_lower_bound hdir s hs with ⟨k, hk⟩
          rcases Set.mem_iInter.1 hy k with ⟨x, hxU, hxy⟩
          refine ⟨x, Set.mem_iInter₂.2 ?_⟩
          intro i hi
          refine ⟨hk i hi hxU, ?_⟩
          simpa [Set.mem_singleton_iff] using hxy
        · rcases hsurj y with ⟨x, rfl⟩
          refine ⟨x, ?_⟩
          simp only [Finset.not_nonempty_iff_eq_empty.mp hs, Finset.notMem_empty,
              iInter_of_empty, iInter_univ,
  mem_univ]
      have hA : (⋂ i, A i).Nonempty := by
        simpa using
          (isCompact_univ : IsCompact (Set.univ : Set X)).inter_iInter_nonempty A hAclosed
            (fun s => by
              simpa [Set.inter_univ] using hAfin s)
      rcases hA with ⟨x, hx⟩
      refine ⟨x, ?_, ?_⟩
      · exact Set.mem_iInter.2 fun i => (Set.mem_iInter.1 hx i).1
      · simpa [Set.mem_singleton_iff] using (Set.mem_iInter.1 hx (Classical.choice hι)).2
    · have : IsEmpty ι := not_nonempty_iff.mp hι
      simpa [Set.iInter_of_empty, this] using hsurj y

/--
Every open subgroup containing a closed subgroup also contains a set of the form \(H U\) with
\(U\) open and normal.
-/
theorem exists_openNormalSubgroup_mul_subset_openSubgroup [CompactSpace G]
    (H : ClosedSubgroup G) (V : OpenSubgroup G)
    (hHV : (H : Subgroup G) ≤ (V : Subgroup G)) :
    ∃ U : OpenNormalSubgroup G, ((H : Set G) * (U : Set G)) ⊆ (V : Set G) := by
  have hVfin : Subgroup.FiniteIndex (V : Subgroup G) := V.finiteIndex_of_finite_quotient
  let U : OpenNormalSubgroup G :=
    { toSubgroup := Subgroup.normalCore V
      isOpen' := Subgroup.isOpen_of_isClosed_of_finiteIndex _ (V.normalCore_isClosed V.isClosed) }
  refine ⟨U, ?_⟩
  intro x hx
  rcases hx with ⟨h, hhH, u, huU, rfl⟩
  exact V.mul_mem (hHV hhH) (V.normalCore_le huU)

/--
A closed normal subgroup of a profinite group is the intersection of all open normal subgroups
containing it.
-/
theorem closedSubgroup_eq_sInf_openNormal [CompactSpace G] [TotallyDisconnectedSpace G]
    (H : ClosedSubgroup G) [((H : Subgroup G).Normal)] :
    (H : Subgroup G) =
      sInf {N : Subgroup G | IsOpen (N : Set G) ∧ (H : Subgroup G) ≤ N ∧ N.Normal} := by
  ext x
  constructor
  · intro hx
    simp only [Subgroup.mem_sInf, Set.mem_ofPred_eq]
    intro N hN
    exact hN.2.1 hx
  · intro hx
    have hxall :
        ∀ N : Subgroup G, IsOpen (N : Set G) ∧ (H : Subgroup G) ≤ N ∧ N.Normal → x ∈ N := by
      simpa only [Subgroup.mem_sInf, Set.mem_ofPred_eq] using hx
    have hxOpen :
        x ∈ sInf {N : Subgroup G | IsOpen (N : Set G) ∧ (H : Subgroup G) ≤ N} := by
      simp only [Subgroup.mem_sInf, Set.mem_ofPred_eq]
      intro N hN
      have hNfin : Subgroup.FiniteIndex N := by
        let : Finite (G ⧸ N) := Subgroup.quotient_finite_of_isOpen N hN.1
        exact Subgroup.finiteIndex_of_finite_quotient
      have hcoreOpen : IsOpen (N.normalCore : Set G) := by
        exact Subgroup.isOpen_of_isClosed_of_finiteIndex _ (N.normalCore_isClosed
          (Subgroup.isClosed_of_isOpen N hN.1))
      have hHcore : (H : Subgroup G) ≤ N.normalCore := (Subgroup.normal_le_normalCore).2 hN.2
      have hxcore : x ∈ N.normalCore := by
        exact hxall N.normalCore ⟨hcoreOpen, hHcore, inferInstance⟩
      exact N.normalCore_le hxcore
    exact (closedSubgroup_eq_sInf_open (G := G) H) ▸ hxOpen

end


section

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- If the intersection of a family of closed subgroups lies inside an
open subgroup, then already a finite subfamily has the same property.

We formulate the family as plain subgroups together with explicit closedness hypotheses in order
to keep the later API flexible.
-/
theorem finite_iInter_subgroup_subset_openSubgroup [CompactSpace G] {ι : Type v}
    (H : ι → Subgroup G)
    (hclosed : ∀ i, IsClosed (((H i : Subgroup G) : Set G)))
    (U : OpenSubgroup G)
    (hInter : (⋂ i, (((H i : Subgroup G) : Set G))) ⊆ (((U : Subgroup G) : Set G))) :
    ∃ s : Finset ι, (⋂ i ∈ s, (((H i : Subgroup G) : Set G))) ⊆ (((U : Subgroup G) : Set G)) := by
  let K : Set G := (((U : Subgroup G) : Set G))ᶜ
  have hKclosed : IsClosed K := by
    simpa [K] using (openSubgroup_isOpen (G := G) U).isClosed_compl
  have hKcompact : IsCompact K := hKclosed.isCompact
  have havoid : K ∩ ⋂ i, (((H i : Subgroup G) : Set G)) = ∅ := by
    ext x
    constructor
    · intro hx
      exact False.elim (hx.1 (hInter hx.2))
    · intro hx
      simp only [mem_empty_iff_false] at hx
  rcases hKcompact.elim_finite_subfamily_closed
      (fun i => (((H i : Subgroup G) : Set G))) hclosed havoid with ⟨s, hs⟩
  refine ⟨s, ?_⟩
  intro x hx
  by_contra hxU
  have hxK : x ∈ K := by
    simpa [K] using hxU
  have hmem : x ∈ K ∩ ⋂ i ∈ s, (((H i : Subgroup G) : Set G)) := by
    exact ⟨hxK, hx⟩
  have : x ∈ (∅ : Set G) := by
    simp only [hs, mem_empty_iff_false] at hmem
  simp only [mem_empty_iff_false] at this

/-- If a family of open subgroups of a profinite group has trivial total
intersection, then finite intersections of members of the family form a neighborhood basis of `1`.
-/
theorem finite_openSubgroup_intersections_form_nhds_basis [CompactSpace G]
    [IsTopologicalGroup G] [TotallyDisconnectedSpace G] {ι : Type v} (U : ι → OpenSubgroup G)
    (hInter : (⋂ i, (((U i : Subgroup G) : Set G))) = ({1} : Set G)) :
    ∀ W : Set G, IsOpen W → (1 : G) ∈ W →
      ∃ s : Finset ι, (⋂ i ∈ s, (((U i : Subgroup G) : Set G))) ⊆ W := by
  intro W hW h1W
  rcases exists_openNormalSubgroup_sub_open_nhds_of_one (G := G) hW h1W with ⟨N, hNW⟩
  have hInterN : (⋂ i, (((U i : Subgroup G) : Set G))) ⊆ (((N : Subgroup G) : Set G)) := by
    intro x hx
    have hx1 : x = 1 := by
      have hxsingleton : x ∈ ({1} : Set G) := by
        rw [← hInter]
        exact hx
      simpa using hxsingleton
    simp only [OpenSubgroup.coe_toSubgroup, hx1, SetLike.mem_coe, one_mem]
  rcases finite_iInter_subgroup_subset_openSubgroup (G := G)
      (fun i => (U i : Subgroup G))
      (fun i => openSubgroup_isClosed (G := G) (U i))
      N.toOpenSubgroup hInterN with ⟨s, hs⟩
  exact ⟨s, hs.trans hNW⟩

end

end ProCGroups.ProC
