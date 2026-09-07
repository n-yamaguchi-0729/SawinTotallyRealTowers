import ProCGroups.Profinite.OpenSubgroups

set_option autoImplicit false

/-!
# Closed subgroups and cosets

This file expresses closed subgroups as intersections of open subgroups and develops separation by
open subgroups. It also proves the disjointness and clopen properties of the relevant cosets.
-/

namespace ProCGroups.ProC

universe u v

section

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/--
A closed subgroup of a profinite group is the intersection of all open subgroups containing it.
-/
theorem closedSubgroup_eq_sInf_open [CompactSpace G] [TotallyDisconnectedSpace G]
    (H : ClosedSubgroup G) :
    (H : Subgroup G) = sInf {N : Subgroup G | IsOpen (N : Set G) ∧ (H : Subgroup G) ≤ N} := by
  ext x
  constructor
  · intro hx
    simp only [Subgroup.mem_sInf, Set.mem_ofPred_eq]
    intro N hN
    exact hN.2 hx
  · intro hx
    by_contra hxH
    let W : Set G := { y : G | x * y⁻¹ ∉ (H : Set G) }
    have hW : IsOpen W := by
      change IsOpen ((fun y : G => x * y⁻¹) ⁻¹' ((H : Set G)ᶜ))
      exact H.isClosed'.isOpen_compl.preimage (continuous_const.mul continuous_inv)
    have h1W : (1 : G) ∈ W := by
      simp only [W, Set.mem_ofPred_eq, inv_one, mul_one]
      exact hxH
    rcases ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
        (G := G) hW h1W with ⟨N, hNW⟩
    let K : OpenSubgroup G :=
      ⟨(H : Subgroup G) ⊔ (N : Subgroup G),
        Subgroup.isOpen_of_openSubgroup ((H : Subgroup G) ⊔ (N : Subgroup G))
          (show (N : Subgroup G) ≤ (H : Subgroup G) ⊔ (N : Subgroup G) from le_sup_right)⟩
    have hHK : (H : Subgroup G) ≤ (K : Subgroup G) := by
      intro y hy
      exact Subgroup.mem_sup_left hy
    have hxK : x ∈ (K : Subgroup G) := by
      have hxall : ∀ N : Subgroup G, IsOpen (N : Set G) ∧ (H : Subgroup G) ≤ N → x ∈ N := by
        simpa only [Subgroup.mem_sInf, Set.mem_ofPred_eq] using hx
      exact hxall (K : Subgroup G) ⟨openSubgroup_isOpen (G := G) K, hHK⟩
    rcases
        (Subgroup.mem_sup_of_normal_right (s := (H : Subgroup G)) (t := (N : Subgroup G))).1
          hxK with
      ⟨h, hhH, n, hnN, hxn⟩
    have hnW : n ∈ W := hNW hnN
    have : h ∉ (H : Set G) := by
      simpa [W, hxn.symm, mul_assoc] using hnW
    exact this hhH

end

section

variable {G : Type u} [Group G]

/--
If the intersection of a family of subgroups is trivial, every nonidentity element is omitted by
at least one member of the family.
-/
theorem exists_not_mem_of_iInf_eq_bot {ι : Type v} (U : ι → Subgroup G)
    (hU : iInf U = (⊥ : Subgroup G)) {x : G} (hx : x ≠ 1) :
    ∃ i : ι, x ∉ U i := by
  by_contra h
  have hxall : ∀ i : ι, x ∈ U i := by
    intro i
    by_contra hxi
    exact h ⟨i, hxi⟩
  have hxinf : x ∈ iInf U := by
    simpa [Subgroup.mem_iInf] using hxall
  have hxbot : x ∈ (⊥ : Subgroup G) := by
    simpa [hU] using hxinf
  exact hx (by simpa using hxbot)

/-- Distinct left cosets of a subgroup are disjoint. -/
theorem disjoint_leftCoset_of_not_mem (U : Subgroup G) {x y : G} (hxy : x⁻¹ * y ∉ U) :
    Disjoint {g : G | x⁻¹ * g ∈ U} {g : G | y⁻¹ * g ∈ U} := by
  refine Set.disjoint_left.2 ?_
  intro g hx hg
  apply hxy
  have hmul : (x⁻¹ * g) * (y⁻¹ * g)⁻¹ ∈ U := U.mul_mem hx (U.inv_mem hg)
  simpa [mul_assoc] using hmul

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- The left coset of an open subgroup is clopen. -/
theorem isClopen_leftCoset_openSubgroup (U : OpenSubgroup G) (x : G) :
    IsClopen {g : G | x⁻¹ * g ∈ (U : Subgroup G)} := by
  let f : G → G := fun g => x⁻¹ * g
  have hf : Continuous f := continuous_const.mul continuous_id
  have hcoset :
      {g : G | x⁻¹ * g ∈ (U : Subgroup G)} =
        f ⁻¹' (U : Set G) := by
    ext g
    rfl
  rw [hcoset]
  refine ⟨?_, ?_⟩
  · exact U.isClosed.preimage hf
  · exact U.isOpen.preimage hf

end

end ProCGroups.ProC
