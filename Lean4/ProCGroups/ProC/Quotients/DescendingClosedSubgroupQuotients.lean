import ProCGroups.ProC.Quotients.OpenSubgroupSections

set_option autoImplicit false

/-!
# Quotients along descending closed-subgroup systems

This file constructs the inverse system of left quotients associated with a directed descending
family of closed subgroups and proves the existence of compatible continuous lifts into its
limit.
-/

open Set
open scoped Topology Pointwise

namespace ProCGroups.ProC

universe u v

open InverseSystems

variable {I : Type v} [Preorder I] [Nonempty I]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- The infimum of a family of closed subgroups, repackaged as a closed subgroup. -/
def closedSubgroup_sInf (L : I → ClosedSubgroup G) : ClosedSubgroup G where
  toSubgroup := iInf fun i => (L i : Subgroup G)
  isClosed' := by
    convert isClosed_iInter fun i => (L i).isClosed' using 1
    ext x
    simp only [Subsemigroup.mem_carrier, Submonoid.mem_toSubsemigroup, Subgroup.mem_toSubmonoid,
  Subgroup.mem_iInf, mem_iInter]

/-- The infimum subgroup is contained in each term of the family. -/
theorem closedSubgroup_sInf_le {I : Type v} {G : Type u} [Group G] [TopologicalSpace G]
    (L : I → ClosedSubgroup G) (i : I) :
    (closedSubgroup_sInf L : Subgroup G) ≤ (L i : Subgroup G) := by
  exact iInf_le _ i

/--
The inverse system of left quotient spaces attached to a decreasing family of closed subgroups.
-/
def descendingClosedSubgroupSystem (L : I → ClosedSubgroup G)
    (hL : ∀ {i j}, i ≤ j → (L j : Subgroup G) ≤ (L i : Subgroup G)) :
    InverseSystems.InverseSystem (I := I) where
  X i := G ⧸ (L i : Subgroup G)
  topologicalSpace i := inferInstance
  map := fun {i j} hij =>
    leftQuotientProjection (L j : Subgroup G) (L i : Subgroup G) (hL hij)
  continuous_map := by
    intro i j hij
    exact continuous_leftQuotientProjection
      (K := (L j : Subgroup G)) (H := (L i : Subgroup G)) (hL hij)
  map_id := by
    intro i
    exact leftQuotientProjection_id (K := (L i : Subgroup G))
  map_comp := by
    intro i j k hij hjk
    exact
      leftQuotientProjection_comp
        (K := (L k : Subgroup G)) (H := (L j : Subgroup G)) (L := (L i : Subgroup G))
        (hL hjk) (hL hij)

omit [T2Space G] [TotallyDisconnectedSpace G] in
/--
A compatible family of maps into a decreasing family of left quotient spaces lifts uniquely to
the quotient by the infimum subgroup.
-/
theorem exists_continuous_leftQuotient_lift_of_directed
    (L : I → ClosedSubgroup G)
    (hL : ∀ {i j}, i ≤ j → (L j : Subgroup G) ≤ (L i : Subgroup G))
    (hdir : Directed (· ≤ ·) (id : I → I))
    {Y : Type v} [TopologicalSpace Y]
    (η : ∀ i, Y → G ⧸ (L i : Subgroup G))
    (hηcont : ∀ i, Continuous (η i))
    (hηcompat : ∀ {i j} (hij : i ≤ j),
      leftQuotientProjection (L j : Subgroup G) (L i : Subgroup G) (hL hij) ∘ η j = η i)
    (y0 : Y)
    (hηone : ∀ i, η i y0 = QuotientGroup.mk (s := (L i : Subgroup G)) (1 : G)) :
    ∃ ηinf : Y → G ⧸ ((closedSubgroup_sInf L : ClosedSubgroup G) : Subgroup G),
      Continuous ηinf ∧
        (∀ i,
          leftQuotientProjection
              (((closedSubgroup_sInf L : ClosedSubgroup G) : Subgroup G))
              (L i : Subgroup G)
              (closedSubgroup_sInf_le (L := L) i) ∘ ηinf = η i) ∧
        ηinf y0 =
          QuotientGroup.mk (s := (((closedSubgroup_sInf L : ClosedSubgroup G) : Subgroup G)))
            (1 : G) := by
  classical
  let Linf : ClosedSubgroup G := closedSubgroup_sInf L
  let S : InverseSystems.InverseSystem (I := I) := descendingClosedSubgroupSystem L hL
  let : ∀ i, T2Space (S.X i) := fun i => by
    change T2Space (G ⧸ (L i : Subgroup G))
    have : IsClosed ((L i : Subgroup G) : Set G) := (L i).isClosed'
    exact QuotientGroup.instT2Space (H := (L i : Subgroup G))
  let ψ : ∀ i, G ⧸ ((Linf : ClosedSubgroup G) : Subgroup G) → S.X i := fun i =>
    leftQuotientProjection
      (((Linf : ClosedSubgroup G) : Subgroup G))
      (L i : Subgroup G)
      (closedSubgroup_sInf_le (L := L) i)
  have hψcont : ∀ i, Continuous (ψ i) := by
    intro i
    exact continuous_leftQuotientProjection
      (K := (((Linf : ClosedSubgroup G) : Subgroup G)))
      (H := (L i : Subgroup G))
      (closedSubgroup_sInf_le (L := L) i)
  have hψcompat : S.CompatibleMaps ψ := by
    intro i j hij
    funext x
    change
      leftQuotientProjection (L j : Subgroup G) (L i : Subgroup G) (hL hij)
          (leftQuotientProjection
            ((Linf : ClosedSubgroup G) : Subgroup G) (L j : Subgroup G)
            (closedSubgroup_sInf_le (L := L) j) x) =
        leftQuotientProjection
          ((Linf : ClosedSubgroup G) : Subgroup G) (L i : Subgroup G)
          (closedSubgroup_sInf_le (L := L) i) x
    exact leftQuotientProjection_comp_apply
      ((Linf : ClosedSubgroup G) : Subgroup G)
      (L j : Subgroup G) (L i : Subgroup G)
      (closedSubgroup_sInf_le (L := L) j) (hL hij) x
  let φ : G ⧸ ((Linf : ClosedSubgroup G) : Subgroup G) → S.inverseLimit :=
    S.inverseLimitLift ψ hψcompat
  have hφcont : Continuous φ := S.continuous_inverseLimitLift ψ hψcont hψcompat
  have hψsurj : ∀ i, Function.Surjective (ψ i) := by
    intro i
    exact surjective_leftQuotientProjection
      (K := (((Linf : ClosedSubgroup G) : Subgroup G)))
      (H := (L i : Subgroup G))
      (closedSubgroup_sInf_le (L := L) i)
  have hφsurj : Function.Surjective φ :=
    S.surjective_inverseLimitLift ψ hψcont hψcompat hψsurj hdir
  have hφinj : Function.Injective φ := by
    intro x y hxy
    rcases Quotient.exists_rep x with ⟨gx, rfl⟩
    rcases Quotient.exists_rep y with ⟨gy, rfl⟩
    apply QuotientGroup.eq.2
    have hcoord :
        ∀ i, gx⁻¹ * gy ∈ (L i : Subgroup G) := by
      intro i
      have hi : ψ i (QuotientGroup.mk (s := (((Linf : ClosedSubgroup G) : Subgroup G))) gx) =
          ψ i (QuotientGroup.mk (s := (((Linf : ClosedSubgroup G) : Subgroup G))) gy) := by
        exact congrArg (fun z : S.inverseLimit => S.projection i z) hxy
      exact QuotientGroup.eq.1 hi
    change gx⁻¹ * gy ∈ iInf fun i => (L i : Subgroup G)
    rw [Subgroup.mem_iInf]
    exact hcoord
  let eTop : G ⧸ ((Linf : ClosedSubgroup G) : Subgroup G) ≃ₜ S.inverseLimit :=
    Continuous.homeoOfEquivCompactToT2
      (f := Equiv.ofBijective φ ⟨hφinj, hφsurj⟩) hφcont
  let ηinf : Y → G ⧸ ((Linf : ClosedSubgroup G) : Subgroup G) :=
    eTop.symm ∘ S.inverseLimitLift η (by
      intro i j hij
      simpa only [S, descendingClosedSubgroupSystem, Function.comp] using hηcompat hij)
  have hηinf_continuous : Continuous ηinf := by
    exact eTop.continuous_invFun.comp <| S.continuous_inverseLimitLift η hηcont <| by
      intro i j hij
      simpa only [S, descendingClosedSubgroupSystem, Function.comp] using hηcompat hij
  have hηinf_fac :
      ∀ i,
        leftQuotientProjection
            (((closedSubgroup_sInf L : ClosedSubgroup G) : Subgroup G))
            (L i : Subgroup G)
            (closedSubgroup_sInf_le (L := L) i) ∘ ηinf = η i := by
    intro i
    funext y
    have hfac :=
      congrFun (S.projection_comp_inverseLimitLift η
        (by
          intro i j hij
          simpa only [S, descendingClosedSubgroupSystem, Function.comp] using hηcompat hij) i) y
    have hcoord :
        S.projection i (eTop (ηinf y)) = η i y := by
      simpa [ηinf, Function.comp] using hfac
    exact hcoord
  have hηinf_one :
      ηinf y0 =
        QuotientGroup.mk (s := (((closedSubgroup_sInf L : ClosedSubgroup G) : Subgroup G)))
          (1 : G) := by
    apply eTop.injective
    apply S.ext
    intro i
    have hy0 := congrFun (hηinf_fac i) y0
    change leftQuotientProjection
        (((closedSubgroup_sInf L : ClosedSubgroup G) : Subgroup G))
        (L i : Subgroup G)
        (closedSubgroup_sInf_le (L := L) i) (ηinf y0) =
      leftQuotientProjection
        (((closedSubgroup_sInf L : ClosedSubgroup G) : Subgroup G))
        (L i : Subgroup G)
        (closedSubgroup_sInf_le (L := L) i)
        (QuotientGroup.mk
          (s := (((closedSubgroup_sInf L : ClosedSubgroup G) : Subgroup G))) (1 : G))
    simpa [hηone i]
      using hy0
  exact ⟨ηinf, hηinf_continuous, hηinf_fac, hηinf_one⟩

end ProCGroups.ProC
