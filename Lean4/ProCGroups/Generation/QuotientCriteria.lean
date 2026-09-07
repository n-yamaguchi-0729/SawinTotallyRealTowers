import ProCGroups.Generation.Basic
import ProCGroups.InverseSystems.ProjectionImageSystems
import ProCGroups.ProC.OpenNormalSubgroups.Basic
import ProCGroups.ProC.OpenNormalSubgroups.ClosedAndCosets
import ProCGroups.Profinite.Basic

set_option autoImplicit false

/-!
# Detecting topological generation in finite quotients

This module characterizes topological generation in inverse limits by generation of every
finite-stage image.  It specializes the criterion to quotients by open normal subgroups, both
for a set alone and for a set together with a fixed subgroup.
-/

open Set
open scoped Topology Pointwise

namespace ProCGroups.Generation

universe u v

open ProCGroups.InverseSystems
open ProCGroups.ProC
open ProCGroups

section Generators

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- Topological generation in a surjective inverse system can be checked after every projection. -/
theorem topologicallyGenerates_iff_forall_projection_inverseLimit
    {I : Type v} [Preorder I] {S : InverseSystem (I := I)} [Nonempty I]
    [∀ i, Group (S.X i)] [ProCGroups.InverseSystems.IsGroupSystem S]
    [∀ i, IsTopologicalGroup (S.X i)] [∀ i, CompactSpace (S.X i)] [∀ i, T2Space (S.X i)]
    (hdir : Directed (· ≤ ·) (id : I → I))
    (hsurj : ∀ {i j : I} (hij : i ≤ j), Function.Surjective (S.map hij))
    {X : Set S.inverseLimit} :
    TopologicallyGenerates (G := S.inverseLimit) X ↔
      ∀ i, TopologicallyGenerates (G := S.X i) (S.projection i '' X) := by
  classical
  let π : (i : I) → S.inverseLimit →* S.X i :=
    fun i => ProCGroups.InverseSystems.projectionHom (S := S) i
  have hπ (i : I) : (π i : S.inverseLimit → S.X i) = S.projection i := by
    funext x
    exact ProCGroups.InverseSystems.projectionHom_apply (S := S) i x
  have hmap (i : I) :
      (Subgroup.closure X).map (π i) = Subgroup.closure (S.projection i '' X) := by
    exact (MonoidHom.map_closure (π i) X).trans
      (congrArg (fun f : S.inverseLimit → S.X i => Subgroup.closure (f '' X)) (hπ i))
  constructor
  · intro hX i
    have hπsurj : Function.Surjective (π i) :=
      (hπ i).symm ▸ S.surjective_π hdir hsurj i
    have htop :
        ((Subgroup.closure X).map (π i)).topologicalClosure = ⊤ := by
      have hX' : (Subgroup.closure X).topologicalClosure = ⊤ := by
        simpa only [TopologicallyGenerates] using hX
      exact DenseRange.topologicalClosure_map_subgroup
        (f := π i) (hf := (hπ i).symm ▸ S.continuous_projection i)
        (hf' := hπsurj.denseRange) hX'
    simpa only [TopologicallyGenerates, hmap i] using htop
  · intro hproj
    let Y : Set S.inverseLimit :=
      (((Subgroup.closure X).topologicalClosure : Subgroup S.inverseLimit) : Set S.inverseLimit)
    have hYclosed : IsClosed Y := Subgroup.isClosed_topologicalClosure _
    have hprojY : ∀ i, S.projection i '' Y = (Set.univ : Set (S.X i)) := by
      intro i
      have hsubset :
          ((Subgroup.closure (S.projection i '' X) : Subgroup (S.X i)) : Set (S.X i)) ⊆
              S.projection i '' Y := by
        intro y hy
        have hy' : y ∈ (Subgroup.closure X).map (π i) := by
          rw [hmap i]
          exact hy
        rcases hy' with ⟨z, hz, rfl⟩
        exact ⟨z, Subgroup.le_topologicalClosure _ hz, congrFun (hπ i).symm z⟩
      have hclosedImg : IsClosed (S.projection i '' Y) := by
        exact (hYclosed.isCompact.image (S.continuous_projection i)).isClosed
      have hdense :
          Dense (((Subgroup.closure (S.projection i '' X) : Subgroup (S.X i)) : Set (S.X i))) :=
        (topologicallyGenerates_iff_dense (G := S.X i) (X := S.projection i '' X)).1 (hproj i)
      apply Set.eq_univ_iff_forall.2
      intro y
      have hy' :
          y ∈ closure (((Subgroup.closure (S.projection i '' X) : Subgroup (S.X i)) : Set (S.X
              i))) := by
        rw [hdense.closure_eq]
        simp only [mem_univ]
      exact closure_minimal hsubset hclosedImg hy'
    have hYuniv : Y = (Set.univ : Set S.inverseLimit) := by
      ext x
      constructor
      · intro hx
        simp only [mem_univ]
      · intro _
        rw [S.mem_isClosed_iff_forall_projection_mem hdir hYclosed]
        intro i
        rw [hprojY i]
        simp only [InverseSystem.projection_apply, mem_univ]
    rw [TopologicallyGenerates]
    exact SetLike.ext' hYuniv

omit [T2Space G] in
/--
A closed-normal quotient version of topological generation: \(X \cup N\) generates if and only
if the image of \(X\) generates modulo every open normal subgroup containing \(N\).
-/
theorem topologicallyGenerates_union_subgroup_iff_forall_openNormalQuotient
    {N : Subgroup G} [N.Normal]
    {X : Set G} :
    TopologicallyGenerates (G := G) (X ∪ (N : Set G)) ↔
      ∀ U : OpenNormalSubgroup G, N ≤ (U : Subgroup G) →
        TopologicallyGenerates (G := G ⧸ (U : Subgroup G))
          ((QuotientGroup.mk' (U : Subgroup G)) '' X) := by
  classical
  constructor
  · intro hX U hNU
    have hmap :
        TopologicallyGenerates (G := G ⧸ (U : Subgroup G))
          ((QuotientGroup.mk' (U : Subgroup G)) '' (X ∪ (N : Set G))) :=
      topologicallyGenerates_quotient_image (G := G) (N := (U : Subgroup G)) hX
    have himg :
        (QuotientGroup.mk' (U : Subgroup G) '' (X ∪ (N : Set G))) =
          ((QuotientGroup.mk' (U : Subgroup G)) '' X) ∪
            ({1} : Set (G ⧸ (U : Subgroup G))) := by
      ext y
      constructor
      · intro hy
        rcases hy with ⟨x, hx, rfl⟩
        rcases hx with hxX | hxN
        · exact Or.inl ⟨x, hxX, rfl⟩
        · exact Or.inr (by
            simp only [QuotientGroup.mk'_apply, mem_singleton_iff, QuotientGroup.eq_one_iff, hNU
                hxN])
      · intro hy
        rcases hy with hyX | hy1
        · rcases hyX with ⟨x, hxX, rfl⟩
          exact ⟨x, Or.inl hxX, rfl⟩
        · refine ⟨1, Or.inr N.one_mem, ?_⟩
          simpa using hy1.symm
    have hmap' :
        TopologicallyGenerates (G := G ⧸ (U : Subgroup G))
          ((((QuotientGroup.mk' (U : Subgroup G)) '' X) ∪
            ({1} : Set (G ⧸ (U : Subgroup G))))) := by
      rwa [← himg]
    exact
      (topologicallyGenerates_union_one_iff
        (G := G ⧸ (U : Subgroup G))
        (X := ((QuotientGroup.mk' (U : Subgroup G)) '' X))).1 hmap'
  · intro hquot
    let H : ClosedSubgroup G :=
      { toSubgroup := (Subgroup.closure (X ∪ (N : Set G))).topologicalClosure
        isClosed' := Subgroup.isClosed_topologicalClosure _ }
    have hXleH : X ⊆ (H : Subgroup G) := by
      intro x hx
      exact Subgroup.le_topologicalClosure _
        (Subgroup.subset_closure (Or.inl hx))
    have hNleH : N ≤ (H : Subgroup G) := by
      intro n hn
      exact Subgroup.le_topologicalClosure _
        (Subgroup.subset_closure (Or.inr hn))
    by_contra hH
    change ¬ ((Subgroup.closure (X ∪ (N : Set G))).topologicalClosure = ⊤) at hH
    have hHproper :
        ((H : Subgroup G) : Set G) ≠ (Set.univ : Set G) := by
      intro hEq
      apply hH
      change (H : Subgroup G) = ⊤
      ext x
      constructor
      · intro _
        simp only [Subgroup.mem_top]
      · intro _
        have hx' : x ∈ (Set.univ : Set G) := by simp only [mem_univ]
        rwa [← hEq] at hx'
    have hxNotAll : ¬ ∀ x : G, x ∈ ((H : Subgroup G) : Set G) := by
      simpa [Set.eq_univ_iff_forall] using hHproper
    push Not at hxNotAll
    rcases hxNotAll with ⟨x, hxH⟩
    have hxNotAll :
        ¬ ∀ V : Subgroup G, IsOpen (V : Set G) → (H : Subgroup G) ≤ V → x ∈ V := by
      intro hxAll
      apply hxH
      change x ∈ (H : Subgroup G)
      rw [closedSubgroup_eq_sInf_open (G := G) H]
      rw [Subgroup.mem_sInf]
      intro V hV
      exact hxAll V hV.1 hV.2
    push Not at hxNotAll
    rcases hxNotAll with ⟨V, hVopen, hHV, hxV⟩
    have hVfin : Subgroup.FiniteIndex V := by
      let : Finite (G ⧸ V) := Subgroup.quotient_finite_of_isOpen V hVopen
      exact Subgroup.finiteIndex_of_finite_quotient
    let U : OpenNormalSubgroup G :=
      { toSubgroup := Subgroup.normalCore V
        isOpen' := Subgroup.isOpen_of_isClosed_of_finiteIndex _ (V.normalCore_isClosed
          (Subgroup.isClosed_of_isOpen V hVopen)) }
    have hNU : N ≤ (U : Subgroup G) :=
      (Subgroup.normal_le_normalCore).2 (hNleH.trans hHV)
    have hUV : (U : Subgroup G) ≤ V := by
      change Subgroup.normalCore V ≤ V
      exact Subgroup.normalCore_le V
    have hxU : x ∉ (U : Set G) := by
      intro hxU
      exact hxV (hUV hxU)
    have hgen := hquot U hNU
    let qH : Subgroup (G ⧸ (U : Subgroup G)) :=
      (H : Subgroup G).map (QuotientGroup.mk' (U : Subgroup G))
    have himage_le_qH :
        ((QuotientGroup.mk' (U : Subgroup G)) '' X) ⊆
          (qH : Set (G ⧸ (U : Subgroup G))) := by
      intro y hy
      rcases hy with ⟨z, hzX, rfl⟩
      exact ⟨z, hXleH hzX, rfl⟩
    have hcl_le_qH :
        Subgroup.closure (((QuotientGroup.mk' (U : Subgroup G)) '' X)) ≤ qH :=
      (Subgroup.closure_le (K := qH)).2 himage_le_qH
    have hclosure_le_qH :
        (Subgroup.closure (((QuotientGroup.mk' (U : Subgroup G)) '' X))).topologicalClosure ≤
          qH := by
      have hqHclosed : IsClosed (qH : Set (G ⧸ (U : Subgroup G))) := by
        let : DiscreteTopology (G ⧸ (U : Subgroup G)) :=
          OpenNormalSubgroup.quotientDiscrete (G := G) U
        exact isClosed_discrete (qH : Set (G ⧸ (U : Subgroup G)))
      exact Subgroup.topologicalClosure_minimal _ hcl_le_qH hqHclosed
    let qx : G ⧸ (U : Subgroup G) := QuotientGroup.mk' (U : Subgroup G) x
    have hx_not_qH : qx ∉ (qH : Set (G ⧸ (U : Subgroup G))) := by
      intro hxq
      rcases hxq with ⟨z, hzH, hzx⟩
      have hzV : z ∈ V := hHV hzH
      have hdiv : z⁻¹ * x ∈ (U : Subgroup G) := by
        exact (QuotientGroup.eq).1 hzx
      have hdivV : z⁻¹ * x ∈ V := hUV hdiv
      have hxV' : x ∈ V := by
        simpa [mul_assoc] using V.mul_mem hzV hdivV
      exact hxV hxV'
    have hxtop : qx ∈ (((⊤ : Subgroup (G ⧸ (U : Subgroup G))) :
        Set (G ⧸ (U : Subgroup G)))) := by
      simp only [Subgroup.coe_top, mem_univ]
    have htop :
        (⊤ : Subgroup (G ⧸ (U : Subgroup G))) ≤
          (Subgroup.closure (((QuotientGroup.mk' (U : Subgroup G)) '' X))).topologicalClosure := by
      simpa [TopologicallyGenerates] using hgen
    exact hx_not_qH (hclosure_le_qH (htop hxtop))

omit [T2Space G] in
/--
This is the direct finite-quotient test for topological generation, phrased with the bundled
quotient projections.
-/
theorem topologicallyGenerates_iff_forall_quotientProj_image
    {X : Set G} :
    TopologicallyGenerates (G := G) X ↔
      ∀ U : OpenNormalSubgroup G,
        TopologicallyGenerates (G := G ⧸ (U : Subgroup G))
          (OpenNormalSubgroup.quotientProj U '' X) := by
  have h :=
    topologicallyGenerates_union_subgroup_iff_forall_openNormalQuotient
      (G := G) (N := (⊥ : Subgroup G)) (X := X)
  constructor
  · intro hX U
    have hUnion :
        TopologicallyGenerates (G := G) (X ∪ (((⊥ : Subgroup G) : Set G))) := by
      rw [show X ∪ (((⊥ : Subgroup G) : Set G)) = X ∪ ({1} : Set G) by
        ext x
        simp only [Subgroup.coe_bot, union_singleton, mem_insert_iff]]
      exact (topologicallyGenerates_union_one_iff (G := G) (X := X)).2 hX
    have hproj :
        (OpenNormalSubgroup.quotientProj U :
            G → G ⧸ (U : Subgroup G)) =
          (QuotientGroup.mk' (U : Subgroup G) :
            G → G ⧸ (U : Subgroup G)) := by
      rfl
    rw [hproj]
    exact h.1 hUnion U bot_le
  · intro hquot
    have hUnion :
        TopologicallyGenerates (G := G) (X ∪ (((⊥ : Subgroup G) : Set G))) :=
      h.2 (fun U _hU => by
        have hproj :
            (OpenNormalSubgroup.quotientProj U :
                G → G ⧸ (U : Subgroup G)) =
              (QuotientGroup.mk' (U : Subgroup G) :
                G → G ⧸ (U : Subgroup G)) := by
          rfl
        rw [← hproj]
        exact hquot U)
    have hUnionOne : TopologicallyGenerates (G := G) (X ∪ ({1} : Set G)) := by
      rw [show X ∪ ({1} : Set G) = X ∪ (((⊥ : Subgroup G) : Set G)) by
        ext x
        simp only [union_singleton, mem_insert_iff, Subgroup.coe_bot]]
      exact hUnion
    exact (topologicallyGenerates_union_one_iff (G := G) (X := X)).1 hUnionOne


variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

end Generators
end ProCGroups.Generation
