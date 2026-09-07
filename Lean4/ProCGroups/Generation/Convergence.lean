import Mathlib.Topology.Compactification.OnePoint.Basic
import ProCGroups.Generation.Basic
import ProCGroups.ProC.OpenNormalSubgroups.BasisAtOne
import ProCGroups.Profinite.Basic

set_option autoImplicit false

/-!
# Convergence of generating sets in profinite groups

The open-subgroup convergence predicate is shown to be stable under pointed continuous maps,
subsets, and finite modifications.  For a generating set containing one, the module identifies
its closure with a compact one-point extension and proves that the convergent set is closed.
-/

open Set
open scoped Topology Pointwise

namespace ProCGroups.Generation

universe u v

open ProCGroups.ProC

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/--
A continuous map between topological groups that sends \(1\) to \(1\) carries convergent sets to
convergent sets, provided the source is profinite.
-/
theorem ConvergesToOneAlongOpenSubgroups.image_of_continuous_pointed
    {H : Type v} [Group H] [TopologicalSpace H]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    {f : G → H} (hf : Continuous f) (hf1 : f 1 = 1)
    {X : Set G} (hX : ConvergesToOneAlongOpenSubgroups (G := G) X) :
    ConvergesToOneAlongOpenSubgroups (G := H) (f '' X) := by
  intro U
  have hpre : IsOpen (f ⁻¹' (U : Set H)) :=
    (openSubgroup_isOpen (G := H) U).preimage hf
  have h1pre : (1 : G) ∈ f ⁻¹' (U : Set H) := by
    simp only [mem_preimage, hf1, SetLike.mem_coe, one_mem]
  rcases exists_openNormalSubgroup_sub_open_nhds_of_one (G := G) hpre h1pre with ⟨V, hVU⟩
  have hsubset : (f '' X) \ (U : Set H) ⊆ f '' (X \ (V : Set G)) := by
    intro y hy
    rcases hy with ⟨hyX, hyU⟩
    rcases hyX with ⟨x, hxX, rfl⟩
    refine ⟨x, ⟨hxX, ?_⟩, rfl⟩
    intro hxV
    exact hyU (hVU hxV)
  exact (hX V.toOpenSubgroup).image f |>.subset hsubset

omit [IsTopologicalGroup G] in
/-- Passing to a subset preserves convergence to \(1\). -/
theorem ConvergesToOneAlongOpenSubgroups.mono {X Y : Set G}
    (hX : ConvergesToOneAlongOpenSubgroups (G := G) X) (hYX : Y ⊆ X) :
    ConvergesToOneAlongOpenSubgroups (G := G) Y := by
  intro U
  exact (hX U).subset (by
    intro y hy
    exact ⟨hYX hy.1, hy.2⟩)

omit [IsTopologicalGroup G] in
/-- Finite enlargements preserve convergence to \(1\). -/
theorem ConvergesToOneAlongOpenSubgroups.union_finite {X F : Set G}
    (hX : ConvergesToOneAlongOpenSubgroups (G := G) X) (hF : F.Finite) :
    ConvergesToOneAlongOpenSubgroups (G := G) (X ∪ F) := by
  intro U
  have h1 : (X \ (U : Set G)).Finite := hX U
  have h2 : (F \ (U : Set G)).Finite := hF.subset (by
    intro y hy
    exact hy.1)
  have hsubset : (X ∪ F) \ (U : Set G) ⊆ (X \ (U : Set G)) ∪ (F \ (U : Set G)) := by
    intro y hy
    rcases hy with ⟨hyXF, hyU⟩
    rcases hyXF with hyX | hyF
    · exact Or.inl ⟨hyX, hyU⟩
    · exact Or.inr ⟨hyF, hyU⟩
  exact (h1.union h2).subset hsubset

omit [IsTopologicalGroup G] in
/--
Convergence to \(1\) is preserved and reflected by the indicated finite union, insertion, or
continuous equivalence operation.
-/
theorem ConvergesToOneAlongOpenSubgroups.union_finite_iff {X F : Set G}
    (hF : F.Finite) :
    ConvergesToOneAlongOpenSubgroups (G := G) (X ∪ F) ↔ ConvergesToOneAlongOpenSubgroups (G :=
        G) X := by
  constructor
  · intro h
    exact ConvergesToOneAlongOpenSubgroups.mono (G := G) h (by
      intro x hx
      exact Or.inl hx)
  · intro h
    exact ConvergesToOneAlongOpenSubgroups.union_finite (G := G) h hF

omit [IsTopologicalGroup G] in
/--
Convergence to \(1\) is preserved and reflected by the indicated finite union, insertion, or
continuous equivalence operation.
-/
theorem ConvergesToOneAlongOpenSubgroups.insert_iff {X : Set G} {x : G} :
    ConvergesToOneAlongOpenSubgroups (G := G) (Set.insert x X) ↔
        ConvergesToOneAlongOpenSubgroups (G := G) X := by
  have hEq : Set.insert x X = X ∪ ({x} : Set G) := by
    ext y
    constructor
    · intro hy
      rcases Set.mem_insert_iff.mp hy with rfl | hyX
      · exact Or.inr (by simp only [mem_singleton_iff])
      · exact Or.inl hyX
    · intro hy
      rcases hy with hyX | hyx
      · exact Set.mem_insert_iff.mpr (Or.inr hyX)
      · exact Set.mem_insert_iff.mpr (Or.inl (by simpa using hyx))
  rw [hEq]
  exact ConvergesToOneAlongOpenSubgroups.union_finite_iff (G := G) (X := X) (F := ({x} : Set G))
    (Set.finite_singleton x)

omit [IsTopologicalGroup G] in
/--
Convergence to \(1\) is preserved and reflected by the indicated finite union, insertion, or
continuous equivalence operation.
-/
theorem ConvergesToOneAlongOpenSubgroups.union_one_iff {X : Set G} :
    ConvergesToOneAlongOpenSubgroups (G := G) (X ∪ ({1} : Set G)) ↔
        ConvergesToOneAlongOpenSubgroups (G := G) X := by
  exact ConvergesToOneAlongOpenSubgroups.union_finite_iff (G := G) (X := X) (F := ({1} : Set G))
    (Set.finite_singleton 1)

/--
A set converging to \(1\) is discrete away from \(1\), and if it is infinite its closure is
obtained by adjoining the unique possible limit point \(1\).
-/
theorem closure_generatorsConvergingToOne
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] {X : Set G}
    (hX : ConvergesToOneAlongOpenSubgroups (G := G) X) :
    IsDiscrete (X \ {1}) ∧
      (Set.Infinite X → closure X = X ∪ ({1} : Set G)) := by
  refine ⟨?_, ?_⟩
  · rw [isDiscrete_iff_forall_mem_exists_isOpen]
    intro y hy
    have hy1 : y ≠ 1 := by simpa using hy.2
    let W : Set G := ({y} : Set G)ᶜ
    have hWopen : IsOpen W := isClosed_singleton.isOpen_compl
    have h1W : (1 : G) ∈ W := by simpa [W, eq_comm] using hy1
    rcases exists_openNormalSubgroup_sub_open_nhds_of_one (G := G) hWopen h1W with ⟨U, hUW⟩
    have hyU : y ∉ (U : Set G) := by
      intro hyU
      have hyW : y ∈ W := hUW hyU
      simp only [mem_compl_iff, mem_singleton_iff, not_true_eq_false, W] at hyW
    let V : Set G := (fun z : G => y⁻¹ * z) ⁻¹' (U : Set G)
    have hVopen : IsOpen V := by
      exact (openNormalSubgroup_isOpen (G := G) U).preimage
        (continuous_const.mul continuous_id)
    have hyV : y ∈ V := by
      simp only [mem_preimage, inv_mul_cancel, SetLike.mem_coe, one_mem, V]
    have hsubset : V ∩ (X \ ({1} : Set G)) ⊆ X \ (U : Set G) := by
      intro z hz
      rcases hz with ⟨hzV, hzX⟩
      refine ⟨hzX.1, ?_⟩
      intro hzU
      have hmem : z * (y⁻¹ * z)⁻¹ ∈ (U : Subgroup G) := U.mul_mem hzU (U.inv_mem hzV)
      have : y ∈ (U : Subgroup G) := by
        simpa [mul_assoc] using hmem
      exact hyU this
    have hfinite : (V ∩ (X \ ({1} : Set G))).Finite := by
      exact (hX U.toOpenSubgroup).subset hsubset
    rcases (isDiscrete_iff_forall_mem_exists_isOpen.mp hfinite.isDiscrete) y ⟨hyV, hy⟩ with
      ⟨V', hV'open, hV'⟩
    refine ⟨V' ∩ V, hV'open.inter hVopen, ?_⟩
    simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using hV'
  · intro hXinfinite
    apply subset_antisymm
    · intro y hycl
      by_cases hy1 : y = 1
      · simp only [union_singleton, hy1, mem_insert_iff, true_or]
      · by_cases hyX : y ∈ X
        · simp only [union_singleton, mem_insert_iff, hy1, hyX, or_true]
        · let W : Set G := ({y} : Set G)ᶜ
          have hWopen : IsOpen W := isClosed_singleton.isOpen_compl
          have h1W : (1 : G) ∈ W := by simpa [W, eq_comm] using hy1
          rcases exists_openNormalSubgroup_sub_open_nhds_of_one (G := G) hWopen h1W with
            ⟨U, hUW⟩
          have hyU : y ∉ (U : Set G) := by
            intro hyU
            have hyW : y ∈ W := hUW hyU
            simp only [mem_compl_iff, mem_singleton_iff, not_true_eq_false, W] at hyW
          let V : Set G := (fun z : G => y⁻¹ * z) ⁻¹' (U : Set G)
          have hVopen : IsOpen V := by
            exact (openNormalSubgroup_isOpen (G := G) U).preimage
              (continuous_const.mul continuous_id)
          have hyV : y ∈ V := by
            simp only [mem_preimage, inv_mul_cancel, SetLike.mem_coe, one_mem, V]
          have hsubset : V ∩ X ⊆ X \ (U : Set G) := by
            intro z hz
            rcases hz with ⟨hzV, hzX⟩
            refine ⟨hzX, ?_⟩
            intro hzU
            have hmem : z * (y⁻¹ * z)⁻¹ ∈ (U : Subgroup G) := U.mul_mem hzU (U.inv_mem hzV)
            have : y ∈ (U : Subgroup G) := by
              simpa [mul_assoc] using hmem
            exact hyU this
          have hfinite : (V ∩ X).Finite := by
            exact (hX U.toOpenSubgroup).subset hsubset
          have hclosed : IsClosed (V ∩ X) := hfinite.isClosed
          have hyVX : y ∉ V ∩ X := by
            simp only [mem_inter_iff, hyV, hyX, and_false, not_false_eq_true]
          have hne :=
            (mem_closure_iff.1 hycl) (V \ (V ∩ X)) (hVopen.sdiff hclosed) ⟨hyV, hyVX⟩
          rcases hne with ⟨z, hz⟩
          exact False.elim (hz.1.2 ⟨hz.1.1, hz.2⟩)
    · intro y hy
      rcases hy with hyX | hy1
      · exact subset_closure hyX
      · subst hy1
        refine mem_closure_iff.2 ?_
        intro W hWopen h1W
        rcases exists_openNormalSubgroup_sub_open_nhds_of_one (G := G) hWopen h1W with
          ⟨U, hUW⟩
        have hproper : ¬ X ⊆ X \ (U : Set G) := by
          intro hsub
          have hXfinite : X.Finite := (hX U.toOpenSubgroup).subset hsub
          exact hXinfinite hXfinite
        rcases Set.not_subset.1 hproper with ⟨x, hxX, hxnot⟩
        have hxU : x ∈ (U : Set G) := by
          by_contra hxU
          exact hxnot ⟨hxX, hxU⟩
        exact ⟨x, hUW hxU, hxX⟩

/-- A convergent set containing its only possible limit point \(1\) is closed. -/
theorem ConvergesToOneAlongOpenSubgroups.isClosed_of_one_mem
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] {X : Set G}
    (hX : ConvergesToOneAlongOpenSubgroups (G := G) X) (h1 : (1 : G) ∈ X) :
    IsClosed X := by
  rcases closure_generatorsConvergingToOne (G := G) hX with ⟨_, hclosure⟩
  by_cases hfinite : X.Finite
  · exact hfinite.isClosed
  · have hEq : closure X = X := by
      calc
        closure X = X ∪ ({1} : Set G) := by
          exact hclosure hfinite
        _ = X := by simp only [union_singleton, h1, insert_eq_of_mem]
    exact closure_eq_iff_isClosed.mp hEq

/--
If \(X\) is infinite, converges to \(1\), and does not contain \(1\), then \(closure X\) is
homeomorphic to the one-point compactification of the discrete space \(X\).
-/
noncomputable def closure_generatorsConvergingToOne_homeomorph_onePoint
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] {X : Set G}
    (hX : ConvergesToOneAlongOpenSubgroups (G := G) X) (hXinfinite : X.Infinite) (h1X : (1 : G)
        ∉ X) :
    OnePoint X ≃ₜ closure X := by
  classical
  rcases closure_generatorsConvergingToOne (G := G) hX with ⟨hdisc, hclosure⟩
  have hdiff : X \ ({1} : Set G) = X := by
    ext x
    by_cases hx : x = 1
    · simp only [h1X, not_false_eq_true, sdiff_singleton_eq_self, hx]
    · simp only [mem_sdiff, mem_singleton_iff, hx, not_false_eq_true, and_true]
  have hdiscX : IsDiscrete X := by
    simpa [hdiff] using hdisc
  have h1closure : (1 : G) ∈ closure X := by
    have : (1 : G) ∈ X ∪ ({1} : Set G) := by simp only [union_singleton, mem_insert_iff, true_or]
    rw [hclosure hXinfinite]
    simp only [union_singleton, mem_insert_iff, true_or]
  let toClosure : OnePoint X → closure X
    | OnePoint.infty => ⟨1, h1closure⟩
    | (x : X) => ⟨x.1, subset_closure x.2⟩
  let fromClosure : closure X → OnePoint X := fun y =>
    if hy : (y : G) = 1 then
      OnePoint.infty
    else
      OnePoint.some ⟨(y : G), by
        have hy' : (y : G) ∈ X ∪ ({1} : Set G) := by
          simpa [hclosure hXinfinite] using y.2
        rcases hy' with hyX | hy1
        · exact hyX
        · exact False.elim (hy hy1)⟩
  have hleft : Function.LeftInverse fromClosure toClosure := by
    intro z
    refine OnePoint.rec ?_ ?_ z
    · simp only [↓reduceDIte, fromClosure, toClosure]
    · intro x
      have hx1 : (x : G) ≠ 1 := by
        intro hx1
        exact h1X (hx1 ▸ x.2)
      simp only [hx1, ↓reduceDIte, Subtype.coe_eta, fromClosure, toClosure]
  have hright : Function.RightInverse fromClosure toClosure := by
    intro y
    by_cases hy : (y : G) = 1
    · apply Subtype.ext
      simp only [hy, ↓reduceDIte, toClosure, fromClosure]
    · apply Subtype.ext
      simp only [hy, ↓reduceDIte, Subtype.coe_eta, toClosure, fromClosure]
  let e : OnePoint X ≃ closure X :=
    { toFun := toClosure
      invFun := fromClosure
      left_inv := hleft
      right_inv := hright }
  have hcont : Continuous e := by
    have : DiscreteTopology X := (isDiscrete_iff_discreteTopology).1 hdiscX
    rw [OnePoint.continuous_iff_from_discrete]
    rw [tendsto_subtype_rng]
    change Filter.Tendsto (fun x : X => ((toClosure (x : OnePoint X) : closure X) : G))
      Filter.cofinite
      (𝓝 (((toClosure OnePoint.infty : closure X) : G)))
    change Filter.Tendsto (fun x : X => (x : G)) Filter.cofinite (𝓝 (1 : G))
    rw [Filter.tendsto_def]
    intro s hs
    rcases mem_nhds_iff.mp hs with ⟨W, hWs, hWopen, h1W⟩
    rcases exists_openNormalSubgroup_sub_open_nhds_of_one (G := G) hWopen h1W with ⟨U, hUW⟩
    have hfinite : (X \ (U : Set G)).Finite := hX U.toOpenSubgroup
    have hcof : ∀ᶠ x : X in Filter.cofinite, (x : G) ∈ (U : Set G) := by
      let f : X ↪ G := ⟨Subtype.val, Subtype.val_injective⟩
      have hpre : {x : X | (x : G) ∉ (U : Set G)}.Finite := by
        simpa [f, Set.preimage] using hfinite.preimage_embedding f
      exact Filter.eventually_cofinite.2 hpre
    exact hcof.mono fun x hx => hWs (hUW hx)
  exact Continuous.homeoOfEquivCompactToT2 (f := e) hcont

end ProCGroups.Generation
