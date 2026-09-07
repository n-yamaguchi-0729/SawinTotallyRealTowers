import ProCGroups.CompletedGroupAlgebra.ProfiniteModules.Basic.OpenSubmodule

set_option autoImplicit false

/-!
# Finite quotients of profinite modules

Open submodules of a profinite module have finite quotients and separate continuous linear maps.
This file packages open submodules and supplies quotient-continuity and finite-refinement
criteria.
-/

open scoped Topology

namespace CompletedGroupAlgebra

universe u v w z

/--
In Lemma 5.1.1(b), linear-topology interface, a profinite module with a linear topology has a
basis of open finite-index submodules at zero.
-/
theorem profiniteModule_hasFiniteIndexSubmoduleBasis_of_linearTopology
    (Λ : Type u) (M : Type v) [Ring Λ] [TopologicalSpace Λ] [AddCommGroup M]
    [TopologicalSpace M] [Module Λ M] [IsLinearTopology Λ M]
    [IsTopologicalAddGroup M] [CompactSpace M] :
    HasFiniteIndexSubmoduleBasis Λ M := by
  intro U hU
  rcases ((IsLinearTopology.hasBasis_open_submodule Λ).mem_iff.mp hU) with
    ⟨N, hNopen, hNU⟩
  exact ⟨N, hNopen, hNU,
    finite_quotient_of_openSubmodule Λ M N hNopen⟩

/--
In Lemma 5.1.1(b), finite-index submodules form a neighborhood basis at zero in a profinite
module.
-/
theorem profiniteModule_hasFiniteIndexSubmoduleBasis
    (Λ : Type u) (M : Type v) [Ring Λ] [TopologicalSpace Λ] [AddCommGroup M]
    [TopologicalSpace M] [Module Λ M] [IsTopologicalRing Λ] [CompactSpace Λ]
    [IsTopologicalAddGroup M] [ContinuousSMul Λ M] [CompactSpace M] [T2Space M]
    [TotallyDisconnectedSpace M] :
    HasFiniteIndexSubmoduleBasis Λ M := by
  let : IsLinearTopology Λ M := profiniteModule_isLinearTopology Λ M
  exact profiniteModule_hasFiniteIndexSubmoduleBasis_of_linearTopology Λ M

/-- Open submodule quotients separate points of a profinite module. -/
theorem profiniteModule_ext_of_openSubmoduleQuotients
    {R : Type u} (N : Type v) [Ring R] [TopologicalSpace R]
    [AddCommGroup N] [TopologicalSpace N] [Module R N]
    [IsTopologicalRing R] [CompactSpace R] [IsTopologicalAddGroup N]
    [ContinuousSMul R N] [CompactSpace N] [T2Space N] [TotallyDisconnectedSpace N]
    {x y : N}
    (h : ∀ W : Submodule R N, IsOpen (W : Set N) → Submodule.mkQ W x = Submodule.mkQ W y) :
    x = y := by
  by_contra hxy
  let O : Set N := ({x - y} : Set N)ᶜ
  have hd0 : x - y ≠ 0 := by
    intro hd
    exact hxy (sub_eq_zero.mp hd)
  have hOopen : IsOpen O := isClosed_singleton.isOpen_compl
  have h0O : (0 : N) ∈ O := by
    change (0 : N) ≠ x - y
    exact hd0.symm
  rcases profiniteModule_hasFiniteIndexSubmoduleBasis R N O (hOopen.mem_nhds h0O) with
    ⟨W, hWopen, hWO, _hfinite⟩
  have hq := h W hWopen
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply] at hq
  have hdiff : x - y ∈ W := (Submodule.Quotient.eq W).1 hq
  exact (hWO hdiff) (by simp only [Set.mem_singleton_iff])

/-- Open submodules of a profinite module. -/
abbrev ProfiniteModuleOpenSubmodule
    (R : Type u) (N : Type v) [Ring R] [AddCommGroup N] [Module R N]
    [TopologicalSpace N] : Type _ :=
  {W : Submodule R N // IsOpen (W : Set N)}

/-- Open submodule quotients detect continuity of maps into a profinite module. -/
theorem continuous_of_forall_openSubmodule_quotient_continuous
    {R : Type u} (N : Type v) [Ring R] [TopologicalSpace R]
    [AddCommGroup N] [TopologicalSpace N] [Module R N]
    [IsTopologicalRing R] [CompactSpace R] [IsTopologicalAddGroup N]
    [ContinuousSMul R N] [CompactSpace N] [T2Space N] [TotallyDisconnectedSpace N]
    {Y : Type z} [TopologicalSpace Y] {F : Y → N}
    (hF : ∀ W : Submodule R N, IsOpen (W : Set N) →
      Continuous fun y : Y => Submodule.mkQ W (F y)) :
    Continuous F := by
  rw [continuous_iff_continuousAt]
  intro y
  rw [continuousAt_def]
  intro A hA
  rcases mem_nhds_iff.mp hA with ⟨O, hOA, hOopen, hFO⟩
  let U0 : Set N := {z | F y + z ∈ O}
  have hU0 : U0 ∈ 𝓝 (0 : N) := by
    apply IsOpen.mem_nhds
    · exact hOopen.preimage (continuous_const.add continuous_id)
    · simp only [Set.mem_ofPred_eq, add_zero, hFO, U0]
  rcases profiniteModule_hasFiniteIndexSubmoduleBasis R N U0 hU0 with
    ⟨W, hWopen, hWU, _hfinite⟩
  let hdisc : IsDiscreteModule R (N ⧸ W) :=
    quotient_openSubmodule_isDiscreteModule R N W hWopen
  let : DiscreteTopology (N ⧸ W) := hdisc.2
  let q : Y → N ⧸ W := fun z => Submodule.mkQ W (F z)
  let B : Set (N ⧸ W) := {Submodule.mkQ W (F y)}
  have hqcont : Continuous q := hF W hWopen
  have hpreOpen : IsOpen (q ⁻¹' B) := (isOpen_discrete B).preimage hqcont
  have hypre : y ∈ q ⁻¹' B := by
    simp only [Submodule.mkQ_apply, Set.mem_preimage, Set.mem_singleton_iff, q, B]
  refine Filter.mem_of_superset (hpreOpen.mem_nhds hypre) ?_
  intro z hz
  apply hOA
  have hquot : Submodule.mkQ W (F z) = Submodule.mkQ W (F y) := by
    simpa [q, B] using hz
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply] at hquot
  have hdiff : F z - F y ∈ W := (Submodule.Quotient.eq W).1 hquot
  have hU : F z - F y ∈ U0 := hWU hdiff
  change F y + (F z - F y) ∈ O at hU
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hU

/-- A finite family of open submodules has an open submodule contained in all of them. -/
theorem exists_openSubmodule_le_finset
    {R : Type u} (N : Type v) [Ring R] [AddCommGroup N] [TopologicalSpace N] [Module R N]
    (s : Finset (ProfiniteModuleOpenSubmodule (R := R) N)) :
    ∃ K : ProfiniteModuleOpenSubmodule (R := R) N,
      ∀ W ∈ s, K.1 ≤ W.1 := by
  classical
  refine Finset.induction_on s ?empty ?insert
  · refine ⟨⟨⊤, isOpen_univ⟩, ?_⟩
    simp only [Finset.notMem_empty, top_le_iff, IsEmpty.forall_iff, implies_true]
  · intro W s hWs ih
    rcases ih with ⟨K, hK⟩
    refine ⟨⟨K.1 ⊓ W.1, K.2.inter W.2⟩, ?_⟩
    intro V hV
    rw [Finset.mem_insert] at hV
    rcases hV with hVW | hVs
    · subst V
      exact inf_le_right
    · exact inf_le_left.trans (hK V hVs)

end CompletedGroupAlgebra
