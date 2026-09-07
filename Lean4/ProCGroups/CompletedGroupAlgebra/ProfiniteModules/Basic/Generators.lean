import ProCGroups.CompletedGroupAlgebra.ProfiniteModules.Basic.FiniteQuotients
import ProCGroups.Generation.QuotientGeneratorConvergingPairs

set_option autoImplicit false

/-!
# Generating sets converging to zero

This file defines sets and maps converging to zero through open submodules and relates them to
one-point extensions and dense additive generation. Every profinite module is shown to admit an
appropriate generating set.
-/

open scoped Topology

namespace CompletedGroupAlgebra

universe u v w z

/-- A subset converges to zero in the all-but-finitely-many-elements sense used in the book. -/
def SetConvergesToZero {M : Type v} [TopologicalSpace M] [Zero M] (S : Set M) : Prop :=
  ∀ U ∈ 𝓝 (0 : M), (S \ U).Finite

/--
A map from an arbitrary index type converges to zero along the cofinite filter. This is the
map-level version used in Lemma 5.2.5(b).
-/
def MapConvergesToZero {S : Type u} {M : Type v} [TopologicalSpace M] [Zero M]
    (f : S → M) : Prop :=
  Filter.Tendsto f Filter.cofinite (𝓝 (0 : M))

/-- A map converging to zero has image set converging to zero. -/
theorem MapConvergesToZero.setConvergesToZero_range
    {S : Type u} {M : Type v} [TopologicalSpace M] [Zero M] {f : S → M}
    (hf : MapConvergesToZero f) :
    SetConvergesToZero (Set.range f) := by
  intro U hU
  have hpre : {s : S | f s ∉ U}.Finite := by
    have hmem : {s : S | f s ∈ U} ∈ (Filter.cofinite : Filter S) := hf hU
    exact Filter.mem_cofinite.mp hmem
  exact (hpre.image f).subset (by
    rintro y ⟨⟨s, rfl⟩, hsU⟩
    exact ⟨s, hsU, rfl⟩)

/-- An injective parametrization of a set converging to zero is a map converging to zero. -/
theorem SetConvergesToZero.mapConvergesToZero_of_injective
    {S : Type u} {M : Type v} [TopologicalSpace M] [Zero M] {f : S → M}
    (hfconv : SetConvergesToZero (Set.range f)) (hfinj : Function.Injective f) :
    MapConvergesToZero f := by
  intro U hU
  have hbad : ({s : S | f s ∉ U} : Set S).Finite := by
    have hpre :
        ({s : S | f s ∉ U} : Set S) = f ⁻¹' (Set.range f \ U) := by
      ext s
      simp only [Set.mem_ofPred_eq, Set.preimage_sdiff, Set.preimage_range, Set.mem_sdiff,
          Set.mem_univ,
  Set.mem_preimage, true_and]
    rw [hpre]
    exact Set.Finite.preimage (f := f) (s := Set.range f \ U) hfinj.injOn
      (hfconv U hU)
  change f ⁻¹' U ∈ (Filter.cofinite : Filter S)
  rw [Filter.mem_cofinite]
  rw [← Set.preimage_compl]
  have hpreimageCompl : f ⁻¹' Uᶜ = {s : S | f s ∉ U} := by
    ext s
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_ofPred_eq]
  rw [hpreimageCompl]
  exact hbad

/-- The inclusion of a set converging to zero, viewed as a parametrized map, converges to zero. -/
theorem SetConvergesToZero.subtype_val
    {M : Type v} [TopologicalSpace M] [Zero M] {S : Set M}
    (hS : SetConvergesToZero S) :
    MapConvergesToZero (fun s : S => (s : M)) := by
  have hrange : Set.range (fun s : S => (s : M)) = S := by
    ext x
    constructor
    · rintro ⟨s, rfl⟩
      exact s.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hRangeConv : SetConvergesToZero (Set.range fun s : S => (s : M)) := by
    simpa [hrange] using hS
  exact hRangeConv.mapConvergesToZero_of_injective Subtype.val_injective

/--
A map from a discrete set converges to zero if and only if its zero-extension to the one-point
compactification is continuous.
-/
theorem continuous_onePoint_zero_extension_iff_mapConvergesToZero
    {S : Type u} {M : Type v} [TopologicalSpace S] [DiscreteTopology S]
    [TopologicalSpace M] [Zero M] {f : S → M} :
    Continuous (fun x : OnePoint S => x.elim 0 f) ↔ MapConvergesToZero f := by
  rw [OnePoint.continuous_iff_from_discrete]
  rfl

/-- Finite subsets converge to zero in the all-but-finitely-many-elements sense used in the book. -/
theorem finite_setConvergesToZero
    {M : Type v} [TopologicalSpace M] [Zero M] {S : Set M} (hS : S.Finite) :
    SetConvergesToZero S := by
  intro U _hU
  exact hS.subset Set.sdiff_subset

/-- A set of topological module generators converging to zero. -/
def HasGeneratingSetConvergingToZero (Λ : Type u) (M : Type v) [Ring Λ]
    [TopologicalSpace M] [AddCommGroup M] [Module Λ M] : Prop :=
  ∃ S : Set M, closure (Submodule.span Λ S : Set M) = Set.univ ∧ SetConvergesToZero S

/--
A finite dense generating set is a generating set converging to zero. This gives the
finite-generated special case of Lemma 5.1.1(c).
-/
theorem finiteGeneratingSet_convergesToZero
    (Λ : Type u) (M : Type v) [Ring Λ] [TopologicalSpace M] [AddCommGroup M]
    [Module Λ M] {S : Set M}
    (hgen : closure (Submodule.span Λ S : Set M) = Set.univ) (hS : S.Finite) :
    HasGeneratingSetConvergingToZero Λ M := by
  exact ⟨S, hgen, finite_setConvergesToZero hS⟩

/-- A dense additive generating set is also a dense module generating set. -/
theorem hasGeneratingSetConvergingToZero_of_dense_addSubgroup
    (Λ : Type u) (M : Type v) [Ring Λ] [TopologicalSpace M] [AddCommGroup M]
    [Module Λ M] {S : Set M}
    (hspan : closure (((AddSubgroup.closure S : AddSubgroup M) : Set M)) = Set.univ)
    (hconv : SetConvergesToZero S) :
    HasGeneratingSetConvergingToZero Λ M := by
  refine ⟨S, ?_, hconv⟩
  have hsubset : ((AddSubgroup.closure S : AddSubgroup M) : Set M) ⊆
      ((Submodule.span Λ S : Submodule Λ M) : Set M) := by
    intro x hx
    have hle : AddSubgroup.closure S ≤ (Submodule.span Λ S).toAddSubgroup :=
      (AddSubgroup.closure_le (K := (Submodule.span Λ S).toAddSubgroup)).2
        fun y hy => Submodule.subset_span hy
    exact hle hx
  have hclosure :
      closure (((AddSubgroup.closure S : AddSubgroup M) : Set M)) ⊆
        closure (((Submodule.span Λ S : Submodule Λ M) : Set M)) :=
    closure_mono hsubset
  exact Set.eq_univ_of_univ_subset (by simpa [hspan] using hclosure)

/--
The multiplicative homeomorphism identifies the additive profinite-module structure with its
multiplicative notation.
-/
private def multiplicativeHomeomorph (M : Type*) [TopologicalSpace M] : M ≃ₜ Multiplicative M where
  toEquiv := Multiplicative.ofAdd
  continuous_toFun := continuous_ofAdd
  continuous_invFun := continuous_toAdd

/-- In Lemma 5.1.1(c), every profinite module has a generating set converging to zero. -/
theorem profiniteModule_hasGeneratingSetConvergingToZero
    (Λ : Type u) (M : Type v) [Ring Λ] [TopologicalSpace Λ]
    [AddCommGroup M] [TopologicalSpace M] [Module Λ M]
    [IsTopologicalRing Λ] [CompactSpace Λ] [IsTopologicalAddGroup M]
    [ContinuousSMul Λ M] [CompactSpace M] [T2Space M] [TotallyDisconnectedSpace M] :
    HasGeneratingSetConvergingToZero Λ M := by
  let e : M ≃ₜ Multiplicative M := multiplicativeHomeomorph M
  let : CompactSpace (Multiplicative M) := e.compactSpace
  let : T2Space (Multiplicative M) := e.t2Space
  let : TotallyDisconnectedSpace (Multiplicative M) := e.totallyDisconnectedSpace
  rcases ProCGroups.Generation.exists_generatorsConvergingToOne
      (G := Multiplicative M) with ⟨X, hXgen, hXconv⟩
  let S : Set M := Multiplicative.toAdd '' X
  have hpre : Multiplicative.toAdd ⁻¹' S = X := by
    ext x
    simp only [Equiv.preimage_image, S]
  have hsub : (AddSubgroup.closure S).toSubgroup = Subgroup.closure X := by
    rw [AddSubgroup.toSubgroup_closure]
    rw [hpre]
  have hspan : closure (((AddSubgroup.closure S : AddSubgroup M) : Set M)) = Set.univ := by
    have htopSub : (Subgroup.closure X).topologicalClosure = ⊤ := by
      simpa [ProCGroups.Generation.TopologicallyGenerates] using hXgen
    have htopMul : ((AddSubgroup.closure S).toSubgroup).topologicalClosure = ⊤ := by
      simpa [hsub] using htopSub
    change ((AddSubgroup.closure S).topologicalClosure : Set M) = Set.univ
    ext x
    constructor
    · intro _
      simp only [Set.mem_univ]
    · intro _
      have hxmul : Multiplicative.ofAdd x ∈
          (((AddSubgroup.closure S).toSubgroup).topologicalClosure :
            Set (Multiplicative M)) := by
        rw [htopMul]
        simp only [Subgroup.coe_top, Set.mem_univ]
      have hxpre :
          x ∈ e ⁻¹' closure
            (((AddSubgroup.closure S).toSubgroup : Subgroup (Multiplicative M)) :
              Set (Multiplicative M)) :=
        hxmul
      rw [e.preimage_closure] at hxpre
      have hpreimage :
          Multiplicative.ofAdd ⁻¹'
              (Multiplicative.toAdd ⁻¹'
                (((AddSubgroup.closure S : AddSubgroup M) : Set M))) =
            ((AddSubgroup.closure S : AddSubgroup M) : Set M) := by
        ext y
        rfl
      rw [show (e ⁻¹'
          (((AddSubgroup.closure S).toSubgroup : Subgroup (Multiplicative M)) :
            Set (Multiplicative M))) =
          ((AddSubgroup.closure S : AddSubgroup M) : Set M) by
            simpa [e, multiplicativeHomeomorph] using hpreimage] at hxpre
      exact hxpre
  have hconv : SetConvergesToZero S := by
    intro U hU
    rcases profiniteModule_hasFiniteIndexSubmoduleBasis Λ M U hU with
      ⟨N, hNopen, hNU, _⟩
    let V : OpenSubgroup (Multiplicative M) :=
      { toSubgroup := N.toAddSubgroup.toSubgroup
        isOpen' := by
          change IsOpen (Multiplicative.toAdd ⁻¹' (N : Set M))
          exact hNopen.preimage continuous_toAdd }
    have hsubset : S \ U ⊆ Multiplicative.toAdd '' (X \ (V : Set (Multiplicative M))) := by
      intro y hy
      rcases hy with ⟨hyS, hyU⟩
      rcases hyS with ⟨x, hxX, rfl⟩
      refine ⟨x, ⟨hxX, ?_⟩, rfl⟩
      intro hxV
      change Multiplicative.toAdd x ∈ N at hxV
      exact hyU (hNU hxV)
    exact ((hXconv V).image Multiplicative.toAdd).subset hsubset
  exact hasGeneratingSetConvergingToZero_of_dense_addSubgroup Λ M hspan hconv

end CompletedGroupAlgebra
