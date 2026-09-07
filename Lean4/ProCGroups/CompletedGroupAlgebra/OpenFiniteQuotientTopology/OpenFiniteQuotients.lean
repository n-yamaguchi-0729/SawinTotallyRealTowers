import ProCGroups.CompletedGroupAlgebra.OpenFiniteQuotientTopology.FiniteQuotients

set_option autoImplicit false

/-!
# The open-finite quotient system

Open coefficient ideals and open normal group subgroups index a cofiltered system of finite group
algebras. This file defines its stages, transitions, projections, and the kernel-neighborhood
topology they induce on the algebraic group algebra.
-/

open scoped Topology

namespace CompletedGroupAlgebra

noncomputable section

open ProCGroups
open ProCGroups.ProC
open ProCGroups.InverseSystems
open ProCGroups.Completion

universe u v

variable (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/--
The open coefficient ideals used in the kernel-neighborhood topology of Ribes--Zalesskii Section
\(5.3\).
-/
abbrev CompletedGroupAlgebraOpenIdeal
    (R : Type u) [CommRing R] [TopologicalSpace R] : Type u :=
  {I : Ideal R // IsOpen (I : Set R)}

omit G [Group G] [TopologicalSpace G] [IsTopologicalGroup G] in
/--
In a profinite coefficient ring, the open-ideal quotients separate points. This is the
coefficient part of the kernel-intersection statement in Lemma 5.3.5(a).
-/
theorem profiniteRing_eq_zero_of_forall_openIdeal_quotient_eq_zero
    [CompactSpace R] [T2Space R] [TotallyDisconnectedSpace R] {r : R}
    (hr : ∀ I : CompletedGroupAlgebraOpenIdeal R, Ideal.Quotient.mk I.1 r = 0) :
    r = 0 := by
  by_contra hne
  have h0 : (0 : R) ∈ ({r}ᶜ : Set R) := by
    exact fun h0r => hne h0r.symm
  have hU : ({r}ᶜ : Set R) ∈ 𝓝 (0 : R) :=
    isOpen_compl_singleton.mem_nhds h0
  rcases profiniteRing_hasOpenIdealBasisAtZero R ({r}ᶜ) hU with
    ⟨I, hIopen, hIU⟩
  have hrI : r ∈ I := by
    exact Ideal.Quotient.eq_zero_iff_mem.1 (hr ⟨I, hIopen⟩)
  exact (hIU hrI) rfl

/--
The two-parameter index set for the kernel-neighborhood quotients \((R/I)[G/U]\), with open
ideals in the coefficient direction and finite group quotients in the group direction.
-/
abbrev CompletedGroupAlgebraOpenQuotientIndex
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] : Type (max u v) :=
  OrderDual (CompletedGroupAlgebraOpenIdeal R) × CompletedGroupAlgebraIndex G

/--
The finite quotient index type is nonempty, witnessed by the terminal quotient or canonical base
object.
-/
instance instNonemptyCompletedGroupAlgebraOpenIdeal
    (R : Type u) [CommRing R] [TopologicalSpace R] :
    Nonempty (CompletedGroupAlgebraOpenIdeal R) :=
  ⟨⟨⊤, isOpen_univ⟩⟩

/-- The family of completed-group-algebra open quotient indices is directed under refinement. -/
theorem directed_completedGroupAlgebraOpenQuotientIndex
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] :
    Directed (α := CompletedGroupAlgebraOpenQuotientIndex R G) (· ≤ ·) fun K => K := by
  intro K L
  rcases directed_openNormalSubgroupInClass
      (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
          ProCGroups.FiniteGroupClass.allFinite_formation
      K.2 L.2 with
    ⟨W, hKW, hLW⟩
  let I : CompletedGroupAlgebraOpenIdeal R :=
    ⟨(OrderDual.ofDual K.1).1 ⊓ (OrderDual.ofDual L.1).1, by
      simpa using (OrderDual.ofDual K.1).2.inter (OrderDual.ofDual L.1).2⟩
  refine ⟨(OrderDual.toDual I, W), ?_, ?_⟩
  · constructor
    · change (I.1 : Ideal R) ≤ (OrderDual.ofDual K.1).1
      exact inf_le_left
    · exact hKW
  · constructor
    · change (I.1 : Ideal R) ≤ (OrderDual.ofDual L.1).1
      exact inf_le_right
    · exact hLW

/-- The stage \((R/I)[G/U]\) attached to an open-ideal/finite-group quotient index. -/
abbrev CompletedGroupAlgebraOpenQuotientStage
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (K : CompletedGroupAlgebraOpenQuotientIndex R G) :
    Type (max u v) :=
  CompletedGroupAlgebraCoeffQuotientStage R G ((OrderDual.ofDual K.1).1 : Ideal R) K.2

/-- The quotient map \(R[G] \to (R/I)[G/U]\) for an open-ideal/finite-group quotient index. -/
def groupAlgebraOpenFiniteQuotientMap
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (K : CompletedGroupAlgebraOpenQuotientIndex R G) :
    MonoidAlgebra R G →+* CompletedGroupAlgebraOpenQuotientStage R G K :=
  groupAlgebraFiniteQuotientMap R G ((OrderDual.ofDual K.1).1 : Ideal R) K.2

/-- The kernel neighborhood attached to an open-ideal/finite-group quotient index. -/
def groupAlgebraOpenFiniteQuotientKernel
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (K : CompletedGroupAlgebraOpenQuotientIndex R G) :
    Ideal (MonoidAlgebra R G) :=
  groupAlgebraFiniteQuotientKernel R G ((OrderDual.ofDual K.1).1 : Ideal R) K.2

/--
An element of \(R[G]\) lies in the kernel attached to the open quotient index \(K\) exactly when
`groupAlgebraOpenFiniteQuotientMap` sends it to zero.
-/
@[simp]
theorem mem_groupAlgebraOpenFiniteQuotientKernel_iff
    {R : Type u} {G : Type v} [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    {K : CompletedGroupAlgebraOpenQuotientIndex R G} {x : MonoidAlgebra R G} :
    x ∈ groupAlgebraOpenFiniteQuotientKernel R G K ↔
      groupAlgebraOpenFiniteQuotientMap R G K x = 0 :=
  Iff.rfl

/-- The transition \((R/I_L)[G/U]_L \to (R/I_K)[G/U]_K\) for \(K \leq L\). -/
def completedGroupAlgebraOpenFiniteQuotientTransition
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    {K L : CompletedGroupAlgebraOpenQuotientIndex R G} (hKL : K ≤ L) :
    CompletedGroupAlgebraOpenQuotientStage R G L →+*
      CompletedGroupAlgebraOpenQuotientStage R G K :=
  completedGroupAlgebraFiniteQuotientTransition R G
    (show ((OrderDual.ofDual L.1).1 : Ideal R) ≤
        ((OrderDual.ofDual K.1).1 : Ideal R) from hKL.1)
    hKL.2

/--
The open finite-quotient transition from \(L\) to \(K\), composed with the abstract quotient map
at \(L\), is the abstract quotient map at \(K\).
-/
@[simp]
theorem completedGroupAlgebraOpenFiniteQuotientTransition_comp_map
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    {K L : CompletedGroupAlgebraOpenQuotientIndex R G} (hKL : K ≤ L) :
    (completedGroupAlgebraOpenFiniteQuotientTransition R G hKL).comp
        (groupAlgebraOpenFiniteQuotientMap R G L) =
      groupAlgebraOpenFiniteQuotientMap R G K := by
  exact completedGroupAlgebraFiniteQuotientTransition_comp_finiteQuotientMap
    (R := R) (G := G)
    (hIJ := (show ((OrderDual.ofDual L.1).1 : Ideal R) ≤
      ((OrderDual.ofDual K.1).1 : Ideal R) from hKL.1))
    (hUV := hKL.2)

/--
The projection \(\widehat{R[G]} \to (R/I)[G/U]\) for an open-ideal/finite-group quotient index.
-/
def completedGroupAlgebraOpenFiniteQuotientProjection
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K : CompletedGroupAlgebraOpenQuotientIndex R G) :
    CompletedGroupAlgebraCarrier R G →+* CompletedGroupAlgebraOpenQuotientStage R G K :=
  completedGroupAlgebraFiniteQuotientProjection R G
    ((OrderDual.ofDual K.1).1 : Ideal R) K.2

/--
Composing the completed-group-algebra projection at the open quotient index \(K\) with the
canonical dense ring homomorphism gives the corresponding open finite-quotient map.
-/
@[simp]
theorem completedGroupAlgebraOpenFiniteQuotientProjection_toCompletedGroupAlgebra
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K : CompletedGroupAlgebraOpenQuotientIndex R G) :
    (completedGroupAlgebraOpenFiniteQuotientProjection R G K).comp
        (toCompletedGroupAlgebraRingHom R G) =
      groupAlgebraOpenFiniteQuotientMap R G K := by
  rfl

/--
The transition from \(L\) to \(K\), composed with the completed projection at \(L\), is the
completed projection at \(K\).
-/
@[simp]
theorem completedGroupAlgebraOpenFiniteQuotientTransition_comp_projection
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {K L : CompletedGroupAlgebraOpenQuotientIndex R G} (hKL : K ≤ L) :
    (completedGroupAlgebraOpenFiniteQuotientTransition R G hKL).comp
        (completedGroupAlgebraOpenFiniteQuotientProjection R G L) =
      completedGroupAlgebraOpenFiniteQuotientProjection R G K := by
  exact completedGroupAlgebraFiniteQuotientTransition_comp_projection
    (R := R) (G := G)
    (hIJ := (show ((OrderDual.ofDual L.1).1 : Ideal R) ≤
      ((OrderDual.ofDual K.1).1 : Ideal R) from hKL.1))
    (hUV := hKL.2)

/-- The open-finite quotient kernel is antitone with respect to quotient refinement. -/
theorem groupAlgebraOpenFiniteQuotientKernel_antitone
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {K L : CompletedGroupAlgebraOpenQuotientIndex R G} (hKL : K ≤ L) :
    groupAlgebraOpenFiniteQuotientKernel R G L ≤
      groupAlgebraOpenFiniteQuotientKernel R G K := by
  intro x hx
  rw [mem_groupAlgebraOpenFiniteQuotientKernel_iff] at hx ⊢
  have hcomp := congrFun
    (congrArg DFunLike.coe
      (completedGroupAlgebraOpenFiniteQuotientTransition_comp_map (R := R) (G := G) hKL))
    x
  rw [RingHom.comp_apply, hx, map_zero] at hcomp
  exact hcomp.symm

/--
The discrete topology on each kernel-neighborhood quotient \((R/I)[G/U]\). This is the topology
used in the construction of the abstract group-algebra topology.
-/
@[reducible]
def completedGroupAlgebraOpenFiniteQuotientStageTopology
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (K : CompletedGroupAlgebraOpenQuotientIndex R G) :
    TopologicalSpace (CompletedGroupAlgebraOpenQuotientStage R G K) :=
  ⊥

/--
The finite stage completed group algebra open-finite quotient stage is discrete for its finite
quotient topology.
-/
theorem completedGroupAlgebraOpenFiniteQuotientStage_discrete
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (K : CompletedGroupAlgebraOpenQuotientIndex R G) :
    letI : TopologicalSpace (CompletedGroupAlgebraOpenQuotientStage R G K) :=
      completedGroupAlgebraOpenFiniteQuotientStageTopology R G K
    DiscreteTopology (CompletedGroupAlgebraOpenQuotientStage R G K) := by
  let : TopologicalSpace (CompletedGroupAlgebraOpenQuotientStage R G K) :=
    completedGroupAlgebraOpenFiniteQuotientStageTopology R G K
  exact ⟨rfl⟩

/--
The coefficient quotient from the finite stage \(R[G/U]\) to the kernel-neighborhood quotient
\((R/I)[G/U]\) is continuous when the target carries the discrete quotient topology.
-/
theorem continuous_completedGroupAlgebraStageCoeffQuotientMap_openIdeal
    (K : CompletedGroupAlgebraOpenQuotientIndex R G) :
    letI : TopologicalSpace (CompletedGroupAlgebraStage R G K.2) :=
      (completedGroupAlgebraSystem R G).topologicalSpace K.2
    letI : TopologicalSpace (CompletedGroupAlgebraOpenQuotientStage R G K) :=
      completedGroupAlgebraOpenFiniteQuotientStageTopology R G K
    Continuous (completedGroupAlgebraStageCoeffQuotientMap R G
      ((OrderDual.ofDual K.1).1 : Ideal R) K.2) := by
  let Iopen : CompletedGroupAlgebraOpenIdeal R := OrderDual.ofDual K.1
  let Q := CompletedGroupAlgebraQuotient G K.2
  let : TopologicalSpace (CompletedGroupAlgebraStage R G K.2) :=
    (completedGroupAlgebraSystem R G).topologicalSpace K.2
  let : TopologicalSpace (R ⧸ (Iopen.1 : Ideal R)) := ⊥
  have : DiscreteTopology (R ⧸ (Iopen.1 : Ideal R)) := ⟨rfl⟩
  have hmk : Continuous (Ideal.Quotient.mk (Iopen.1 : Ideal R)) :=
    continuous_idealQuotient_mk_openIdeal_discrete
      (R := R) (I := Iopen.1) Iopen.2
  have hcont :
      letI : TopologicalSpace (CompletedGroupAlgebraCoeffQuotientStage R G Iopen.1 K.2) :=
        finiteGroupAlgebraTopology (R ⧸ (Iopen.1 : Ideal R)) Q
      Continuous (completedGroupAlgebraStageCoeffQuotientMap R G Iopen.1 K.2) := by
    dsimp [CompletedGroupAlgebraStage, CompletedGroupAlgebraCoeffQuotientStage, Q]
    exact finiteGroupAlgebra_mapRangeRingHom_continuous
      (R := R) (S := R ⧸ (Iopen.1 : Ideal R)) Q
      (Ideal.Quotient.mk (Iopen.1 : Ideal R)) hmk
  have hdisc :
      letI : TopologicalSpace (CompletedGroupAlgebraCoeffQuotientStage R G Iopen.1 K.2) :=
        finiteGroupAlgebraTopology (R ⧸ (Iopen.1 : Ideal R)) Q
      DiscreteTopology (CompletedGroupAlgebraCoeffQuotientStage R G Iopen.1 K.2) := by
    dsimp [CompletedGroupAlgebraCoeffQuotientStage, Q]
    exact finiteGroupAlgebraTopology_discrete_of_discrete_coeff
      (S := R ⧸ (Iopen.1 : Ideal R)) Q
  let tfin : TopologicalSpace (CompletedGroupAlgebraOpenQuotientStage R G K) :=
    finiteGroupAlgebraTopology (R ⧸ (Iopen.1 : Ideal R)) Q
  let tdisc : TopologicalSpace (CompletedGroupAlgebraOpenQuotientStage R G K) :=
    completedGroupAlgebraOpenFiniteQuotientStageTopology R G K
  have ht : tfin = tdisc := by
    dsimp [tfin, tdisc, completedGroupAlgebraOpenFiniteQuotientStageTopology]
    exact hdisc.eq_bot
  change @Continuous (CompletedGroupAlgebraStage R G K.2)
    (CompletedGroupAlgebraOpenQuotientStage R G K)
    ((completedGroupAlgebraSystem R G).topologicalSpace K.2) tdisc
    (completedGroupAlgebraStageCoeffQuotientMap R G Iopen.1 K.2)
  rw [← ht]
  exact hcont

/--
The projection \(\widehat{R[G]} \to (R/I)[G/U]\) to any two-parameter finite quotient is
continuous.
-/
theorem continuous_completedGroupAlgebraOpenFiniteQuotientProjection
    (K : CompletedGroupAlgebraOpenQuotientIndex R G) :
    letI : TopologicalSpace (CompletedGroupAlgebraOpenQuotientStage R G K) :=
      completedGroupAlgebraOpenFiniteQuotientStageTopology R G K
    Continuous (completedGroupAlgebraOpenFiniteQuotientProjection R G K) := by
  let : TopologicalSpace (CompletedGroupAlgebraStage R G K.2) :=
    (completedGroupAlgebraSystem R G).topologicalSpace K.2
  let : TopologicalSpace (CompletedGroupAlgebraOpenQuotientStage R G K) :=
    completedGroupAlgebraOpenFiniteQuotientStageTopology R G K
  exact (continuous_completedGroupAlgebraStageCoeffQuotientMap_openIdeal
    (R := R) (G := G) K).comp ((completedGroupAlgebraSystem R G).continuous_projection K.2)

/-- The product of all open-finite quotient maps \(R[G] \to (R/I)[G/U]\). -/
def groupAlgebraOpenFiniteQuotientProductMap
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] :
    MonoidAlgebra R G →
      (K : CompletedGroupAlgebraOpenQuotientIndex R G) →
        CompletedGroupAlgebraOpenQuotientStage R G K :=
  fun x K => groupAlgebraOpenFiniteQuotientMap R G K x

/--
The kernel-neighborhood topology on \(R[G]\), induced by all maps \(R[G] \to (R/I)[G/U]\) with
\(I\) open and \(U\) open normal with finite quotient.
-/
@[reducible]
def groupAlgebraOpenFiniteQuotientKernelTopology
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] :
    TopologicalSpace (MonoidAlgebra R G) :=
  letI : ∀ K : CompletedGroupAlgebraOpenQuotientIndex R G,
      TopologicalSpace (CompletedGroupAlgebraOpenQuotientStage R G K) :=
    fun K => completedGroupAlgebraOpenFiniteQuotientStageTopology R G K
  TopologicalSpace.induced (groupAlgebraOpenFiniteQuotientProductMap R G) inferInstance

/-- The product of the finite quotient maps is continuous for the kernel-neighborhood topology. -/
theorem continuous_groupAlgebraOpenFiniteQuotientProductMap_kernelTopology
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] :
    letI : TopologicalSpace (MonoidAlgebra R G) :=
      groupAlgebraOpenFiniteQuotientKernelTopology R G
    letI : ∀ K : CompletedGroupAlgebraOpenQuotientIndex R G,
        TopologicalSpace (CompletedGroupAlgebraOpenQuotientStage R G K) :=
      fun K => completedGroupAlgebraOpenFiniteQuotientStageTopology R G K
    Continuous (groupAlgebraOpenFiniteQuotientProductMap R G) := by
  let : TopologicalSpace (MonoidAlgebra R G) :=
    groupAlgebraOpenFiniteQuotientKernelTopology R G
  let : ∀ K : CompletedGroupAlgebraOpenQuotientIndex R G,
      TopologicalSpace (CompletedGroupAlgebraOpenQuotientStage R G K) :=
    fun K => completedGroupAlgebraOpenFiniteQuotientStageTopology R G K
  exact continuous_induced_dom

/--
The finite quotient map \(R[G]\to (R/I)[G/U]\) is continuous for the kernel-neighborhood
topology.
-/
theorem continuous_groupAlgebraOpenFiniteQuotientMap_kernelTopology
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (K : CompletedGroupAlgebraOpenQuotientIndex R G) :
    letI : TopologicalSpace (MonoidAlgebra R G) :=
      groupAlgebraOpenFiniteQuotientKernelTopology R G
    letI : TopologicalSpace (CompletedGroupAlgebraOpenQuotientStage R G K) :=
      completedGroupAlgebraOpenFiniteQuotientStageTopology R G K
    Continuous (groupAlgebraOpenFiniteQuotientMap R G K) := by
  let : TopologicalSpace (MonoidAlgebra R G) :=
    groupAlgebraOpenFiniteQuotientKernelTopology R G
  let : ∀ K : CompletedGroupAlgebraOpenQuotientIndex R G,
      TopologicalSpace (CompletedGroupAlgebraOpenQuotientStage R G K) :=
    fun K => completedGroupAlgebraOpenFiniteQuotientStageTopology R G K
  change Continuous fun x : MonoidAlgebra R G =>
    groupAlgebraOpenFiniteQuotientProductMap R G x K
  exact (continuous_apply K).comp
    (continuous_groupAlgebraOpenFiniteQuotientProductMap_kernelTopology R G)

/-- Each open-finite quotient kernel is open in the kernel topology. -/
theorem groupAlgebraOpenFiniteQuotientKernel_isOpen_kernelTopology
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (K : CompletedGroupAlgebraOpenQuotientIndex R G) :
    letI : TopologicalSpace (MonoidAlgebra R G) :=
      groupAlgebraOpenFiniteQuotientKernelTopology R G
    IsOpen (groupAlgebraOpenFiniteQuotientKernel R G K : Set (MonoidAlgebra R G)) := by
  let : TopologicalSpace (MonoidAlgebra R G) :=
    groupAlgebraOpenFiniteQuotientKernelTopology R G
  let : TopologicalSpace (CompletedGroupAlgebraOpenQuotientStage R G K) :=
    completedGroupAlgebraOpenFiniteQuotientStageTopology R G K
  have : DiscreteTopology (CompletedGroupAlgebraOpenQuotientStage R G K) :=
    completedGroupAlgebraOpenFiniteQuotientStage_discrete R G K
  change IsOpen ((groupAlgebraOpenFiniteQuotientMap R G K) ⁻¹'
    ({0} : Set (CompletedGroupAlgebraOpenQuotientStage R G K)))
  exact (isOpen_discrete ({0} : Set (CompletedGroupAlgebraOpenQuotientStage R G K))).preimage
    (continuous_groupAlgebraOpenFiniteQuotientMap_kernelTopology R G K)

/-- Every open-finite quotient kernel is a neighborhood of zero for the kernel topology. -/
theorem groupAlgebraOpenFiniteQuotientKernel_mem_nhds_zero_kernelTopology
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (K : CompletedGroupAlgebraOpenQuotientIndex R G) :
    letI : TopologicalSpace (MonoidAlgebra R G) :=
      groupAlgebraOpenFiniteQuotientKernelTopology R G
    (groupAlgebraOpenFiniteQuotientKernel R G K : Set (MonoidAlgebra R G)) ∈
      𝓝 (0 : MonoidAlgebra R G) := by
  let : TopologicalSpace (MonoidAlgebra R G) :=
    groupAlgebraOpenFiniteQuotientKernelTopology R G
  apply IsOpen.mem_nhds
    (groupAlgebraOpenFiniteQuotientKernel_isOpen_kernelTopology R G K)
  change (0 : MonoidAlgebra R G) ∈ groupAlgebraOpenFiniteQuotientKernel R G K
  rw [mem_groupAlgebraOpenFiniteQuotientKernel_iff]
  exact map_zero (groupAlgebraOpenFiniteQuotientMap R G K)

/--
An open finite-quotient transition sends a singleton by applying the induced group-quotient map
to its support and the induced ideal-quotient factor to its coefficient.
-/
@[simp]
theorem completedGroupAlgebraOpenFiniteQuotientTransition_single
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    {K L : CompletedGroupAlgebraOpenQuotientIndex R G} (hKL : K ≤ L)
    (q : CompletedGroupAlgebraQuotient G L.2)
    (r : R ⧸ ((OrderDual.ofDual L.1).1 : Ideal R)) :
    completedGroupAlgebraOpenFiniteQuotientTransition R G hKL
        (MonoidAlgebra.single q r) =
      MonoidAlgebra.single
        ((OpenNormalSubgroupInClass.map
          (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
          (U := OrderDual.ofDual K.2) (V := OrderDual.ofDual L.2) hKL.2) q)
        (Ideal.Quotient.factor
          (show ((OrderDual.ofDual L.1).1 : Ideal R) ≤
            ((OrderDual.ofDual K.1).1 : Ideal R) from hKL.1) r) := by
  exact completedGroupAlgebraFiniteQuotientTransition_single (R := R) (G := G)
    (hIJ := (show ((OrderDual.ofDual L.1).1 : Ideal R) ≤
      ((OrderDual.ofDual K.1).1 : Ideal R) from hKL.1))
    (hUV := hKL.2) q r

/-- The open finite-quotient transition associated to \(K\leq K\) is the identity ring map. -/
@[simp]
theorem completedGroupAlgebraOpenFiniteQuotientTransition_id
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (K : CompletedGroupAlgebraOpenQuotientIndex R G) :
    completedGroupAlgebraOpenFiniteQuotientTransition R G (le_rfl : K ≤ K) =
      RingHom.id (CompletedGroupAlgebraOpenQuotientStage R G K) := by
  apply MonoidAlgebra.ringHom_ext
  · intro r
    rw [completedGroupAlgebraOpenFiniteQuotientTransition_single,
      Ideal.Quotient.factor_eq]
    change MonoidAlgebra.single
        ((OpenNormalSubgroupInClass.map
          (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
          (U := OrderDual.ofDual K.2) (V := OrderDual.ofDual K.2)
          (le_rfl : K.2 ≤ K.2)) 1) r =
      MonoidAlgebra.single 1 r
    rw [OpenNormalSubgroupInClass.map_id]
    rfl
  · intro q
    rw [completedGroupAlgebraOpenFiniteQuotientTransition_single]
    change MonoidAlgebra.single
        ((OpenNormalSubgroupInClass.map
          (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
          (U := OrderDual.ofDual K.2) (V := OrderDual.ofDual K.2)
          (le_rfl : K.2 ≤ K.2)) q) 1 =
      MonoidAlgebra.single q 1
    rw [OpenNormalSubgroupInClass.map_id]
    rfl

/--
Successive open finite-quotient transitions from \(M\) through \(L\) to \(K\) equal the transition
attached to the composite refinement \(K\leq M\).
-/
@[simp 900]
theorem completedGroupAlgebraOpenFiniteQuotientTransition_comp
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    {K L M : CompletedGroupAlgebraOpenQuotientIndex R G} (hKL : K ≤ L) (hLM : L ≤ M) :
    (completedGroupAlgebraOpenFiniteQuotientTransition R G hKL).comp
        (completedGroupAlgebraOpenFiniteQuotientTransition R G hLM) =
      completedGroupAlgebraOpenFiniteQuotientTransition R G (hKL.trans hLM) := by
  change
    (completedGroupAlgebraFiniteQuotientTransition R G
      (show ((OrderDual.ofDual L.1).1 : Ideal R) ≤
        ((OrderDual.ofDual K.1).1 : Ideal R) from hKL.1) hKL.2).comp
        (completedGroupAlgebraFiniteQuotientTransition R G
          (show ((OrderDual.ofDual M.1).1 : Ideal R) ≤
            ((OrderDual.ofDual L.1).1 : Ideal R) from hLM.1) hLM.2) =
      completedGroupAlgebraFiniteQuotientTransition R G
        (show ((OrderDual.ofDual M.1).1 : Ideal R) ≤
          ((OrderDual.ofDual K.1).1 : Ideal R) from (hKL.trans hLM).1)
        (hKL.trans hLM).2
  simp only [completedGroupAlgebraFiniteQuotientTransition,
    completedGroupAlgebraCoeffQuotientTransition,
    completedGroupAlgebraCoeffQuotientGroupTransition]
  let fKL := Ideal.Quotient.factor
    (show ((OrderDual.ofDual L.1).1 : Ideal R) ≤
      ((OrderDual.ofDual K.1).1 : Ideal R) from hKL.1)
  let fLM := Ideal.Quotient.factor
    (show ((OrderDual.ofDual M.1).1 : Ideal R) ≤
      ((OrderDual.ofDual L.1).1 : Ideal R) from hLM.1)
  let fKM := Ideal.Quotient.factor
    (show ((OrderDual.ofDual M.1).1 : Ideal R) ≤
      ((OrderDual.ofDual K.1).1 : Ideal R) from (hKL.trans hLM).1)
  let gKL :=
    OpenNormalSubgroupInClass.map
      (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
      (U := OrderDual.ofDual K.2) (V := OrderDual.ofDual L.2) hKL.2
  let gLM :=
    OpenNormalSubgroupInClass.map
      (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
      (U := OrderDual.ofDual L.2) (V := OrderDual.ofDual M.2) hLM.2
  let gKM :=
    OpenNormalSubgroupInClass.map
      (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
      (U := OrderDual.ofDual K.2) (V := OrderDual.ofDual M.2)
      (hKL.trans hLM).2
  let cKL := MonoidAlgebra.mapRingHom (CompletedGroupAlgebraQuotient G K.2) fKL
  let cLM := MonoidAlgebra.mapRingHom (CompletedGroupAlgebraQuotient G L.2) fLM
  let cKM := MonoidAlgebra.mapRingHom (CompletedGroupAlgebraQuotient G K.2) fKM
  let dKL := MonoidAlgebra.mapDomainRingHom
    (R ⧸ ((OrderDual.ofDual L.1).1 : Ideal R)) gKL
  let dLM := MonoidAlgebra.mapDomainRingHom
    (R ⧸ ((OrderDual.ofDual M.1).1 : Ideal R)) gLM
  let dKM := MonoidAlgebra.mapDomainRingHom
    (R ⧸ ((OrderDual.ofDual M.1).1 : Ideal R)) gKM
  let cLMK := MonoidAlgebra.mapRingHom (CompletedGroupAlgebraQuotient G K.2) fLM
  let dKLM := MonoidAlgebra.mapDomainRingHom
    (R ⧸ ((OrderDual.ofDual M.1).1 : Ideal R)) gKL
  change (cKL.comp dKL).comp (cLM.comp dLM) = cKM.comp dKM
  have hswap : dKL.comp cLM = cLMK.comp dKLM := by
    exact (MonoidAlgebra.mapRingHom_comp_mapDomainRingHom fLM gKL).symm
  have hcoeff : fKL.comp fLM = fKM := by
    dsimp [fKL, fLM, fKM]
    exact Ideal.Quotient.factor_comp _ _
  have hgroup : gKL.comp gLM = gKM := by
    dsimp [gKL, gLM, gKM]
    exact OpenNormalSubgroupInClass.map_comp
      (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
      (U := OrderDual.ofDual K.2) (V := OrderDual.ofDual L.2)
      (W := OrderDual.ofDual M.2) hKL.2 hLM.2
  calc
    (cKL.comp dKL).comp (cLM.comp dLM) =
        cKL.comp ((dKL.comp cLM).comp dLM) := by
      rfl
    _ = cKL.comp ((cLMK.comp dKLM).comp dLM) := by
      rw [hswap]
      rfl
    _ = (cKL.comp cLMK).comp (dKLM.comp dLM) := by
      rfl
    _ = (MonoidAlgebra.mapRingHom (CompletedGroupAlgebraQuotient G K.2)
          (fKL.comp fLM)).comp
        (MonoidAlgebra.mapDomainRingHom
          (R ⧸ ((OrderDual.ofDual M.1).1 : Ideal R)) (gKL.comp gLM)) := by
      rw [← MonoidAlgebra.mapRingHom_comp,
        ← MonoidAlgebra.mapDomainRingHom_comp]
      rfl
    _ = cKM.comp dKM := by
      rw [hcoeff, hgroup]
      rfl

/-- Every open finite-quotient transition associated to \(K\leq L\) is surjective. -/
theorem completedGroupAlgebraOpenFiniteQuotientTransition_surjective
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    {K L : CompletedGroupAlgebraOpenQuotientIndex R G} (hKL : K ≤ L) :
    Function.Surjective (completedGroupAlgebraOpenFiniteQuotientTransition R G hKL) :=
  completedGroupAlgebraFiniteQuotientTransition_surjective
    (R := R) (G := G)
    (hIJ := (show ((OrderDual.ofDual L.1).1 : Ideal R) ≤
      ((OrderDual.ofDual K.1).1 : Ideal R) from hKL.1))
    (hUV := hKL.2)
end

end CompletedGroupAlgebra
