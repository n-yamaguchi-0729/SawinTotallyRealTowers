/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.SetTheory.Cardinal.Arithmetic
import Nyll.ProCGroups.FiniteGeneration.CharacteristicChainsAndIndices

/-!
# Cardinal invariants and local weight

This file defines the cardinality of a family, topological weight, the clopen invariant `rho`,
and local weight. It compares these invariants using topological and neighborhood bases and proves
that continuous homomorphisms are determined by a topological generating set.
-/

open Set
open TopologicalSpace
open Order
open scoped Cardinal
open scoped Topology Pointwise

namespace ProCGroups.LocalWeight

universe u v

open ProCGroups.ProC ProCGroups.Generation
open ProCGroups.FiniteGeneration

section CardinalInvariants

variable (X : Type u) [TopologicalSpace X]

/-- The cardinality of a family of subsets is viewed as a subtype. -/
noncomputable def familyCardinal (B : Set (Set X)) : Cardinal :=
  Cardinal.mk { U : Set X // U ∈ B }

/--
A family \(B\) is a neighborhood basis at \(x\) if each member of \(B\) is an open neighborhood
of \(x\), and every open neighborhood of \(x\) contains an element of \(B\).
-/
def IsNeighborhoodBasisAt (x : X) (B : Set (Set X)) : Prop :=
  (∀ U ∈ B, IsOpen U ∧ x ∈ U) ∧
    ∀ V, IsOpen V → x ∈ V → ∃ U ∈ B, U ⊆ V

/-- The weight \(w(X)\) is the least cardinality of a basis of open sets. -/
noncomputable def weight : Cardinal :=
  sInf { κ : Cardinal |
    ∃ B : Set (Set X), IsTopologicalBasis B ∧ familyCardinal (X := X) B ≤ κ }

/-- \(\rho(X)\) is the cardinality of the set of all clopen subsets of \(X\). -/
noncomputable def rho : Cardinal :=
  familyCardinal (X := X) { U : Set X | IsClopen U }

/-- The local weight at \(x\) is the least cardinality of a neighborhood basis at \(x\). -/
noncomputable def localWeightAt (x : X) : Cardinal :=
  sInf { κ : Cardinal |
    ∃ B : Set (Set X),
      IsNeighborhoodBasisAt (X := X) x B ∧ familyCardinal (X := X) B ≤ κ }

/-- Any explicit basis bounds the weight from above. -/
theorem weight_le_familyCardinal_of_basis {B : Set (Set X)} (hB : IsTopologicalBasis B) :
    weight X ≤ familyCardinal (X := X) B := by
  unfold weight
  have hmem :
      familyCardinal (X := X) B ∈ { κ : Cardinal |
        ∃ B : Set (Set X), IsTopologicalBasis B ∧ familyCardinal (X := X) B ≤ κ } := by
    exact ⟨B, hB, le_rfl⟩
  exact csInf_le (OrderBot.bddBelow _) hmem

/-- Any explicit neighborhood basis at \(x\) bounds the local weight from above. -/
theorem localWeightAt_le_familyCardinal_of_basis {x : X} {B : Set (Set X)}
    (hB : IsNeighborhoodBasisAt (X := X) x B) :
    localWeightAt X x ≤ familyCardinal (X := X) B := by
  unfold localWeightAt
  have hmem :
      familyCardinal (X := X) B ∈ { κ : Cardinal |
        ∃ B : Set (Set X),
          IsNeighborhoodBasisAt (X := X) x B ∧ familyCardinal (X := X) B ≤ κ } := by
    exact ⟨B, hB, le_rfl⟩
  exact csInf_le (OrderBot.bddBelow _) hmem

/-- If the singleton \(\{x\}\) is open, then the local weight at \(x\) is at most 1. -/
theorem localWeightAt_le_one_of_isOpen_singleton {x : X} (hx : IsOpen ({x} : Set X)) :
    localWeightAt X x ≤ 1 := by
  classical
  let B : Set (Set X) := { {x} }
  have hB : IsNeighborhoodBasisAt (X := X) x B := by
    refine ⟨?_, ?_⟩
    · intro U hU
      rcases Set.mem_singleton_iff.mp hU with rfl
      exact ⟨hx, by simp only [mem_singleton_iff]⟩
    · intro V hVopen hxV
      refine ⟨{x}, by simp only [mem_singleton_iff, B], ?_⟩
      intro y hy
      rcases Set.mem_singleton_iff.mp hy with rfl
      exact hxV
  calc
    localWeightAt X x ≤ familyCardinal (X := X) B :=
      localWeightAt_le_familyCardinal_of_basis (X := X) (x := x) hB
    _ = 1 := by
      simp only [familyCardinal, mem_singleton_iff, Cardinal.mk_fintype, Fintype.card_unique,
          Nat.cast_one, B]

omit [TopologicalSpace X] in
/-- The family cardinal is monotone under inclusion of families. -/
theorem familyCardinal_mono {B C : Set (Set X)} (hBC : B ⊆ C) :
    familyCardinal (X := X) B ≤ familyCardinal (X := X) C := by
  unfold familyCardinal
  exact Cardinal.mk_le_of_injective
    (f := fun U : { U : Set X // U ∈ B } => ⟨U.1, hBC U.2⟩)
    (by
      intro U V hUV
      exact Subtype.ext (congrArg (fun W : { U : Set X // U ∈ C } => W.1) hUV))

/--
Any family of clopen sets injects into the type of all clopen subsets, so its cardinality is
bounded by \(\rho(X)\).
-/
theorem familyCardinal_le_rho_of_clopenFamily {B : Set (Set X)}
    (hB : ∀ U ∈ B, IsClopen U) :
    familyCardinal (X := X) B ≤ rho X := by
  unfold familyCardinal rho
  let f : { U : Set X // U ∈ B } → { U : Set X // IsClopen U } :=
    fun U => ⟨U.1, hB U.1 U.2⟩
  refine Cardinal.mk_le_of_injective (f := f) ?_
  intro U V hUV
  exact Subtype.ext (congrArg (fun W : { U : Set X // IsClopen U } => W.1) hUV)

/-- A finite basis on a \(T_1\) space forces the underlying space itself to be finite. -/
theorem finite_of_finite_basisSubtype [T1Space X] {B : Set (Set X)}
    (hB : IsTopologicalBasis B) [Finite { U : Set X // U ∈ B }] : Finite X := by
  classical
  let β : Type u := { U : Set X // U ∈ B }
  let : Fintype β := Fintype.ofFinite β
  let code : X → Set β := fun x => { U | x ∈ (U : Set X) }
  have hcode : Function.Injective code := by
    intro x y hxy
    by_contra hne
    have hx_mem : x ∈ ({y}ᶜ : Set X) := by
      change x ∉ ({y} : Set X)
      intro hxy
      exact hne (by simpa [Set.mem_singleton_iff] using hxy)
    have hOpen : IsOpen ({y}ᶜ : Set X) :=
      (isClosed_singleton : IsClosed ({y} : Set X)).isOpen_compl
    rcases hB.exists_subset_of_mem_open hx_mem hOpen with ⟨U, hUB, hxU, hUsub⟩
    have hyU : y ∉ U := by
      intro hyU
      have : y ∈ ({y}ᶜ : Set X) := hUsub hyU
      have hnot : y ∉ ({y} : Set X) := by
        exact this
      exact hnot (Set.mem_singleton_iff.mpr rfl)
    have hxCode : (⟨U, hUB⟩ : β) ∈ code x := by
      change x ∈ U
      exact hxU
    have hyCode : (⟨U, hUB⟩ : β) ∈ code y := by
      rw [← hxy]
      exact hxCode
    change y ∈ U at hyCode
    exact hyU hyCode
  exact Finite.of_injective code hcode

/-- An infinite \(T_1\) space cannot have a finite topological basis. -/
theorem infinite_familySubtype_of_basis [T1Space X] [Infinite X] {B : Set (Set X)}
    (hB : IsTopologicalBasis B) : Infinite { U : Set X // U ∈ B } := by
  classical
  by_contra hfinite
  let : Finite { U : Set X // U ∈ B } := not_infinite_iff_finite.mp hfinite
  have hXfin : Finite X := finite_of_finite_basisSubtype (X := X) hB
  exact hXfin.false

/--
In a compact space, every clopen set is the union of finitely many members of any chosen
topological basis.
-/
theorem exists_finset_basisSUnion_eq_of_isClopen [CompactSpace X] {B : Set (Set X)}
    (hB : IsTopologicalBasis B) {U : Set X} (hU : IsClopen U) :
    ∃ s : Finset { V : Set X // V ∈ B },
      U = ⋃₀ (Subtype.val '' (↑s : Set { V : Set X // V ∈ B })) := by
  classical
  obtain ⟨s, hs⟩ :=
    eq_sUnion_finset_of_isTopologicalBasis_of_isCompact_open B hB U hU.isClosed.isCompact
      hU.isOpen
  refine ⟨s, ?_⟩
  simpa only [Set.sUnion_image] using hs

/-- In an infinite compact Hausdorff space, every basis controls the number of clopen subsets. -/
theorem rho_le_familyCardinal_of_basis [CompactSpace X] [T2Space X] [Infinite X]
    {B : Set (Set X)} (hB : IsTopologicalBasis B) :
    rho X ≤ familyCardinal (X := X) B := by
  classical
  let β : Type u := { U : Set X // U ∈ B }
  have hβinf : Infinite β := infinite_familySubtype_of_basis (X := X) hB
  let encode : { U : Set X // IsClopen U } → Finset β :=
    fun U =>
      Classical.choose
        (exists_finset_basisSUnion_eq_of_isClopen (X := X) hB (U := U.1) U.2)
  have hencode :
      ∀ U : { U : Set X // IsClopen U },
        U.1 = ⋃₀ (Subtype.val '' (↑(encode U) : Set β)) := by
    intro U
    exact Classical.choose_spec
      (exists_finset_basisSUnion_eq_of_isClopen (X := X) hB (U := U.1) U.2)
  have henc_inj : Function.Injective encode := by
    intro U V hUV
    apply Subtype.ext
    calc
      U.1 = ⋃₀ (Subtype.val '' (↑(encode U) : Set β)) := hencode U
      _ = ⋃₀ (Subtype.val '' (↑(encode V) : Set β)) := by simp only [hUV, sUnion_image,
          SetLike.mem_coe, iUnion_coe_set]
      _ = V.1 := (hencode V).symm
  unfold rho familyCardinal
  calc
    Cardinal.mk { U : Set X // IsClopen U } ≤ Cardinal.mk (Finset β) :=
      Cardinal.mk_le_of_injective (f := encode) henc_inj
    _ = Cardinal.mk β := by
      exact Cardinal.mk_finset_of_infinite β
    _ = Cardinal.mk { U : Set X // U ∈ B } := by
      rfl

/--
For an infinite compact Hausdorff space, the cardinal invariant \(\rho(X)\) is bounded above by
the topological weight of \(X\).
-/
theorem rho_le_weight [CompactSpace X] [T2Space X] [Infinite X] :
    rho X ≤ weight X := by
  unfold weight
  refine le_csInf ?_ ?_
  · refine ⟨familyCardinal (X := X) { U : Set X | IsOpen U }, ?_⟩
    exact ⟨{ U : Set X | IsOpen U }, isTopologicalBasis_opens, le_rfl⟩
  intro κ hκ
  rcases hκ with ⟨B, hB, hcard⟩
  exact le_trans (rho_le_familyCardinal_of_basis (X := X) hB) hcard

/--
Every global basis yields a local basis at any chosen point, so the local weight is always
bounded by the weight.
-/
theorem localWeightAt_le_weight {x : X} :
    localWeightAt X x ≤ weight X := by
  unfold weight
  refine le_csInf ?_ ?_
  · refine ⟨familyCardinal (X := X) { U : Set X | IsOpen U }, ?_⟩
    exact ⟨{ U : Set X | IsOpen U }, isTopologicalBasis_opens, le_rfl⟩
  · intro κ hκ
    rcases hκ with ⟨B, hB, hBcard⟩
    let Bx : Set (Set X) := { U : Set X | U ∈ B ∧ x ∈ U }
    have hBx : IsNeighborhoodBasisAt (X := X) x Bx := by
      constructor
      · intro U hU
        exact ⟨hB.isOpen hU.1, hU.2⟩
      · intro V hVopen hxV
        rcases hB.exists_subset_of_mem_open hxV hVopen with ⟨U, hUB, hxU, hUsub⟩
        exact ⟨U, ⟨hUB, hxU⟩, hUsub⟩
    calc
      localWeightAt X x ≤ familyCardinal (X := X) Bx :=
        localWeightAt_le_familyCardinal_of_basis (X := X) hBx
      _ ≤ familyCardinal (X := X) B :=
        familyCardinal_mono (X := X) (by
          intro U hU
          exact hU.1)
      _ ≤ κ := hBcard

/-- Any clopen basis bounds the weight by \(\rho(X)\). -/
theorem weight_le_rho_of_exists_clopenBasis
    (hB : ∃ B : Set (Set X), IsTopologicalBasis B ∧ ∀ U ∈ B, IsClopen U) :
    weight X ≤ rho X := by
  rcases hB with ⟨B, hBasis, hClopen⟩
  calc
    weight X ≤ familyCardinal (X := X) B :=
      weight_le_familyCardinal_of_basis (X := X) hBasis
    _ ≤ rho X :=
      familyCardinal_le_rho_of_clopenFamily (X := X) hClopen

/-- Any clopen basis of an infinite compact Hausdorff space has cardinality exactly \(\rho(X)\). -/
theorem familyCardinal_eq_rho_of_clopenBasis [CompactSpace X] [T2Space X] [Infinite X]
    {B : Set (Set X)} (hB : IsTopologicalBasis B) (hClopen : ∀ U ∈ B, IsClopen U) :
    familyCardinal (X := X) B = rho X := by
  apply le_antisymm
  · exact familyCardinal_le_rho_of_clopenFamily (X := X) hClopen
  · exact rho_le_familyCardinal_of_basis (X := X) hB

/--
If the clopen subsets already form a topological basis, the weight is bounded by the same
cardinal invariant.
-/
theorem weight_le_rho_of_clopenBasis
    (hBasis : IsTopologicalBasis { U : Set X | IsClopen U }) :
    weight X ≤ rho X := by
  calc
    weight X ≤ familyCardinal (X := X) { U : Set X | IsClopen U } :=
      weight_le_familyCardinal_of_basis (X := X) hBasis
    _ = rho X := rfl

/-- 6.1(a) in the special case where all clopen subsets already form a basis. -/
theorem weight_eq_rho_of_clopenBasis [CompactSpace X] [T2Space X] [Infinite X]
    (hBasis : IsTopologicalBasis { U : Set X | IsClopen U }) :
    weight X = rho X := by
  apply le_antisymm
  · exact weight_le_rho_of_clopenBasis (X := X) hBasis
  · exact rho_le_weight (X := X)

/-- Any clopen neighborhood basis at \(x\) bounds the local weight at \(x\) by \(\rho(X)\). -/
theorem localWeightAt_le_rho_of_exists_clopenNeighborhoodBasis {x : X}
    (hB : ∃ B : Set (Set X),
      IsNeighborhoodBasisAt (X := X) x B ∧ ∀ U ∈ B, IsClopen U) :
    localWeightAt X x ≤ rho X := by
  rcases hB with ⟨B, hBasis, hClopen⟩
  calc
    localWeightAt X x ≤ familyCardinal (X := X) B :=
      localWeightAt_le_familyCardinal_of_basis (X := X) hBasis
    _ ≤ rho X :=
      familyCardinal_le_rho_of_clopenFamily (X := X) hClopen

end CardinalInvariants

section LocalWeightOfGroups

variable (G : Type u) [Group G] [TopologicalSpace G]

/-- the local weight `w₀(G)` of a topological group is the local weight at `1`.

The continuity assumptions needed for later results are imposed where they are used; the cardinal
invariant itself only depends on the underlying topology and distinguished point. -/
noncomputable def localWeight : Cardinal :=
  localWeightAt (X := G) (1 : G)

/-- The local weight of a topological group is bounded by its weight. -/
theorem localWeight_le_weight :
    localWeight G ≤ weight G := by
  simpa [localWeight] using
    (localWeightAt_le_weight (X := G) (x := (1 : G)))

/-- A clopen neighborhood basis of cardinal at most \(\rho\) bounds the local weight by \(\rho\). -/
theorem localWeight_le_rho_of_exists_clopenNeighborhoodBasis
    (hB : ∃ B : Set (Set G),
      IsNeighborhoodBasisAt (X := G) (1 : G) B ∧ ∀ U ∈ B, IsClopen U) :
    localWeight G ≤ rho G := by
  simpa [localWeight] using
    (localWeightAt_le_rho_of_exists_clopenNeighborhoodBasis (X := G) (x := (1 : G)) hB)

end LocalWeightOfGroups

section GroupTranslateBases

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/--
The family of all left translates of members of \(B\). This is the global basis naturally
associated to a neighborhood basis at \(1\).
-/
def leftTranslateFamily (B : Set (Set G)) : Set (Set G) :=
  { V : Set G | ∃ g : G, ∃ U ∈ B, V = g • U }

/-- In a group, left translates of a neighborhood basis at \(1\) form a topological basis. -/
theorem isTopologicalBasis_leftTranslateFamily {B : Set (Set G)}
    (hB : IsNeighborhoodBasisAt (X := G) (1 : G) B) :
    IsTopologicalBasis (leftTranslateFamily (G := G) B) := by
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · intro V hV
    rcases hV with ⟨g, U, hUB, rfl⟩
    exact (hB.1 U hUB).1.leftCoset g
  · intro g V hgV hOpenV
    have hOpenPre : IsOpen (g⁻¹ • V) := hOpenV.leftCoset g⁻¹
    have hmemPre : (1 : G) ∈ g⁻¹ • V := by
      exact ⟨g, hgV, by simp only [smul_eq_mul, inv_mul_cancel]⟩
    rcases hB.2 (g⁻¹ • V) hOpenPre hmemPre with ⟨U, hUB, hUsub⟩
    refine ⟨g • U, ⟨g, U, hUB, rfl⟩, ?_, ?_⟩
    · exact ⟨1, (hB.1 U hUB).2, by simp only [smul_eq_mul, mul_one]⟩
    · intro y hy
      rcases hy with ⟨u, huU, rfl⟩
      rcases hUsub huU with ⟨v, hvV, rfl⟩
      simpa [mul_assoc] using hvV

/--
Any neighborhood basis at \(1\) yields a global basis whose cardinality is the cardinality of
its translate family.
-/
theorem weight_le_familyCardinal_leftTranslateFamily_of_neighborhoodBasis {B : Set (Set G)}
    (hB : IsNeighborhoodBasisAt (X := G) (1 : G) B) :
    weight G ≤ familyCardinal (X := G) (leftTranslateFamily (G := G) B) := by
  exact weight_le_familyCardinal_of_basis (X := G)
    (isTopologicalBasis_leftTranslateFamily (G := G) hB)

end GroupTranslateBases

section GroupTranslateClopen

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Left translation preserves clopen subsets in a topological group. -/
theorem IsClopen.leftTranslate {U : Set G} (hU : IsClopen U) (g : G) :
    IsClopen (g • U) := by
  constructor
  · exact hU.1.leftCoset g
  · exact hU.2.leftCoset g

/--
If the identity has a clopen neighborhood basis, then w(G) \(\le\) \(\rho\)(G). The remaining
work for the full proposition is the comparison with \(w_0(G)\) in the using
cardinality-preserving form used in the book.
-/
theorem weight_le_rho_of_exists_clopenNeighborhoodBasisAtOne
    (hB : ∃ B : Set (Set G),
      IsNeighborhoodBasisAt (X := G) (1 : G) B ∧ ∀ U ∈ B, IsClopen U) :
    weight G ≤ rho G := by
  rcases hB with ⟨B, hBasis, hClopen⟩
  apply weight_le_rho_of_exists_clopenBasis (X := G)
  refine ⟨leftTranslateFamily (G := G) B,
    isTopologicalBasis_leftTranslateFamily (G := G) hBasis, ?_⟩
  intro V hV
  rcases hV with ⟨g, U, hUB, rfl⟩
  exact IsClopen.leftTranslate (G := G) (hClopen U hUB) g

end GroupTranslateClopen


/--
A continuous homomorphism out of a profinite group is determined by any topological generating
set.
-/
theorem continuousMonoidHom_eq_of_eqOn_topologicalGeneratingSet
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {R : Type v} [Group R] [TopologicalSpace R] [T2Space R]
    {X : Set G} (hXgen : TopologicallyGenerates (G := G) X)
    {f g : ContinuousMonoidHom G R} (hfg : Set.EqOn f g X) :
    f = g := by
  let K : Subgroup G := {
    carrier := { x | f x = g x }
    one_mem' := by simp only [mem_ofPred_eq, map_one]
    mul_mem' := by
      intro a b ha hb
      change f (a * b) = g (a * b)
      rw [map_mul, map_mul, ha, hb]
    inv_mem' := by
      intro a ha
      simpa using congrArg Inv.inv ha
  }
  have hKclosed : IsClosed ((K : Subgroup G) : Set G) := by
    change IsClosed { x | f x = g x }
    exact isClosed_eq f.continuous_toFun g.continuous_toFun
  have hsub : Subgroup.closure X ≤ K := by
    rw [Subgroup.closure_le]
    intro x hx
    exact hfg hx
  have htop : (⊤ : Subgroup G) ≤ K := by
    have hcl :
        (Subgroup.closure X).topologicalClosure ≤ K :=
      Subgroup.topologicalClosure_minimal _ hsub hKclosed
    change (Subgroup.closure X).topologicalClosure = ⊤ at hXgen
    rw [hXgen] at hcl
    simpa using hcl
  ext x
  simpa [K] using htop (show x ∈ (⊤ : Subgroup G) from by simp only [Subgroup.mem_top])

/--
For a finite discrete codomain, the set of continuous maps from a profinite space has
cardinality at most \(\rho(X)\).
-/
theorem cardinal_continuousMap_to_finite_le_rho
    (X : Type u) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] [Infinite X]
    (H : Type v) [Finite H] [TopologicalSpace H] [DiscreteTopology H] :
    Cardinal.mk C(X, H) ≤ Cardinal.lift (rho X) := by
  classical
  by_cases hH : Nonempty H
  · let β : Type u := { U : Set X // IsClopen U }
    have hβinf : Infinite β := by
      simpa [β] using
        (infinite_familySubtype_of_basis (X := X)
          (B := { U : Set X | IsClopen U })
          (InverseSystems.isTopologicalBasis_isClopen_of_compact_t2_totallyDisconnected
            (X := X)))
    let : Fintype H := Fintype.ofFinite H
    let encode : C(X, H) → H → β := fun f h =>
      ⟨f ⁻¹' ({h} : Set H), by
        refine ⟨?_, ?_⟩
        · simpa using (isClosed_discrete ({h} : Set H)).preimage f.continuous_toFun
        · simpa using (isOpen_discrete ({h} : Set H)).preimage f.continuous_toFun⟩
    have hencode_inj : Function.Injective encode := by
      intro f g hfg
      ext x
      have hx : x ∈ (encode f (f x)).1 := by
        simp only [mem_preimage, mem_singleton_iff, encode]
      have hx' : x ∈ (encode g (f x)).1 := by
        simpa [hfg] using hx
      simpa [eq_comm, encode] using hx'
    have hAlephLe : Cardinal.aleph0 ≤ Cardinal.lift (rho X) := by
      apply (Cardinal.aleph0_le_lift).2
      simp only [rho, familyCardinal, mem_ofPred_eq, Cardinal.aleph0_le_mk, β]
    have hHcardPos : 1 ≤ Fintype.card H := Fintype.card_pos_iff.mpr hH
    calc
      Cardinal.mk C(X, H) ≤ Cardinal.mk (H → β) :=
        Cardinal.mk_le_of_injective (f := encode) hencode_inj
      _ = Cardinal.lift (Cardinal.mk β) ^ Cardinal.lift (Cardinal.mk H) := by
        rw [Cardinal.mk_arrow]
      _ = Cardinal.lift (rho X) ^ Fintype.card H := by
        rw [Cardinal.mk_fintype H, Cardinal.lift_natCast]
        rfl
      _ = Cardinal.lift (rho X) :=
        Cardinal.power_nat_eq hAlephLe hHcardPos
  · have hEmpty : IsEmpty H := not_nonempty_iff.mp hH
    have : IsEmpty C(X, H) := by
      refine ⟨fun f => ?_⟩
      exact isEmptyElim (f (Classical.choice (inferInstanceAs (Nonempty X))))
    have hzero : Cardinal.mk C(X, H) = 0 := by
      rw [Cardinal.mk_eq_zero_iff]
      infer_instance
    rw [hzero]
    exact zero_le

/-- Passing to a closed subspace does not increase \(\rho\). -/
theorem rho_subtype_le_rho_of_closed
    (X : Type u) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] {A : Set X} (hAclosed : IsClosed A) :
    rho ↥A ≤ rho X := by
  classical
  have hlift :
      ∀ U : { U : Set A // IsClopen U }, ∃ C : { C : Set X // IsClopen C },
        Subtype.val ⁻¹' C.1 = U.1 := by
    intro U
    rcases isOpen_induced_iff.mp U.2.2 with ⟨O, hOopen, hOeq⟩
    rcases isClosed_induced_iff.mp U.2.1 with ⟨F, hFclosed, hFeq⟩
    have hAF_subset_O : A ∩ F ⊆ O := by
      intro x hx
      have hxU : (⟨x, hx.1⟩ : A) ∈ U.1 := by
        rw [← hFeq]
        simpa using hx.2
      rw [← hOeq] at hxU
      simpa using hxU
    rcases exists_clopen_of_closed_subset_open
        (Z := A ∩ F) (U := O) (hAclosed.inter hFclosed) hOopen hAF_subset_O with
      ⟨C, hCclopen, hAF_sub_C, hCsubO⟩
    refine ⟨⟨C, hCclopen⟩, ?_⟩
    ext x
    constructor
    · intro hxC
      have hxO : x.1 ∈ O := hCsubO hxC
      rw [← hOeq]
      simpa using hxO
    · intro hxU
      have hxF : x.1 ∈ F := by
        have hxF' : x ∈ (Subtype.val ⁻¹' F : Set A) := by
          rwa [← hFeq] at hxU
        simpa using hxF'
      exact hAF_sub_C ⟨x.2, hxF⟩
  choose liftClopen hLiftClopen using hlift
  unfold rho familyCardinal
  refine Cardinal.mk_le_of_injective (f := liftClopen) ?_
  intro U V hUV
  apply Subtype.ext
  have hpre :
      (Subtype.val ⁻¹' (liftClopen U).1 : Set A) =
        (Subtype.val ⁻¹' (liftClopen V).1 : Set A) := by
    simpa using congrArg (fun C : { C : Set X // IsClopen C } =>
      (Subtype.val ⁻¹' C.1 : Set A)) hUV
  rw [hLiftClopen U, hLiftClopen V] at hpre
  exact hpre

/--
The finite coset action is a continuous homomorphism into a discrete permutation group, with the
finite-quotient certificate supplied by openness.
-/
noncomputable abbrev openSubgroupIndexContinuousHom
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (H : Subgroup G) (hH : IsOpen (H : Set G)) {n : ℕ} (hn : Nat.card (G ⧸ H) = n) :
    ContinuousMonoidHom G (Equiv.Perm (Fin n)) :=
  ProCGroups.FiniteGeneration.openSubgroupIndexContinuousHom
    (G := G) H hH (Subgroup.quotient_finite_of_isOpen H hH) hn

/-- The clopen-subset cardinal \(\rho\) is a topological invariant. -/
theorem rho_eq_of_homeomorph
    (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    rho X = rho Y := by
  classical
  unfold rho familyCardinal
  refine Cardinal.mk_congr ?_
  refine
    { toFun := fun U => ⟨e.symm ⁻¹' U.1, U.2.preimage e.symm.continuous⟩
      invFun := fun V => ⟨e ⁻¹' V.1, V.2.preimage e.continuous⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro U
    apply Subtype.ext
    ext x
    simp only [mem_preimage, Homeomorph.symm_apply_apply]
  · intro V
    apply Subtype.ext
    ext y
    simp only [mem_preimage, Homeomorph.apply_symm_apply]

/--
For an infinite discrete space \(X\), the one-point compactification has exactly \(\#X\) clopen
subsets: finite subsets coming from \(X\), and complements of finite subsets.
-/
theorem rho_onePoint_eq_cardinal_of_infinite_discrete
    (X : Type u) [TopologicalSpace X] [DiscreteTopology X] [Infinite X] :
    rho (OnePoint X) = Cardinal.mk X := by
  classical
  let imageClopen : Finset X → Set (OnePoint X) :=
    fun s => ((↑) '' (s : Set X) : Set (OnePoint X))
  have hImageClopen : ∀ s : Finset X, IsClopen (imageClopen s) := by
    intro s
    constructor
    · exact (OnePoint.isClosed_image_coe (s := (s : Set X))).2
        ⟨s.finite_toSet.isClosed, s.finite_toSet.isCompact⟩
    · exact (OnePoint.isOpen_image_coe (s := (s : Set X))).2 (isOpen_discrete _)
  have himage_eq_of_notMem_infty {s : Set (OnePoint X)} (hs : OnePoint.infty ∉ s) :
      ((↑) '' (((↑) : X → OnePoint X) ⁻¹' s) : Set (OnePoint X)) = s := by
    ext z
    cases z using OnePoint.rec with
    | infty =>
        simp only [mem_image, mem_preimage, OnePoint.coe_ne_infty, and_false, exists_const, hs]
    | coe x =>
        simp only [mem_image, mem_preimage, OnePoint.some_eq_iff, exists_eq_right]
  let decode : Finset X ⊕ Finset X → { U : Set (OnePoint X) // IsClopen U }
    | Sum.inl s => ⟨imageClopen s, hImageClopen s⟩
    | Sum.inr s => ⟨(imageClopen s)ᶜ,
        ⟨(hImageClopen s).2.isClosed_compl, (hImageClopen s).1.isOpen_compl⟩⟩
  let code : { U : Set (OnePoint X) // IsClopen U } → Finset X ⊕ Finset X := fun U => by
    by_cases hinfty : OnePoint.infty ∈ U.1
    · have hfinite :
          ((((↑) : X → OnePoint X) ⁻¹' (U.1ᶜ : Set (OnePoint X))) : Set X).Finite := by
        have hcompact :
            IsCompact (((↑) : X → OnePoint X) ⁻¹' (U.1ᶜ : Set (OnePoint X))) := by
          exact ((OnePoint.isClosed_iff_of_notMem (s := U.1ᶜ) (by simpa using hinfty)
            ).1 U.2.2.isClosed_compl).2
        exact isCompact_iff_finite.mp hcompact
      exact Sum.inr hfinite.toFinset
    · have hfinite :
          ((((↑) : X → OnePoint X) ⁻¹' U.1) : Set X).Finite := by
        have hcompact :
            IsCompact (((↑) : X → OnePoint X) ⁻¹' U.1 : Set X) := by
          exact ((OnePoint.isClosed_iff_of_notMem (s := U.1) hinfty).1 U.2.1).2
        exact isCompact_iff_finite.mp hcompact
      exact Sum.inl hfinite.toFinset
  have hdecode_code :
      Function.LeftInverse decode code := by
    intro U
    dsimp [code]
    by_cases hinfty : OnePoint.infty ∈ U.1
    · simp only [hinfty, decode]
      apply Subtype.ext
      have hfinite :
          ((((↑) : X → OnePoint X) ⁻¹' (U.1ᶜ : Set (OnePoint X))) : Set X).Finite := by
        have hcompact :
            IsCompact (((↑) : X → OnePoint X) ⁻¹' (U.1ᶜ : Set (OnePoint X))) := by
          exact ((OnePoint.isClosed_iff_of_notMem (s := U.1ᶜ) (by simpa using hinfty)
            ).1 U.2.2.isClosed_compl).2
        exact isCompact_iff_finite.mp hcompact
      change (((↑) '' ((hfinite.toFinset : Set X)) : Set (OnePoint X))ᶜ) = U.1
      rw [hfinite.coe_toFinset]
      rw [himage_eq_of_notMem_infty (s := U.1ᶜ) (by simpa using hinfty)]
      simp only [compl_compl]
    · simp only [hinfty, decode]
      apply Subtype.ext
      have hfinite :
          ((((↑) : X → OnePoint X) ⁻¹' U.1) : Set X).Finite := by
        have hcompact :
            IsCompact (((↑) : X → OnePoint X) ⁻¹' U.1 : Set X) := by
          exact ((OnePoint.isClosed_iff_of_notMem (s := U.1) hinfty).1 U.2.1).2
        exact isCompact_iff_finite.mp hcompact
      change ((↑) '' ((hfinite.toFinset : Set X)) : Set (OnePoint X)) = U.1
      rw [hfinite.coe_toFinset]
      exact himage_eq_of_notMem_infty (s := U.1) hinfty
  have hupper : rho (OnePoint X) ≤ Cardinal.mk X := by
    unfold rho familyCardinal
    calc
      Cardinal.mk { U : Set (OnePoint X) // IsClopen U } ≤ Cardinal.mk (Finset X ⊕ Finset X) :=
        Cardinal.mk_le_of_injective (f := code) hdecode_code.injective
      _ = Cardinal.mk (Finset X) + Cardinal.mk (Finset X) := by
        rw [Cardinal.mk_sum]
        simp only [Cardinal.mk_finset_of_infinite, Cardinal.lift_id, Cardinal.add_mk_eq_max,
            max_self]
      _ = Cardinal.mk X + Cardinal.mk X := by
        simp only [Cardinal.mk_finset_of_infinite X, Cardinal.add_mk_eq_max, max_self]
      _ = Cardinal.mk X := Cardinal.add_eq_self (Cardinal.aleph0_le_mk X)
  have hlower : Cardinal.mk X ≤ rho (OnePoint X) := by
    let singletonClopen : X → { U : Set (OnePoint X) // IsClopen U } := fun x =>
      ⟨({(x : OnePoint X)} : Set (OnePoint X)), by
        constructor
        · rw [← Set.image_singleton]
          exact (OnePoint.isClosed_image_coe (s := ({x} : Set X))).2
            ⟨(Set.finite_singleton x).isClosed, (Set.finite_singleton x).isCompact⟩
        · rw [← Set.image_singleton]
          exact (OnePoint.isOpen_image_coe (s := ({x} : Set X))).2
            (isOpen_discrete ({x} : Set X))⟩
    have hsingle_inj : Function.Injective singletonClopen := by
      intro x y hxy
      have hset :
          ({(x : OnePoint X)} : Set (OnePoint X)) = ({(y : OnePoint X)} : Set (OnePoint X)) :=
        congrArg Subtype.val hxy
      simpa using Set.singleton_injective hset
    unfold rho familyCardinal
    exact Cardinal.mk_le_of_injective (f := singletonClopen) hsingle_inj
  exact le_antisymm hupper hlower

/--
The generating and convergence data imply the stated local-weight or cardinal-invariant
relation.
-/
theorem rho_closure_eq_cardinal_of_generatesAndConvergesToOneAlongOpenSubgroups_infinite
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (X : Set G)
    (hX : GeneratesAndConvergesToOneAlongOpenSubgroups (G := G) X) (hXinfinite : Set.Infinite X)
    (hclosure : closure X = X ∪ ({1} : Set G)) :
    rho ↥(closure X) = Cardinal.mk X := by
  by_cases h1X : (1 : G) ∈ X
  · let Y : Set G := X \ ({1} : Set G)
    have hYunion : Y ∪ ({1} : Set G) = X := by
      ext x
      by_cases hx : x = 1
      · subst hx
        simp only [union_singleton, h1X, insert_sdiff_self_of_mem, Y]
      · simp only [union_singleton, insert_sdiff_singleton, mem_insert_iff, hx, false_or, Y]
    have hYinf : Set.Infinite Y := by
      by_contra hfin
      have hXfin : Set.Finite X := by
        rw [← hYunion]
        exact (Set.not_infinite.mp hfin).union (Set.finite_singleton 1)
      exact hXinfinite hXfin
    have hYconv : ConvergesToOneAlongOpenSubgroups (G := G) Y := by
      have hconvUnion : ConvergesToOneAlongOpenSubgroups (G := G) (Y ∪ ({1} : Set G)) := by
        simpa [hYunion] using hX.2
      exact (ConvergesToOneAlongOpenSubgroups.union_one_iff (G := G) (X := Y)).1 hconvUnion
    have hclosureY : closure Y = X := by
      calc
        closure Y = Y ∪ ({1} : Set G) := by
          exact (closure_generatorsConvergingToOne (G := G) hYconv).2 hYinf
        _ = X := hYunion
    have h1notY : (1 : G) ∉ Y := by
      simp only [mem_sdiff, mem_singleton_iff, not_true_eq_false, and_false, not_false_eq_true, Y]
    let : Infinite Y := Set.infinite_coe_iff.mpr hYinf
    have hYdiff : Y \ ({1} : Set G) = Y := by
      ext y
      by_cases hy : y = 1
      · subst hy
        simp only [sdiff_idem, mem_sdiff, mem_singleton_iff, not_true_eq_false, and_false, Y]
      · simp only [sdiff_idem, mem_sdiff, mem_singleton_iff, hy, not_false_eq_true, and_true, Y]
    have hdiscY : IsDiscrete Y := by
      rcases closure_generatorsConvergingToOne (G := G) hYconv with ⟨hdisc, _⟩
      simpa [hYdiff] using hdisc
    let : DiscreteTopology ↥Y := (isDiscrete_iff_discreteTopology).mp hdiscY
    have hinsertY : (insert (1 : G) Y : Set G) = X := by
      ext y
      constructor
      · intro hy
        rcases Set.mem_insert_iff.mp hy with rfl | hyY
        · exact h1X
        · exact hyY.1
      · intro hyX
        by_cases hy : y = 1
        · exact Set.mem_insert_iff.mpr (Or.inl hy)
        · exact Set.mem_insert_iff.mpr (Or.inr (by simpa [Y, hy] using hyX))
    have hcardY : Cardinal.mk Y = Cardinal.mk X := by
      calc
        Cardinal.mk Y = Cardinal.mk Y + 1 := by
          symm
          exact Cardinal.add_one_eq (Cardinal.aleph0_le_mk Y)
        _ = Cardinal.mk (insert (1 : G) Y : Set G) :=
          (Cardinal.mk_insert h1notY).symm
        _ = Cardinal.mk X := Cardinal.mk_congr (Set.equivOfEq hinsertY)
    have hclosureX_eq : closure X = X := by
      simpa [Set.insert_eq_of_mem h1X] using hclosure
    have hclosureXY : closure X = closure Y := by
      rw [hclosureX_eq, hclosureY]
    calc
      rho ↥(closure X) = rho ↥(closure Y) := by
        exact rho_eq_of_homeomorph _ _ (Homeomorph.setCongr hclosureXY)
      _ = rho (OnePoint Y) := by
        exact rho_eq_of_homeomorph _ _
          ((closure_generatorsConvergingToOne_homeomorph_onePoint
            (G := G) hYconv hYinf h1notY).symm)
      _ = Cardinal.mk Y := rho_onePoint_eq_cardinal_of_infinite_discrete Y
      _ = Cardinal.mk X := hcardY
  · let : Infinite X := Set.infinite_coe_iff.mpr hXinfinite
    have hXdiff : X \ ({1} : Set G) = X := by
      ext x
      by_cases hx : x = 1
      · subst hx
        simp only [h1X, not_false_eq_true, sdiff_singleton_eq_self]
      · simp only [mem_sdiff, mem_singleton_iff, hx, not_false_eq_true, and_true]
    have hdiscX : IsDiscrete X := by
      rcases closure_generatorsConvergingToOne (G := G) hX.2 with ⟨hdisc, _⟩
      simpa [hXdiff] using hdisc
    let : DiscreteTopology ↥X := (isDiscrete_iff_discreteTopology).mp hdiscX
    calc
      rho ↥(closure X) = rho (OnePoint X) := by
        exact rho_eq_of_homeomorph _ _
          ((closure_generatorsConvergingToOne_homeomorph_onePoint
            (G := G) hX.2 hXinfinite h1X).symm)
      _ = Cardinal.mk X := rho_onePoint_eq_cardinal_of_infinite_discrete X

/--
The datum exists neighborhood Basis At cardinal le of local Weight At le fixes the component
used in the corresponding finite-stage construction.
-/
theorem exists_neighborhoodBasisAt_cardinal_le_of_localWeightAt_le
    {X : Type u} [TopologicalSpace X] {x : X} {κ : Cardinal}
    (hcount : localWeightAt (X := X) x ≤ κ) :
    ∃ B : Set (Set X), IsNeighborhoodBasisAt (X := X) x B ∧ familyCardinal (X := X) B ≤ κ := by
  let B0 : Set (Set X) := {V | IsOpen V ∧ x ∈ V}
  have hB0 : IsNeighborhoodBasisAt (X := X) x B0 := by
    constructor
    · intro U hU
      exact hU
    · intro V hVopen hVx
      exact ⟨V, ⟨hVopen, hVx⟩, subset_rfl⟩
  have hS : Set.Nonempty
      {κ' : Cardinal | ∃ B : Set (Set X), IsNeighborhoodBasisAt (X := X) x B ∧
        familyCardinal (X := X) B ≤ κ'} := by
    refine ⟨familyCardinal (X := X) B0, ?_⟩
    exact ⟨B0, hB0, le_rfl⟩
  rcases (show
    ∃ B : Set (Set X), IsNeighborhoodBasisAt (X := X) x B ∧
      familyCardinal (X := X) B ≤ localWeightAt (X := X) x from by
        simpa [localWeightAt] using (csInf_mem (s := {κ' : Cardinal | ∃ B : Set (Set X),
          IsNeighborhoodBasisAt (X := X) x B ∧ familyCardinal (X := X) B ≤ κ'}) hS)
  ) with ⟨B, hBbasis, hBcard⟩
  exact ⟨B, hBbasis, hBcard.trans hcount⟩

/-- Open maps do not increase local weight at the image point. -/
theorem localWeightAt_image_le_of_continuous_open
    {X : Type u} {Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {x : X} (hfcont : Continuous f) (hfopen : IsOpenMap f) :
    localWeightAt (X := Y) (f x) ≤ localWeightAt (X := X) x := by
  rcases exists_neighborhoodBasisAt_cardinal_le_of_localWeightAt_le
      (X := X) (x := x) (κ := localWeightAt (X := X) x) le_rfl with
    ⟨B, hBbasis, hBcard⟩
  let ι : Type u := { U : Set X // U ∈ B }
  let C : Set (Set Y) := Set.range fun i : ι => f '' i.1
  have hCbasis : IsNeighborhoodBasisAt (X := Y) (f x) C := by
    constructor
    · intro V hV
      rcases hV with ⟨i, rfl⟩
      constructor
      · exact hfopen _ ((hBbasis.1 i.1 i.2).1)
      · exact ⟨x, (hBbasis.1 i.1 i.2).2, rfl⟩
    · intro V hVopen hfxV
      have hpreOpen : IsOpen (f ⁻¹' V) := hVopen.preimage hfcont
      have hxpre : x ∈ f ⁻¹' V := hfxV
      rcases hBbasis.2 (f ⁻¹' V) hpreOpen hxpre with ⟨U, hUB, hUsub⟩
      refine ⟨f '' U, ?_, ?_⟩
      · exact ⟨⟨U, hUB⟩, rfl⟩
      · rintro y ⟨z, hzU, rfl⟩
        exact hUsub hzU
  have hCcard : familyCardinal (X := Y) C ≤ localWeightAt (X := X) x := by
    calc
      familyCardinal (X := Y) C ≤ Cardinal.mk ι := by
        unfold familyCardinal C
        exact Cardinal.mk_range_le
      _ = familyCardinal (X := X) B := by rfl
      _ ≤ localWeightAt (X := X) x := hBcard
  exact (localWeightAt_le_familyCardinal_of_basis (X := Y) (x := f x) hCbasis).trans hCcard

/--
In a profinite group, the identity admits a neighborhood basis of open normal subgroups whose
indexing cardinality is bounded by \(w_0(G)\).
-/
theorem exists_openNormalNeighborhoodBasisAtOne_cardinal_le_localWeight
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    ∃ ι : Type u, ∃ W : ι → OpenNormalSubgroup G,
      IsNeighborhoodBasisAt (X := G) (1 : G)
        (Set.range fun i : ι => (((W i : Subgroup G) : Set G))) ∧
      Cardinal.mk ι ≤ localWeight G := by
  rcases exists_neighborhoodBasisAt_cardinal_le_of_localWeightAt_le
      (X := G) (x := (1 : G)) (κ := localWeight G) le_rfl with
    ⟨B, hBbasis, hBcard⟩
  let ι : Type u := { U : Set G // U ∈ B }
  have hchoose :
      ∀ i : ι, ∃ N : OpenNormalSubgroup G, (N : Set G) ⊆ i.1 := by
    intro i
    have hi : IsOpen i.1 ∧ (1 : G) ∈ i.1 := hBbasis.1 i.1 i.2
    rcases exists_openNormalSubgroup_sub_open_nhds_of_one (G := G) hi.1 hi.2 with
      ⟨N, hN⟩
    exact ⟨N, hN⟩
  choose W hW using hchoose
  refine ⟨ι, W, ?_, ?_⟩
  · constructor
    · intro U hU
      rcases hU with ⟨i, rfl⟩
      exact ⟨openNormalSubgroup_isOpen (G := G) (W i), (W i).one_mem'⟩
    · intro V hVopen h1V
      rcases hBbasis.2 V hVopen h1V with ⟨U, hUB, hUV⟩
      refine ⟨((W ⟨U, hUB⟩ : Subgroup G) : Set G), ?_, ?_⟩
      · exact ⟨⟨U, hUB⟩, rfl⟩
      · exact (hW ⟨U, hUB⟩).trans hUV
  · simpa [familyCardinal, ι] using hBcard

/--
In a pro-\(C\) group, the identity admits a neighborhood basis of open normal subgroups whose
quotients lie in \(C\), still indexed by at most \(w_0(G)\).
-/
theorem exists_openNormalNeighborhoodBasisAtOne_inClass_cardinal_le_localWeight
    (C : FiniteGroupClass.{u}) (G : Type u)
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : HasOpenNormalBasisInClass C G) :
    ∃ ι : Type u, ∃ W : ι → OpenNormalSubgroup G,
      (∀ i, C (G ⧸ (W i : Subgroup G))) ∧
      IsNeighborhoodBasisAt (X := G) (1 : G)
        (Set.range fun i : ι => (((W i : Subgroup G) : Set G))) ∧
      Cardinal.mk ι ≤ localWeight G := by
  rcases exists_openNormalNeighborhoodBasisAtOne_cardinal_le_localWeight (G := G) with
    ⟨ι, W, hWbasis, hWcard⟩
  have hchoose :
      ∀ i : ι, ∃ U : OpenNormalSubgroup G,
        C (G ⧸ (U : Subgroup G)) ∧ (((U : Subgroup G) : Set G)) ⊆ ((W i : Subgroup G) : Set G) := by
    intro i
    rcases hG.exists_openNormalSubgroupInClass_sub_open_nhds_of_one
        (openNormalSubgroup_isOpen (G := G) (W i)) (W i).one_mem' with ⟨U, hUW⟩
    exact ⟨U.1, U.2, hUW⟩
  choose U hUC hUsub using hchoose
  refine ⟨ι, U, hUC, ?_, hWcard⟩
  constructor
  · intro V hV
    rcases hV with ⟨i, rfl⟩
    exact ⟨openNormalSubgroup_isOpen (G := G) (U i), (U i).one_mem'⟩
  · intro V hVopen hVone
    rcases hWbasis.2 V hVopen hVone with ⟨W', hW'range, hW'sub⟩
    rcases hW'range with ⟨i, rfl⟩
    refine ⟨((U i : Subgroup G) : Set G), ?_, (hUsub i).trans hW'sub⟩
    exact ⟨i, rfl⟩

/-- A neighborhood basis at \(1\) consisting of open normal subgroups has trivial intersection. -/
theorem iInf_eq_bot_of_openNormalNeighborhoodBasisAtOne
    (G : Type u) [Group G] [TopologicalSpace G] [T2Space G]
    {ι : Type v} (W : ι → OpenNormalSubgroup G)
    (hWbasis : IsNeighborhoodBasisAt (X := G) (1 : G)
      (Set.range fun i : ι => (((W i : Subgroup G) : Set G)))) :
    iInf (fun i => (W i : Subgroup G)) = (⊥ : Subgroup G) := by
  ext x
  constructor
  · intro hx
    by_cases hx1 : x = 1
    · simp only [hx1, one_mem]
    · have hxall : ∀ i : ι, x ∈ (W i : Subgroup G) := by
        rw [Subgroup.mem_iInf] at hx
        exact hx
      have hOpen : IsOpen ({x}ᶜ : Set G) := isClosed_singleton.isOpen_compl
      have hOne : (1 : G) ∈ ({x}ᶜ : Set G) := by
        simpa [Set.mem_compl_iff, eq_comm] using hx1
      rcases hWbasis.2 ({x}ᶜ : Set G) hOpen hOne with ⟨U, hUrange, hUsub⟩
      rcases hUrange with ⟨i, rfl⟩
      have : x ∈ ({x}ᶜ : Set G) := hUsub (hxall i)
      simp only [mem_compl_iff, mem_singleton_iff, not_true_eq_false] at this
  · intro hx
    have hx1 : x = 1 := by
      exact Subgroup.mem_bot.mp hx
    simp only [hx1, one_mem]

/--
A closed topological generating subset of an infinite profinite group has clopen cardinal at
least the local weight.
-/
theorem localWeight_le_rho_of_closedGeneratingSet
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (X : Set G) (hXclosed : IsClosed X)
    (hXgen : TopologicallyGenerates (G := G) X) (hXinfinite : Set.Infinite X) :
    localWeight G ≤ rho ↥X := by
  classical
  let : CompactSpace ↥X := by
    simpa using hXclosed.isClosedEmbedding_subtypeVal.compactSpace
  let : Infinite ↥X := hXinfinite.to_subtype
  rcases exists_openNormalNeighborhoodBasisAtOne_cardinal_le_localWeight (G := G) with
    ⟨ι, W, hWbasis, _hWcard⟩
  let B : Set (Set G) := Set.range fun i : ι => (((W i : Subgroup G) : Set G))
  have hBbasis : IsNeighborhoodBasisAt (X := G) (1 : G) B := by
    simpa [B] using hWbasis
  have hRhoAleph : ℵ₀ ≤ rho ↥X := by
    have hBasis : IsTopologicalBasis { U : Set ↥X | IsClopen U } :=
      InverseSystems.isTopologicalBasis_isClopen_of_compact_t2_totallyDisconnected (X := ↥X)
    have hInfClopen :
        Infinite { U : Set ↥X // U ∈ ({ U : Set ↥X | IsClopen U } : Set (Set ↥X)) } :=
      infinite_familySubtype_of_basis (X := ↥X)
        (B := ({ U : Set ↥X | IsClopen U } : Set (Set ↥X))) hBasis
    let : Infinite { U : Set ↥X // IsClopen U } := by
      change Infinite { U : Set ↥X // U ∈ ({ U : Set ↥X | IsClopen U } : Set (Set ↥X)) }
      exact hInfClopen
    unfold rho familyCardinal
    exact Cardinal.aleph0_le_mk { U : Set ↥X // IsClopen U }
  have hBcard : familyCardinal (X := G) B ≤ rho ↥X := by
    let rep : { V : Set G // V ∈ B } → ι :=
      fun V => Classical.choose V.2
    have hrep : ∀ V : { V : Set G // V ∈ B }, (((W (rep V) : Subgroup G) : Set G)) = V.1 := by
      intro V
      exact Classical.choose_spec V.2
    let homCode : { V : Set G // V ∈ B } → Σ n : ℕ, ContinuousMonoidHom G (Equiv.Perm (Fin n)) :=
      fun V => by
        let U : OpenNormalSubgroup G := W (rep V)
        let n : ℕ := Nat.card (G ⧸ (U : Subgroup G))
        let φ : ContinuousMonoidHom G (Equiv.Perm (Fin n)) :=
          openSubgroupIndexContinuousHom (G := G) (U : Subgroup G)
            (openNormalSubgroup_isOpen (G := G) U)
            (show Nat.card (G ⧸ (U : Subgroup G)) = n from by simp only [n])
        exact ⟨n, φ⟩
    have hhomCode_inj : Function.Injective homCode := by
      intro V₁ V₂ hEq
      let U₁ : OpenNormalSubgroup G := W (rep V₁)
      let U₂ : OpenNormalSubgroup G := W (rep V₂)
      let n₁ : ℕ := Nat.card (G ⧸ (U₁ : Subgroup G))
      let n₂ : ℕ := Nat.card (G ⧸ (U₂ : Subgroup G))
      have hn₁ : Nat.card (G ⧸ (U₁ : Subgroup G)) = n₁ := by simp only [n₁]
      have hn₂ : Nat.card (G ⧸ (U₂ : Subgroup G)) = n₂ := by simp only [n₂]
      let φ₁ : ContinuousMonoidHom G (Equiv.Perm (Fin n₁)) :=
        openSubgroupIndexContinuousHom (G := G) (U₁ : Subgroup G)
          (openNormalSubgroup_isOpen (G := G) U₁) hn₁
      let φ₂ : ContinuousMonoidHom G (Equiv.Perm (Fin n₂)) :=
        openSubgroupIndexContinuousHom (G := G) (U₂ : Subgroup G)
          (openNormalSubgroup_isOpen (G := G) U₂) hn₂
      have hEq' :
          (Sigma.mk n₁ φ₁ : Σ n : ℕ, ContinuousMonoidHom G (Equiv.Perm (Fin n))) =
            (Sigma.mk n₂ φ₂ : Σ n : ℕ, ContinuousMonoidHom G (Equiv.Perm (Fin n))) := by
        simpa [homCode, U₁, U₂, n₁, n₂, φ₁, φ₂] using hEq
      have hker₁ : (φ₁.ker : Subgroup G) = (U₁ : Subgroup G) := by
        have hU₁finite : Finite (G ⧸ (U₁ : Subgroup G)) :=
          Subgroup.quotient_finite_of_isOpen (U₁ : Subgroup G)
            (openNormalSubgroup_isOpen (G := G) U₁)
        let e := openSubgroupIndexEquiv (G := G) (U₁ : Subgroup G)
          hU₁finite hn₁
        have hkerAction :
            (φ₁.ker : Subgroup G) =
              (MulAction.toPermHom G (G ⧸ (U₁ : Subgroup G))).ker := by
          ext g
          change e.permCongr (MulAction.toPerm g) = 1 ↔ MulAction.toPerm g = 1
          have hperm_one :
              e.permCongr (1 : Equiv.Perm (G ⧸ (U₁ : Subgroup G))) =
                (1 : Equiv.Perm (Fin n₁)) := by
            ext x
            simp only [Equiv.permCongr_apply, Equiv.Perm.coe_one, id_eq, Equiv.apply_symm_apply]
          rw [← hperm_one]
          exact e.permCongr.injective.eq_iff
        calc
          (φ₁.ker : Subgroup G) = (MulAction.toPermHom G (G ⧸ (U₁ : Subgroup G))).ker :=
            hkerAction
          _ = (U₁ : Subgroup G).normalCore := by
            symm
            exact Subgroup.normalCore_eq_ker (H := (U₁ : Subgroup G))
          _ = (U₁ : Subgroup G) := Subgroup.normalCore_eq_self (U₁ : Subgroup G)
      have hker₂ : (φ₂.ker : Subgroup G) = (U₂ : Subgroup G) := by
        have hU₂finite : Finite (G ⧸ (U₂ : Subgroup G)) :=
          Subgroup.quotient_finite_of_isOpen (U₂ : Subgroup G)
            (openNormalSubgroup_isOpen (G := G) U₂)
        let e := openSubgroupIndexEquiv (G := G) (U₂ : Subgroup G)
          hU₂finite hn₂
        have hkerAction :
            (φ₂.ker : Subgroup G) =
              (MulAction.toPermHom G (G ⧸ (U₂ : Subgroup G))).ker := by
          ext g
          change e.permCongr (MulAction.toPerm g) = 1 ↔ MulAction.toPerm g = 1
          have hperm_one :
              e.permCongr (1 : Equiv.Perm (G ⧸ (U₂ : Subgroup G))) =
                (1 : Equiv.Perm (Fin n₂)) := by
            ext x
            simp only [Equiv.permCongr_apply, Equiv.Perm.coe_one, id_eq, Equiv.apply_symm_apply]
          rw [← hperm_one]
          exact e.permCongr.injective.eq_iff
        calc
          (φ₂.ker : Subgroup G) = (MulAction.toPermHom G (G ⧸ (U₂ : Subgroup G))).ker :=
            hkerAction
          _ = (U₂ : Subgroup G).normalCore := by
            symm
            exact Subgroup.normalCore_eq_ker (H := (U₂ : Subgroup G))
          _ = (U₂ : Subgroup G) := Subgroup.normalCore_eq_self (U₂ : Subgroup G)
      have hkerEq : (φ₁.ker : Subgroup G) = (φ₂.ker : Subgroup G) := by
        exact congrArg (fun p : Σ n : ℕ, ContinuousMonoidHom G (Equiv.Perm (Fin n)) =>
          (p.2.ker : Subgroup G)) hEq'
      have hsub :
          (U₁ : Subgroup G) = (U₂ : Subgroup G) := by
        calc
          (U₁ : Subgroup G) = (φ₁.ker : Subgroup G) := hker₁.symm
          _ = (φ₂.ker : Subgroup G) := hkerEq
          _ = (U₂ : Subgroup G) := hker₂
      apply Subtype.ext
      calc
        V₁.1 = (((U₁ : Subgroup G) : Set G)) := (hrep V₁).symm
        _ = (((U₂ : Subgroup G) : Set G)) := by simp only [hsub, OpenSubgroup.coe_toSubgroup]
        _ = V₂.1 := hrep V₂
    have hhom_le :
        Cardinal.mk (Σ n : ℕ, ContinuousMonoidHom G (Equiv.Perm (Fin n))) ≤
          Cardinal.mk (Σ n : ℕ, C(↥X, Equiv.Perm (Fin n))) := by
      refine Cardinal.mk_le_of_injective
        (f := fun p => ⟨p.1, {
          toFun := fun x => p.2 x.1
          continuous_toFun := p.2.continuous_toFun.comp continuous_subtype_val }⟩) ?_
      intro a b h
      cases a with
      | mk n φ =>
          cases b with
          | mk m ψ =>
              have hnm : n = m := (Sigma.mk.inj_iff.mp h).1
              subst m
              have hrest :
                  ({ toFun := fun x : X => φ x.1
                     continuous_toFun := φ.continuous_toFun.comp continuous_subtype_val } :
                    C(↥X, Equiv.Perm (Fin n))) =
                  { toFun := fun x : X => ψ x.1
                    continuous_toFun := ψ.continuous_toFun.comp continuous_subtype_val } := by
                exact eq_of_heq (Sigma.mk.inj_iff.mp h).2
              have hEqOn : Set.EqOn φ ψ X := by
                intro x hx
                have := congrArg (fun f : C(↥X, Equiv.Perm (Fin n)) => f ⟨x, hx⟩) hrest
                exact this
              have hφ : φ = ψ :=
                continuousMonoidHom_eq_of_eqOn_topologicalGeneratingSet
                  (G := G) hXgen hEqOn
              subst hφ
              rfl
    have hsigma_le :
        Cardinal.mk (Σ n : ℕ, C(↥X, Equiv.Perm (Fin n))) ≤ rho ↥X := by
      let ρ : Cardinal := rho ↥X
      let f : ℕ → Cardinal := fun n => Cardinal.mk (C(↥X, Equiv.Perm (Fin n)))
      have hf_le : ∀ n, f n ≤ ρ := by
        intro n
        simpa [f, ρ] using
          (cardinal_continuousMap_to_finite_le_rho (X := ↥X) (H := Equiv.Perm (Fin n)))
      calc
        Cardinal.mk (Σ n : ℕ, C(↥X, Equiv.Perm (Fin n))) = Cardinal.sum f := by
          exact Cardinal.mk_sigma (fun n : ℕ => C(↥X, Equiv.Perm (Fin n)))
        _ ≤ Cardinal.sum (fun _ : ℕ => ρ) := by
          apply Cardinal.sum_le_sum
          intro n
          exact hf_le n
        _ = Cardinal.lift.{u} ℵ₀ * ρ := by
          convert (Cardinal.sum_const.{0, u} ℕ ρ) using 1
          simp only [Cardinal.lift_id, Cardinal.mk_eq_aleph0, Cardinal.lift_aleph0,
              Cardinal.lift_uzero, ρ]
        _ = ρ := by
          rw [Cardinal.lift_id, mul_comm]
          simpa [ρ] using Cardinal.mul_aleph0_eq hRhoAleph
        _ = rho ↥X := by rfl
    unfold familyCardinal
    exact ((Cardinal.mk_le_of_injective (f := homCode) hhomCode_inj).trans hhom_le).trans hsigma_le
  simpa [localWeight, B] using
    (localWeightAt_le_familyCardinal_of_basis (X := G) (x := (1 : G)) hBbasis).trans hBcard

/-- An infinite profinite group has local weight at least \(\aleph_0\). -/
theorem aleph0_le_localWeight_of_infinite_profiniteGroup
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Infinite G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    ℵ₀ ≤ localWeight G := by
  by_contra h
  have hlt : localWeight G < ℵ₀ := lt_of_not_ge h
  rcases exists_openNormalNeighborhoodBasisAtOne_cardinal_le_localWeight
      (G := G) with ⟨ι, W, hWbasis, hWcard⟩
  have hιfinite : Finite ι := by
    exact Cardinal.lt_aleph0_iff_finite.mp (lt_of_le_of_lt hWcard hlt)
  let U : Set G := ⋂ i : ι, (((W i : Subgroup G) : Set G))
  have hUopen : IsOpen U := by
    refine isOpen_iInter_of_finite ?_
    intro i
    exact openNormalSubgroup_isOpen (G := G) (W i)
  have h1U : (1 : G) ∈ U := by
    refine Set.mem_iInter.2 ?_
    intro i
    exact (W i).one_mem'
  have hUsubset : U ⊆ ({1} : Set G) := by
    intro x hx
    by_cases hx1 : x = 1
    · simp only [hx1, mem_singleton_iff]
    · have hVopen : IsOpen ({x}ᶜ : Set G) := by
        exact (isClosed_singleton : IsClosed ({x} : Set G)).isOpen_compl
      have h1V : (1 : G) ∈ ({x}ᶜ : Set G) := by
        simpa [eq_comm] using hx1
      rcases hWbasis.2 ({x}ᶜ : Set G) hVopen h1V with ⟨V, hVrange, hVsub⟩
      rcases hVrange with ⟨i, rfl⟩
      have hxi : x ∈ (((W i : Subgroup G) : Set G)) := by
        exact Set.mem_iInter.mp hx i
      have : x ∈ ({x}ᶜ : Set G) := hVsub hxi
      simp only [mem_compl_iff, mem_singleton_iff, not_true_eq_false] at this
  have hsingleton_subset : ({1} : Set G) ⊆ U := by
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact h1U
  have hUeq : U = ({1} : Set G) := Subset.antisymm hUsubset hsingleton_subset
  have hOneOpen : IsOpen ({1} : Set G) := by
    simpa [hUeq] using hUopen
  let : DiscreteTopology G := discreteTopology_of_isOpen_singleton_one hOneOpen
  have hfinite : Finite G := finite_of_compact_of_discrete
  exact not_finite G



/-- 6.1(b). Local weight equals weight for an infinite profinite group. -/
theorem localWeight_eq_weight_of_infinite_profiniteGroup
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Infinite G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    localWeight G = weight G := by
  classical
  have hAleph : ℵ₀ ≤ localWeight G :=
    aleph0_le_localWeight_of_infinite_profiniteGroup (G := G)
  rcases exists_openNormalNeighborhoodBasisAtOne_cardinal_le_localWeight
      (G := G) with ⟨ι, W, hWbasis, hWcard⟩
  let B : Set (Set G) := Set.range fun i : ι => (((W i : Subgroup G) : Set G))
  have hBbasis : IsNeighborhoodBasisAt (X := G) (1 : G) B := by
    simpa [B] using hWbasis
  have hweight_le :
      weight G ≤ familyCardinal (X := G) (leftTranslateFamily (G := G) B) :=
    weight_le_familyCardinal_leftTranslateFamily_of_neighborhoodBasis
      (G := G) hBbasis
  let decode :
      (Σ i : ι, G ⧸ (W i : Subgroup G)) →
        { V : Set G // V ∈ leftTranslateFamily (G := G) B } := fun p =>
      ⟨Quotient.out p.2 • (((W p.1 : Subgroup G) : Set G)), by
        exact ⟨Quotient.out p.2, (((W p.1 : Subgroup G) : Set G)), ⟨p.1, rfl⟩, rfl⟩⟩
  have hdecode_surj : Function.Surjective decode := by
    intro V
    rcases V with ⟨V, hV⟩
    rcases hV with ⟨g, U, hU, hVeq⟩
    rcases hU with ⟨i, hi⟩
    refine ⟨⟨i, (QuotientGroup.mk' (W i : Subgroup G)) g⟩, ?_⟩
    apply Subtype.ext
    have hquot :
        (QuotientGroup.mk' (W i : Subgroup G))
            (Quotient.out ((QuotientGroup.mk' (W i : Subgroup G)) g)) =
          (QuotientGroup.mk' (W i : Subgroup G)) g := by
      exact Quotient.out_eq' ((QuotientGroup.mk' (W i : Subgroup G)) g)
    have hmem :
        (Quotient.out ((QuotientGroup.mk' (W i : Subgroup G)) g))⁻¹ * g ∈ (W i : Subgroup G) :=
      (QuotientGroup.eq).1 hquot
    calc
      ↑(decode ⟨i, (QuotientGroup.mk' (W i : Subgroup G)) g⟩) =
          Quotient.out ((QuotientGroup.mk' (W i : Subgroup G)) g) •
            (((W i : Subgroup G) : Set G)) := by
        rfl
      _ = g • (((W i : Subgroup G) : Set G)) := by
        simpa using (leftCoset_eq_iff (s := (W i : Subgroup G))).2 hmem
      _ = g • U := by
        simp only [hi]
      _ = V := hVeq.symm
  have htranslate_card :
      familyCardinal (X := G) (leftTranslateFamily (G := G) B) ≤ localWeight G := by
    unfold familyCardinal
    calc
      Cardinal.mk { V : Set G // V ∈ leftTranslateFamily (G := G) B } ≤
          Cardinal.mk (Σ i : ι, G ⧸ (W i : Subgroup G)) :=
        Cardinal.mk_le_of_surjective (f := decode) hdecode_surj
      _ = Cardinal.sum (fun i : ι => Cardinal.mk (G ⧸ (W i : Subgroup G))) := by
        exact Cardinal.mk_sigma (fun i : ι => G ⧸ (W i : Subgroup G))
      _ ≤ Cardinal.sum (fun _ : ι => ℵ₀) := by
        refine Cardinal.sum_le_sum _ _ ?_
        intro i
        let : Finite (G ⧸ (W i : Subgroup G)) :=
          openNormalSubgroup_finiteQuotient (G := G) (W i)
        exact Cardinal.mk_le_aleph0_iff.mpr inferInstance
      _ = Cardinal.mk ι * ℵ₀ := by
        exact Cardinal.sum_const' ι ℵ₀
      _ ≤ localWeight G * localWeight G := by
        exact mul_le_mul' hWcard hAleph
      _ = localWeight G := Cardinal.mul_eq_self hAleph
  exact le_antisymm (localWeight_le_weight (G := G)) (hweight_le.trans htranslate_card)




/--
For an infinite profinite space, the weight agrees with the clopen cardinal invariant, and every
clopen basis has the same cardinality.
-/
theorem weight_eq_rho_and_familyCardinal_eq_rho_of_profiniteSpace
    (X : Type u) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] [Infinite X] :
    weight X = rho X ∧
      ∀ B : Set (Set X), IsTopologicalBasis B → (∀ U ∈ B, IsClopen U) →
        familyCardinal (X := X) B = rho X := by
  have hBasis : TopologicalSpace.IsTopologicalBasis { U : Set X | IsClopen U } :=
    InverseSystems.isTopologicalBasis_isClopen_of_compact_t2_totallyDisconnected
  refine ⟨weight_eq_rho_of_clopenBasis (X := X) hBasis, ?_⟩
  intro B hB hBclopen
  exact familyCardinal_eq_rho_of_clopenBasis (X := X) hB hBclopen

/--
For an infinite profinite group, local weight, weight, and the clopen cardinal invariant all
coincide.
-/
theorem localWeight_eq_weight_and_weight_eq_rho_of_infinite_profiniteGroup
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Infinite G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    localWeight G = weight G ∧ weight G = rho G := by
  have hBasis : TopologicalSpace.IsTopologicalBasis { U : Set G | IsClopen U } :=
    InverseSystems.isTopologicalBasis_isClopen_of_compact_t2_totallyDisconnected
  refine ⟨localWeight_eq_weight_of_infinite_profiniteGroup (G := G), ?_⟩
  exact weight_eq_rho_of_clopenBasis (X := G) hBasis



end ProCGroups.LocalWeight
