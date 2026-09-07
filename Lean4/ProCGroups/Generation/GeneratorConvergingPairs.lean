import ProCGroups.Generation.QuotientCriteria
import ProCGroups.ProC.Quotients.LeftQuotientProjectionSections

set_option autoImplicit false

/-!
# Partial converging generators modulo a closed normal subgroup

`GeneratorConvergingPair` packages representatives that converge modulo a closed normal subgroup
and generate together with that subgroup.  The refinement preorder is developed far enough to
construct upper bounds for chains and to extract finite generating data after passage to an open
normal quotient.
-/

open Set
open scoped Topology Pointwise

namespace ProCGroups.Generation

universe u v

open ProCGroups.InverseSystems
open ProCGroups.ProC

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]


/-- A partial generating set together with a closed normal subgroup modulo which it converges. -/
structure GeneratorConvergingPair where
  /-- The subgroup that is retained alongside the chosen generators. -/
  N : Subgroup G
  /-- The retained subgroup is normal, so convergence may be interpreted in the quotient. -/
  normal_N : N.Normal
  /-- The retained subgroup is closed in `G`. -/
  closed_N : IsClosed (N : Set G)
  /-- The selected representatives outside the retained subgroup. -/
  X : Set G
  /-- No selected representative lies in `N`. -/
  subset_compl : X ⊆ (N : Set G)ᶜ
  /--
  For every open subgroup containing `N`, only finitely many selected representatives lie
  outside that open subgroup; equivalently, their images converge to one modulo `N`.
  -/
  convergesToOneAlongOpenSubgroups_mod :
    ∀ U : OpenSubgroup G, N ≤ (U : Subgroup G) → (X \ (U : Set G)).Finite
  /-- The union of the selected representatives and `N` topologically generates `G`. -/
  generates : TopologicallyGenerates (G := G) (X ∪ (N : Set G))

/-- The order relation is the refinement relation on the corresponding data. -/
instance instLEGeneratorConvergingPair : LE (GeneratorConvergingPair (G := G)) where
  le A B := B.N ≤ A.N ∧ A.X ⊆ B.X ∧ B.X \ A.X ⊆ (A.N : Set G)

/-- The preorder is induced by refinement of the corresponding data. -/
instance instPreorderGeneratorConvergingPair : Preorder (GeneratorConvergingPair (G := G)) where
  le_refl A := ⟨le_rfl, subset_rfl, by simp only [sdiff_self, empty_subset]⟩
  le_trans A B C hAB hBC := by
    rcases hAB with ⟨hABN, hABX, hABdiff⟩
    rcases hBC with ⟨hBCN, hBCX, hBCdiff⟩
    refine ⟨hBCN.trans hABN, hABX.trans hBCX, ?_⟩
    intro x hx
    rcases hx with ⟨hxC, hxA⟩
    by_cases hxB : x ∈ B.X
    · exact hABdiff ⟨hxB, hxA⟩
    · exact hABN (hBCdiff ⟨hxC, hxB⟩)

/-- The initial generator-converging pair. -/
noncomputable def initialGeneratorConvergingPair : GeneratorConvergingPair (G := G) where
  N := ⊤
  normal_N := by infer_instance
  closed_N := isClosed_univ
  X := ∅
  subset_compl := by intro x hx; simp only [mem_empty_iff_false] at hx
  convergesToOneAlongOpenSubgroups_mod := by
    intro U hU
    simp only [empty_sdiff, finite_empty]
  generates := by
    simpa [TopologicallyGenerates, Set.empty_union, Subgroup.closure_eq] using
      (top_unique (Subgroup.le_topologicalClosure (⊤ : Subgroup G)) :
        (⊤ : Subgroup G).topologicalClosure = ⊤)

/-- A finite subset of a chain has an upper element from that subset. -/
theorem finite_subset_chain_has_upper {α : Type*} [Preorder α] {c : Set α}
    (hc : IsChain (· ≤ ·) c) :
    ∀ s : Finset α, ↑s ⊆ c → s.Nonempty → ∃ m ∈ s, ∀ z ∈ s, z ≤ m := by
  classical
  intro s
  refine Finset.induction_on s ?_ ?_
  · intro hs hne
    exact False.elim (hne.ne_empty rfl)
  · intro a s ha ih hs hne
    by_cases hsne : s.Nonempty
    · rcases ih
        (by
          intro z hz
          exact hs (by simp only [Finset.coe_insert, mem_insert_iff, hz, or_true]))
        hsne with ⟨m, hm, hmax⟩
      have ha' : a ∈ c := hs (by simp only [Finset.coe_insert, mem_insert_iff, SetLike.mem_coe,
          true_or])
      have hm' : m ∈ c := hs (by simp only [Finset.coe_insert, mem_insert_iff, SetLike.mem_coe,
          hm, or_true])
      have hcmp : a ≤ m ∨ m ≤ a := by
        by_cases hEq : a = m
        · exact Or.inl (hEq ▸ le_rfl)
        · exact hc ha' hm' hEq
      cases hcmp with
      | inl ham =>
          refine ⟨m, by simp only [Finset.mem_insert, hm, or_true], ?_⟩
          intro z hz
          rcases Finset.mem_insert.mp hz with rfl | hz'
          · exact ham
          · exact hmax z hz'
      | inr hma =>
          refine ⟨a, by simp only [Finset.mem_insert, true_or], ?_⟩
          intro z hz
          rcases Finset.mem_insert.mp hz with rfl | hz'
          · exact le_rfl
          · exact (hmax z hz').trans hma
    · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hsne
      refine ⟨a, by simp only [hs0, insert_empty_eq, Finset.mem_singleton], ?_⟩
      intro z hz
      have hz' : z = a := by simpa [hs0] using hz
      subst z
      exact le_rfl

omit [T2Space G] [TotallyDisconnectedSpace G] in
/--
If the infimum of the closed normal subgroups in a chain lies in an open subgroup, then one
stage already lies in that open subgroup.
-/
theorem exists_pair_le_openSubgroup_of_chain_iInf_le
    {c : Set (GeneratorConvergingPair (G := G))}
    (hc : IsChain (· ≤ ·) c) (hcne : c.Nonempty)
    (U : OpenSubgroup G)
    (hInf : iInf (fun p : c => p.1.N) ≤ (U : Subgroup G)) :
    ∃ p : c, p.1.N ≤ (U : Subgroup G) := by
  classical
  have hInter :
      (⋂ p : c, (((p.1.N : Subgroup G) : Set G))) ⊆ ((U : Subgroup G) : Set G) := by
    intro x hx
    exact hInf (by simpa [Subgroup.mem_iInf] using hx)
  rcases finite_iInter_subgroup_subset_openSubgroup (G := G)
      (H := fun p : c => p.1.N)
      (hclosed := fun p => p.1.closed_N)
      U hInter with ⟨s, hs⟩
  by_cases hsne : s.Nonempty
  · have hc' : IsChain (· ≤ ·) (Set.univ : Set c) := by
      intro a ha b hb hne
      have hne' : (a : GeneratorConvergingPair (G := G)) ≠ b := by
        intro h
        exact hne (Subtype.ext h)
      simpa using hc a.2 b.2 hne'
    rcases finite_subset_chain_has_upper hc' s (by intro z hz; simp only [mem_univ]) hsne with
        ⟨m, hm, hmax⟩
    refine ⟨m, ?_⟩
    intro x hx
    have hx' :
        x ∈ ⋂ p ∈ s, (((p.1.N : Subgroup G) : Set G)) := by
      refine mem_iInter₂.2 ?_
      intro p hp
      exact (hmax p hp).1 hx
    exact hs hx'
  · rcases hcne with ⟨p, hp⟩
    refine ⟨⟨p, hp⟩, ?_⟩
    have htop : ((⊤ : Subgroup G) : Set G) ⊆ ((U : Subgroup G) : Set G) := by
      have : (⋂ p ∈ s, (((p.1.N : Subgroup G) : Set G))) ⊆ ((U : Subgroup G) : Set G) := hs
      simpa [Finset.not_nonempty_iff_eq_empty.mp hsne] using this
    intro x hx
    exact htop (by simp only [Subgroup.coe_top, mem_univ])

/-- Upper bound of a nonempty chain of generator-converging pairs. -/
noncomputable def chainUpperBoundOfNonempty
    {c : Set (GeneratorConvergingPair (G := G))}
    (hc : IsChain (· ≤ ·) c) (hcne : c.Nonempty) :
    GeneratorConvergingPair (G := G) where
  N := iInf fun p : c => p.1.N
  normal_N := by
    classical
    exact Subgroup.normal_iInf_normal fun p : c => p.1.normal_N
  closed_N := by
    classical
    simpa using isClosed_iInter (fun p : c => p.1.closed_N)
  X := ⋃ p : c, p.1.X
  subset_compl := by
    intro x hx
    rcases mem_iUnion.mp hx with ⟨p, hpx⟩
    refine by
      intro hxK
      exact p.1.subset_compl hpx ((iInf_le (fun q : c => q.1.N) p) hxK)
  convergesToOneAlongOpenSubgroups_mod := by
    intro U hKU
    rcases exists_pair_le_openSubgroup_of_chain_iInf_le (G := G) hc hcne U
      hKU with ⟨p, hpU⟩
    have hEq : ((⋃ q : c, q.1.X) \ (U : Set G)) = (p.1.X \ (U : Set G)) := by
      ext x
      constructor
      · intro hx
        rcases hx with ⟨hxX, hxU⟩
        rcases mem_iUnion.mp hxX with ⟨q, hqx⟩
        have hcmp :
            (q.1 ≤ p.1) ∨ (p.1 ≤ q.1) := by
          by_cases hqp : q = p
          · exact Or.inl (hqp ▸ le_rfl)
          · have hqp' : (q : GeneratorConvergingPair (G := G)) ≠ p := by
              intro h
              exact hqp (Subtype.ext h)
            exact hc q.2 p.2 hqp'
        cases hcmp with
        | inl hqp =>
            exact ⟨hqp.2.1 hqx, hxU⟩
        | inr hpq =>
            by_cases hxp : x ∈ p.1.X
            · exact ⟨hxp, hxU⟩
            · have hxN : x ∈ (p.1.N : Set G) := hpq.2.2 ⟨hqx, hxp⟩
              exact False.elim (hxU (hpU hxN))
      · intro hx
        exact ⟨mem_iUnion.mpr ⟨p, hx.1⟩, hx.2⟩
    rw [hEq]
    exact p.1.convergesToOneAlongOpenSubgroups_mod U hpU
  generates := by
    let K : Subgroup G := iInf fun p : c => p.1.N
    have : K.Normal := Subgroup.normal_iInf_normal fun p : c => p.1.normal_N
    apply (topologicallyGenerates_union_subgroup_iff_forall_openNormalQuotient
      (G := G)
      (N := K) (X := ⋃ p : c, p.1.X)).2
    intro U hKU
    rcases exists_pair_le_openSubgroup_of_chain_iInf_le (G := G) hc hcne U.toOpenSubgroup
      (by simpa [K] using hKU) with ⟨p, hpU⟩
    have hpgen :
        TopologicallyGenerates (G := G ⧸ (U : Subgroup G))
          ((QuotientGroup.mk' (U : Subgroup G)) '' p.1.X) := by
      have : p.1.N.Normal := p.1.normal_N
      exact
        (topologicallyGenerates_union_subgroup_iff_forall_openNormalQuotient
          (G := G)
          (N := p.1.N) (X := p.1.X)).1
          p.1.generates U hpU
    exact topologicallyGenerates_mono hpgen (by
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      exact ⟨x, mem_iUnion.mpr ⟨p, hx⟩, rfl⟩)

omit [T2Space G] in
/-- The generator-converging-pair order is inductive over chains. -/
theorem chain_bounded_generatorConvergingPair
    (c : Set (GeneratorConvergingPair (G := G)))
    (hc : IsChain (· ≤ ·) c) :
    BddAbove c := by
  classical
  rcases c.eq_empty_or_nonempty with rfl | hcne
  · exact ⟨initialGeneratorConvergingPair (G := G), by intro a ha; cases ha⟩
  · refine ⟨chainUpperBoundOfNonempty (G := G) hc hcne, ?_⟩
    intro p hp
    refine ⟨?_, ?_, ?_⟩
    · exact iInf_le (fun q : {q // q ∈ c} => q.1.N) ⟨p, hp⟩
    · intro x hx
      exact mem_iUnion.mpr ⟨⟨p, hp⟩, hx⟩
    · intro x hx
      rcases hx with ⟨hxX, hxpX⟩
      rcases mem_iUnion.mp hxX with ⟨q, hqx⟩
      by_cases hqp : q = ⟨p, hp⟩
      · exact False.elim (hxpX (by simpa [hqp] using hqx))
      · have hqp' : (q : GeneratorConvergingPair (G := G)) ≠ p := by
          intro h
          exact hqp (Subtype.ext h)
        rcases hc q.2 hp hqp' with hqle | hple
        · exact False.elim (hxpX (hqle.2.1 hqx))
        · exact hple.2.2 ⟨hqx, hxpX⟩

omit [T2Space G] [TotallyDisconnectedSpace G] in
/--
An open-normal quotient of a closed normal subgroup has a finite generating set modulo the
intersection with the open normal subgroup.
-/
theorem exists_finite_subset_generating_subgroup_mod_openNormal
    {M : Subgroup G}
    (hMclosed : IsClosed (M : Set G)) (U : OpenNormalSubgroup G) :
    ∃ T : Set G,
      T.Finite ∧
      T ⊆ (M : Set G) \ (((U : Subgroup G) ⊓ M : Subgroup G) : Set G) ∧
      M ≤ Subgroup.closure (T ∪ ((((U : Subgroup G) ⊓ M : Subgroup G) : Subgroup G) : Set G)) := by
  classical
  have : CompactSpace M := hMclosed.isClosedEmbedding_subtypeVal.compactSpace
  let UM : OpenNormalSubgroup M :=
    OpenNormalSubgroup.comap (M.subtype) continuous_subtype_val U
  obtain ⟨σ, -, hσright, -⟩ :=
    quotient_openNormalSubgroup_hasContinuousSection (G := M) UM
  let q1 : M ⧸ (UM : Subgroup M) := ((1 : M) : M ⧸ (UM : Subgroup M))
  let Tsub : Set M := σ '' ({q1} : Set (M ⧸ (UM : Subgroup M)))ᶜ
  let T : Set G := Subtype.val '' Tsub
  refine ⟨T, ?_, ?_, ?_⟩
  · have : Finite (M ⧸ (UM : Subgroup M)) := openNormalSubgroup_finiteQuotient (G := M) UM
    have hfin : ({q1} : Set (M ⧸ (UM : Subgroup M)))ᶜ.Finite := Set.toFinite _
    exact hfin.image σ |>.image Subtype.val
  · intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    rcases hy with ⟨q, hq, rfl⟩
    refine ⟨(σ q).2, ?_⟩
    intro hxUM
    have hσUM : σ q ∈ (UM : Subgroup M) := by
      change (((σ q : M) : G) ∈ (U : Subgroup G))
      exact hxUM.1
    have : q = q1 := by
      calc
        q = QuotientGroup.mk' (UM : Subgroup M) (σ q) := (hσright q).symm
        _ = q1 := by
          have hq1 :
              QuotientGroup.mk' (UM : Subgroup M) (σ q) = (1 : M ⧸ (UM : Subgroup M)) :=
            (QuotientGroup.eq_one_iff (N := (UM : Subgroup M)) (σ q)).2 hσUM
          simpa [q1] using hq1
    exact hq this
  · intro m hmM
    let mM : M := ⟨m, hmM⟩
    let q : M ⧸ (UM : Subgroup M) := QuotientGroup.mk' (UM : Subgroup M) mM
    by_cases hq : q = q1
    · have hmUM : (⟨m, hmM⟩ : M) ∈ (UM : Subgroup M) := by
        have hq1 : QuotientGroup.mk' (UM : Subgroup M) mM = (1 : M ⧸ (UM : Subgroup M)) := by
          simpa [q, q1, mM] using hq
        exact (QuotientGroup.eq_one_iff (N := (UM : Subgroup M)) mM).1 hq1
      have hmN' : m ∈ ((U : Subgroup G) ⊓ M : Subgroup G) := by
        refine ⟨?_, hmM⟩
        have hmU := hmUM
        change m ∈ (U : Subgroup G) at hmU
        exact hmU
      exact Subgroup.subset_closure (Or.inr hmN')
    · have hT : ((σ q : M) : G) ∈ T := by
        exact ⟨σ q, ⟨q, hq, rfl⟩, rfl⟩
      have hEq :
          QuotientGroup.mk' (UM : Subgroup M) (σ q) =
            QuotientGroup.mk' (UM : Subgroup M) mM := by
        simpa [q, mM] using hσright q
      have hdiv : (σ q)⁻¹ * mM ∈ (UM : Subgroup M) := by
        exact (QuotientGroup.eq).1 hEq
      have hdivU : (((σ q : M) : G)⁻¹ * m) ∈ (U : Subgroup G) := by
        have hdiv' := hdiv
        change ((↑(σ q) : G)⁻¹ * m) ∈ (U : Subgroup G) at hdiv'
        exact hdiv'
      have hdivM : (((σ q : M) : G)⁻¹ * m) ∈ M := by
        change ((((σ q)⁻¹ * mM : M) : G) ∈ M)
        exact (((σ q)⁻¹ * mM : M)).2
      have hN' : (((σ q : M) : G)⁻¹ * m) ∈ ((U : Subgroup G) ⊓ M : Subgroup G) := by
        exact ⟨hdivU, hdivM⟩
      have hσ' :
          ((σ q : M) : G) ∈
            Subgroup.closure (T ∪ ((((U : Subgroup G) ⊓ M : Subgroup G) : Subgroup G) : Set G)) :=
        Subgroup.subset_closure (Or.inl hT)
      have hdiv' :
          ((σ q : M) : G)⁻¹ * m ∈
            Subgroup.closure (T ∪ ((((U : Subgroup G) ⊓ M : Subgroup G) : Subgroup G) : Set G)) :=
        Subgroup.subset_closure (Or.inr hN')
      have hmEq : m = ((σ q : M) : G) * (((σ q : M) : G)⁻¹ * m) := by
        simp only [mul_inv_cancel_left]
      rw [hmEq]
      exact (Subgroup.closure _).mul_mem hσ' hdiv'


end ProCGroups.Generation
