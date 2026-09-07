import ProCGroups.ProC.OpenNormalSubgroups.BasisAtOne
import ProCGroups.ProC.Quotients.DescendingClosedSubgroupQuotients

set_option autoImplicit false

/-!
# Continuous sections of left-quotient projections

Using normalized section data ordered by intermediate closed subgroups, this file applies a chain
upper-bound argument to construct continuous sections of \(G/K \to G/H\). It concludes with a
continuous section of the quotient map by any closed subgroup of a profinite group.
-/

open Set
open scoped Topology Pointwise

namespace ProCGroups.ProC

universe u v

open InverseSystems

/--
If an intermediate closed subgroup is not contained in the base subgroup, the set-theoretic
difference contains an element.
-/
theorem exists_mem_of_not_le {G : Type u} [Group G] [TopologicalSpace G] {K L : ClosedSubgroup G}
    (hnotle : ¬ (L : Subgroup G) ≤ (K : Subgroup G)) :
    ∃ x : G, x ∈ (L : Subgroup G) ∧ x ∉ (K : Subgroup G) := by
  by_contra hNo
  apply hnotle
  intro x hxL
  by_cases hxK : x ∈ (K : Set G)
  · exact hxK
  · exact False.elim (hNo ⟨x, hxL, hxK⟩)

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

omit [T2Space G] in
/--
For any nontrivial element of a profinite group, there is an open normal subgroup that does not
contain it.
-/
theorem exists_openNormalSubgroup_not_mem
    {x : G} (hx : x ≠ 1) :
    ∃ U : OpenNormalSubgroup G, x ∉ (U : Subgroup G) := by
  let W : Set G := ({x} : Set G)ᶜ
  have hW : IsOpen W := by
    simp only [isOpen_compl_iff, finite_singleton, Finite.isClosed, W]
  have h1W : (1 : G) ∈ W := by
    simpa [W] using hx.symm
  obtain ⟨U, hUW⟩ :=
    exists_openNormalSubgroup_sub_open_nhds_of_one (G := G) hW h1W
  refine ⟨U, ?_⟩
  intro hxU
  exact hx <| by
    have hxW : x ∈ W := hUW hxU
    simp only [mem_compl_iff, mem_singleton_iff, not_true_eq_false, W] at hxW

omit [T2Space G] in
/--
A point outside a closed subgroup of a profinite group is omitted by some open subgroup
containing that closed subgroup.
-/
theorem exists_openSubgroup_ge_closedSubgroup_not_mem
    (K : ClosedSubgroup G) {x : G} (hx : x ∉ (K : Set G)) :
    ∃ U : OpenSubgroup G, (K : Subgroup G) ≤ (U : Subgroup G) ∧ x ∉ (U : Set G) := by
  have hxInf :
      x ∉ sInf {N : Subgroup G | IsOpen (N : Set G) ∧ (K : Subgroup G) ≤ N} := by
    rw [← closedSubgroup_eq_sInf_open (G := G) K]
    exact hx
  rw [Subgroup.mem_sInf] at hxInf
  push Not at hxInf
  rcases hxInf with ⟨U, hU, hxU⟩
  exact ⟨⟨U, hU.1⟩, hU.2, hxU⟩

/--
An open subgroup of a closed subgroup of a profinite group, viewed again as a closed subgroup of
the ambient group.
-/
noncomputable def closedSubgroupOfOpenSubgroup
    (T : ClosedSubgroup G) (N : OpenSubgroup T) :
    ClosedSubgroup G where
  toSubgroup := (N : Subgroup T).map ((T : Subgroup G).subtype)
  isClosed' := by
    have : IsTopologicalGroup ↥(T : Subgroup G) :=
      Topology.IsInducing.subtypeVal.topologicalGroup (T : Subgroup G).subtype
    have hNclosed : IsClosed ((N : Subgroup T) : Set T) :=
      Subgroup.isClosed_of_isOpen (N : Subgroup T) N.isOpen'
    have hNcompact : IsCompact ((N : Subgroup T) : Set T) := hNclosed.isCompact
    have hEq :
        ((T : Subgroup G).subtype '' ((N : Subgroup T) : Set T)) =
          (((N : Subgroup T).map ((T : Subgroup G).subtype) : Subgroup G) : Set G) := by
      ext x
      constructor <;> rintro ⟨y, hy, rfl⟩ <;> exact ⟨y, hy, rfl⟩
    change IsClosed ((((N : Subgroup T).map ((T : Subgroup G).subtype) : Subgroup G) : Set G))
    rw [← hEq]
    exact hNcompact.image continuous_subtype_val |>.isClosed

omit [TotallyDisconnectedSpace G] in
/--
Membership in the ambient closed subgroup induced by an open subgroup is tested inside the
original subgroup.
-/
@[simp] theorem mem_closedSubgroupOfOpenSubgroup
    {T : ClosedSubgroup G} {N : OpenSubgroup T} {x : T} :
    (x : G) ∈ (closedSubgroupOfOpenSubgroup (G := G) T N : Subgroup G) ↔
      x ∈ (N : Subgroup T) := by
  constructor
  · intro hx
    rcases hx with ⟨y, hy, hyx⟩
    have : y = x := Subtype.ext hyx
    simpa [this] using hy
  · intro hx
    exact ⟨x, hx, rfl⟩

omit [TotallyDisconnectedSpace G] in
/-- The ambient closed subgroup attached to an open subgroup of T still lies inside T. -/
theorem closedSubgroupOfOpenSubgroup_le
    (T : ClosedSubgroup G) (N : OpenSubgroup T) :
    (closedSubgroupOfOpenSubgroup (G := G) T N : Subgroup G) ≤ (T : Subgroup G) := by
  intro x hx
  rcases hx with ⟨y, hy, rfl⟩
  exact y.2

omit [TotallyDisconnectedSpace G] in
/--
The closed subgroup obtained inside an open subgroup agrees with the corresponding subgroup of
the ambient group.
-/
@[simp 900] theorem closedSubgroupOfOpenSubgroup_subgroupOf_eq
    (T : ClosedSubgroup G) (N : OpenSubgroup T) :
    (((closedSubgroupOfOpenSubgroup (G := G) T N : ClosedSubgroup G) : Subgroup G).subgroupOf
      (T : Subgroup G)) = (N : Subgroup T) := by
  ext x
  simp only [Subgroup.mem_subgroupOf, mem_closedSubgroupOfOpenSubgroup, OpenSubgroup.mem_toSubgroup]

/-- The canonical quotient map \(G \to G/\bot\) is a homeomorphism for profinite groups. -/
noncomputable def quotientBotHomeomorph :
    G ≃ₜ G ⧸ (⊥ : Subgroup G) := by
  letI : IsClosed (((⊥ : Subgroup G) : Set G)) := by
    change IsClosed ({(1 : G)} : Set G)
    simp only [finite_singleton, Finite.isClosed]
  exact Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective
      (QuotientGroup.mk (s := (⊥ : Subgroup G)))
      (by
        constructor
        · intro x y hxy
          have hmem : x⁻¹ * y ∈ (⊥ : Subgroup G) := QuotientGroup.eq.1 hxy
          exact inv_mul_eq_one.mp <| by simpa using hmem
        · intro q
          rcases Quotient.exists_rep q with ⟨g, rfl⟩
          exact ⟨g, rfl⟩))
    (by
      change Continuous
        (QuotientGroup.mk (s := (⊥ : Subgroup G)) : G → G ⧸ (⊥ : Subgroup G))
      exact QuotientGroup.continuous_mk)

omit [T2Space G] in
/-- The continuous equivalence is evaluated by the corresponding comparison formula. -/
@[simp 900] theorem quotientBotHomeomorph_apply (g : G) :
    quotientBotHomeomorph (G := G) g = QuotientGroup.mk (s := (⊥ : Subgroup G)) g :=
  rfl

/--
Data of a normalized continuous section of a left quotient projection \(G/L \to G/H\), ordered
so that smaller intermediate subgroups correspond to larger elements. This is the Zorn package
used for the closed-subgroup section theorem.
-/
structure LeftQuotientSectionData (K H : ClosedSubgroup G) where
  /-- The intermediate closed subgroup through which the section is constructed. -/
  L : ClosedSubgroup G
  /-- The lower endpoint \(K\) is contained in the intermediate subgroup \(L\). -/
  hKL : (K : Subgroup G) ≤ (L : Subgroup G)
  /-- The intermediate subgroup \(L\) is contained in the upper endpoint \(H\). -/
  hLH : (L : Subgroup G) ≤ (H : Subgroup G)
  /-- A section from the left quotient by \(H\) to the left quotient by \(L\). -/
  σ : G ⧸ (H : Subgroup G) → G ⧸ (L : Subgroup G)
  /-- The section \(\sigma\) is continuous. -/
  continuous_σ : Continuous σ
  /-- The map \(\sigma\) is a right inverse of the quotient projection from \(G/L\) to \(G/H\). -/
  rightInv : Function.RightInverse σ
    (leftQuotientProjection (L : Subgroup G) (H : Subgroup G) hLH)
  /-- The section sends the identity coset modulo \(H\) to the identity coset modulo \(L\). -/
  one_eq :
    σ (QuotientGroup.mk (s := (H : Subgroup G)) (1 : G)) =
      QuotientGroup.mk (s := (L : Subgroup G)) (1 : G)

namespace LeftQuotientSectionData

variable {K H : ClosedSubgroup G}

/-- The order relation is the refinement relation on the corresponding data. -/
instance instLELeftQuotientSectionData : LE (LeftQuotientSectionData (G := G) K H) where
  le a b :=
    ∃ hba : (b.L : Subgroup G) ≤ (a.L : Subgroup G),
      leftQuotientProjection (b.L : Subgroup G) (a.L : Subgroup G) hba ∘ b.σ = a.σ

/-- The preorder is induced by refinement of the corresponding data. -/
instance instPreorderLeftQuotientSectionData : Preorder (LeftQuotientSectionData (G := G) K H) where
  le_refl a := by
    refine ⟨le_rfl, ?_⟩
    funext x
    simp only [leftQuotientProjection_id, Function.comp_apply, id_eq]
  le_trans a b c hab hbc := by
    rcases hab with ⟨hba, hbaσ⟩
    rcases hbc with ⟨hcb, hcbσ⟩
    refine ⟨hcb.trans hba, ?_⟩
    funext x
    calc
      leftQuotientProjection (c.L : Subgroup G) (a.L : Subgroup G) (hcb.trans hba) (c.σ x)
                = leftQuotientProjection (b.L : Subgroup G) (a.L : Subgroup G) hba
                    (leftQuotientProjection (c.L : Subgroup G) (b.L : Subgroup G) hcb (c.σ x)) := by
                convert
                  (leftQuotientProjection_comp_apply
                    (K := (c.L : Subgroup G)) (H := (b.L : Subgroup G))
                    (L := (a.L : Subgroup G)) hcb hba (c.σ x)).symm
      _ = leftQuotientProjection (b.L : Subgroup G) (a.L : Subgroup G) hba (b.σ x) := by
            exact congrArg (leftQuotientProjection (b.L : Subgroup G) (a.L : Subgroup G) hba)
              (congrFun hcbσ x)
      _ = a.σ x := congrFun hbaσ x

/-- The maximal element of the Zorn poset, given by the identity section over H itself. -/
def top (hKH : (K : Subgroup G) ≤ (H : Subgroup G)) :
    LeftQuotientSectionData (G := G) K H where
  L := H
  hKL := hKH
  hLH := le_rfl
  σ := id
  continuous_σ := continuous_id
  rightInv := by
    intro x
    simp only [id_eq, leftQuotientProjection_id]
  one_eq := rfl

omit [T2Space G] [TotallyDisconnectedSpace G] in
/-- Any nonempty chain of partial sections admits an upper bound over the infimum subgroup. -/
theorem exists_upperBound_of_chain
    (c : Set (LeftQuotientSectionData (G := G) K H))
    (hc : IsChain (· ≤ ·) c) (hcn : c.Nonempty) :
    ∃ ub : LeftQuotientSectionData (G := G) K H, ∀ a ∈ c, a ≤ ub := by
  classical
  let I : Type u := {a : LeftQuotientSectionData (G := G) K H // a ∈ c}
  have hI_nonempty : Nonempty I := by
    rcases hcn with ⟨a, ha⟩
    exact ⟨⟨a, ha⟩⟩
  let L : I → ClosedSubgroup G := fun i => i.1.L
  have hL : ∀ {i j : I}, i ≤ j → (L j : Subgroup G) ≤ (L i : Subgroup G) := by
    intro i j hij
    rcases hij with ⟨hji, -⟩
    exact hji
  have hdir : Directed (· ≤ ·) (id : I → I) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      exact ⟨i, le_rfl, le_rfl⟩
    · have hcmp := hc i.2 j.2 (by
        intro hij'
        apply hij
        exact Subtype.ext hij')
      rcases hcmp with hij' | hji'
      · exact ⟨j, hij', le_rfl⟩
      · exact ⟨i, le_rfl, hji'⟩
  obtain ⟨ηinf, hηinf_continuous, hηinf_fac, hηinf_one⟩ :=
    exists_continuous_leftQuotient_lift_of_directed (G := G) L hL hdir
      (η := fun i => i.1.σ) (hηcont := fun i => i.1.continuous_σ)
      (hηcompat := by
        intro i j hij
        rcases hij with ⟨hji, hσ⟩
        exact hσ)
      (QuotientGroup.mk (s := (H : Subgroup G)) (1 : G))
      (by
        intro i
        exact i.1.one_eq)
  let Linf : ClosedSubgroup G := closedSubgroup_sInf L
  have hKinf : (K : Subgroup G) ≤ (Linf : Subgroup G) := by
    intro x hx
    change x ∈ iInf fun i => (L i : Subgroup G)
    rw [Subgroup.mem_iInf]
    intro i
    exact i.1.hKL hx
  let i0 : I := Classical.choice hI_nonempty
  have hInfH : (Linf : Subgroup G) ≤ (H : Subgroup G) := by
    exact (closedSubgroup_sInf_le (L := L) i0).trans i0.1.hLH
  refine ⟨{ L := Linf
            hKL := hKinf
            hLH := hInfH
            σ := ηinf
            continuous_σ := hηinf_continuous
            rightInv := by
              intro y
              calc
                leftQuotientProjection (Linf : Subgroup G) (H : Subgroup G) hInfH (ηinf y)
                    = leftQuotientProjection (i0.1.L : Subgroup G) (H : Subgroup G) i0.1.hLH
                        (leftQuotientProjection (Linf : Subgroup G) (i0.1.L : Subgroup G)
                          (closedSubgroup_sInf_le (L := L) i0) (ηinf y)) := by
                            convert
                              (leftQuotientProjection_comp_apply
                                (K := (Linf : Subgroup G)) (H := (i0.1.L : Subgroup G))
                                (L := (H : Subgroup G)) (closedSubgroup_sInf_le (L := L) i0)
                                i0.1.hLH (ηinf y)).symm
                _ = leftQuotientProjection (i0.1.L : Subgroup G) (H : Subgroup G) i0.1.hLH
                      (i0.1.σ y) := by
                        exact congrArg
                          (leftQuotientProjection (i0.1.L : Subgroup G) (H : Subgroup G) i0.1.hLH)
                          (congrFun (hηinf_fac i0) y)
                _ = y := i0.1.rightInv y
            one_eq := hηinf_one }, ?_⟩
  intro a ha
  refine ⟨closedSubgroup_sInf_le (L := L) ⟨a, ha⟩, ?_⟩
  exact hηinf_fac ⟨a, ha⟩

end LeftQuotientSectionData

/--
General section theorem for left quotient projections between closed subgroups of a profinite
group.
-/
theorem leftQuotientProjection_hasContinuousSection
    (K H : ClosedSubgroup G)
    (hKH : (K : Subgroup G) ≤ (H : Subgroup G)) :
    ∃ σ : G ⧸ (H : Subgroup G) → G ⧸ (K : Subgroup G),
      Continuous σ ∧
        Function.RightInverse σ
          (leftQuotientProjection (K : Subgroup G) (H : Subgroup G) hKH) ∧
        σ (QuotientGroup.mk (s := (H : Subgroup G)) (1 : G)) =
          QuotientGroup.mk (s := (K : Subgroup G)) (1 : G) := by
  classical
  let P := LeftQuotientSectionData (G := G) K H
  let : Nonempty P := ⟨LeftQuotientSectionData.top (G := G) hKH⟩
  obtain ⟨m, hmmax⟩ := zorn_le_nonempty (α := P) <| by
    intro c hc hcn
    rcases LeftQuotientSectionData.exists_upperBound_of_chain (G := G) (K := K) (H := H)
        c hc hcn with ⟨ub, hub⟩
    exact ⟨ub, hub⟩
  have hmLK : m.L = K := by
    by_contra hne
    have hnotle : ¬ (m.L : Subgroup G) ≤ (K : Subgroup G) := by
      intro hmK
      apply hne
      ext x
      change x ∈ (m.L : Subgroup G) ↔ x ∈ (K : Subgroup G)
      exact ⟨fun hx => hmK hx, fun hx => m.hKL hx⟩
    let : CompactSpace ↥(m.L : Subgroup G) :=
      m.L.isClosed'.isClosedEmbedding_subtypeVal.compactSpace
    rcases exists_mem_of_not_le (G := G) (K := K) (L := m.L) hnotle with ⟨x, hxL, hxK⟩
    let KT : ClosedSubgroup ↥(m.L : Subgroup G) := {
      toSubgroup := (K : Subgroup G).subgroupOf (m.L : Subgroup G)
      isClosed' := by
        change IsClosed (((↑) : ↥(m.L : Subgroup G) → G) ⁻¹'
          (K : Subgroup G).carrier)
        exact K.isClosed'.preimage continuous_subtype_val }
    let xT : ↥(m.L : Subgroup G) := ⟨x, hxL⟩
    have hxTK : xT ∉ (KT : Set ↥(m.L : Subgroup G)) := by
      change x ∉ (K : Subgroup G)
      exact hxK
    obtain ⟨N, hKTN, hxN⟩ :=
      exists_openSubgroup_ge_closedSubgroup_not_mem (G := ↥(m.L : Subgroup G)) KT hxTK
    let L' : ClosedSubgroup G := closedSubgroupOfOpenSubgroup (G := G) m.L N
    have hL'm : (L' : Subgroup G) ≤ (m.L : Subgroup G) :=
      closedSubgroupOfOpenSubgroup_le (G := G) m.L N
    have hKL' : (K : Subgroup G) ≤ (L' : Subgroup G) := by
      intro g hg
      have hgT : (⟨g, m.hKL hg⟩ : ↥(m.L : Subgroup G)) ∈ (KT : Subgroup ↥(m.L : Subgroup G)) := by
        simpa [KT, Subgroup.mem_subgroupOf] using hg
      have hgN : (⟨g, m.hKL hg⟩ : ↥(m.L : Subgroup G)) ∈ (N : Subgroup ↥(m.L : Subgroup G)) :=
        hKTN hgT
      exact (mem_closedSubgroupOfOpenSubgroup (G := G) (T := m.L) (N := N)
        (x := ⟨g, m.hKL hg⟩)).2 hgN
    have hL'H : (L' : Subgroup G) ≤ (H : Subgroup G) := hL'm.trans m.hLH
    have hL'open :
        IsOpen (((L' : Subgroup G).subgroupOf (m.L : Subgroup G)) : Set ↥(m.L : Subgroup G)) := by
      rw [closedSubgroupOfOpenSubgroup_subgroupOf_eq (G := G) m.L N]
      exact N.isOpen'
    have hxL' : x ∉ (L' : Subgroup G) := by
      intro hxL'
      have : xT ∈ (N : Subgroup ↥(m.L : Subgroup G)) := by
        exact (mem_closedSubgroupOfOpenSubgroup (G := G) (T := m.L) (N := N)
          (x := xT)).1 (by simpa [xT] using hxL')
      exact hxN this
    obtain ⟨ξ, hξcont, hξright, hξone⟩ :=
      leftQuotientProjection_hasContinuousSection_of_openSubgroup (G := G) L' m.L hL'm hL'open
    let m' : P :=
      { L := L'
        hKL := hKL'
        hLH := hL'H
        σ := ξ ∘ m.σ
        continuous_σ := hξcont.comp m.continuous_σ
        rightInv := by
          intro y
          calc
            leftQuotientProjection (L' : Subgroup G) (H : Subgroup G) hL'H ((ξ ∘ m.σ) y)
                = leftQuotientProjection (m.L : Subgroup G) (H : Subgroup G) m.hLH
                    (leftQuotientProjection (L' : Subgroup G) (m.L : Subgroup G) hL'm
                      (ξ (m.σ y))) := by
                        change
                          leftQuotientProjection (L' : Subgroup G) (H : Subgroup G) hL'H
                              (ξ (m.σ y)) =
                            leftQuotientProjection (m.L : Subgroup G) (H : Subgroup G)
                              m.hLH
                              (leftQuotientProjection (L' : Subgroup G)
                                (m.L : Subgroup G) hL'm (ξ (m.σ y)))
                        exact
                          (leftQuotientProjection_comp_apply
                            (K := (L' : Subgroup G)) (H := (m.L : Subgroup G))
                            (L := (H : Subgroup G)) hL'm m.hLH (ξ (m.σ y))).symm
            _ = leftQuotientProjection (m.L : Subgroup G) (H : Subgroup G) m.hLH (m.σ y) := by
                  rw [hξright (m.σ y)]
            _ = y := m.rightInv y
        one_eq := by
          change ξ (m.σ (QuotientGroup.mk (s := (H : Subgroup G)) (1 : G))) =
            QuotientGroup.mk (s := (L' : Subgroup G)) (1 : G)
          rw [m.one_eq]
          exact hξone }
    have hmm' : m ≤ m' := by
      refine ⟨hL'm, ?_⟩
      funext y
      exact hξright (m.σ y)
    have hm'm : m' ≤ m := hmmax hmm'
    rcases hm'm with ⟨hm'mL, -⟩
    exact hxL' (hm'mL hxL)
  have hLKsub : (m.L : Subgroup G) = (K : Subgroup G) := congrArg ClosedSubgroup.toSubgroup hmLK
  have hmLleK : (m.L : Subgroup G) ≤ (K : Subgroup G) := by
    intro x hx
    simpa [hLKsub] using hx
  let σ : G ⧸ (H : Subgroup G) → G ⧸ (K : Subgroup G) :=
    leftQuotientProjection (m.L : Subgroup G) (K : Subgroup G) hmLleK ∘ m.σ
  refine ⟨σ, (continuous_leftQuotientProjection
      (K := (m.L : Subgroup G)) (H := (K : Subgroup G)) hmLleK).comp m.continuous_σ, ?_, ?_⟩
  · intro y
    have hproof : hmLleK.trans hKH = m.hLH := Subsingleton.elim _ _
    calc
      leftQuotientProjection (K : Subgroup G) (H : Subgroup G) hKH (σ y) =
          leftQuotientProjection
            (m.L : Subgroup G)
            (H : Subgroup G)
            (hmLleK.trans hKH)
            (m.σ y) := by
              simpa only [σ, Function.comp] using
                (leftQuotientProjection_comp_apply
                  (K := (m.L : Subgroup G)) (H := (K : Subgroup G))
                  (L := (H : Subgroup G)) hmLleK hKH (m.σ y))
      _ = leftQuotientProjection (m.L : Subgroup G) (H : Subgroup G) m.hLH (m.σ y) := by
            rw [hproof]
      _ = y := m.rightInv y
  · calc
      σ (QuotientGroup.mk (s := (H : Subgroup G)) (1 : G))
          = leftQuotientProjection (m.L : Subgroup G) (K : Subgroup G) hmLleK
              (m.σ (QuotientGroup.mk (s := (H : Subgroup G)) (1 : G))) := by
                  rfl
      _ = leftQuotientProjection (m.L : Subgroup G) (K : Subgroup G) hmLleK
            (QuotientGroup.mk (s := (m.L : Subgroup G)) (1 : G)) := by
              rw [m.one_eq]
      _ = QuotientGroup.mk (s := (K : Subgroup G)) (1 : G) := rfl

/--
A quotient by a closed normal subgroup of a profinite group admits a continuous section that
sends the identity coset to the identity.
-/
theorem exists_continuousSection_quotientMk_of_isClosed
    (H : Subgroup G) (hH : IsClosed (H : Set G)) :
        ∃ σ : (G ⧸ H) → G,
          Continuous σ ∧
            Function.RightInverse σ (QuotientGroup.mk (s := H)) ∧
            σ (QuotientGroup.mk (s := H) (1 : G)) = 1 := by
  let K0 : ClosedSubgroup G := ⟨⊥, by
    change IsClosed ({(1 : G)} : Set G)
    simp only [finite_singleton, Finite.isClosed]⟩
  let HC : ClosedSubgroup G := ⟨H, hH⟩
  have hbotH : (⊥ : Subgroup G) ≤ H := by
    intro x hx
    have hx1 : x = 1 := by
      simpa [Subgroup.mem_bot] using hx
    simp only [hx1, one_mem]
  obtain ⟨σ0, hσ0cont, hσ0right, hσ0one⟩ :=
    leftQuotientProjection_hasContinuousSection (G := G) K0 HC hbotH
  let e : G ≃ₜ G ⧸ (⊥ : Subgroup G) := quotientBotHomeomorph (G := G)
  refine ⟨e.symm ∘ σ0, e.symm.continuous.comp hσ0cont, ?_, ?_⟩
  · intro y
    calc
      QuotientGroup.mk (s := H) ((e.symm ∘ σ0) y)
          = leftQuotientProjection (⊥ : Subgroup G) H hbotH
              (e ((e.symm ∘ σ0) y)) := by
                  rfl
      _ = leftQuotientProjection (⊥ : Subgroup G) H hbotH (σ0 y) := by
            exact congrArg (leftQuotientProjection (⊥ : Subgroup G) H hbotH) (e.right_inv (σ0 y))
      _ = y := hσ0right y
  · change e.symm (σ0 (QuotientGroup.mk (s := H) (1 : G))) = 1
    rw [hσ0one]
    change e.symm (e (1 : G)) = 1
    exact e.left_inv (1 : G)

end ProCGroups.ProC
