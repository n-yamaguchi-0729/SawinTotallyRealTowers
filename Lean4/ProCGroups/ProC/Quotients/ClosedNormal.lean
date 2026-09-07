import ProCGroups.Generation.Basic
import ProCGroups.ProC.Quotients.LeftQuotientProjectionSections

set_option autoImplicit false

/-!
# Quotients by closed normal subgroups

This file supplies the profinite topology and normalized continuous sections for closed-normal
quotients, identifies iterated quotients, proves closedness of quotient images, and transfers
topological generation between a group, its kernel, and its quotient.
-/

open Set
open scoped Topology Pointwise

namespace ProCGroups

universe u v

/-- A quotient by a closed normal subgroup of a compact Hausdorff totally disconnected
topological group is totally disconnected. -/
theorem totallyDisconnectedSpace_quotient_closedNormal
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) :
    TotallyDisconnectedSpace (G ⧸ N) := by
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  have hsep : Pairwise (fun a b : G ⧸ N =>
      ∃ U : Set (G ⧸ N), IsClopen U ∧ a ∈ U ∧ b ∈ Uᶜ) := by
    intro a b hab
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N b
    let g : G := x⁻¹ * y
    have hgN : g ∉ N := by
      intro hgN
      apply hab
      apply inv_mul_eq_one.mp
      change q g = 1
      exact (QuotientGroup.eq_one_iff g).2 hgN
    let W : Set G := {u | g * u⁻¹ ∉ N}
    have hWopen : IsOpen W := by
      change IsOpen ((fun u : G => g * u⁻¹) ⁻¹' ((N : Set G)ᶜ))
      exact hN.isOpen_compl.preimage (continuous_const.mul continuous_inv)
    have hWone : (1 : G) ∈ W := by
      simpa [W] using hgN
    obtain ⟨V, hVW⟩ :=
      ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
        (G := G) hWopen hWone
    let K : Subgroup G := N ⊔ (V : Subgroup G)
    have hKopen : IsOpen (K : Set G) :=
      Subgroup.isOpen_of_openSubgroup K
        (show (V : Subgroup G) ≤ K from le_sup_right)
    have hNK : N ≤ K := le_sup_left
    have hgK : g ∉ K := by
      intro hgK
      rcases (Subgroup.mem_sup_of_normal_right
          (s := N) (t := (V : Subgroup G))).1 hgK with
        ⟨n, hnN, v, hvV, hnv⟩
      have hvW : v ∈ W := hVW hvV
      have hgn : g * v⁻¹ = n := by
        calc
          g * v⁻¹ = (n * v) * v⁻¹ := by rw [hnv]
          _ = n := by simp
      apply hvW
      simpa [hgn] using hnN
    let Kbar : Subgroup (G ⧸ N) := K.map q
    have hKbarOpen : IsOpen (Kbar : Set (G ⧸ N)) := by
      change IsOpen (((↑) : G → G ⧸ N) '' (K : Set G))
      exact QuotientGroup.isOpenMap_coe (K : Set G) hKopen
    have hqgKbar : q g ∉ Kbar := by
      intro hqgKbar
      have hgComap : g ∈ Kbar.comap q := hqgKbar
      have hker : q.ker ≤ K := by
        simpa [q] using hNK
      have hcomap : Kbar.comap q = K := by
        simpa [Kbar] using Subgroup.comap_map_eq_self hker
      rw [hcomap] at hgComap
      exact hgK hgComap
    let U : Set (G ⧸ N) := {z | (q x)⁻¹ * z ∈ Kbar}
    have hUclopen : IsClopen U := by
      have hcont : Continuous (fun z : G ⧸ N => (q x)⁻¹ * z) :=
        (continuous_const : Continuous (fun _ : G ⧸ N => (q x)⁻¹)).mul continuous_id'
      exact
        ⟨(Subgroup.isClosed_of_isOpen Kbar hKbarOpen).preimage hcont,
          hKbarOpen.preimage hcont⟩
    refine ⟨U, hUclopen, ?_, ?_⟩
    · simp [U, q]
    · change (q x)⁻¹ * q y ∉ Kbar
      simpa [g, q] using hqgKbar
  let : TotallySeparatedSpace (G ⧸ N) :=
    totallySeparatedSpace_iff_exists_isClopen.2 hsep
  infer_instance

end ProCGroups

namespace ProCGroups.Generation

universe u v

open ProCGroups.ProC

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/--
A chosen continuous section of the quotient map by a closed normal subgroup of a profinite
group.
-/
noncomputable def closedNormalQuotientSection
    {N : Subgroup G} (hNclosed : IsClosed (N : Set G)) :
    G ⧸ N → G :=
  Classical.choose (exists_continuousSection_quotientMk_of_isClosed (G := G) N hNclosed)

/-- The chosen closed-normal quotient section is continuous. -/
theorem closedNormalQuotientSection_continuous
    {N : Subgroup G} (hNclosed : IsClosed (N : Set G)) :
    Continuous (closedNormalQuotientSection (G := G) (N := N) hNclosed) := by
  exact (Classical.choose_spec
    (exists_continuousSection_quotientMk_of_isClosed (G := G) N hNclosed)).1

/-- The chosen closed-normal quotient section is a right inverse to the quotient map. -/
theorem closedNormalQuotientSection_rightInverse
    {N : Subgroup G} (hNclosed : IsClosed (N : Set G)) :
    Function.RightInverse
      (closedNormalQuotientSection (G := G) (N := N) hNclosed)
      (QuotientGroup.mk (s := N)) := by
  simpa [closedNormalQuotientSection] using (Classical.choose_spec
    (exists_continuousSection_quotientMk_of_isClosed (G := G) N hNclosed)).2.1

/-- The chosen closed-normal quotient section sends the identity coset to \(1\). -/
theorem closedNormalQuotientSection_one
    {N : Subgroup G} (hNclosed : IsClosed (N : Set G)) :
    closedNormalQuotientSection (G := G) (N := N) hNclosed
      (QuotientGroup.mk (s := N) (1 : G)) = 1 := by
  simpa [closedNormalQuotientSection] using (Classical.choose_spec
    (exists_continuousSection_quotientMk_of_isClosed (G := G) N hNclosed)).2.2

/--
The quotient by the bottom subgroup is continuously multiplicatively equivalent to the original
profinite group.
-/
noncomputable def quotientBotContinuousMulEquiv :
    G ≃ₜ* G ⧸ (⊥ : Subgroup G) :=
  ContinuousMulEquiv.mk' (quotientBotHomeomorph (G := G)) (by
    intro x y
    simp only [quotientBotHomeomorph_apply, QuotientGroup.mk_mul])

omit [T2Space G] [TotallyDisconnectedSpace G] in
/--
Adding a closed normal subgroup to a generating set is equivalent to generating the quotient
from the image of the set.
-/
theorem topologicallyGenerates_union_closedNormal_iff_quotient
    {N : Subgroup G} [N.Normal]
    (hNclosed : IsClosed (N : Set G)) {X : Set G} :
    TopologicallyGenerates (G := G) (X ∪ (N : Set G)) ↔
      TopologicallyGenerates (G := G ⧸ N) ((QuotientGroup.mk' N) '' X) := by
  constructor
  · intro hX
    have himg :
        (QuotientGroup.mk' N) '' (X ∪ (N : Set G)) =
          ((QuotientGroup.mk' N) '' X) ∪ ({1} : Set (G ⧸ N)) := by
      ext q
      constructor
      · intro hq
        rcases hq with ⟨x, hx, rfl⟩
        rcases hx with hxX | hxN
        · exact Or.inl ⟨x, hxX, rfl⟩
        · exact Or.inr ((QuotientGroup.eq_one_iff (N := N) x).2 hxN)
      · intro hq
        rcases hq with hqX | hq1
        · rcases hqX with ⟨x, hxX, rfl⟩
          exact ⟨x, Or.inl hxX, rfl⟩
        · exact ⟨1, Or.inr N.one_mem, by simpa using hq1.symm⟩
    have hquot :
        TopologicallyGenerates (G := G ⧸ N)
          ((QuotientGroup.mk' N) '' (X ∪ (N : Set G))) := by
      exact topologicallyGenerates_image_of_continuousSurjective
        (G := G)
        (H := G ⧸ N)
        (QuotientGroup.mk' N)
        continuous_quotient_mk'
        (QuotientGroup.mk'_surjective N)
        hX
    have hquot' :
        TopologicallyGenerates (G := G ⧸ N)
          ((((QuotientGroup.mk' N) '' X) ∪ ({1} : Set (G ⧸ N)))) := by
      rwa [himg] at hquot
    exact (topologicallyGenerates_union_one_iff (G := G ⧸ N)
      (X := (QuotientGroup.mk' N) '' X)).1
      hquot'
  · intro hX
    let H : Subgroup G := (Subgroup.closure (X ∪ (N : Set G))).topologicalClosure
    have hXleH : X ⊆ (H : Set G) := by
      intro x hx
      exact Subgroup.le_topologicalClosure _
        (Subgroup.subset_closure (Or.inl hx))
    have hNleH : N ≤ H := by
      intro n hn
      exact Subgroup.le_topologicalClosure _
        (Subgroup.subset_closure (Or.inr hn))
    let qH : Subgroup (G ⧸ N) := H.map (QuotientGroup.mk' N)
    have hqHclosed : IsClosed (qH : Set (G ⧸ N)) := by
      have hHcompact : IsCompact (H : Set G) := (Subgroup.isClosed_topologicalClosure _).isCompact
      have himage : IsCompact ((QuotientGroup.mk' N) '' (H : Set G)) :=
        hHcompact.image continuous_quotient_mk'
      have hEq : (QuotientGroup.mk' N) '' (H : Set G) = (qH : Set (G ⧸ N)) := by
        ext q
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact ⟨x, hx, rfl⟩
        · rintro ⟨x, hx, rfl⟩
          exact ⟨x, hx, rfl⟩
      rw [← hEq]
      exact himage.isClosed
    have himage_le_qH :
        ((QuotientGroup.mk' N) '' X) ⊆ (qH : Set (G ⧸ N)) := by
      intro q hq
      rcases hq with ⟨x, hx, rfl⟩
      exact ⟨x, hXleH hx, rfl⟩
    have hcl_le_qH :
        Subgroup.closure ((QuotientGroup.mk' N) '' X) ≤ qH := by
      exact (Subgroup.closure_le (K := qH)).2 himage_le_qH
    have hclosure_le_qH :
        (Subgroup.closure ((QuotientGroup.mk' N) '' X)).topologicalClosure ≤ qH := by
      exact Subgroup.topologicalClosure_minimal _ hcl_le_qH hqHclosed
    have htop :
        (⊤ : Subgroup (G ⧸ N)) ≤
          (Subgroup.closure ((QuotientGroup.mk' N) '' X)).topologicalClosure := by
      simpa [TopologicallyGenerates] using hX
    have hqHtop :
        qH = ⊤ := by
      apply top_unique
      intro q hq
      exact hclosure_le_qH (htop hq)
    rw [TopologicallyGenerates]
    apply top_unique
    intro g hg
    have hgq : QuotientGroup.mk' N g ∈ qH := by
      rw [hqHtop]
      simp only [QuotientGroup.mk'_apply, Subgroup.mem_top]
    rcases hgq with ⟨h, hhH, hhEq⟩
    have hdivN : h⁻¹ * g ∈ N := by
      exact (QuotientGroup.eq).1 hhEq
    have hdivH : h⁻¹ * g ∈ H := hNleH hdivN
    have hhH' : h ∈ H := hhH
    have hgH : g = h * (h⁻¹ * g) := by simp only [mul_inv_cancel_left]
    rw [hgH]
    exact H.mul_mem hhH' hdivH

omit [T2Space G] [TotallyDisconnectedSpace G] in
/-- The image of a closed subgroup in a quotient by a closed normal subgroup is closed. -/
theorem isClosed_image_closedNormal_quotient
    {N N' : Subgroup G} [N'.Normal]
    (hNclosed : IsClosed (N : Set G)) (hN'closed : IsClosed (N' : Set G)) :
    IsClosed ((N.map (QuotientGroup.mk' N') : Subgroup (G ⧸ N')) : Set (G ⧸ N')) := by
  have hNcompact : IsCompact (N : Set G) := hNclosed.isCompact
  have himage : IsCompact ((QuotientGroup.mk' N') '' (N : Set G)) :=
    hNcompact.image continuous_quotient_mk'
  have hEq :
      (QuotientGroup.mk' N') '' (N : Set G) =
        ((N.map (QuotientGroup.mk' N') : Subgroup (G ⧸ N')) : Set (G ⧸ N')) := by
    ext q
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
  rw [← hEq]
  exact himage.isClosed

/--
The quotient-of-quotient isomorphism for closed normal subgroups as a continuous multiplicative
equivalence.
-/
noncomputable def quotientQuotientContinuousMulEquiv
    {N N' : Subgroup G} [N.Normal] [N'.Normal]
    (hNclosed : IsClosed (N : Set G))
    (hN'N : N' ≤ N) :
    ((G ⧸ N') ⧸ N.map (QuotientGroup.mk' N')) ≃ₜ* G ⧸ N := by
  let K : Subgroup (G ⧸ N') := N.map (QuotientGroup.mk' N')
  let f : ((G ⧸ N') ⧸ K) →* G ⧸ N :=
    QuotientGroup.quotientQuotientEquivQuotientAux N' N hN'N
  have hfcont : Continuous f := by
    refine (QuotientGroup.isQuotientMap_mk K).continuous_iff.2 ?_
    change Continuous (leftQuotientProjection N' N hN'N)
    exact continuous_leftQuotientProjection (G := G) (K := N') (H := N) hN'N
  have hfbij : Function.Bijective f := by
    exact (QuotientGroup.quotientQuotientEquivQuotient N' N hN'N).bijective
  exact ContinuousMulEquiv.ofBijectiveCompactToT2 f hfcont hfbij

omit [T2Space G] [TotallyDisconnectedSpace G] in
/--
A quotient section together with generators for the kernel generates the intermediate quotient.
-/
theorem topologicallyGenerates_of_quotient_section_union_kernel
    {N N' : Subgroup G} [N.Normal] [N'.Normal]
    (hNclosed : IsClosed (N : Set G)) (hN'closed : IsClosed (N' : Set G))
    (hN'N : N' ≤ N)
    {Y : Set (G ⧸ N)}
    (hYgen : TopologicallyGenerates (G := G ⧸ N) Y)
    {σ : (G ⧸ N) → (G ⧸ N')}
    (hσright : Function.RightInverse σ (leftQuotientProjection N' N hN'N))
    {T : Set G}
    (hTgen : N ≤ Subgroup.closure (T ∪ (N' : Set G))) :
    TopologicallyGenerates (G := G ⧸ N')
      (σ '' Y ∪ ((QuotientGroup.mk' N') '' T)) := by
  classical
  let K : Subgroup (G ⧸ N') := N.map (QuotientGroup.mk' N')
  let X : Set (G ⧸ N') := σ '' Y ∪ ((QuotientGroup.mk' N') '' T)
  have hKclosed : IsClosed (K : Set (G ⧸ N')) := by
    simpa [K] using
      isClosed_image_closedNormal_quotient (G := G) hNclosed hN'closed
  let e : ((G ⧸ N') ⧸ K) ≃ₜ* G ⧸ N :=
    quotientQuotientContinuousMulEquiv
      (G := G) hNclosed hN'N
  have hsright :
      Function.RightInverse
        (fun y : G ⧸ N => QuotientGroup.mk' K (σ y))
        e := by
    intro y
    change leftQuotientProjection N' N hN'N (σ y) = y
    exact hσright y
  have hsleft :
      Function.LeftInverse
        (fun y : G ⧸ N => QuotientGroup.mk' K (σ y))
        e := by
    intro z
    apply e.injective
    simpa using hsright (e z)
  have hs_eq :
      e.symm = (fun y : G ⧸ N => QuotientGroup.mk' K (σ y)) := by
    funext y
    simpa using (hsleft (e.symm y)).symm
  have hgenInv :
      TopologicallyGenerates (G := ((G ⧸ N') ⧸ K)) (e.symm '' Y) := by
    exact topologicallyGenerates_continuousMulEquiv_image
      (G := G ⧸ N) e.symm hYgen
  have hEq :
      e.symm '' Y = (QuotientGroup.mk' K) '' (σ '' Y) := by
    ext q
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨σ y, ⟨y, hy, rfl⟩, by simp only [QuotientGroup.mk'_apply, hs_eq]⟩
    · rintro ⟨x, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, by simp only [hs_eq, QuotientGroup.mk'_apply]⟩
  have hgenQuotY : TopologicallyGenerates (G := ((G ⧸ N') ⧸ K))
      ((QuotientGroup.mk' K) '' (σ '' Y)) := by
    simpa [hEq] using hgenInv
  have hgenQuotX :
      TopologicallyGenerates (G := ((G ⧸ N') ⧸ K))
        ((QuotientGroup.mk' K) '' X) := by
    exact topologicallyGenerates_mono hgenQuotY (by
      intro q hq
      rcases hq with ⟨x, hx, rfl⟩
      exact ⟨x, Or.inl hx, rfl⟩)
  have hgenUnionK :
      TopologicallyGenerates (G := G ⧸ N') (X ∪ (K : Set (G ⧸ N'))) := by
    exact
      (topologicallyGenerates_union_closedNormal_iff_quotient
        (G := G ⧸ N') (N := K) hKclosed (X := X)).2 hgenQuotX
  have hKsubset :
      (K : Set (G ⧸ N')) ⊆ ((Subgroup.closure X : Subgroup (G ⧸ N')) : Set (G ⧸ N')) := by
    have himgSubset :
        (QuotientGroup.mk' N' '' (T ∪ (N' : Set G))) ⊆
          ((Subgroup.closure X : Subgroup (G ⧸ N')) : Set (G ⧸ N')) := by
      intro q hq
      rcases hq with ⟨g, hg, rfl⟩
      rcases hg with hgT | hgN'
      · exact Subgroup.subset_closure (Or.inr ⟨g, hgT, rfl⟩)
      · have hg1 : QuotientGroup.mk' N' g = (1 : G ⧸ N') := by
          exact (QuotientGroup.eq_one_iff (N := N') g).2 hgN'
        rw [hg1]
        exact (Subgroup.closure X).one_mem
    have hclosureSubset :
        Subgroup.closure ((QuotientGroup.mk' N') '' (T ∪ (N' : Set G))) ≤
          Subgroup.closure X := by
      exact (Subgroup.closure_le (K := Subgroup.closure X)).2 himgSubset
    intro q hq
    have hq' :
        q ∈ Subgroup.closure ((QuotientGroup.mk' N') '' (T ∪ (N' : Set G))) := by
      rcases hq with ⟨n, hnN, rfl⟩
      have hncl : n ∈ Subgroup.closure (T ∪ (N' : Set G)) := hTgen hnN
      have hmap :
          QuotientGroup.mk' N' n ∈
            (Subgroup.closure (T ∪ (N' : Set G))).map (QuotientGroup.mk' N') := by
        exact ⟨n, hncl, rfl⟩
      have hmapEq :
          (Subgroup.closure (T ∪ (N' : Set G))).map (QuotientGroup.mk' N') =
            Subgroup.closure ((QuotientGroup.mk' N') '' (T ∪ (N' : Set G))) := by
        simpa using
          (MonoidHom.map_closure (QuotientGroup.mk' N') (T ∪ (N' : Set G)))
      exact hmapEq ▸ hmap
    exact hclosureSubset hq'
  exact topologicallyGenerates_of_subset_closure hgenUnionK (by
    intro q hq
    rcases hq with hqX | hqK
    · exact Subgroup.subset_closure hqX
    · exact hKsubset hqK)

end ProCGroups.Generation
