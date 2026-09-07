import ProCGroups.InverseSystems.ProfiniteSpace

set_option autoImplicit false

/-!
# Factorization through finite stages

Products are presented as inverse limits of their finite subproducts.  The main factorization
results show that continuous maps from a compact inverse limit to a finite discrete target
depend on one stage; specialized versions produce factorizations by group homomorphisms and
additive monoid homomorphisms.
-/

open Set
open scoped Topology


namespace ProCGroups.InverseSystems

attribute [local instance] instAddCommGroupAddInverseLimit

universe u v w

/--
The additive-multiplicative homeomorphism is compatible with the profinite topology and is
determined by finite-quotient data.
-/
private def additiveMultiplicativeHomeomorph (A : Type*) [TopologicalSpace A] :
    A ≃ₜ Multiplicative A where
  toEquiv := Multiplicative.ofAdd
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id

/--
The inverse system whose stage at \(F\) is the finite subproduct over the finite subset \(F\).
-/
def finiteSubsetProductSystem {α : Type u} (X : α → Type v)
    [∀ a, TopologicalSpace (X a)] : InverseSystem.{u, max u v} (I := Finset α) where
  X := fun F => ∀ a : F, X a.1
  topologicalSpace := fun _ => inferInstance
  map := fun {F G} hFG x a => x ⟨a.1, hFG a.2⟩
  continuous_map := fun {F G} hFG => by
    exact continuous_pi fun a => continuous_apply (⟨a.1, hFG a.2⟩ : G)
  map_id := fun F => by
    funext x a
    rfl
  map_comp := fun {F G H} hFG hGH => by
    funext x a
    rfl

/-- An arbitrary product is homeomorphic to the inverse limit of its finite subproducts. -/
def homeomorph_inverseLimit_finiteSubsetProductSystem {α : Type u} (X : α → Type v)
    [∀ a, TopologicalSpace (X a)] :
    (∀ a, X a) ≃ₜ (finiteSubsetProductSystem X).inverseLimit := by
  let S : InverseSystem.{u, max u v} (I := Finset α) := finiteSubsetProductSystem X
  let toS : (∀ a, X a) → S.inverseLimit := fun x =>
    ⟨fun F a => x a.1, by
      intro F G hFG
      funext a
      rfl⟩
  let fromS : S.inverseLimit → (∀ a, X a) :=
    fun y a => S.projection ({a} : Finset α) y ⟨a, by simp only [Finset.mem_singleton]⟩
  have hleft : Function.LeftInverse fromS toS := by
    intro x
    funext a
    rfl
  have hright : Function.RightInverse fromS toS := by
    intro y
    apply S.ext
    intro F
    funext a
    change fromS y a.1 = S.projection F y a
    have hs : ({a.1} : Finset α) ≤ F := by
      intro b hb
      have hb' : b = a.1 := by simpa using hb
      exact hb' ▸ a.2
    have hcompat := congrFun
      (S.projection_compatible y ({a.1} : Finset α) F hs)
      ⟨a.1, by simp only [Finset.mem_singleton]⟩
    change S.projection F y a = fromS y a.1 at hcompat
    exact hcompat.symm
  have hcontinuous_toS : Continuous toS := by
    exact Continuous.subtype_mk
      (by
        refine continuous_pi fun F => ?_
        refine continuous_pi fun a => ?_
        exact continuous_apply a.1)
      (fun x F G hFG => by
        funext a
        rfl)
  have hcontinuous_fromS : Continuous fromS := by
    refine continuous_pi fun a => ?_
    exact (continuous_apply ⟨a, by simp only [Finset.mem_singleton]⟩).comp
        (S.continuous_projection ({a} : Finset α))
  exact
    { toFun := toS
      invFun := fromS
      left_inv := hleft
      right_inv := hright
      continuous_toFun := hcontinuous_toS
      continuous_invFun := hcontinuous_fromS }

/--
A continuous map from a profinite inverse limit to a finite discrete space factors through one
projection.
-/
theorem InverseSystem.factors_through_projection_finite
    {I : Type u} [Preorder I] (S : InverseSystem (I := I)) [Nonempty I]
    [∀ i, CompactSpace (S.X i)] [∀ i, T2Space (S.X i)]
    [∀ i, TotallyDisconnectedSpace (S.X i)] (hdir : Directed (· ≤ ·) (id : I → I))
    {Y : Type w} [TopologicalSpace Y] [Finite Y] [Nonempty Y] [DiscreteTopology Y]
    (ρ : S.inverseLimit → Y) (hρ : Continuous ρ) :
    ∃ k : I, ∃ ρ' : S.X k → Y, Continuous ρ' ∧ ρ = ρ' ∘ S.projection k := by
  classical
  let : Fintype Y := Fintype.ofFinite Y
  let Uy : Y → Set S.inverseLimit := fun y => ρ ⁻¹' ({y} : Set Y)
  have hUy_clopen : ∀ y, IsClopen (Uy y) := by
    intro y
    refine ⟨?_, ?_⟩
    · simpa [Uy] using (isClosed_discrete ({y} : Set Y)).preimage hρ
    · simpa [Uy] using (isOpen_discrete ({y} : Set Y)).preimage hρ
  have hlocal :
      ∀ y (x : S.inverseLimit), x ∈ Uy y →
        ∃ i, ∃ V : Set (S.X i), IsClopen V ∧ S.projection i x ∈ V ∧ S.projection i ⁻¹' V ⊆ Uy y
            := by
    intro y x hx
    rcases S.exists_projection_preimage_subset hdir (hUy_clopen y).2 hx with
      ⟨i, W, hWopen, hxW, hWU⟩
    rcases exists_clopen_subset_of_mem_open (X := S.X i) hWopen hxW with ⟨V, hVclopen, hxV, hVW⟩
    exact ⟨i, V, hVclopen, hxV, (Set.preimage_mono hVW).trans hWU⟩
  choose ix V hVclopen hxV hVsub using hlocal
  have hsubcover :
      ∀ y, ∃ t : Finset ↥(Uy y), Uy y ⊆ ⋃ x ∈ t, S.projection (ix y x.1 x.2) ⁻¹' V y x.1 x.2 := by
    intro y
    have hcompactUy : IsCompact (Uy y) := (hUy_clopen y).1.isCompact
    simpa using hcompactUy.elim_nhds_subcover'
      (U := fun x hx => S.projection (ix y x hx) ⁻¹' V y x hx)
      (hU := fun x hx =>
        ((hVclopen y x hx).2.preimage (S.continuous_projection (ix y x hx))).mem_nhds (hxV y x hx))
  choose t htcover using hsubcover
  let i0 : I := Classical.choice ‹Nonempty I›
  let used : Finset I :=
    (Finset.univ.biUnion fun y : Y => (t y).image (fun x => ix y x.1 x.2)) ∪ {i0}
  have hused_nonempty : used.Nonempty := ⟨i0, by simp only [Finset.union_singleton,
      Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_image,
  Subtype.exists, true_and, true_or, used]⟩
  rcases exists_upperBound_finset (I := I) hdir used hused_nonempty with ⟨k, hk⟩
  have hix_le_k : ∀ y (x : ↥(Uy y)) (hx : x ∈ t y), ix y x.1 x.2 ≤ k := by
    intro y x hx
    apply hk
    apply Finset.mem_union.mpr
    left
    apply Finset.mem_biUnion.mpr
    refine ⟨y, Finset.mem_univ y, ?_⟩
    apply Finset.mem_image.mpr
    exact ⟨x, hx, rfl⟩
  let B : Y → Set (S.X k) := fun y =>
    ⋃ x ∈ (Finset.univ : Finset ↥(t y)),
      S.map (hix_le_k y x.1 x.2) ⁻¹' V y x.1.1 x.1.2
  have hBclopen : ∀ y, IsClopen (B y) := by
    intro y
    refine ⟨?_, ?_⟩
    · simpa [B] using
        isClosed_biUnion_finset (s := (Finset.univ : Finset ↥(t y))) fun x hx =>
          (hVclopen y x.1.1 x.1.2).1.preimage (S.continuous_map (hix_le_k y x.1 x.2))
    · simpa [B] using
        isOpen_biUnion (s := (((Finset.univ : Finset ↥(t y)) : Set ↥(t y)))) fun x hx =>
          (hVclopen y x.1.1 x.1.2).2.preimage (S.continuous_map (hix_le_k y x.1 x.2))
  have hUy_eq : ∀ y, Uy y = S.projection k ⁻¹' B y := by
    intro y
    ext z
    constructor
    · intro hz
      have hzcover := htcover y hz
      rcases mem_iUnion.1 hzcover with ⟨x, hxcover⟩
      rcases mem_iUnion.1 hxcover with ⟨hx, hzV⟩
      change S.projection k z ∈ B y
      refine mem_iUnion.2 ⟨⟨x, hx⟩, ?_⟩
      refine mem_iUnion.2 ⟨Finset.mem_univ _, ?_⟩
      change S.map (hix_le_k y x hx) (S.projection k z) ∈ V y x.1 x.2
      rw [S.projection_compatible z (ix y x.1 x.2) k (hix_le_k y x hx)]
      exact hzV
    · intro hz
      have hzB : S.projection k z ∈ B y := hz
      rcases mem_iUnion.1 hzB with ⟨x, hxB⟩
      rcases mem_iUnion.1 hxB with ⟨_hxuniv, hzV⟩
      have hzV' : S.projection (ix y x.1.1 x.1.2) z ∈ V y x.1.1 x.1.2 := by
        change S.map (hix_le_k y x.1 x.2) (S.projection k z) ∈ V y x.1.1 x.1.2 at hzV
        rw [S.projection_compatible z (ix y x.1.1 x.1.2) k (hix_le_k y x.1 x.2)] at hzV
        exact hzV
      exact hVsub y x.1.1 x.1.2 (by simpa using hzV')
  have hRangeClosed : IsClosed (Set.range (S.projection k)) := by
    exact (isCompact_range (S.continuous_projection k)).isClosed
  let Z : Y → Set (S.X k) := fun y => B y ∩ Set.range (S.projection k)
  have hZclosed : ∀ y, IsClosed (Z y) := by
    intro y
    exact (hBclopen y).1.inter hRangeClosed
  have hZdisj : Set.univ.PairwiseDisjoint Z := by
    intro y _ y' _ hyy'
    change Disjoint (Z y) (Z y')
    rw [Set.disjoint_left]
    intro z hz hz'
    rcases hz.2 with ⟨x, rfl⟩
    have hx : x ∈ Uy y := by
      rw [hUy_eq y]
      exact hz.1
    have hx' : x ∈ Uy y' := by
      rw [hUy_eq y']
      exact hz'.1
    have hxy : ρ x = y := by simpa [Uy] using hx
    have hxy' : ρ x = y' := by simpa [Uy] using hx'
    exact hyy' (hxy.symm.trans hxy')
  rcases exists_clopen_partition_of_clopen_cover
    (X := S.X k) (I := Y)
    (Z_closed := fun y => hZclosed y)
    (D_clopen := fun _ => isClopen_univ)
    (Z_subset_D := fun _ => by simp only [subset_univ, Z])
    (Z_disj := hZdisj) with ⟨C, hCclopen, hZsubsetC, _hCsubsetD, hcoverC, hCdisj⟩
  have hcoverC' : (Set.univ : Set (S.X k)) ⊆ ⋃ y, C y := by
    simpa using hcoverC
  have huniqC : ∀ z : S.X k, ∃! y, z ∈ C y := by
    intro z
    have hz : z ∈ ⋃ y, C y := hcoverC' (by simp only [mem_univ])
    rcases mem_iUnion.1 hz with ⟨y, hy⟩
    refine ⟨y, hy, ?_⟩
    intro y' hy'
    by_contra hne
    have hne' : y ≠ y' := by simpa [eq_comm] using hne
    have hdisj : Disjoint (C y) (C y') := hCdisj (by simp only [mem_univ]) (by simp only
        [mem_univ]) hne'
    exact (Set.disjoint_left.1 hdisj) hy hy'
  let ρ' : S.X k → Y := fun z => Classical.choose (huniqC z)
  have hρ' : Continuous ρ' := by
    rw [continuous_discrete_rng]
    intro y
    have hpre : ρ' ⁻¹' ({y} : Set Y) = C y := by
      ext z
      constructor
      · intro hz
        have hz' : z ∈ C (ρ' z) := (Classical.choose_spec (huniqC z)).1
        simpa [Set.mem_preimage, Set.mem_singleton_iff.mp hz] using hz'
      · intro hz
        have hchoose_eq : y = ρ' z := (Classical.choose_spec (huniqC z)).2 y hz
        simp only [hchoose_eq, mem_preimage, mem_singleton_iff]
    simpa [hpre] using (hCclopen y).2
  refine ⟨k, ρ', hρ', ?_⟩
  funext x
  change ρ x = ρ' (S.projection k x)
  have hxUy : x ∈ Uy (ρ x) := by
    simp only [mem_preimage, mem_singleton_iff, Uy]
  have hxB : S.projection k x ∈ B (ρ x) := by
    have : x ∈ S.projection k ⁻¹' B (ρ x) := by
      rw [← hUy_eq (ρ x)]
      exact hxUy
    exact this
  have hxZ : S.projection k x ∈ Z (ρ x) := ⟨hxB, ⟨x, rfl⟩⟩
  have hxC : S.projection k x ∈ C (ρ x) := hZsubsetC (ρ x) hxZ
  have hchoose_eq : ∀ y, S.projection k x ∈ C y → y = ρ' (S.projection k x) :=
    (Classical.choose_spec (huniqC (S.projection k x))).2
  exact hchoose_eq (ρ x) hxC



section

variable {I : Type u} [Preorder I] (S : InverseSystem (I := I))

/-- Finite-subset product stages inherit their product group structures. -/
instance finiteSubsetProductSystem_instGroup {α : Type u} (X : α → Type v)
    [∀ a, TopologicalSpace (X a)] [∀ a, Group (X a)] :
    ∀ s, Group ((finiteSubsetProductSystem X).X s) := by
  intro s
  classical
  dsimp [finiteSubsetProductSystem]
  infer_instance

/-- Finite-subset product stages inherit their product topological group structures. -/
instance finiteSubsetProductSystem_instIsTopologicalGroup {α : Type u} (X : α → Type v)
    [∀ a, TopologicalSpace (X a)] [∀ a, Group (X a)] [∀ a, IsTopologicalGroup (X a)] :
    ∀ s, IsTopologicalGroup ((finiteSubsetProductSystem X).X s) := by
  intro s
  classical
  dsimp [finiteSubsetProductSystem]
  exact Pi.topologicalGroup

/-- The finite-subset product system is a group-valued inverse system. -/
instance finiteSubsetProductSystem_instIsGroupSystem {α : Type u} (X : α → Type v)
    [∀ a, TopologicalSpace (X a)] [∀ a, Group (X a)] :
    IsGroupSystem (finiteSubsetProductSystem X) where
  map_one := by
    intro i j hij
    funext a
    change (1 : X a.1) = 1
    rfl
  map_mul := by
    intro i j hij x y
    funext a
    change
      x ⟨a.1, hij a.2⟩ * y ⟨a.1, hij a.2⟩ =
        x ⟨a.1, hij a.2⟩ * y ⟨a.1, hij a.2⟩
    rfl
  map_inv := by
    intro i j hij x
    funext a
    change (x ⟨a.1, hij a.2⟩)⁻¹ = (x ⟨a.1, hij a.2⟩)⁻¹
    rfl

/--
A continuous homomorphism from an inverse limit of profinite groups to a finite discrete group
factors through one of the projections.
-/
theorem InverseSystem.factors_through_projection_finite_group_hom [Nonempty I]
    [∀ i, Group (S.X i)] [IsGroupSystem S] [∀ i, IsTopologicalGroup (S.X i)]
    [∀ i, CompactSpace (S.X i)] [∀ i, T2Space (S.X i)]
    [∀ i, TotallyDisconnectedSpace (S.X i)]
    (hdir : Directed (· ≤ ·) (id : I → I))
    {H : Type w} [Group H] [TopologicalSpace H] [Finite H] [DiscreteTopology H]
    (β : S.inverseLimit →* H) (_hβ : Continuous β) :
    ∃ k : I, ∃ βk : S.X k →* H, Continuous βk ∧ β = βk ∘ S.projection k := by
  classical
  let rangeβ : S.inverseLimit → Set.range β := fun x => ⟨β x, ⟨x, rfl⟩⟩
  have hrangeβ_continuous : Continuous rangeβ := by
    exact Continuous.subtype_mk _hβ fun x => ⟨x, rfl⟩
  rcases S.factors_through_projection_finite hdir rangeβ hrangeβ_continuous with
      ⟨i0, β0range, hβ0range_continuous, hβ0range_fac⟩
  let β0 : S.X i0 → H := fun x => (β0range x).1
  have hβ0_continuous : Continuous β0 := continuous_subtype_val.comp hβ0range_continuous
  have hβ0_fac : β = β0 ∘ S.projection i0 := by
    funext x
    exact congrArg Subtype.val (congrFun hβ0range_fac x)
  let J : Set I := {i | i0 ≤ i}
  have hdirJ : Directed (· ≤ ·) (id : J → J) := by
    intro i j
    rcases hdir i.1 j.1 with ⟨k, hik, hjk⟩
    exact ⟨⟨k, i.2.trans hik⟩, hik, hjk⟩
  have hcofinal : ∀ i : I, ∃ j : J, i ≤ j.1 := by
    intro i
    rcases hdir i i0 with ⟨k, hik, hi0k⟩
    exact ⟨⟨k, hi0k⟩, hik⟩
  let βJ : ∀ j : J, S.X j.1 → H := fun j => β0 ∘ S.map j.2
  have hβJ_continuous : ∀ j : J, Continuous (βJ j) := by
    intro j
    dsimp [βJ]
    exact hβ0_continuous.comp (S.continuous_map j.2)
  have hβJ_map : ∀ {i j : J} (hij : i ≤ j) (x : S.X j.1), βJ i (S.map hij x) = βJ j x := by
    intro i j hij x
    dsimp [βJ, β0]
    calc
      (β0range (S.map i.2 (S.map hij x))).1 = (β0range (S.map (i.2.trans hij) x)).1 := by
        rw [S.map_comp_apply i.2 hij]
      _ = (β0range (S.map j.2 x)).1 := by
        have hproof : i.2.trans hij = j.2 := Subsingleton.elim _ _
        rw [hproof]
  have hβJ_fac : ∀ j : J, β = βJ j ∘ S.projection j.1 := by
    intro j
    funext x
    calc
      β x = β0 (S.projection i0 x) := by
        simpa [β0] using congrArg Subtype.val (congrFun hβ0range_fac x)
      _ = β0 (S.map j.2 (S.projection j.1 x)) := by rw [S.projection_compatible x i0 j.1 j.2]
      _ = βJ j (S.projection j.1 x) := rfl
  let η : S.inverseLimit × S.inverseLimit → H × H := fun xy =>
    (β xy.1 * β xy.2, β (xy.1 * xy.2))
  let Δ : Set (H × H) := {z | z.1 = z.2}
  have hη_delta : Set.range η ⊆ Δ := by
    intro z hz
    rcases hz with ⟨xy, rfl⟩
    exact (β.map_mul xy.1 xy.2).symm
  let E : J → Set (H × H) := fun j =>
    Set.range fun xy : S.X j.1 × S.X j.1 => (βJ j xy.1 * βJ j xy.2, βJ j (xy.1 * xy.2))
  have hE_mono : ∀ {i j : J}, i ≤ j → E j ⊆ E i := by
    intro i j hij z hz
    rcases hz with ⟨xy, rfl⟩
    refine ⟨(S.map hij xy.1, S.map hij xy.2), ?_⟩
    have h1 : βJ i (S.map hij xy.1) = βJ j xy.1 := hβJ_map hij xy.1
    have h2 : βJ i (S.map hij xy.2) = βJ j xy.2 := hβJ_map hij xy.2
    have h3 : βJ i (S.map hij xy.1 * S.map hij xy.2) = βJ j (xy.1 * xy.2) := by
      calc
        βJ i (S.map hij xy.1 * S.map hij xy.2)
            = βJ i (S.map hij (xy.1 * xy.2)) := by
                rw [IsGroupSystem.map_mul (S := S) hij xy.1 xy.2]
        _ = βJ j (xy.1 * xy.2) := hβJ_map hij (xy.1 * xy.2)
    apply Prod.ext
    · change βJ i (S.map hij xy.1) * βJ i (S.map hij xy.2) =
        βJ j xy.1 * βJ j xy.2
      rw [h1, h2]
    · exact h3
  have hrange_eta_subset_iInter : Set.range η ⊆ ⋂ j, E j := by
    intro z hz
    rcases hz with ⟨xy, rfl⟩
    rw [Set.mem_iInter]
    intro j
    refine ⟨(S.projection j.1 xy.1, S.projection j.1 xy.2), ?_⟩
    apply Prod.ext
    · have hx : β xy.1 = βJ j (S.projection j.1 xy.1) :=
        congrFun (hβJ_fac j) xy.1
      have hy : β xy.2 = βJ j (S.projection j.1 xy.2) :=
        congrFun (hβJ_fac j) xy.2
      change βJ j (S.projection j.1 xy.1) * βJ j (S.projection j.1 xy.2) =
        β xy.1 * β xy.2
      rw [← hx, ← hy]
    · calc
        βJ j (S.projection j.1 xy.1 * S.projection j.1 xy.2)
            = βJ j (S.projection j.1 (xy.1 * xy.2)) := by
                rw [projection_mul (S := S) j.1 xy.1 xy.2]
        _ = β (xy.1 * xy.2) := by
          simpa [Function.comp] using (congrFun (hβJ_fac j) (xy.1 * xy.2)).symm
  have hiInter_E_subset_range : (⋂ j, E j) ⊆ Set.range η := by
    intro z hz
    let Yset : ∀ j : J, Set (S.X j.1 × S.X j.1) := fun j =>
      {xy | (βJ j xy.1 * βJ j xy.2, βJ j (xy.1 * xy.2)) = z}
    have hYclosed : ∀ j : J, IsClosed (Yset j) := by
      intro j
      have hleft :
          Continuous fun xy : S.X j.1 × S.X j.1 => βJ j xy.1 * βJ j xy.2 :=
        ((hβJ_continuous j).comp continuous_fst).mul ((hβJ_continuous j).comp continuous_snd)
      have hright :
          Continuous fun xy : S.X j.1 × S.X j.1 => βJ j (xy.1 * xy.2) :=
        (hβJ_continuous j).comp continuous_mul
      exact isClosed_singleton.preimage (hleft.prodMk hright)
    let T : InverseSystem (I := J) := {
      X := fun j => Yset j
      topologicalSpace := fun _ => inferInstance
      map := fun {i j} hij xy =>
        ⟨(S.map hij xy.1.1, S.map hij xy.1.2), by
          have h1 : βJ i (S.map hij xy.1.1) = βJ j xy.1.1 := hβJ_map hij xy.1.1
          have h2 : βJ i (S.map hij xy.1.2) = βJ j xy.1.2 := hβJ_map hij xy.1.2
          have h3 : βJ i (S.map hij xy.1.1 * S.map hij xy.1.2) = βJ j (xy.1.1 * xy.1.2) := by
            calc
              βJ i (S.map hij xy.1.1 * S.map hij xy.1.2)
                  = βJ i (S.map hij (xy.1.1 * xy.1.2)) := by
                      rw [IsGroupSystem.map_mul (S := S) hij xy.1.1 xy.1.2]
              _ = βJ j (xy.1.1 * xy.1.2) := hβJ_map hij (xy.1.1 * xy.1.2)
          have hxy : (βJ j xy.1.1 * βJ j xy.1.2, βJ j (xy.1.1 * xy.1.2)) = z := by
            exact xy.2
          change
            (βJ i (S.map hij xy.1.1) * βJ i (S.map hij xy.1.2),
              βJ i (S.map hij xy.1.1 * S.map hij xy.1.2)) = z
          rw [h1, h2, h3]
          exact hxy⟩
      continuous_map := fun {i j} hij =>
        Continuous.subtype_mk
          (((S.continuous_map hij).comp (continuous_fst.comp continuous_subtype_val)).prodMk
            ((S.continuous_map hij).comp (continuous_snd.comp continuous_subtype_val)))
          (fun xy => by
            have h1 : βJ i (S.map hij xy.1.1) = βJ j xy.1.1 := hβJ_map hij xy.1.1
            have h2 : βJ i (S.map hij xy.1.2) = βJ j xy.1.2 := hβJ_map hij xy.1.2
            have h3 : βJ i (S.map hij xy.1.1 * S.map hij xy.1.2) = βJ j (xy.1.1 * xy.1.2) := by
              calc
                βJ i (S.map hij xy.1.1 * S.map hij xy.1.2)
                    = βJ i (S.map hij (xy.1.1 * xy.1.2)) := by
                        rw [IsGroupSystem.map_mul (S := S) hij xy.1.1 xy.1.2]
                _ = βJ j (xy.1.1 * xy.1.2) := hβJ_map hij (xy.1.1 * xy.1.2)
            have hxy : (βJ j xy.1.1 * βJ j xy.1.2, βJ j (xy.1.1 * xy.1.2)) = z := by
              exact xy.2
            change
              (βJ i (S.map hij xy.1.1) * βJ i (S.map hij xy.1.2),
                βJ i (S.map hij xy.1.1 * S.map hij xy.1.2)) = z
            rw [h1, h2, h3]
            exact hxy)
      map_id := fun j => by
        funext xy
        apply Subtype.ext
        apply Prod.ext
        · exact S.map_id_apply j.1 xy.1.1
        · exact S.map_id_apply j.1 xy.1.2
      map_comp := fun {i j k} hij hjk => by
        funext xy
        apply Subtype.ext
        apply Prod.ext
        · exact S.map_comp_apply hij hjk xy.1.1
        · exact S.map_comp_apply hij hjk xy.1.2 }
    have hzall : ∀ j : J, z ∈ E j := by
      rw [Set.mem_iInter] at hz
      exact hz
    have hnonemptyT : ∀ j : J, Nonempty (T.X j) := by
      intro j
      rcases hzall j with ⟨xy, hxy⟩
      exact ⟨⟨xy, hxy⟩⟩
    let : ∀ j : J, CompactSpace (T.X j) := fun j => by
      simpa [T] using (isCompact_iff_compactSpace.mp (hYclosed j).isCompact)
    rcases T.nonempty_inverseLimit hdirJ with ⟨u⟩
    let xlim : (S.restrict J).inverseLimit := by
      refine ⟨fun j => (u.1 j).1.1, ?_⟩
      intro i j hij
      exact congrArg Prod.fst (congrArg Subtype.val (u.2 i j hij))
    let ylim : (S.restrict J).inverseLimit := by
      refine ⟨fun j => (u.1 j).1.2, ?_⟩
      intro i j hij
      exact congrArg Prod.snd (congrArg Subtype.val (u.2 i j hij))
    let e := S.homeomorph_restrict_cofinal J hdirJ hcofinal
    let j0 : J := ⟨i0, le_rfl⟩
    let xj : S.X j0.1 := (S.restrict J).projection j0 xlim
    let yj : S.X j0.1 := (S.restrict J).projection j0 ylim
    have hu0 :
        (βJ j0 ((u.1 j0).1.1) * βJ j0 ((u.1 j0).1.2),
          βJ j0 (((u.1 j0).1.1) * ((u.1 j0).1.2))) = z := by
      exact (u.1 j0).2
    have hπx : (S.restrict J).projection j0 xlim = S.projection j0.1 (e.symm xlim) := by
      simpa [e, xlim] using
        congrFun (S.π_comp_homeomorph_restrict_cofinal J hdirJ hcofinal j0) (e.symm xlim)
    have hπy : (S.restrict J).projection j0 ylim = S.projection j0.1 (e.symm ylim) := by
      simpa [e, ylim] using
        congrFun (S.π_comp_homeomorph_restrict_cofinal J hdirJ hcofinal j0) (e.symm ylim)
    refine ⟨(e.symm xlim, e.symm ylim), ?_⟩
    apply Prod.ext
    · calc
        β (e.symm xlim) * β (e.symm ylim)
            = βJ j0 ((S.restrict J).projection j0 xlim) * βJ j0 ((S.restrict J).projection j0
                ylim) := by
                have hxβ : β (e.symm xlim) = βJ j0 ((S.restrict J).projection j0 xlim) := by
                  calc
                    β (e.symm xlim) = βJ j0 (S.projection j0.1 (e.symm xlim)) := by
                      simpa [Function.comp] using congrFun (hβJ_fac j0) (e.symm xlim)
                    _ = βJ j0 ((S.restrict J).projection j0 xlim) := by rw [← hπx]
                have hyβ : β (e.symm ylim) = βJ j0 ((S.restrict J).projection j0 ylim) := by
                  calc
                    β (e.symm ylim) = βJ j0 (S.projection j0.1 (e.symm ylim)) := by
                      simpa [Function.comp] using congrFun (hβJ_fac j0) (e.symm ylim)
                    _ = βJ j0 ((S.restrict J).projection j0 ylim) := by rw [← hπy]
                rw [hxβ, hyβ]
        _ = z.1 := by simpa [xlim, ylim] using congrArg Prod.fst hu0
    · calc
        β (e.symm xlim * e.symm ylim)
            = βJ j0 (S.projection j0.1 (e.symm xlim * e.symm ylim)) := by
                simpa [Function.comp] using congrFun (hβJ_fac j0) (e.symm xlim * e.symm ylim)
        _ = βJ j0 (S.projection j0.1 (e.symm xlim) * S.projection j0.1 (e.symm ylim)) := by
              rw [projection_mul (S := S) j0.1 (e.symm xlim) (e.symm ylim)]
        _ = βJ j0 (xj * yj) := by
              rw [← hπx, ← hπy]
        _ = z.2 := by
          have hsnd := congrArg Prod.snd hu0
          change
            βJ j0 (xj * yj) = z.2 at hsnd
          exact hsnd
  have hnot_iInter : ∀ {t : H × H}, t ∉ Set.range η → ∃ j : J, t ∉ E j := by
    intro t ht
    by_contra hno
    apply ht
    apply hiInter_E_subset_range
    rw [Set.mem_iInter]
    intro j
    by_contra htj
    exact hno ⟨j, htj⟩
  let j0 : J := ⟨i0, le_rfl⟩
  let jchoose : ∀ t : H × H, t ∉ Set.range η → J := fun t ht => Classical.choose (hnot_iInter ht)
  have hjchoose : ∀ t ht, t ∉ E (jchoose t ht) := by
    intro t ht
    exact Classical.choose_spec (hnot_iInter ht)
  let : Fintype H := Fintype.ofFinite H
  let used : Finset J := Finset.univ.image fun t : H × H =>
    if ht : t ∈ Set.range η then j0 else jchoose t ht
  have hused_nonempty : used.Nonempty := by
    refine ⟨if h : ((1 : H), (1 : H)) ∈ Set.range η then j0 else jchoose ((1 : H), (1 : H)) h, ?_⟩
    refine Finset.mem_image.mpr ?_
    exact ⟨((1 : H), (1 : H)), Finset.mem_univ _, by split_ifs <;> rfl⟩
  rcases exists_upperBound_finset (I := J) hdirJ used hused_nonempty with ⟨k, hk⟩
  have hrange_eta_subset_Ek : Set.range η ⊆ E k := by
    intro t ht
    have hmem : t ∈ ⋂ j, E j := hrange_eta_subset_iInter ht
    rw [Set.mem_iInter] at hmem
    exact hmem k
  have hEk_subset_range_eta : E k ⊆ Set.range η := by
    intro t ht
    by_cases htr : t ∈ Set.range η
    · exact htr
    · have hmem_used : (if ht' : t ∈ Set.range η then j0 else jchoose t ht') ∈ used := by
        refine Finset.mem_image.mpr ?_
        exact ⟨t, Finset.mem_univ _, by split_ifs; rfl⟩
      have hle : (if ht' : t ∈ Set.range η then j0 else jchoose t ht') ≤ k := hk _ hmem_used
      have ht' : t ∈ E (if ht' : t ∈ Set.range η then j0 else jchoose t ht') := hE_mono hle ht
      simp only [htr, ↓reduceDIte, hjchoose] at ht'
  have hEk_subset_delta : E k ⊆ Δ := by
    intro t ht
    exact hη_delta (hEk_subset_range_eta ht)
  let βkFun : S.X k.1 → H := βJ k
  have hβk_mul : ∀ x y : S.X k.1, βkFun (x * y) = βkFun x * βkFun y := by
    intro x y
    have hxy : (βkFun x * βkFun y, βkFun (x * y)) ∈ E k := ⟨(x, y), rfl⟩
    have hxyΔ : (βkFun x * βkFun y, βkFun (x * y)) ∈ Δ := hEk_subset_delta hxy
    simpa [Δ] using hxyΔ.symm
  have hβk_one : βkFun 1 = 1 := by
    have h := hβk_mul 1 1
    have h' := congrArg (fun t : H => t * (βkFun 1)⁻¹) h
    simpa [mul_assoc] using h'.symm
  let βk : S.X k.1 →* H :=
    { toFun := βkFun
      map_one' := hβk_one
      map_mul' := hβk_mul }
  have hβk_continuous : Continuous βk := by
    change Continuous βkFun
    exact hβJ_continuous k
  refine ⟨k.1, βk, hβk_continuous, ?_⟩
  exact hβJ_fac k

/--
A continuous additive homomorphism from an inverse limit of profinite additive groups to a
finite discrete additive group factors through one finite stage.
-/
theorem InverseSystem.factors_through_projection_finite_addMonoidHom [Nonempty I]
    [∀ i, AddCommGroup (S.X i)] [IsAddGroupSystem S] [∀ i, IsTopologicalAddGroup (S.X i)]
    [∀ i, CompactSpace (S.X i)] [∀ i, T2Space (S.X i)]
    [∀ i, TotallyDisconnectedSpace (S.X i)]
    (hdir : Directed (· ≤ ·) (id : I → I))
    {H : Type w} [AddCommGroup H] [TopologicalSpace H] [Finite H] [DiscreteTopology H]
    (β : S.inverseLimit →+ H) (hβ : Continuous β) :
    ∃ k : I, ∃ βk : S.X k →+ H, Continuous βk ∧ β = βk ∘ S.projection k := by
  classical
  let T : InverseSystem (I := I) :=
    { X := fun i => Multiplicative (S.X i)
      topologicalSpace := fun _ => inferInstance
      map := fun {i j} hij x => Multiplicative.ofAdd (S.map hij x.toAdd)
      continuous_map := fun {i j} hij => by
        let ei := additiveMultiplicativeHomeomorph (S.X i)
        let ej := additiveMultiplicativeHomeomorph (S.X j)
        exact ei.continuous_toFun.comp ((S.continuous_map hij).comp ej.continuous_invFun)
      map_id := fun i => by
        funext x
        apply Multiplicative.ext
        change S.map (le_rfl : i ≤ i) x.toAdd = x.toAdd
        exact S.map_id_apply i x.toAdd
      map_comp := fun {i j k} hij hjk => by
        funext x
        apply Multiplicative.ext
        change S.map hij (S.map hjk x.toAdd) = S.map (hij.trans hjk) x.toAdd
        exact S.map_comp_apply hij hjk x.toAdd }
  let : IsGroupSystem T :=
    { map_one := by
        intro i j hij
        apply Multiplicative.ext
        exact IsAddGroupSystem.map_zero (S := S) hij
      map_mul := by
        intro i j hij x y
        apply Multiplicative.ext
        exact IsAddGroupSystem.map_add (S := S) hij x.toAdd y.toAdd
      map_inv := by
        intro i j hij x
        apply Multiplicative.ext
        exact IsAddGroupSystem.map_neg (S := S) hij x.toAdd }
  let : ∀ i, T2Space (T.X i) := fun i =>
    (additiveMultiplicativeHomeomorph (S.X i)).t2Space
  let toAddLimit : T.inverseLimit → S.inverseLimit := fun x =>
    ⟨fun i => (T.projection i x).toAdd, by
      intro i j hij
      change S.map hij ((T.projection j x).toAdd) = (T.projection i x).toAdd
      exact congrArg Multiplicative.toAdd (T.projection_compatible x i j hij)⟩
  let toMulLimit : S.inverseLimit → T.inverseLimit := fun x =>
    ⟨fun i => Multiplicative.ofAdd (S.projection i x), by
      intro i j hij
      apply Multiplicative.ext
      change S.map hij (S.projection j x) = S.projection i x
      exact S.projection_compatible x i j hij⟩
  let toAddLimitMulHom : T.inverseLimit →* Multiplicative S.inverseLimit :=
    { toFun := fun x => Multiplicative.ofAdd (toAddLimit x)
      map_one' := by
        apply Multiplicative.ext
        apply S.ext
        intro i
        rfl
      map_mul' := by
        intro x y
        apply Multiplicative.ext
        apply S.ext
        intro i
        rfl }
  let βMul : T.inverseLimit →* Multiplicative H :=
    (AddMonoidHom.toMultiplicative β).comp toAddLimitMulHom
  have htoAddLimit_continuous : Continuous toAddLimit := by
    exact Continuous.subtype_mk
      (continuous_pi fun i =>
        (additiveMultiplicativeHomeomorph (S.X i)).continuous_invFun.comp
          (T.continuous_projection i))
      (fun x => (toAddLimit x).2)
  have hβMul_continuous : Continuous βMul := by
    change Continuous fun x => Multiplicative.ofAdd (β (toAddLimit x))
    exact (additiveMultiplicativeHomeomorph H).continuous_toFun.comp
      (hβ.comp htoAddLimit_continuous)
  let : Finite (Multiplicative H) := Finite.of_equiv H Multiplicative.ofAdd
  rcases T.factors_through_projection_finite_group_hom hdir βMul hβMul_continuous with
    ⟨k, γk, hγk_continuous, hγk_fac⟩
  let βk : S.X k →+ H :=
    { toFun := fun x => (γk (Multiplicative.ofAdd x)).toAdd
      map_zero' := by
        exact congrArg Multiplicative.toAdd γk.map_one
      map_add' := by
        intro x y
        exact congrArg Multiplicative.toAdd
          (γk.map_mul (Multiplicative.ofAdd x) (Multiplicative.ofAdd y)) }
  have hβk_continuous : Continuous βk := by
    change Continuous fun x : S.X k => (γk (Multiplicative.ofAdd x)).toAdd
    exact (additiveMultiplicativeHomeomorph H).continuous_invFun.comp
      (hγk_continuous.comp (additiveMultiplicativeHomeomorph (S.X k)).continuous_toFun)
  refine ⟨k, βk, hβk_continuous, ?_⟩
  funext x
  have hlim : toAddLimit (toMulLimit x) = x := by
    apply S.ext
    intro i
    rfl
  have hpoint := congrArg Multiplicative.toAdd (congrFun hγk_fac (toMulLimit x))
  have hleft : (βMul (toMulLimit x)).toAdd = β x := by
    simp only [MonoidHom.coe_comp, AddMonoidHom.coe_toMultiplicative, MonoidHom.coe_mk,
        OneHom.coe_mk,
  Function.comp_apply, hlim, toAdd_ofAdd, βMul, toAddLimitMulHom]
  have hright :
      (γk (T.projection k (toMulLimit x))).toAdd = βk (S.projection k x) := by
    rfl
  exact hleft.symm.trans (hpoint.trans hright)

end

end ProCGroups.InverseSystems
