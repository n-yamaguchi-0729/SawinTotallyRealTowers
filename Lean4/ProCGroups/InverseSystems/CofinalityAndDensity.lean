import ProCGroups.InverseSystems.CompatibilityAndSurjectivity

set_option autoImplicit false

/-!
# Cofinal reindexing, density, and projection neighborhoods

For inverse systems over directed preorders, this module controls neighborhoods by finitely many
coordinates and studies the map induced by a morphism on limits.  It proves density and
surjectivity criteria, invariance of the limit under cofinal reindexing or restriction, and the
projection-preimage basis for compact Hausdorff systems.
-/

open Set
open scoped Topology

namespace ProCGroups.InverseSystems

universe u v w

section

variable {I : Type u} [Preorder I]

attribute [instance] InverseSystem.topologicalSpace

namespace InverseSystem

variable (S : InverseSystem (I := I))

/--
Every open neighborhood in the inverse limit contains the inverse image of an open set along one
projection.
-/
theorem exists_projection_preimage_subset [Nonempty I]
    (hdir : Directed (· ≤ ·) (id : I → I)) {x : S.inverseLimit} {U : Set S.inverseLimit}
    (hU : IsOpen U) (hx : x ∈ U) :
    ∃ i, ∃ V : Set (S.X i), IsOpen V ∧ S.projection i x ∈ V ∧ S.projection i ⁻¹' V ⊆ U := by
  classical
  have hUx : U ∈ 𝓝 x := hU.mem_nhds hx
  rw [nhds_subtype_eq_comap, Filter.mem_comap] at hUx
  rcases hUx with ⟨W, hW, hWU⟩
  rw [mem_nhds_iff] at hW
  rcases hW with ⟨W', hW'W, hW'open, hxW'⟩
  rcases (isOpen_pi_iff.mp hW'open) x.1 hxW' with ⟨s, Us, hUs, hsW'⟩
  by_cases hs : s.Nonempty
  · rcases exists_upperBound_finset (I := I) hdir s hs with ⟨j, hj⟩
    let V : Set (S.X j) := ⋂ i ∈ s, if hi : i ∈ s then S.map (hj i hi) ⁻¹' Us i else univ
    refine ⟨j, V, ?_, ?_, ?_⟩
    · refine isOpen_biInter_finset fun i hi => ?_
      simpa [hi] using (hUs i hi).1.preimage (S.continuous_map (hj i hi))
    · change S.projection j x ∈ ⋂ i ∈ s, if hi : i ∈ s then S.map (hj i hi) ⁻¹' Us i else univ
      rw [Set.mem_iInter]
      intro i
      rw [Set.mem_iInter]
      intro hi
      have hxji : S.map (hj i hi) (S.projection j x) ∈ Us i := by
        rw [S.projection_compatible x i j (hj i hi)]
        exact (hUs i hi).2
      simpa [hi, Set.mem_preimage] using hxji
    · intro y hy
      apply hWU
      apply hW'W
      apply hsW'
      change S.projection j y ∈ ⋂ i ∈ s, if hi : i ∈ s then S.map (hj i hi) ⁻¹' Us i else univ at hy
      rw [Set.mem_iInter] at hy
      intro i hi
      have hyi : S.map (hj i hi) (S.projection j y) ∈ Us i := by
        have hyji := Set.mem_iInter.1 (hy i) hi
        have hif :
            (if hi' : i ∈ s then S.map (hj i hi') ⁻¹' Us i else univ) =
              S.map (hj i hi) ⁻¹' Us i := by
          ext z
          by_cases h : i ∈ s
          · rw [dif_pos h]
          · exact (h.elim hi)
        rw [hif] at hyji
        simpa [Set.mem_preimage] using hyji
      rw [S.projection_compatible y i j (hj i hi)] at hyi
      exact hyi
  · let j : I := Classical.choice ‹Nonempty I›
    refine ⟨j, univ, isOpen_univ, mem_univ _, ?_⟩
    intro y hy
    apply hWU
    apply hW'W
    apply hsW'
    have hs' : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    have : y.1 ∈ ((↑s : Set I).pi Us) := by
      simp only [hs', Finset.coe_empty, empty_pi, mem_univ]
    exact this

/--
A compatible family of surjections over a nonempty directed index preorder induces a dense map
to the inverse limit.
-/
theorem denseRange_lift {X : Type w} [Nonempty I]
    (ρ : ∀ i, X → S.X i) (hρ : S.CompatibleMaps ρ)
    (hsurj : ∀ i, Function.Surjective (ρ i)) (hdir : Directed (· ≤ ·) (id : I → I)) :
    DenseRange (S.inverseLimitLift ρ hρ) := by
  rw [DenseRange, dense_iff_inter_open]
  intro U hU hUne
  rcases hUne with ⟨y, hyU⟩
  rcases S.exists_projection_preimage_subset hdir hU hyU with ⟨i, V, hVopen, hyV, hVU⟩
  rcases hsurj i (S.projection i y) with ⟨x, hx⟩
  refine ⟨S.inverseLimitLift ρ hρ x, hVU ?_, ⟨x, rfl⟩⟩
  change ρ i x ∈ V
  rw [hx]
  exact hyV

/-- Reindexing an inverse system along a monotone map. -/
def reindex {K : Type w} [Preorder K] (σ : K → I) (hσ : Monotone σ) :
    InverseSystem (I := K) where
  X := fun k => S.X (σ k)
  topologicalSpace := fun k => inferInstance
  map := fun {i j} hij => S.map (hσ hij)
  continuous_map := fun {i j} hij => S.continuous_map (hσ hij)
  map_id := fun k => by
    simpa using S.map_id (σ k)
  map_comp := fun {i j k} hij hjk => by
    simpa using S.map_comp (hσ hij) (hσ hjk)

/-- The inverse system obtained by restricting the index preorder to a subset. -/
def restrict (J : Set I) : InverseSystem (I := J) :=
  S.reindex (fun j : J => j.1) (fun {_ _} hij => hij)

/-- The inverse limit is unchanged after reindexing along a monotone cofinal map. -/
noncomputable def homeomorph_reindex_cofinal {K : Type w} [Preorder K]
    (σ : K → I) (hσ : Monotone σ) (hdirK : Directed (· ≤ ·) (id : K → K))
    (hcofinal : ∀ i : I, ∃ k : K, i ≤ σ k) :
    S.inverseLimit ≃ₜ (S.reindex σ hσ).inverseLimit := by
  classical
  let R := S.reindex σ hσ
  have hcompatR : R.CompatibleMaps (fun k => S.projection (σ k)) := by
    intro i j hij
    funext x
    exact S.projection_compatible x (σ i) (σ j) (hσ hij)
  let r : S.inverseLimit → R.inverseLimit := R.inverseLimitLift (fun k => S.projection (σ k))
      hcompatR
  choose τ hτ using hcofinal
  let ψ : ∀ i, R.inverseLimit → S.X i := fun i => S.map (hτ i) ∘ R.projection (τ i)
  have hψ_eq :
      ∀ {i : I} (k : K) (hik : i ≤ σ k) (x : R.inverseLimit),
        ψ i x = S.map hik (R.projection k x) := by
    intro i k hik x
    rcases hdirK (τ i) k with ⟨ℓ, hτℓ, hkℓ⟩
    calc
      ψ i x = S.map (hτ i) (R.projection (τ i) x) := rfl
      _ = S.map (hτ i) (S.map (hσ hτℓ) (R.projection ℓ x)) := by
        simpa [R, reindex] using congrArg (S.map (hτ i)) ((R.projection_compatible x (τ i) ℓ
            hτℓ).symm)
      _ = S.map ((hτ i).trans (hσ hτℓ)) (R.projection ℓ x) := by
        exact S.map_comp_apply (hτ i) (hσ hτℓ) (R.projection ℓ x)
      _ = S.map (hik.trans (hσ hkℓ)) (R.projection ℓ x) := by
        have hproof : (hτ i).trans (hσ hτℓ) = hik.trans (hσ hkℓ) := Subsingleton.elim _ _
        rw [hproof]
      _ = S.map hik (S.map (hσ hkℓ) (R.projection ℓ x)) := by
        exact (S.map_comp_apply hik (hσ hkℓ) (R.projection ℓ x)).symm
      _ = S.map hik (R.projection k x) := by
        simpa [R, reindex] using congrArg (S.map hik) (R.projection_compatible x k ℓ hkℓ)
  have hcompatψ : S.CompatibleMaps ψ := by
    intro i j hij
    funext x
    calc
      S.map hij (ψ j x) = S.map hij (S.map (hτ j) (R.projection (τ j) x)) := rfl
      _ = S.map (hij.trans (hτ j)) (R.projection (τ j) x) := by
        exact S.map_comp_apply hij (hτ j) (R.projection (τ j) x)
      _ = ψ i x := by
        symm
        exact hψ_eq (k := τ j) (hik := hij.trans (hτ j)) x
  let s : R.inverseLimit → S.inverseLimit := S.inverseLimitLift ψ hcompatψ
  refine
    { toFun := r
      invFun := s
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := R.continuous_inverseLimitLift (fun k => S.projection (σ k))
        (fun k => S.continuous_projection (σ k)) hcompatR
      continuous_invFun := S.continuous_inverseLimitLift ψ
        (fun i => (S.continuous_map (hτ i)).comp (R.continuous_projection (τ i))) hcompatψ } <;>
    intro x
  · apply S.ext
    intro i
    calc
      S.projection i (s (r x)) = ψ i (r x) := by
        rfl
      _ = S.map (hτ i) (R.projection (τ i) (r x)) := rfl
      _ = S.map (hτ i) (S.projection (σ (τ i)) x) := by
        have hrproj :=
          R.projection_inverseLimitLift_apply
            (fun k => S.projection (σ k)) hcompatR (τ i) x
        change R.projection (τ i) (r x) = S.projection (σ (τ i)) x at hrproj
        exact congrArg (S.map (hτ i)) hrproj
      _ = S.projection i x := S.projection_compatible x i (σ (τ i)) (hτ i)
  · apply R.ext
    intro k
    have hrproj :=
      R.projection_inverseLimitLift_apply
        (fun k => S.projection (σ k)) hcompatR k (s x)
    change R.projection k (r (s x)) = S.projection (σ k) (s x) at hrproj
    have hsproj : S.projection (σ k) (s x) = ψ (σ k) x := rfl
    exact hrproj.trans (hsproj.trans
      ((hψ_eq (k := k) (hik := le_rfl) x).trans
        (S.map_id_apply (σ k) (R.projection k x))))

/--
After cofinal reindexing, the projection to \(k\) composed with the reindexing homeomorphism is
the original projection to \(\sigma k\).
-/
@[simp 900] theorem π_comp_homeomorph_reindex_cofinal {K : Type w} [Preorder K]
    (σ : K → I) (hσ : Monotone σ) (hdirK : Directed (· ≤ ·) (id : K → K))
    (hcofinal : ∀ i : I, ∃ k : K, i ≤ σ k) (k : K) :
    (S.reindex σ hσ).projection k ∘ S.homeomorph_reindex_cofinal σ hσ hdirK hcofinal =
        S.projection (σ k) := by
  classical
  let R := S.reindex σ hσ
  have hcompatR : R.CompatibleMaps (fun k => S.projection (σ k)) := by
    intro i j hij
    funext x
    exact S.projection_compatible x (σ i) (σ j) (hσ hij)
  funext x
  change
    R.projection k
        (R.inverseLimitLift (fun k => S.projection (σ k)) hcompatR x) =
      S.projection (σ k) x
  exact
    R.projection_inverseLimitLift_apply
      (fun k => S.projection (σ k)) hcompatR k x

/-- The cofinal reindexing homeomorphism is characterized by its projections. -/
noncomputable def homeomorph_restrict_cofinal (J : Set I)
    (hdirJ : Directed (· ≤ ·) (id : J → J)) (hcofinal : ∀ i, ∃ j : J, i ≤ j.1) :
    S.inverseLimit ≃ₜ (S.restrict J).inverseLimit :=
  S.homeomorph_reindex_cofinal (fun j : J => j.1) (fun {_ _} hij => hij) hdirJ hcofinal

/--
For a cofinal restriction, projecting to \(j\) after the restriction homeomorphism is the same
as the original projection to the underlying index of \(j\).
-/
@[simp 900] theorem π_comp_homeomorph_restrict_cofinal (J : Set I)
    (hdirJ : Directed (· ≤ ·) (id : J → J)) (hcofinal : ∀ i, ∃ j : J, i ≤ j.1) (j : J) :
    (S.restrict J).projection j ∘ S.homeomorph_restrict_cofinal J hdirJ hcofinal = S.projection
        j.1 := by
  exact
    (S.π_comp_homeomorph_reindex_cofinal (σ := fun j : J => j.1)
      (hσ := fun {_ _} hij => hij) hdirJ hcofinal j)

/--
In a surjective inverse system of compact Hausdorff nonempty spaces, each projection from the
inverse limit is surjective.
-/
theorem surjective_π [∀ i, CompactSpace (S.X i)] [∀ i, T2Space (S.X i)]
    (hdir : Directed (· ≤ ·) (id : I → I))
    (hsurj : ∀ {i j : I} (hij : i ≤ j), Function.Surjective (S.map hij)) (j : I) :
    Function.Surjective (S.projection j) := by
  let J : Set I := Set.Ici j
  have hdirJ : Directed (· ≤ ·) (id : J → J) := by
    intro a b
    rcases hdir a.1 b.1 with ⟨k, hak, hbk⟩
    refine ⟨⟨k, a.2.trans hak⟩, hak, hbk⟩
  have hcofinal : ∀ i, ∃ k : J, i ≤ k.1 := by
    intro i
    rcases hdir i j with ⟨k, hik, hjk⟩
    exact ⟨⟨k, hjk⟩, hik⟩
  let e := S.homeomorph_restrict_cofinal J hdirJ hcofinal
  let j0 : J := ⟨j, le_rfl⟩
  intro xj
  let T : InverseSystem (I := J) := {
    X := fun k => {x : S.X k.1 // S.map k.2 x = xj}
    topologicalSpace := fun _ => inferInstance
    map := fun {a b} hab x =>
      ⟨S.map hab x.1, by
        have hproof : a.2.trans hab = b.2 := Subsingleton.elim _ _
        calc
          S.map a.2 (S.map hab x.1) = S.map (a.2.trans hab) x.1 := by rw [S.map_comp_apply a.2 hab]
          _ = S.map b.2 x.1 := by rw [hproof]
          _ = xj := x.2⟩
    continuous_map := fun {a b} hab =>
      Continuous.subtype_mk ((S.continuous_map hab).comp continuous_subtype_val) fun x => by
        have hproof : a.2.trans hab = b.2 := Subsingleton.elim _ _
        calc
          S.map a.2 (S.map hab x.1) = S.map (a.2.trans hab) x.1 := by rw [S.map_comp_apply a.2 hab]
          _ = S.map b.2 x.1 := by rw [hproof]
          _ = xj := x.2
    map_id := fun a => by
      funext x
      apply Subtype.ext
      simp only [map_id_apply, id_eq]
    map_comp := fun {a b c} hab hbc => by
      funext x
      apply Subtype.ext
      simp only [Function.comp_apply, S.map_comp_apply hab hbc]}
  let : ∀ k, Nonempty (T.X k) := fun k => by
    rcases hsurj k.2 xj with ⟨x, hx⟩
    exact ⟨⟨x, hx⟩⟩
  let : ∀ k, T2Space (T.X k) := fun _ => inferInstance
  let : ∀ k, CompactSpace (T.X k) := fun k => by
    let hs : IsClosed {x : S.X k.1 | S.map k.2 x = xj} :=
      isClosed_eq (S.continuous_map k.2) continuous_const
    change CompactSpace {x : S.X k.1 // S.map k.2 x = xj}
    exact hs.isClosedEmbedding_subtypeVal.compactSpace
  rcases InverseSystem.nonempty_inverseLimit (S := T) hdirJ with ⟨y⟩
  let xlimJ : (S.restrict J).inverseLimit := ⟨fun k => (y.1 k).1, by
    intro a b hab
    exact congrArg Subtype.val (y.2 a b hab)⟩
  have hj0 : (S.restrict J).projection j0 xlimJ = xj := by
    change (y.1 j0).1 = xj
    have hprop := (y.1 j0).2
    have hproof : j0.2 = (le_rfl : j ≤ j) := Subsingleton.elim _ _
    rw [hproof] at hprop
    exact (S.map_id_apply j (y.1 j0).1).symm.trans hprop
  have hstep : S.projection j (e.symm xlimJ) = (S.restrict J).projection j0 xlimJ := by
    have he :=
      congrFun (S.π_comp_homeomorph_restrict_cofinal J hdirJ hcofinal j0)
        (e.symm xlimJ)
    change
      (S.restrict J).projection j0 (e (e.symm xlimJ)) =
        S.projection j (e.symm xlimJ) at he
    rw [e.apply_symm_apply] at he
    exact he.symm
  refine ⟨e.symm xlimJ, ?_⟩
  rw [hstep]
  exact hj0

end InverseSystem
end

/--
If each component has a chosen basis, then the inverse images of basis elements under the
projection maps form a basis of the inverse limit.
-/
theorem InverseSystem.isTopologicalBasis_projection_preimages {I : Type u} [Preorder I]
    (S : InverseSystem (I := I)) [Nonempty I] (hdir : Directed (· ≤ ·) (id : I → I))
    (B : ∀ i, Set (Set (S.X i))) (hB : ∀ i, TopologicalSpace.IsTopologicalBasis (B i)) :
    TopologicalSpace.IsTopologicalBasis
      {W : Set S.inverseLimit | ∃ i, ∃ V ∈ B i, W = S.projection i ⁻¹' V} := by
  classical
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro W ⟨i, V, hV, rfl⟩
    exact ((hB i).isOpen hV).preimage (S.continuous_projection i)
  · intro x U hx hU
    rcases S.exists_projection_preimage_subset hdir hU hx with ⟨i, V, hVopen, hxV, hVU⟩
    rcases (hB i).exists_subset_of_mem_open hxV hVopen with ⟨W, hW, hxW, hWV⟩
    refine ⟨S.projection i ⁻¹' W, ⟨i, W, hW, rfl⟩, hxW, ?_⟩
    exact (Set.preimage_mono hWV).trans hVU

end ProCGroups.InverseSystems
