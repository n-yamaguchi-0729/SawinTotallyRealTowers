import ProCGroups.Generation.Convergence
import ProCGroups.Generation.GeneratorConvergingPairs
import ProCGroups.ProC.Quotients.ClosedNormal

set_option autoImplicit false

/-!
# Converging generators constructed through quotient refinements

`QuotientGeneratorConvergingPair` records a convergent generating family in a closed-normal
quotient together with coherent refinement maps.  Chain upper bounds and strict extensions feed
a maximality argument producing generators converging to one; the final results transport this
property and the resulting topological rank across surjections and continuous equivalences.
-/

open Set
open scoped Topology Pointwise

namespace ProCGroups.Generation

universe u v

open ProCGroups.InverseSystems
open ProCGroups.ProC

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

section Proposition244

/-- A quotient generator converging pair records compatible source and quotient generator data. -/
structure QuotientGeneratorConvergingPair where
  /-- The subgroup used to form the quotient carrying the generator family. -/
  N : Subgroup G
  /-- The quotienting subgroup is normal. -/
  normal_N : N.Normal
  /-- The quotienting subgroup is closed, so the quotient has the intended profinite topology. -/
  closed_N : IsClosed (N : Set G)
  /-- The distinguished generator set in `G ⧸ N`. -/
  Y : Set (G ⧸ N)
  /-- The quotient identity is excluded from the distinguished generator set. -/
  subset_compl : Y ⊆ ({1} : Set (G ⧸ N))ᶜ
  /-- The generator set converges to the quotient identity along open subgroups. -/
  converges : ConvergesToOneAlongOpenSubgroups (G := G ⧸ N) Y
  /-- The distinguished set topologically generates the entire quotient `G ⧸ N`. -/
  generates : TopologicallyGenerates (G := G ⧸ N) Y

attribute [instance] QuotientGeneratorConvergingPair.normal_N

/-- The source set is the set of generators carried by the quotient generator pair. -/
def QuotientGeneratorConvergingPair.sourceSet
    (A : QuotientGeneratorConvergingPair (G := G)) :
    Set (G ⧸ A.N) :=
  ({1} : Set (G ⧸ A.N)) ∪ A.Y

/--
The source of a quotient generator-converging pair consists of the original group, index data,
and generator family before passage to the quotient.
-/
abbrev QuotientGeneratorConvergingPair.Source
    (A : QuotientGeneratorConvergingPair (G := G)) :=
  ↥(A.sourceSet)

/--
The constructed object carries the topological space structure inherited from its construction.
-/
instance instTopologicalSpaceQuotientGeneratorConvergingPairSource
    (A : QuotientGeneratorConvergingPair (G := G)) :
    TopologicalSpace A.Source :=
  inferInstanceAs (TopologicalSpace ↥(A.sourceSet))

/-- The identity element belongs to the source data of the quotient generator pair. -/
def QuotientGeneratorConvergingPair.sourceOne
    (A : QuotientGeneratorConvergingPair (G := G)) : A.Source :=
  ⟨1, Or.inl rfl⟩

/-- The source of the selected generator is the source specified by the quotient generator pair. -/
def QuotientGeneratorConvergingPair.sourceOfY
    (A : QuotientGeneratorConvergingPair (G := G)) (y : A.Y) : A.Source :=
  ⟨y.1, Or.inr y.2⟩

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/--
Every source element of a quotient generator pair is either the distinguished identity source or
comes from an element of the generator set.
-/
theorem QuotientGeneratorConvergingPair.source_cases
    (A : QuotientGeneratorConvergingPair (G := G)) (x : A.Source) :
    x = A.sourceOne ∨ ∃ y : A.Y, x = A.sourceOfY y := by
  rcases x with ⟨x, hx⟩
  rcases hx with hx1 | hxY
  · left
    ext
    simpa [QuotientGeneratorConvergingPair.sourceOne] using hx1
  · right
    refine ⟨⟨x, hxY⟩, ?_⟩
    ext
    rfl

/--
The image of the distinguished generator set of one quotient generator pair under a chosen
source map into another quotient.
-/
def QuotientGeneratorConvergingPair.yImage
    (A B : QuotientGeneratorConvergingPair (G := G))
    (σ : A.Source → G ⧸ B.N) : Set (G ⧸ B.N) :=
  Set.range fun y : A.Y => σ (A.sourceOfY y)

/-- This relation orders quotient generator pairs by refinement of their quotient data. -/
def QuotientGeneratorConvergingPair.Le
    (A B : QuotientGeneratorConvergingPair (G := G)) : Prop :=
  ∃ hBA : B.N ≤ A.N,
    ∃ σ : A.Source → (G ⧸ B.N),
      Continuous σ ∧
      (∀ x : A.Source, leftQuotientProjection (B.N) (A.N) hBA (σ x) = x.1) ∧
      σ A.sourceOne = 1 ∧
      (∀ y : A.Y, σ (A.sourceOfY y) ∈ B.Y) ∧
      B.Y \ A.yImage B σ ⊆
        {q : G ⧸ B.N | leftQuotientProjection (B.N) (A.N) hBA q = 1}

/-- The order relation is the refinement relation on the corresponding data. -/
instance instLEQuotientGeneratorConvergingPair :
    LE (QuotientGeneratorConvergingPair (G := G)) where
  le := QuotientGeneratorConvergingPair.Le

/-- The preorder is induced by refinement of the corresponding data. -/
instance instPreorderQuotientGeneratorConvergingPair :
    Preorder (QuotientGeneratorConvergingPair (G := G)) where
  le_refl A := by
    refine ⟨le_rfl, Subtype.val, ?_, ?_, rfl, ?_, ?_⟩
    · change Continuous (fun x : A.Source => (x : G ⧸ A.N))
      exact continuous_subtype_val
    · intro q
      simp only [leftQuotientProjection_id, id_eq]
    · intro y
      simp only [QuotientGeneratorConvergingPair.sourceOfY, Subtype.coe_prop]
    · simp only [QuotientGeneratorConvergingPair.yImage, QuotientGeneratorConvergingPair.sourceOfY,
  Subtype.range_coe_subtype, ofPred_mem_eq, sdiff_self, leftQuotientProjection_id, id_eq,
  ofPred_eq_eq_singleton, subset_singleton_iff, mem_empty_iff_false, IsEmpty.forall_iff,
      implies_true]
  le_trans A B C hAB hBC := by
    classical
    rcases hAB with ⟨hBA, σAB, hσABcont, hσABright, hσABone, hσABmem, hσABdiff⟩
    rcases hBC with ⟨hCB, σBC, hσBCcont, hσBCright, hσBCone, hσBCmem, hσBCdiff⟩
    let τ : A.Source → B.Source := fun x =>
      ⟨σAB x, by
        rcases A.source_cases x with h1 | ⟨y, rfl⟩
        · rw [h1]
          exact Or.inl hσABone
        · exact Or.inr (hσABmem y)⟩
    have hτcont : Continuous τ := by
      exact hσABcont.subtype_mk <| by
        intro x
        rcases A.source_cases x with h1 | ⟨y, rfl⟩
        · rw [h1]
          exact Or.inl hσABone
        · exact Or.inr (hσABmem y)
    have hτone : τ A.sourceOne = B.sourceOne := by
      apply Subtype.ext
      exact hσABone
    have hτofY (y : A.Y) :
        τ (A.sourceOfY y) = B.sourceOfY ⟨σAB (A.sourceOfY y), hσABmem y⟩ := by
      apply Subtype.ext
      rfl
    have hEqBC :
        ∀ (y : B.Y) {q : G ⧸ C.N},
          q ∈ C.Y →
          leftQuotientProjection (C.N) (B.N) hCB q = y.1 →
            q = σBC (B.sourceOfY y) := by
      intro y q hqY hqproj
      by_cases hqim : q ∈ B.yImage C σBC
      · rcases hqim with ⟨y', hy'Eq⟩
        have hproj' :
            leftQuotientProjection (C.N) (B.N) hCB q = y'.1 := by
          calc
            leftQuotientProjection (C.N) (B.N) hCB q =
                leftQuotientProjection (C.N) (B.N) hCB
                  (σBC (B.sourceOfY y')) := congrArg
                    (leftQuotientProjection (C.N) (B.N) hCB) hy'Eq.symm
            _ = y'.1 := by
              exact hσBCright (B.sourceOfY y')
        have hyEq : y' = y := by
          apply Subtype.ext
          exact hproj'.symm.trans hqproj
        simpa [hyEq] using hy'Eq.symm
      · have hker :
          leftQuotientProjection (C.N) (B.N) hCB q = 1 := hσBCdiff ⟨hqY, hqim⟩
        have hyne : y.1 ≠ 1 := by
          simpa using B.subset_compl y.2
        exact False.elim (hyne (hqproj.symm.trans hker))
    refine ⟨hCB.trans hBA, fun x => σBC (τ x), hσBCcont.comp hτcont, ?_, ?_, ?_, ?_⟩
    · intro x
      calc
        leftQuotientProjection (C.N) (A.N) (hCB.trans hBA) (σBC (τ x)) =
            leftQuotientProjection (B.N) (A.N) hBA
              (leftQuotientProjection (C.N) (B.N) hCB (σBC (τ x))) := by
                exact leftQuotientProjection_comp_apply_symm
                  (K := (C.N : Subgroup G)) (H := (B.N : Subgroup G))
                  (L := (A.N : Subgroup G)) hCB hBA (σBC (τ x))
        _ = leftQuotientProjection (B.N) (A.N) hBA ((τ x).1) := by
              rw [hσBCright (τ x)]
        _ = leftQuotientProjection (B.N) (A.N) hBA (σAB x) := by
              rfl
        _ = x.1 := hσABright x
    · simpa [hτone] using hσBCone
    · intro y
      let yB : B.Y := ⟨σAB (A.sourceOfY y), hσABmem y⟩
      simpa [hτofY, yB] using hσBCmem yB
    · intro q hq
      rcases hq with ⟨hqY, hqnotAC⟩
      by_cases hqimB : q ∈ B.yImage C σBC
      · rcases hqimB with ⟨z, hzEq⟩
        have hzNotInA : z.1 ∉ A.yImage B σAB := by
          intro hzInA
          rcases hzInA with ⟨y, hyEq⟩
          let yB : B.Y := ⟨σAB (A.sourceOfY y), hσABmem y⟩
          have hprojqz :
              leftQuotientProjection (C.N) (B.N) hCB q = z.1 := by
            calc
              leftQuotientProjection (C.N) (B.N) hCB q =
                  leftQuotientProjection (C.N) (B.N) hCB
                    (σBC (B.sourceOfY z)) := congrArg
                      (leftQuotientProjection (C.N) (B.N) hCB) hzEq.symm
              _ = z.1 := by
                exact hσBCright (B.sourceOfY z)
          have hprojq :
              leftQuotientProjection (C.N) (B.N) hCB q = yB.1 := by
            calc
              leftQuotientProjection (C.N) (B.N) hCB q = z.1 := hprojqz
              _ = yB.1 := by
                    simpa [yB] using hyEq.symm
          have hqEq : q = σBC (B.sourceOfY yB) := hEqBC yB hqY hprojq
          have hqInAC : q ∈ A.yImage C (fun x => σBC (τ x)) := by
            refine ⟨y, ?_⟩
            simpa [hτofY] using hqEq.symm
          exact hqnotAC hqInAC
        have hzProjA :
            leftQuotientProjection (B.N) (A.N) hBA z.1 = 1 :=
          hσABdiff ⟨z.2, hzNotInA⟩
        have hprojqB :
            leftQuotientProjection (C.N) (B.N) hCB q = z.1 := by
          calc
            leftQuotientProjection (C.N) (B.N) hCB q =
                leftQuotientProjection (C.N) (B.N) hCB
                  (σBC (B.sourceOfY z)) := congrArg
                    (leftQuotientProjection (C.N) (B.N) hCB) hzEq.symm
            _ = z.1 := by
              exact hσBCright (B.sourceOfY z)
        calc
          leftQuotientProjection (C.N) (A.N) (hCB.trans hBA) q =
              leftQuotientProjection (B.N) (A.N) hBA
                (leftQuotientProjection (C.N) (B.N) hCB q) := by
                  exact leftQuotientProjection_comp_apply_symm
                    (K := (C.N : Subgroup G)) (H := (B.N : Subgroup G))
                    (L := (A.N : Subgroup G)) hCB hBA q
          _ = leftQuotientProjection (B.N) (A.N) hBA z.1 := by
                rw [hprojqB]
          _ = 1 := hzProjA
      · have hprojqB :
          leftQuotientProjection (C.N) (B.N) hCB q = 1 := hσBCdiff ⟨hqY, hqimB⟩
        calc
          leftQuotientProjection (C.N) (A.N) (hCB.trans hBA) q =
              leftQuotientProjection (B.N) (A.N) hBA
                (leftQuotientProjection (C.N) (B.N) hCB q) := by
                  exact leftQuotientProjection_comp_apply_symm
                    (K := (C.N : Subgroup G)) (H := (B.N : Subgroup G))
                    (L := (A.N : Subgroup G)) hCB hBA q
          _ = leftQuotientProjection (B.N) (A.N) hBA 1 := by
                rw [hprojqB]
          _ = 1 := by
                rfl

noncomputable section

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/--
The refinement relation includes the required compatibility between the source and target
quotient data.
-/
theorem QuotientGeneratorConvergingPair.le_hBA
    {A B : QuotientGeneratorConvergingPair (G := G)} (hAB : A ≤ B) :
    B.N ≤ A.N :=
  Classical.choose hAB

end

/-- The refinement relation provides the induced map between quotient generator pairs. -/
noncomputable def QuotientGeneratorConvergingPair.le_map
    {A B : QuotientGeneratorConvergingPair (G := G)} (hAB : A ≤ B) :
    A.Source → G ⧸ B.N :=
  Classical.choose (Classical.choose_spec hAB)

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/--
For a refinement of quotient generator pairs, the chosen lift map between source sets is
continuous.
-/
theorem QuotientGeneratorConvergingPair.le_map_continuous
    {A B : QuotientGeneratorConvergingPair (G := G)} (hAB : A ≤ B) :
    Continuous (A.le_map hAB) :=
  (Classical.choose_spec (Classical.choose_spec hAB)).1

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- The quotient generator pair is compatible with the specified quotient map. -/
@[simp] theorem QuotientGeneratorConvergingPair.le_map_right
    {A B : QuotientGeneratorConvergingPair (G := G)} (hAB : A ≤ B)
    (x : A.Source) :
    leftQuotientProjection (B.N) (A.N) (A.le_hBA hAB) (A.le_map hAB x) = x.1 :=
  (Classical.choose_spec (Classical.choose_spec hAB)).2.1 x

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- A refinement map sends the distinguished source element over `1` to the identity. -/
@[simp] theorem QuotientGeneratorConvergingPair.le_map_one
    {A B : QuotientGeneratorConvergingPair (G := G)} (hAB : A ≤ B) :
    A.le_map hAB A.sourceOne = 1 :=
  (Classical.choose_spec (Classical.choose_spec hAB)).2.2.1

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/--
Under a refinement, the chosen lift map sends every distinguished generator of the smaller pair
into the distinguished set of the larger pair.
-/
@[simp] theorem QuotientGeneratorConvergingPair.le_map_mem
    {A B : QuotientGeneratorConvergingPair (G := G)} (hAB : A ≤ B)
    (y : A.Y) :
    A.le_map hAB (A.sourceOfY y) ∈ B.Y :=
  (Classical.choose_spec (Classical.choose_spec hAB)).2.2.2.1 y

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/--
Elements of the larger distinguished set not in the lifted image project to the identity in the
smaller quotient.
-/
theorem QuotientGeneratorConvergingPair.le_map_diff
    {A B : QuotientGeneratorConvergingPair (G := G)} (hAB : A ≤ B) :
    B.Y \ A.yImage B (A.le_map hAB) ⊆
      {q : G ⧸ B.N |
        leftQuotientProjection (B.N) (A.N) (A.le_hBA hAB) q = 1} :=
  (Classical.choose_spec (Classical.choose_spec hAB)).2.2.2.2

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- The quotient generator comparison respects membership and projection equality. -/
theorem QuotientGeneratorConvergingPair.eq_le_map_of_mem_of_proj_eq
    {A B : QuotientGeneratorConvergingPair (G := G)} (hAB : A ≤ B)
    (y : A.Y) {q : G ⧸ B.N}
    (hqY : q ∈ B.Y)
    (hqproj : leftQuotientProjection (B.N) (A.N) (A.le_hBA hAB) q = y.1) :
    q = A.le_map hAB (A.sourceOfY y) := by
  by_cases hqim : q ∈ A.yImage B (A.le_map hAB)
  · rcases hqim with ⟨y', hy'Eq⟩
    have hproj' :
          leftQuotientProjection (B.N) (A.N) (A.le_hBA hAB) q = y'.1 := by
            calc
              leftQuotientProjection (B.N) (A.N) (A.le_hBA hAB) q =
                  leftQuotientProjection (B.N) (A.N) (A.le_hBA hAB)
                    (A.le_map hAB (A.sourceOfY y')) := congrArg
                      (leftQuotientProjection (B.N) (A.N) (A.le_hBA hAB))
                      hy'Eq.symm
              _ = y'.1 := by
                exact A.le_map_right hAB (A.sourceOfY y')
    have hyEq : y' = y := by
      ext
      exact hproj'.symm.trans hqproj
    simpa [hyEq] using hy'Eq.symm
  · have hker :
      leftQuotientProjection (B.N) (A.N) (A.le_hBA hAB) q = 1 :=
      A.le_map_diff hAB ⟨hqY, hqim⟩
    have hyne : y.1 ≠ 1 := by
      simpa using A.subset_compl y.2
    exact False.elim (hyne (hqproj.symm.trans hker))

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- The induced map between quotient generator pairs is compatible with refinement. -/
theorem QuotientGeneratorConvergingPair.le_map_compat
    {A B C : QuotientGeneratorConvergingPair (G := G)}
    (hAB : A ≤ B) (hAC : A ≤ C) (hBC : B ≤ C)
    (y : A.Y) :
    leftQuotientProjection (C.N) (B.N) (B.le_hBA hBC)
      (A.le_map hAC (A.sourceOfY y)) =
      A.le_map hAB (A.sourceOfY y) := by
  have hCy :
      A.le_map hAC (A.sourceOfY y) ∈ C.Y := A.le_map_mem hAC y
  have hIn :
      A.le_map hAC (A.sourceOfY y) ∈ B.yImage C (B.le_map hBC) := by
    by_contra hNot
    have hker :
        leftQuotientProjection (C.N) (B.N) (B.le_hBA hBC)
          (A.le_map hAC (A.sourceOfY y)) = 1 :=
      B.le_map_diff hBC ⟨hCy, hNot⟩
    have hy1 : y.1 = 1 := by
      calc
        y.1 = leftQuotientProjection (C.N) (A.N) (A.le_hBA hAC)
              (A.le_map hAC (A.sourceOfY y)) := by
                exact (A.le_map_right hAC (A.sourceOfY y)).symm
        _ = leftQuotientProjection (B.N) (A.N) (A.le_hBA hAB)
              (leftQuotientProjection (C.N) (B.N) (B.le_hBA hBC)
                (A.le_map hAC (A.sourceOfY y))) := by
              exact
                (leftQuotientProjection_comp_apply_symm
                  (K := (C.N : Subgroup G)) (H := (B.N : Subgroup G))
                  (L := (A.N : Subgroup G)) (B.le_hBA hBC) (A.le_hBA hAB)
                  (A.le_map hAC (A.sourceOfY y)))
        _ = leftQuotientProjection (B.N) (A.N) (A.le_hBA hAB) 1 := by rw [hker]
        _ = 1 := by rfl
    have hyne : y.1 ≠ 1 := by
      simpa using A.subset_compl y.2
    exact hyne hy1
  rcases hIn with ⟨z, hzEq⟩
  have hqY :
      leftQuotientProjection (C.N) (B.N) (B.le_hBA hBC)
        (A.le_map hAC (A.sourceOfY y)) ∈ B.Y := by
    have hEq :
        leftQuotientProjection (C.N) (B.N) (B.le_hBA hBC)
          (A.le_map hAC (A.sourceOfY y)) = z.1 := by
      calc
        leftQuotientProjection (C.N) (B.N) (B.le_hBA hBC)
            (A.le_map hAC (A.sourceOfY y)) =
            leftQuotientProjection (C.N) (B.N) (B.le_hBA hBC)
              (B.le_map hBC (B.sourceOfY z)) := congrArg
                (leftQuotientProjection (C.N) (B.N) (B.le_hBA hBC))
                hzEq.symm
        _ = z.1 := by
          exact B.le_map_right hBC (B.sourceOfY z)
    exact hEq ▸ z.2
  have hqproj :
      leftQuotientProjection (B.N) (A.N) (A.le_hBA hAB)
        (leftQuotientProjection (C.N) (B.N) (B.le_hBA hBC)
          (A.le_map hAC (A.sourceOfY y))) = y.1 := by
    exact (leftQuotientProjection_comp_apply
      (K := (C.N : Subgroup G)) (H := (B.N : Subgroup G))
      (L := (A.N : Subgroup G)) (B.le_hBA hBC) (A.le_hBA hAB)
      (A.le_map hAC (A.sourceOfY y))).trans
      (A.le_map_right hAC (A.sourceOfY y))
  exact A.eq_le_map_of_mem_of_proj_eq hAB y hqY hqproj

omit [T2Space G] in
/-- The range subtype of a pointed map contains the chosen basepoint. -/
theorem ConvergesToOneAlongOpenSubgroups.range_subtype_pointed
    {H : Type v} [Group H] [TopologicalSpace H]
    {X : Set G}
    {f : ↥((({1} : Set G) ∪ X)) → H}
    (hf : Continuous f)
    (hf1 : f ⟨1, Or.inl rfl⟩ = 1)
    (hX : ConvergesToOneAlongOpenSubgroups (G := G) X) :
    ConvergesToOneAlongOpenSubgroups (G := H)
      (Set.range fun x : X => f ⟨x.1, Or.inr x.2⟩) := by
  let S : Set G := ({1} : Set G) ∪ X
  let g : X → H := fun x => f ⟨x.1, Or.inr x.2⟩
  intro U
  have hpre : IsOpen (f ⁻¹' (U : Set H)) :=
    (openSubgroup_isOpen (G := H) U).preimage hf
  have h1pre : (⟨1, Or.inl rfl⟩ : ↥S) ∈ f ⁻¹' (U : Set H) := by
    change f ⟨1, Or.inl rfl⟩ ∈ U
    rw [hf1]
    exact U.one_mem'
  rcases isOpen_induced_iff.mp hpre with ⟨W, hWopen, hWeq⟩
  have h1W : (1 : G) ∈ W := by
    have : (⟨1, Or.inl rfl⟩ : ↥S) ∈ Subtype.val ⁻¹' W := by
      exact hWeq.symm ▸ h1pre
    simpa using this
  rcases exists_openNormalSubgroup_sub_open_nhds_of_one (G := G) hWopen h1W with ⟨V, hVW⟩
  have hsubset :
      Set.range g \ (U : Set H) ⊆ g '' {x : X | (x : G) ∉ (V : Set G)} := by
    intro y hy
    rcases hy with ⟨hyY, hyU⟩
    rcases hyY with ⟨x, rfl⟩
    refine ⟨x, ?_, rfl⟩
    intro hxV
    have hxW : (x : G) ∈ W := hVW hxV
    have hxpre : (⟨x.1, Or.inr x.2⟩ : ↥S) ∈ Subtype.val ⁻¹' W := by
      change (x : G) ∈ W
      exact hxW
    have hxpreU : (⟨x.1, Or.inr x.2⟩ : ↥S) ∈ f ⁻¹' (U : Set H) := by
      exact hWeq ▸ hxpre
    have : g x ∈ (U : Set H) := by
      change f ⟨x.1, Or.inr x.2⟩ ∈ U
      exact hxpreU
    exact hyU this
  have hfinite_pre : {x : X | (x : G) ∉ (V : Set G)}.Finite := by
    let e : X ↪ G := ⟨Subtype.val, Subtype.val_injective⟩
    have hfinite : (X \ (V : Set G)).Finite := hX V.toOpenSubgroup
    have hfinite' : {x : X | e x ∈ X ∧ e x ∉ (V : Set G)}.Finite := by
      simpa [Set.preimage] using hfinite.preimage_embedding e
    have hEq : {x : X | e x ∈ X ∧ e x ∉ (V : Set G)} = {x : X | (x : G) ∉ (V : Set G)} := by
      ext x
      simp only [Function.Embedding.coeFn_mk, Subtype.coe_prop, SetLike.mem_coe, true_and,
          mem_ofPred_eq, e]
    exact hEq ▸ hfinite'
  exact hfinite_pre.image g |>.subset hsubset

omit [T2Space G] [TotallyDisconnectedSpace G] in
/--
The quotient generator-converging-pair construction is compatible with open-normal finite
quotients and refinement maps.
-/
theorem exists_quotientPair_le_openSubgroup_of_chain_iInf_le
    {c : Set (QuotientGeneratorConvergingPair (G := G))}
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
      have hne' : (a : QuotientGeneratorConvergingPair (G := G)) ≠ b := by
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
      exact (QuotientGeneratorConvergingPair.le_hBA (hmax p hp)) hx
    exact hs hx'
  · rcases hcne with ⟨p, hp⟩
    refine ⟨⟨p, hp⟩, ?_⟩
    have htop : ((⊤ : Subgroup G) : Set G) ⊆ ((U : Subgroup G) : Set G) := by
      have :
          (⋂ p ∈ s, (((p.1.N : Subgroup G) : Set G))) ⊆ ((U : Subgroup G) : Set G) := hs
      simpa [Finset.not_nonempty_iff_eq_empty.mp hsne] using this
    intro x hx
    exact htop (by simp only [Subgroup.coe_top, mem_univ])

omit [T2Space G] [TotallyDisconnectedSpace G] in
/--
A chain of quotient generator pairs has a refinement lifting to the intersection of its kernels.
-/
theorem quotientGeneratorPair_exists_liftToInf
    {c : Set (QuotientGeneratorConvergingPair (G := G))}
    (hc : IsChain (· ≤ ·) c) (a : c) :
    let K : Subgroup G := iInf fun p : c => p.1.N
    letI : K.Normal := Subgroup.normal_iInf_normal fun p : c => p.1.normal_N
    ∃ σ : a.1.Source → G ⧸ K,
      Continuous σ ∧
      (∀ b : c, ∀ hab : a.1 ≤ b.1,
        leftQuotientProjection K b.1.N
          (iInf_le (fun p : c => p.1.N) b) ∘ σ =
          a.1.le_map hab) ∧
      σ a.1.sourceOne = 1 := by
  classical
  intro K
  have : K.Normal := Subgroup.normal_iInf_normal fun p : c => p.1.normal_N
  let Tail := {b : c // a.1 ≤ b.1}
  have : Nonempty Tail := ⟨⟨a, le_rfl⟩⟩
  let L : Tail → ClosedSubgroup G := fun b =>
    ⟨b.1.1.N, b.1.1.closed_N⟩
  have hL : ∀ {i j : Tail}, i ≤ j → (L j : Subgroup G) ≤ (L i : Subgroup G) := by
    intro i j hij
    exact QuotientGeneratorConvergingPair.le_hBA hij
  have hdir : Directed (· ≤ ·) (id : Tail → Tail) := by
    intro i j
    by_cases hij : i ≤ j
    · exact ⟨j, hij, le_rfl⟩
    · have hji : j ≤ i := by
        by_cases hEq : i = j
        · exact hEq ▸ le_rfl
        · rcases hc i.1.2 j.1.2 (by
            intro h
            exact hEq (Subtype.ext (Subtype.ext h))) with hij' | hji'
          · exact False.elim (hij hij')
          · exact hji'
      exact ⟨i, le_rfl, hji⟩
  let η : ∀ b : Tail, a.1.Source → G ⧸ (L b : Subgroup G) := fun b =>
    a.1.le_map b.2
  have hηcont : ∀ b : Tail, Continuous (η b) := by
    intro b
    exact a.1.le_map_continuous b.2
  have hηcompat : ∀ {i j : Tail} (hij : i ≤ j),
      leftQuotientProjection (L j : Subgroup G) (L i : Subgroup G) (hL hij) ∘ η j = η i := by
    intro i j hij
    funext x
    rcases a.1.source_cases x with rfl | ⟨y, rfl⟩
    · have h1j : η j a.1.sourceOne = 1 := by
        change a.1.le_map j.2 a.1.sourceOne = 1
        exact a.1.le_map_one j.2
      have h1i : η i a.1.sourceOne = 1 := by
        change a.1.le_map i.2 a.1.sourceOne = 1
        exact a.1.le_map_one i.2
      calc
        (leftQuotientProjection (L j : Subgroup G) (L i : Subgroup G) (hL hij) ∘ η j)
            a.1.sourceOne
            = leftQuotientProjection (L j : Subgroup G) (L i : Subgroup G) (hL hij)
                (η j a.1.sourceOne) := by
                    simp only [Function.comp]
        _ = leftQuotientProjection (L j : Subgroup G) (L i : Subgroup G) (hL hij) 1 := by
              rw [h1j]
        _ = 1 := by rfl
        _ = η i a.1.sourceOne := by rw [h1i]
    · simpa [η] using a.1.le_map_compat i.2 j.2 hij y
  have hηone : ∀ b : Tail, η b a.1.sourceOne = 1 := by
    intro b
    change a.1.le_map b.2 a.1.sourceOne = 1
    exact a.1.le_map_one b.2
  obtain ⟨ηinf, hηinf_continuous, hηinf_fac, hηinf_one⟩ :=
    exists_continuous_leftQuotient_lift_of_directed
      (G := G) L hL hdir η hηcont hηcompat a.1.sourceOne hηone
  let H : Subgroup G := ((closedSubgroup_sInf L : ClosedSubgroup G) : Subgroup G)
  have hKeq : H = K := by
    apply le_antisymm
    · refine le_iInf ?_
      intro p
      by_cases hap : a.1 ≤ p.1
      · exact iInf_le (fun b : Tail => (L b : Subgroup G)) ⟨p, hap⟩
      · have hKa :
          H ≤ a.1.N :=
          iInf_le (fun b : Tail => (L b : Subgroup G)) ⟨a, le_rfl⟩
        by_cases hEq : p = a
        · simpa [K, hEq] using hKa
        · rcases hc p.2 a.2 (by
            intro h
            exact hEq (Subtype.ext h)) with hpa | hap'
          · exact hKa.trans (QuotientGeneratorConvergingPair.le_hBA hpa)
          · exact False.elim (hap hap')
    · refine le_iInf ?_
      intro b
      exact iInf_le (fun p : c => p.1.N) b.1
  have : H.Normal := by
    exact Subgroup.normal_iInf_normal fun b : Tail => b.1.1.normal_N
  have hGoal :
      ∃ σ : a.1.Source → G ⧸ H,
        Continuous σ ∧
        (∀ b : c, ∀ hab : a.1 ≤ b.1,
          leftQuotientProjection H b.1.N
              (closedSubgroup_sInf_le (L := L) ⟨b, hab⟩) ∘ σ =
            a.1.le_map hab) ∧
        σ a.1.sourceOne = 1 := by
    refine ⟨ηinf, hηinf_continuous, ?_, hηinf_one⟩
    intro b hab
    simpa [Tail, L, η] using hηinf_fac ⟨b, hab⟩
  have hGoal' :
      ∃ σ : a.1.Source → G ⧸ H,
        Continuous σ ∧
        (∀ b : c, ∀ hab : a.1 ≤ b.1,
          leftQuotientProjection H b.1.N
              (hKeq.trans_le (iInf_le (fun p : c => p.1.N) b)) ∘ σ =
            a.1.le_map hab) ∧
        σ a.1.sourceOne = 1 := by
    rcases hGoal with ⟨σ, hσcont, hσfac, hσone⟩
    refine ⟨σ, hσcont, ?_, hσone⟩
    intro b hab
    simpa using hσfac b hab
  change
    ∃ σ : a.1.Source → G ⧸ K,
      Continuous σ ∧
      (∀ b : c, ∀ hab : a.1 ≤ b.1,
        leftQuotientProjection K b.1.N
          (iInf_le (fun p : c => p.1.N) b) ∘ σ =
          a.1.le_map hab) ∧
      σ a.1.sourceOne = 1
  let Data : Type _ := { J : Subgroup G // J.Normal ∧ ∀ b : c, J ≤ b.1.N }
  let P : Data → Prop := fun d =>
    letI : d.1.Normal := d.2.1
    ∃ σ : a.1.Source → G ⧸ d.1,
      Continuous σ ∧
      (∀ b : c, ∀ hab : a.1 ≤ b.1,
        leftQuotientProjection d.1 b.1.N (d.2.2 b) ∘ σ =
          a.1.le_map hab) ∧
      σ a.1.sourceOne = 1
  let dH : Data :=
    ⟨H, ⟨inferInstance, fun b => hKeq.trans_le (iInf_le (fun p : c => p.1.N) b)⟩⟩
  let dK : Data :=
    ⟨K, ⟨inferInstance, fun b => iInf_le (fun p : c => p.1.N) b⟩⟩
  have hd : dH = dK := by
    apply Subtype.ext
    exact hKeq
  have hPdH : P dH := by
    simpa [P, dH] using hGoal'
  have hPdK : P dK := by
    exact Eq.mp (congrArg P hd) hPdH
  simpa [P, dK] using hPdK

/-- The top quotient generator pair is the maximal object in the quotient-generator construction. -/
noncomputable def quotientGeneratorPairTop :
    QuotientGeneratorConvergingPair (G := G) where
  N := ⊤
  normal_N := by infer_instance
  closed_N := isClosed_univ
  Y := ∅
  subset_compl := by intro q hq; simp only [mem_empty_iff_false] at hq
  converges := by intro U; simp only [empty_sdiff, finite_empty]
  generates := by
    classical
    rw [TopologicallyGenerates]
    apply top_unique
    intro q hq
    rcases Quotient.exists_rep q with ⟨g, rfl⟩
    have hg1 : QuotientGroup.mk' (⊤ : Subgroup G) g = (1 : G ⧸ (⊤ : Subgroup G)) := by
      exact (QuotientGroup.eq_one_iff (N := (⊤ : Subgroup G)) g).2 (by simp only [Subgroup.mem_top])
    have hbot :
        QuotientGroup.mk' (⊤ : Subgroup G) g ∈ (⊥ : Subgroup (G ⧸ (⊤ : Subgroup G))) := by
      change QuotientGroup.mk' (⊤ : Subgroup G) g = (1 : G ⧸ (⊤ : Subgroup G))
      exact hg1
    simpa [Subgroup.closure_eq] using
      (Subgroup.le_topologicalClosure (⊥ : Subgroup (G ⧸ (⊤ : Subgroup G))) hbot)

/-- A nonmaximal quotient generator pair admits a strict extension refining its quotient data. -/
theorem quotientGeneratorPair_exists_strictExtension
    (p : QuotientGeneratorConvergingPair (G := G))
    (hne : p.N ≠ ⊥) :
    ∃ p' : QuotientGeneratorConvergingPair (G := G), p ≤ p' ∧ ¬ p' ≤ p := by
  classical
  rcases (Subgroup.ne_bot_iff_exists_ne_one).1 hne with ⟨m, hmne⟩
  have hmne' : (m : G) ≠ 1 := by
    intro hm1
    apply hmne
    ext
    simpa using hm1
  rcases exists_openNormalSubgroup_not_mem (G := G) hmne' with ⟨U, hmU⟩
  let N' : Subgroup G := (U : Subgroup G) ⊓ p.N
  have hN'closed : IsClosed (N' : Set G) := by
    exact (openNormalSubgroup_isClosed (G := G) U).inter p.closed_N
  have hN'proper : ¬ p.N ≤ N' := by
    intro hp
    exact hmU (hp m.2).1
  obtain ⟨σ, hσcont, hσright, hσone⟩ :=
    leftQuotientProjection_hasContinuousSection
      (G := G)
      ⟨N', hN'closed⟩
      ⟨p.N, p.closed_N⟩
      inf_le_right
  rcases exists_finite_subset_generating_subgroup_mod_openNormal (G := G)
      (M := p.N) (hMclosed := p.closed_N) U with ⟨T, hTfin, hTsub, hTgen⟩
  let Tbar : Set (G ⧸ N') := (QuotientGroup.mk' N') '' T
  let Y' : Set (G ⧸ N') := σ '' p.Y ∪ Tbar
  have hY'compl : Y' ⊆ ({1} : Set (G ⧸ N'))ᶜ := by
    intro q hq
    rcases hq with hq | hq
    · rcases hq with ⟨y, hy, rfl⟩
      intro hq1
      have hσy1 : σ y = 1 := by
        simpa using hq1
      have : y = 1 := by
        calc
          y = leftQuotientProjection (N') (p.N) inf_le_right (σ y) := (hσright y).symm
          _ = leftQuotientProjection (N') (p.N) inf_le_right 1 := by rw [hσy1]
          _ = 1 := rfl
      exact p.subset_compl hy this
    · rcases hq with ⟨t, ht, rfl⟩
      intro hq1
      have htN' : t ∈ N' := (QuotientGroup.eq_one_iff (N := N') t).1 hq1
      exact (hTsub ht).2 htN'
  have hY'conv : ConvergesToOneAlongOpenSubgroups (G := G ⧸ N') Y' := by
    have : TotallyDisconnectedSpace (G ⧸ p.N) :=
      ProCGroups.totallyDisconnectedSpace_quotient_closedNormal p.N p.closed_N
    intro V
    have hσconv :
        ((σ '' p.Y) \ (V : Set (G ⧸ N'))).Finite := by
      exact
        (ConvergesToOneAlongOpenSubgroups.image_of_continuous_pointed
          (G := G ⧸ p.N) (H := G ⧸ N')
          hσcont hσone p.converges) V
    have hTconv : (Tbar \ (V : Set (G ⧸ N'))).Finite :=
      (hTfin.image (QuotientGroup.mk' N')).subset (by
        intro q hq
        exact hq.1)
    exact (hσconv.union hTconv).subset (by
      intro q hq
      rcases hq with ⟨hqY, hqV⟩
      rcases hqY with hqσ | hqT
      · exact Or.inl ⟨hqσ, hqV⟩
      · exact Or.inr ⟨hqT, hqV⟩)
  have hY'gen :
      TopologicallyGenerates (G := G ⧸ N') Y' := by
    exact topologicallyGenerates_of_quotient_section_union_kernel
      (G := G) p.closed_N hN'closed inf_le_right
      p.generates hσright hTgen
  refine ⟨{ N := N'
            normal_N := by infer_instance
            closed_N := hN'closed
            Y := Y'
            subset_compl := hY'compl
            converges := hY'conv
            generates := hY'gen }, ?_, ?_⟩
  · let σ' : p.Source → G ⧸ N' := fun x => σ x.1
    refine ⟨inf_le_right, σ', ?_, ?_, ?_, ?_, ?_⟩
    · change Continuous (fun x : p.Source => σ x.1)
      exact hσcont.comp continuous_subtype_val
    · intro x
      exact hσright x.1
    · exact hσone
    · intro q
      exact Or.inl ⟨q.1, q.2, rfl⟩
    · intro q hq
      rcases hq with ⟨hqY', hqnotσ⟩
      rcases hqY' with hqσ | hqT
      · rcases hqσ with ⟨y, hy, rfl⟩
        exact False.elim (hqnotσ ⟨⟨y, hy⟩, rfl⟩)
      · rcases hqT with ⟨t, ht, rfl⟩
        have htN : t ∈ p.N := (hTsub ht).1
        simpa [leftQuotientProjection_mk] using
          (QuotientGroup.eq_one_iff (N := p.N) t).2 htN
  · intro hp'
    exact hN'proper hp'.1

/-- The closed-normal quotient section at the bottom subgroup is the identity section. -/
theorem closedNormalQuotientSection_bot_eq
    (hbotClosed : IsClosed (((⊥ : Subgroup G) : Set G))) :
    closedNormalQuotientSection (G := G)
      (N := (⊥ : Subgroup G)) hbotClosed =
      (quotientBotContinuousMulEquiv (G := G)).symm := by
  funext q
  apply (quotientBotContinuousMulEquiv (G := G)).injective
  have h1 :
      quotientBotContinuousMulEquiv (G := G)
        (closedNormalQuotientSection (G := G)
          (N := (⊥ : Subgroup G)) hbotClosed q) = q := by
    change quotientBotHomeomorph (G := G)
      (closedNormalQuotientSection (G := G) (N := (⊥ : Subgroup G)) hbotClosed q) = q
    exact (quotientBotHomeomorph_apply (G := G)
      (closedNormalQuotientSection (G := G) (N := (⊥ : Subgroup G)) hbotClosed q)).trans
      (closedNormalQuotientSection_rightInverse (G := G)
        (N := (⊥ : Subgroup G)) hbotClosed q)
  have h2 :
      quotientBotContinuousMulEquiv (G := G)
        ((quotientBotContinuousMulEquiv (G := G)).symm q) = q := by
    simp only [ContinuousMulEquiv.apply_symm_apply]
  exact h1.trans h2.symm

/-- The quotient generator pair maps its source set into the ambient generating set. -/
noncomputable def QuotientGeneratorConvergingPair.toAmbientSet
    (p : QuotientGeneratorConvergingPair (G := G)) : Set G :=
  closedNormalQuotientSection (G := G) (N := p.N) p.closed_N '' p.Y

/--
The ambient representatives attached to a quotient generator pair topologically generate and
converge to one.
-/
theorem QuotientGeneratorConvergingPair.toAmbientSet_generatesAndConvergesToOneAlongOpenSubgroups
    (p : QuotientGeneratorConvergingPair (G := G))
    (hbot : p.N = ⊥) :
    GeneratesAndConvergesToOneAlongOpenSubgroups (G := G) p.toAmbientSet := by
  rcases p with ⟨N, hNnormal, hNclosed, Y, hYcompl, hYconv, hYgen⟩
  cases hbot
  have hbotClosed : IsClosed (((⊥ : Subgroup G) : Set G)) :=
    (isClosed_singleton : IsClosed ({(1 : G)} : Set G))
  constructor
  · let e : (G ⧸ (⊥ : Subgroup G)) ≃ₜ* G := (quotientBotContinuousMulEquiv (G := G)).symm
    have hgen :
        TopologicallyGenerates (G := G)
          (e '' Y) := topologicallyGenerates_continuousMulEquiv_image
            (G := G ⧸ (⊥ : Subgroup G)) e hYgen
    rw [QuotientGeneratorConvergingPair.toAmbientSet,
      closedNormalQuotientSection_bot_eq (G := G) hbotClosed]
    simpa using hgen
  · have : TotallyDisconnectedSpace (G ⧸ (⊥ : Subgroup G)) :=
      ProCGroups.totallyDisconnectedSpace_quotient_closedNormal
        (⊥ : Subgroup G) hbotClosed
    have hconv :
        ConvergesToOneAlongOpenSubgroups (G := G)
          ((closedNormalQuotientSection (G := G)
            (N := (⊥ : Subgroup G)) hbotClosed) '' Y) := by
      exact ConvergesToOneAlongOpenSubgroups.image_of_continuous_pointed
        (G := G ⧸ (⊥ : Subgroup G)) (H := G)
        (closedNormalQuotientSection_continuous (G := G)
          (N := (⊥ : Subgroup G)) hbotClosed)
        (closedNormalQuotientSection_one (G := G)
          (N := (⊥ : Subgroup G)) hbotClosed)
        hYconv
    rw [QuotientGeneratorConvergingPair.toAmbientSet]
    exact hconv

end Proposition244
section Generators

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]


/-- Every nonempty chain of quotient generator pairs has an upper bound. -/
theorem quotientGeneratorPair_exists_upperBound_of_chain
    (c : Set (QuotientGeneratorConvergingPair (G := G)))
    (hc : IsChain (· ≤ ·) c) (hcn : c.Nonempty) :
    ∃ ub : QuotientGeneratorConvergingPair (G := G), ∀ a ∈ c, a ≤ ub := by
  classical
  let K : Subgroup G := iInf fun p : c => p.1.N
  have : K.Normal := Subgroup.normal_iInf_normal fun p : c => p.1.normal_N
  have hKclosed : IsClosed (K : Set G) := by
    simpa [K] using isClosed_iInter (fun p : c => p.1.closed_N)
  have : TotallyDisconnectedSpace (G ⧸ K) :=
    ProCGroups.totallyDisconnectedSpace_quotient_closedNormal K hKclosed
  let lift : (a : c) → a.1.Source → G ⧸ K := fun a =>
    Classical.choose (quotientGeneratorPair_exists_liftToInf (G := G) hc a)
  have hlift_continuous : ∀ a : c, Continuous (lift a) := by
    intro a
    exact (Classical.choose_spec
      (quotientGeneratorPair_exists_liftToInf (G := G) hc a)).1
  have hlift_fac :
      ∀ (a b : c) (hab : a.1 ≤ b.1),
        leftQuotientProjection K b.1.N
          (iInf_le (fun p : c => p.1.N) b) ∘ lift a =
        a.1.le_map hab := by
    intro a b hab
    exact (Classical.choose_spec
      (quotientGeneratorPair_exists_liftToInf (G := G) hc a)).2.1 b hab
  have hlift_one : ∀ a : c, lift a a.1.sourceOne = 1 := by
    intro a
    exact (Classical.choose_spec
      (quotientGeneratorPair_exists_liftToInf (G := G) hc a)).2.2
  have exists_stage_above_le_open :
      ∀ (a : c) {U : OpenSubgroup G}, K ≤ (U : Subgroup G) →
        ∃ b : c, a.1 ≤ b.1 ∧ b.1.N ≤ (U : Subgroup G) := by
    intro a U hKU
    let d : Set (QuotientGeneratorConvergingPair (G := G)) :=
      {p | p ∈ c ∧ a.1 ≤ p}
    have hdchain : IsChain (· ≤ ·) d := by
      intro x hx y hy hxy
      exact hc hx.1 hy.1 hxy
    have hdne : d.Nonempty := ⟨a.1, a.2, le_rfl⟩
    have hdEq : iInf (fun p : d => p.1.N) = K := by
      apply le_antisymm
      · refine le_iInf ?_
        intro p
        by_cases hap : a.1 ≤ p.1
        · exact iInf_le (fun q : d => q.1.N) ⟨p.1, p.2, hap⟩
        · have hda :
            iInf (fun q : d => q.1.N) ≤ a.1.N :=
            iInf_le (fun q : d => q.1.N) ⟨a.1, a.2, le_rfl⟩
          by_cases hEq : p.1 = a.1
          · simpa [hEq] using hda
          · rcases hc p.2 a.2 hEq with hpa | hap'
            · exact hda.trans (QuotientGeneratorConvergingPair.le_hBA hpa)
            · exact False.elim (hap hap')
      · refine le_iInf ?_
        intro p
        exact iInf_le (fun q : c => q.1.N) ⟨p.1, p.2.1⟩
    have hdKU : iInf (fun p : d => p.1.N) ≤ (U : Subgroup G) := by
      simpa [hdEq] using hKU
    rcases exists_quotientPair_le_openSubgroup_of_chain_iInf_le
        (G := G) hdchain hdne U hdKU with ⟨b, hbU⟩
    exact ⟨⟨b.1, b.2.1⟩, b.2.2, hbU⟩
  let stageImage : c → Set (G ⧸ K) := fun a =>
    Set.range fun y : a.1.Y => lift a (a.1.sourceOfY y)
  have hlift_eq_of_le :
      ∀ {a b : c} (hAB : a.1 ≤ b.1) (y : a.1.Y),
        lift a (a.1.sourceOfY y) =
          lift b (b.1.sourceOfY
            ⟨a.1.le_map hAB (a.1.sourceOfY y), a.1.le_map_mem hAB y⟩) := by
    intro a b hAB y
    let yb : b.1.Y :=
      ⟨a.1.le_map hAB (a.1.sourceOfY y), a.1.le_map_mem hAB y⟩
    let q1 := lift a (a.1.sourceOfY y)
    let q2 := lift b (b.1.sourceOfY yb)
    have hmem :
        ∀ W : OpenNormalSubgroup (G ⧸ K), q1⁻¹ * q2 ∈ (W : Set (G ⧸ K)) := by
      intro W
      let V : OpenNormalSubgroup G :=
        OpenNormalSubgroup.comap (QuotientGroup.mk' K) QuotientGroup.continuous_mk W
      have hKV : K ≤ (V : Subgroup G) := by
        intro g hg
        change QuotientGroup.mk' K g ∈ W
        have hg1 : QuotientGroup.mk' K g = (1 : G ⧸ K) :=
          (QuotientGroup.eq_one_iff (N := K) g).2 hg
        rw [hg1]
        exact W.one_mem'
      obtain ⟨p, hbp, hpV⟩ := exists_stage_above_le_open b hKV
      have hcompat :
          a.1.le_map (hAB.trans hbp) (a.1.sourceOfY y) =
            b.1.le_map hbp (b.1.sourceOfY yb) := by
        have hqY :
            a.1.le_map (hAB.trans hbp) (a.1.sourceOfY y) ∈ p.1.Y :=
          a.1.le_map_mem (hAB.trans hbp) y
        have hqproj :
            leftQuotientProjection (p.1.N) (b.1.N) (b.1.le_hBA hbp)
              (a.1.le_map (hAB.trans hbp) (a.1.sourceOfY y)) = yb.1 := by
          simpa [yb] using a.1.le_map_compat hAB (hAB.trans hbp) hbp y
        exact b.1.eq_le_map_of_mem_of_proj_eq hbp yb hqY hqproj
      have hEqp :
          leftQuotientProjection K p.1.N
              (iInf_le (fun r : c => r.1.N) p) q1 =
            leftQuotientProjection K p.1.N
              (iInf_le (fun r : c => r.1.N) p) q2 := by
        have hq1 :=
          congrFun (hlift_fac a p (hAB.trans hbp)) (a.1.sourceOfY y)
        have hq2 :=
          congrFun (hlift_fac b p hbp) (b.1.sourceOfY yb)
        calc
          leftQuotientProjection K p.1.N
              (iInf_le (fun r : c => r.1.N) p) q1
              = a.1.le_map (hAB.trans hbp) (a.1.sourceOfY y) := by
                  simpa [q1] using hq1
          _ = b.1.le_map hbp (b.1.sourceOfY yb) := hcompat
          _ = leftQuotientProjection K p.1.N
                (iInf_le (fun r : c => r.1.N) p) q2 := by
                  simpa [q2] using hq2.symm
      have hEqV :
          leftQuotientProjection K (V : Subgroup G) hKV q1 =
            leftQuotientProjection K (V : Subgroup G) hKV q2 := by
        calc
          leftQuotientProjection K (V : Subgroup G) hKV q1
              = leftQuotientProjection (p.1.N) (V : Subgroup G) hpV
                  (leftQuotientProjection K p.1.N
                    (iInf_le (fun r : c => r.1.N) p) q1) := by
                      exact
                        leftQuotientProjection_comp_apply_symm
                          (K := (K : Subgroup G)) (H := (p.1.N : Subgroup G))
                          (L := (V : Subgroup G)) (iInf_le (fun r : c => r.1.N) p)
                          hpV q1
        _ = leftQuotientProjection (p.1.N) (V : Subgroup G) hpV
                (leftQuotientProjection K p.1.N
                  (iInf_le (fun r : c => r.1.N) p) q2) := by
                    rw [hEqp]
          _ = leftQuotientProjection K (V : Subgroup G) hKV q2 := by
                exact (leftQuotientProjection_comp_apply_symm
                  (K := (K : Subgroup G)) (H := (p.1.N : Subgroup G))
                  (L := (V : Subgroup G)) (iInf_le (fun r : c => r.1.N) p) hpV q2).symm
      revert hEqV
      refine Quotient.inductionOn₂' q1 q2 ?_
      intro g1 g2 hEqV
      change QuotientGroup.mk' K (g1⁻¹ * g2) ∈ W
      have hEqV' :
          QuotientGroup.mk' (V : Subgroup G) g1 =
            QuotientGroup.mk' (V : Subgroup G) g2 := by
        simpa [leftQuotientProjection_mk] using hEqV
      have hgV : g1⁻¹ * g2 ∈ (V : Subgroup G) := (QuotientGroup.eq).1 hEqV'
      change QuotientGroup.mk' K (g1⁻¹ * g2) ∈ W at hgV
      exact hgV
    have hq1 :
        q1⁻¹ * q2 = 1 := by
      exact ProfiniteGrp.eq_one_of_mem_all_openNormalSubgroups
        (G := G ⧸ K) hmem
    calc
      q1 = q1 * 1 := by simp only [mul_one]
      _ = q1 * (q1⁻¹ * q2) := by rw [hq1]
      _ = q2 := by simp only [mul_inv_cancel_left]
  have hstage_mono :
      ∀ {a b : c} (hAB : a.1 ≤ b.1), stageImage a ⊆ stageImage b := by
    intro a b hAB q hq
    rcases hq with ⟨y, rfl⟩
    refine ⟨⟨a.1.le_map hAB (a.1.sourceOfY y), a.1.le_map_mem hAB y⟩, ?_⟩
    exact (hlift_eq_of_le hAB y).symm
  have hstage_diff :
      ∀ {a b : c} (hAB : a.1 ≤ b.1),
        stageImage b \ stageImage a ⊆
          {q : G ⧸ K |
            leftQuotientProjection K a.1.N
              (iInf_le (fun p : c => p.1.N) a) q = 1} := by
    intro a b hAB q hq
    rcases hq.1 with ⟨yb, rfl⟩
    by_cases hybim : yb.1 ∈ a.1.yImage b.1 (a.1.le_map hAB)
    · rcases hybim with ⟨y, hyEq⟩
      have hEq :
          lift b (b.1.sourceOfY yb) = lift a (a.1.sourceOfY y) := by
        calc
          lift b (b.1.sourceOfY yb)
              = lift b (b.1.sourceOfY
                  ⟨a.1.le_map hAB (a.1.sourceOfY y), a.1.le_map_mem hAB y⟩) := by
                    simp only [hyEq, Subtype.coe_eta]
          _ = lift a (a.1.sourceOfY y) := (hlift_eq_of_le hAB y).symm
      exact False.elim (hq.2 ⟨y, hEq.symm⟩)
    · have hybker :
          leftQuotientProjection (b.1.N) (a.1.N) (a.1.le_hBA hAB) yb.1 = 1 :=
        a.1.le_map_diff hAB ⟨yb.2, hybim⟩
      have hqb :
          leftQuotientProjection K b.1.N
            (iInf_le (fun p : c => p.1.N) b)
            (lift b (b.1.sourceOfY yb)) = yb.1 := by
        calc
          leftQuotientProjection K b.1.N
              (iInf_le (fun p : c => p.1.N) b)
              (lift b (b.1.sourceOfY yb)) = b.1.le_map le_rfl (b.1.sourceOfY yb) := by
            exact congrFun (hlift_fac b b le_rfl) (b.1.sourceOfY yb)
          _ = yb.1 := by
            simpa only [leftQuotientProjection_id, id_eq,
              QuotientGeneratorConvergingPair.sourceOfY] using
              b.1.le_map_right le_rfl (b.1.sourceOfY yb)
      calc
        leftQuotientProjection K a.1.N
            (iInf_le (fun p : c => p.1.N) a)
            (lift b (b.1.sourceOfY yb))
            = leftQuotientProjection (b.1.N) (a.1.N) (a.1.le_hBA hAB)
                (leftQuotientProjection K b.1.N
                  (iInf_le (fun p : c => p.1.N) b)
                  (lift b (b.1.sourceOfY yb))) := by
            exact
              (leftQuotientProjection_comp_apply
                (K := (K : Subgroup G)) (H := (b.1.N : Subgroup G))
                (L := (a.1.N : Subgroup G)) (iInf_le (fun p : c => p.1.N) b)
                (a.1.le_hBA hAB) (lift b (b.1.sourceOfY yb))).symm
        _ = leftQuotientProjection (b.1.N) (a.1.N) (a.1.le_hBA hAB) yb.1 := by
            rw [hqb]
        _ = 1 := hybker
  let Y : Set (G ⧸ K) := ⋃ a : c, stageImage a
  have hYcompl : Y ⊆ ({1} : Set (G ⧸ K))ᶜ := by
    intro q hq
    rcases mem_iUnion.mp hq with ⟨a, hqa⟩
    rcases hqa with ⟨y, rfl⟩
    have hqy :
        leftQuotientProjection K a.1.N
          (iInf_le (fun p : c => p.1.N) a)
          (lift a (a.1.sourceOfY y)) = y.1 := by
      have hliftProjection := congrFun (hlift_fac a a le_rfl) (a.1.sourceOfY y)
      calc
        leftQuotientProjection K a.1.N
            (iInf_le (fun p : c => p.1.N) a)
            (lift a (a.1.sourceOfY y))
            = a.1.le_map le_rfl (a.1.sourceOfY y) := by
                simpa using hliftProjection
        _ = y.1 := by
            simpa only [leftQuotientProjection_id, id_eq,
              QuotientGeneratorConvergingPair.sourceOfY] using
              a.1.le_map_right le_rfl (a.1.sourceOfY y)
    intro hq1
    have hq1' : lift a (a.1.sourceOfY y) = 1 := by simpa using hq1
    have hy1 : y.1 = 1 := by
      calc
        y.1 = leftQuotientProjection K a.1.N
              (iInf_le (fun p : c => p.1.N) a)
              (lift a (a.1.sourceOfY y)) := hqy.symm
        _ = leftQuotientProjection K a.1.N
              (iInf_le (fun p : c => p.1.N) a) 1 := by rw [hq1']
        _ = 1 := by rfl
    exact a.1.subset_compl y.2 hy1
  have hYconv : ConvergesToOneAlongOpenSubgroups (G := G ⧸ K) Y := by
    intro W
    let V : OpenSubgroup G :=
      OpenSubgroup.comap (QuotientGroup.mk' K) QuotientGroup.continuous_mk W
    have hKV : K ≤ (V : Subgroup G) := by
      intro g hg
      change QuotientGroup.mk' K g ∈ W
      have hg1 : QuotientGroup.mk' K g = (1 : G ⧸ K) :=
        (QuotientGroup.eq_one_iff (N := K) g).2 hg
      rw [hg1]
      exact W.one_mem'
    rcases exists_quotientPair_le_openSubgroup_of_chain_iInf_le
        (G := G) hc hcn V (by simpa [K] using hKV) with ⟨a, haV⟩
    have hstageconv : ConvergesToOneAlongOpenSubgroups (G := G ⧸ K) (stageImage a) := by
      have : TotallyDisconnectedSpace (G ⧸ a.1.N) :=
        ProCGroups.totallyDisconnectedSpace_quotient_closedNormal
          a.1.N a.1.closed_N
      have hconv :=
        ConvergesToOneAlongOpenSubgroups.range_subtype_pointed
          (G := G ⧸ a.1.N) (H := G ⧸ K)
          (hf := hlift_continuous a) (hf1 := hlift_one a) (hX := a.1.converges)
      have himage :
          stageImage a =
            Set.range (fun y : a.1.Y =>
              lift a ⟨y.1, Or.inr y.2⟩) := by
        ext q
        constructor <;> rintro ⟨y, rfl⟩ <;> exact ⟨y, rfl⟩
      rw [himage]
      exact hconv
    have hsubset : Y \ (W : Set (G ⧸ K)) ⊆ stageImage a \ (W : Set (G ⧸ K)) := by
      intro q hq
      rcases hq with ⟨hqY, hqW⟩
      rcases mem_iUnion.mp hqY with ⟨b, hbq⟩
      by_cases hba : b.1 ≤ a.1
      · exact ⟨hstage_mono hba hbq, hqW⟩
      · have hcmp : a.1 ≤ b.1 := by
          by_cases hEq : a = b
          · exact hEq ▸ le_rfl
          · rcases hc a.2 b.2 (by
              intro h
              exact hEq (Subtype.ext h)) with hab | hba'
            · exact hab
            · exact False.elim (hba hba')
        by_cases hqa : q ∈ stageImage a
        · exact ⟨hqa, hqW⟩
        · have hq1 :
            leftQuotientProjection K a.1.N
              (iInf_le (fun p : c => p.1.N) a) q = 1 :=
            hstage_diff hcmp ⟨hbq, hqa⟩
          have hqWin : q ∈ W := by
            rcases Quotient.exists_rep q with ⟨g, rfl⟩
            change QuotientGroup.mk' K g ∈ W
            have hgA : g ∈ a.1.N := by
              simpa [leftQuotientProjection_mk] using
                (QuotientGroup.eq_one_iff (N := a.1.N) g).1 hq1
            have hgV : g ∈ (V : Subgroup G) := haV hgA
            exact (OpenSubgroup.mem_comap
              (H := W) (f := QuotientGroup.mk' K)
              (hf := QuotientGroup.continuous_mk) (x := g)).1 hgV
          exact False.elim (hqW hqWin)
    exact (hstageconv W).subset hsubset
  have hYgen : TopologicallyGenerates (G := G ⧸ K) Y := by
    have hbotclosed : IsClosed ((⊥ : Subgroup (G ⧸ K)) : Set (G ⧸ K)) := by
      change IsClosed ({(1 : G ⧸ K)} : Set (G ⧸ K))
      simp only [finite_singleton, Finite.isClosed]
    have hgen1 :
        TopologicallyGenerates (G := G ⧸ K) (Y ∪ ({1} : Set (G ⧸ K))) := by
      apply (topologicallyGenerates_union_subgroup_iff_forall_openNormalQuotient
        (G := G ⧸ K)
        (N := (⊥ : Subgroup (G ⧸ K))) (X := Y)).2
      intro W hbotW
      let V : OpenNormalSubgroup G :=
        OpenNormalSubgroup.comap (QuotientGroup.mk' K) QuotientGroup.continuous_mk W
      have hKV : K ≤ (V : Subgroup G) := by
        intro g hg
        change QuotientGroup.mk' K g ∈ W
        have hg1 : QuotientGroup.mk' K g = (1 : G ⧸ K) :=
          (QuotientGroup.eq_one_iff (N := K) g).2 hg
        rw [hg1]
        exact W.one_mem'
      rcases exists_quotientPair_le_openSubgroup_of_chain_iInf_le
          (G := G) hc hcn V.toOpenSubgroup (by simpa [K] using hKV) with ⟨a, haV⟩
      have hVaClosed : IsClosed ((V : Subgroup G) : Set G) :=
        openNormalSubgroup_isClosed (G := G) V
      have hmapW :
          ((V : Subgroup G).map (QuotientGroup.mk' K)) = (W : Subgroup (G ⧸ K)) := by
        ext q
        rcases Quotient.exists_rep q with ⟨g, rfl⟩
        constructor
        · rintro ⟨g', hg'V, hg'q⟩
          have : QuotientGroup.mk' K g' ∈ W := by
            change QuotientGroup.mk' K g' ∈ W at hg'V
            exact hg'V
          change QuotientGroup.mk' K g ∈ W
          have hg'q' :
              QuotientGroup.mk' K g' = QuotientGroup.mk' K g := hg'q
          exact hg'q' ▸ this
        · intro hgW
          refine ⟨g, ?_, rfl⟩
          change QuotientGroup.mk' K g ∈ W
          exact hgW
      let QV : Subgroup (G ⧸ K) := (V : Subgroup G).map (QuotientGroup.mk' K)
      let Wmap : OpenNormalSubgroup (G ⧸ K) :=
        { toOpenSubgroup :=
            { toSubgroup := QV
              isOpen' := by
                simpa [QV, hmapW] using W.isOpen' }
          isNormal' := by
            simpa [QV, hmapW] using (show (W : Subgroup (G ⧸ K)).Normal from inferInstance) }
      have hWmap : Wmap = W := by
        ext q
        change q ∈ QV ↔ q ∈ (W : Subgroup (G ⧸ K))
        simp only [hmapW, OpenSubgroup.mem_toSubgroup, QV]
      let e0 :
          ((G ⧸ K) ⧸ QV) ≃ₜ* G ⧸ (V : Subgroup G) :=
        quotientQuotientContinuousMulEquiv
          (G := G) hVaClosed hKV
      have hstageProj :
          ∀ y : a.1.Y,
            leftQuotientProjection K (V : Subgroup G) hKV
              (lift a (a.1.sourceOfY y)) =
              leftQuotientProjection a.1.N (V : Subgroup G) haV y.1 := by
        intro y
        have hqy0 :=
          congrFun (hlift_fac a a le_rfl) (a.1.sourceOfY y)
        have hqy :
            leftQuotientProjection K a.1.N
              (iInf_le (fun p : c => p.1.N) a)
              (lift a (a.1.sourceOfY y)) = y.1 := by
          calc
            leftQuotientProjection K a.1.N
                (iInf_le (fun p : c => p.1.N) a)
                (lift a (a.1.sourceOfY y)) = a.1.le_map le_rfl (a.1.sourceOfY y) := by
              exact hqy0
            _ = y.1 := by
              simpa only [leftQuotientProjection_id, id_eq,
                QuotientGeneratorConvergingPair.sourceOfY] using
                a.1.le_map_right le_rfl (a.1.sourceOfY y)
        calc
          leftQuotientProjection K (V : Subgroup G) hKV
              (lift a (a.1.sourceOfY y))
              = leftQuotientProjection (a.1.N) (V : Subgroup G) haV
                  (leftQuotientProjection K a.1.N
                    (iInf_le (fun p : c => p.1.N) a)
                    (lift a (a.1.sourceOfY y))) := by
                      exact
                        leftQuotientProjection_comp_apply_symm
                          (K := (K : Subgroup G)) (H := (a.1.N : Subgroup G))
                          (L := (V : Subgroup G)) (iInf_le (fun p : c => p.1.N) a) haV
                          (lift a (a.1.sourceOfY y))
          _ = leftQuotientProjection (a.1.N) (V : Subgroup G) haV y.1 := by
                rw [hqy]
      have hstageImgEq :
          (leftQuotientProjection K (V : Subgroup G) hKV) '' stageImage a =
            (leftQuotientProjection a.1.N (V : Subgroup G) haV) '' a.1.Y := by
        ext q
        constructor
        · rintro ⟨x, ⟨y, rfl⟩, rfl⟩
          exact ⟨y.1, y.2, (hstageProj y).symm⟩
        · rintro ⟨y, hyY, hyq⟩
          let y' : a.1.Y := ⟨y, hyY⟩
          refine ⟨lift a (a.1.sourceOfY y'), ⟨y', rfl⟩, ?_⟩
          calc
            leftQuotientProjection K (V : Subgroup G) hKV
                (lift a (a.1.sourceOfY y'))
                = leftQuotientProjection a.1.N (V : Subgroup G) haV y := by
                    simpa [y'] using hstageProj y'
            _ = q := hyq
      have hstageGenV :
          TopologicallyGenerates (G := G ⧸ (V : Subgroup G))
            ((leftQuotientProjection K (V : Subgroup G) hKV) '' stageImage a) := by
        let fV : (G ⧸ a.1.N) →* G ⧸ (V : Subgroup G) :=
          { toFun := leftQuotientProjection a.1.N (V : Subgroup G) haV
            map_one' := rfl
            map_mul' := by
              intro x y
              refine Quotient.inductionOn₂' x y ?_
              intro g h
              rfl }
        have hgenV :
            TopologicallyGenerates (G := G ⧸ (V : Subgroup G))
              (fV '' a.1.Y) := by
          exact topologicallyGenerates_image_of_continuousSurjective
            (G := G ⧸ a.1.N) (H := G ⧸ (V : Subgroup G)) fV
            (by
              change Continuous (leftQuotientProjection a.1.N (V : Subgroup G) haV)
              exact continuous_leftQuotientProjection
                (G := G) (K := a.1.N) (H := (V : Subgroup G)) haV)
            (by
              change Function.Surjective (leftQuotientProjection a.1.N (V : Subgroup G) haV)
              exact surjective_leftQuotientProjection
                (G := G) (K := a.1.N) (H := (V : Subgroup G)) haV)
            a.1.generates
        rw [hstageImgEq]
        change TopologicallyGenerates (G := G ⧸ (V : Subgroup G)) (fV '' a.1.Y)
        exact hgenV
      have hquotProj0 :
          ∀ y : G ⧸ K,
            e0 ((QuotientGroup.mk' QV) y) =
              leftQuotientProjection K (V : Subgroup G) hKV y := by
        intro y
        refine Quotient.inductionOn y ?_
        intro g
        rfl
      have hquotPreimgEq0 :
          e0.symm '' ((leftQuotientProjection K (V : Subgroup G) hKV) '' Y) =
            (QuotientGroup.mk' QV '' Y) := by
        ext q
        constructor
        · rintro ⟨z, ⟨y, hy, hzy⟩, hqz⟩
          refine ⟨y, hy, ?_⟩
          have hzq : z = e0 q := by
            calc
              z = e0 (e0.symm z) := by symm; exact e0.right_inv z
              _ = e0 q := by rw [hqz]
          have heqy : e0 ((QuotientGroup.mk' QV) y) = z := by
            exact (hquotProj0 y).trans hzy
          exact e0.injective (heqy.trans hzq)
        · rintro ⟨y, hy, rfl⟩
          refine ⟨leftQuotientProjection K (V : Subgroup G) hKV y, ⟨y, hy, rfl⟩, ?_⟩
          calc
            e0.symm (leftQuotientProjection K (V : Subgroup G) hKV y)
                = e0.symm (e0 ((QuotientGroup.mk' QV) y)) := by
                    rw [hquotProj0 y]
            _ = QuotientGroup.mk' QV y := e0.left_inv _
      have hgenYV :
          TopologicallyGenerates (G := G ⧸ (V : Subgroup G))
            ((leftQuotientProjection K (V : Subgroup G) hKV) '' Y) := by
        exact topologicallyGenerates_mono hstageGenV (by
          intro q hq
          rcases hq with ⟨x, hx, rfl⟩
          exact ⟨x, mem_iUnion.mpr ⟨a, hx⟩, rfl⟩)
      have hgenQuot0 :
          TopologicallyGenerates (G := ((G ⧸ K) ⧸ QV))
            ((QuotientGroup.mk' QV) '' Y) := by
        rw [← hquotPreimgEq0]
        exact topologicallyGenerates_continuousMulEquiv_image
          (G := G ⧸ (V : Subgroup G)) e0.symm hgenYV
      have hgenQuotMap :
          TopologicallyGenerates
            (G := ((G ⧸ K) ⧸ (Wmap : Subgroup (G ⧸ K))))
            ((QuotientGroup.mk' (Wmap : Subgroup (G ⧸ K))) '' Y) := by
        simpa [QV, Wmap] using hgenQuot0
      have hgenQuot :
          TopologicallyGenerates (G := ((G ⧸ K) ⧸ (W : Subgroup (G ⧸ K))))
            ((QuotientGroup.mk' (W : Subgroup (G ⧸ K))) '' Y) := by
        simpa using (hWmap ▸ hgenQuotMap)
      exact hgenQuot
    exact (topologicallyGenerates_union_one_iff (G := G ⧸ K) (X := Y)).1 hgen1
  refine ⟨{ N := K
            normal_N := inferInstance
            closed_N := hKclosed
            Y := Y
            subset_compl := hYcompl
            converges := hYconv
            generates := hYgen }, ?_⟩
  intro a ha
  let a' : c := ⟨a, ha⟩
  refine ⟨iInf_le (fun p : c => p.1.N) a', lift a', ?_, ?_, ?_, ?_, ?_⟩
  · exact hlift_continuous a'
  · intro x
    have hliftProjection := congrFun (hlift_fac a' a' le_rfl) x
    calc
      leftQuotientProjection K a.N (iInf_le (fun p : c => p.1.N) a')
          (lift a' x) = a.le_map le_rfl x := by
          simpa using hliftProjection
      _ = x.1 := by
            simpa [QuotientGeneratorConvergingPair.le_map,
              QuotientGeneratorConvergingPair.le_hBA] using
              a.le_map_right le_rfl x
  · exact hlift_one a'
  · intro y
    exact mem_iUnion.mpr ⟨a', ⟨y, rfl⟩⟩
  · intro q hq
    rcases mem_iUnion.mp hq.1 with ⟨b, hbq⟩
    by_cases hba : b.1 ≤ a
    · exact False.elim (hq.2 (hstage_mono (a := b) (b := a') hba hbq))
    · have hab : a ≤ b.1 := by
        by_cases hEq : a = b.1
        · exact hEq ▸ le_rfl
        · rcases hc ha b.2 (by
            intro h
            exact hEq h) with hab | hba'
          · exact hab
          · exact False.elim (hba hba')
      exact hstage_diff (a := a') (b := b) hab ⟨hbq, hq.2⟩

/-- 4.4. Existence theorem used by the public theorem. -/
theorem exists_generatorsConvergingToOne :
    ∃ X : Set G, GeneratesAndConvergesToOneAlongOpenSubgroups (G := G) X := by
  classical
  let Pair := QuotientGeneratorConvergingPair (G := G)
  have : Nonempty Pair := ⟨quotientGeneratorPairTop (G := G)⟩
  obtain ⟨m, hmmax⟩ := zorn_le_nonempty (α := Pair) <| by
    intro c hc hcn
    rcases quotientGeneratorPair_exists_upperBound_of_chain (G := G) c hc hcn with
      ⟨ub, hub⟩
    exact ⟨ub, hub⟩
  have hmbot : m.N = ⊥ := by
    by_contra hne
    rcases quotientGeneratorPair_exists_strictExtension (G := G) m hne with
      ⟨m', hmm', hm'm⟩
    exact hm'm (hmmax hmm')
  exact ⟨m.toAmbientSet, m.toAmbientSet_generatesAndConvergesToOneAlongOpenSubgroups hmbot⟩



omit [T2Space G] in
/-- A surjective continuous homomorphism preserves generating sets converging to `1`. -/
theorem GeneratesAndConvergesToOneAlongOpenSubgroups.image_of_continuousSurjective
    {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (f : G →* H) (hf : Continuous f) (hfsurj : Function.Surjective f)
    {X : Set G} (hX : GeneratesAndConvergesToOneAlongOpenSubgroups (G := G) X) :
    GeneratesAndConvergesToOneAlongOpenSubgroups (G := H) (f '' X) := by
  refine ⟨?_, ?_⟩
  · exact topologicallyGenerates_image_of_continuousSurjective
      (G := G) (H := H) f hf hfsurj hX.1
  · exact ConvergesToOneAlongOpenSubgroups.image_of_continuous_pointed
      (G := G) (H := H) hf (by simp only [map_one]) hX.2

omit [T2Space G] in
/-- A continuous multiplicative equivalence preserves generating sets converging to `1`. -/
theorem GeneratesAndConvergesToOneAlongOpenSubgroups.image_of_continuousMulEquiv
    {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (e : G ≃ₜ* H) {X : Set G}
    (hX : GeneratesAndConvergesToOneAlongOpenSubgroups (G := G) X) :
    GeneratesAndConvergesToOneAlongOpenSubgroups (G := H) (e '' X) := by
  refine ⟨?_, ?_⟩
  · exact topologicallyGenerates_continuousMulEquiv_image
      (G := G) e hX.1
  · exact ConvergesToOneAlongOpenSubgroups.image_of_continuous_pointed
      (G := G) (H := H) e.continuous (by simp only [Homeomorph.homeomorph_mk_coe,
          ContinuousMulEquiv.toMulEquiv_eq_coe, MulEquiv.toEquiv_eq_coe,
  EquivLike.coe_coe, map_one]) hX.2

omit [T2Space G] in
/-- A continuous multiplicative equivalence preserves and reflects convergence to `1`. -/
theorem ConvergesToOneAlongOpenSubgroups.image_of_continuousMulEquiv_iff
    {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (e : G ≃ₜ* H) {X : Set G} :
    ConvergesToOneAlongOpenSubgroups (G := H) (e '' X) ↔ ConvergesToOneAlongOpenSubgroups (G :=
        G) X := by
  constructor
  · intro h
    have hback : ConvergesToOneAlongOpenSubgroups (G := G) (e.symm '' (e '' X)) :=
      ConvergesToOneAlongOpenSubgroups.image_of_continuous_pointed
        (G := H) (H := G) e.symm.continuous (by simp only [Homeomorph.homeomorph_mk_coe,
            ContinuousMulEquiv.toMulEquiv_eq_coe, MulEquiv.toEquiv_eq_coe,
  EquivLike.coe_coe, map_one]) (X := e '' X) h
    have himage : e.symm '' (e '' X) = X := by
      ext x
      constructor
      · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
        simpa using hz
      · intro hx
        exact ⟨e x, ⟨x, hx, rfl⟩, by simp only [ContinuousMulEquiv.symm_apply_apply]⟩
    simpa [himage] using hback
  · intro h
    exact ConvergesToOneAlongOpenSubgroups.image_of_continuous_pointed
      (G := G) (H := H) e.continuous (by simp only [Homeomorph.homeomorph_mk_coe,
          ContinuousMulEquiv.toMulEquiv_eq_coe, MulEquiv.toEquiv_eq_coe,
  EquivLike.coe_coe, map_one]) h

omit [T2Space G] in
/-- A continuous multiplicative equivalence preserves and reflects the combined predicate. -/
theorem GeneratesAndConvergesToOneAlongOpenSubgroups.image_of_continuousMulEquiv_iff
    {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (e : G ≃ₜ* H) {X : Set G} :
    GeneratesAndConvergesToOneAlongOpenSubgroups (G := H) (e '' X) ↔
        GeneratesAndConvergesToOneAlongOpenSubgroups (G := G) X := by
  constructor
  · intro h
    exact ⟨
      (topologicallyGenerates_continuousMulEquiv_image_iff (G := G) (H := H) e (X := X)).1 h.1,
      (ConvergesToOneAlongOpenSubgroups.image_of_continuousMulEquiv_iff
        (G := G) (H := H) e (X := X)).1 h.2⟩
  · intro h
    exact ⟨
      (topologicallyGenerates_continuousMulEquiv_image_iff (G := G) (H := H) e (X := X)).2 h.1,
      (ConvergesToOneAlongOpenSubgroups.image_of_continuousMulEquiv_iff
        (G := G) (H := H) e (X := X)).2 h.2⟩

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- Topological rank is invariant under continuous multiplicative equivalence. -/
theorem topologicalRank_eq_of_continuousMulEquiv
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (e : G ≃ₜ* H) :
    topologicalRank G = topologicalRank H := by
  apply le_antisymm
  · rcases exists_topologicallyGenerates_card_eq_topologicalRank (G := H) with
      ⟨Ymin, hYmin, hYcard⟩
    calc
      topologicalRank G ≤ Cardinal.mk (e.symm '' Ymin) := by
        exact topologicalRank_le_mk_of_topologicallyGenerates
          (G := G)
          (topologicallyGenerates_continuousMulEquiv_image
            (G := H) e.symm hYmin)
      _ ≤ Cardinal.mk Ymin := Cardinal.mk_image_le
      _ = topologicalRank H := hYcard
  · rcases exists_topologicallyGenerates_card_eq_topologicalRank (G := G) with
      ⟨Xmin, hXmin, hXcard⟩
    calc
      topologicalRank H ≤ Cardinal.mk (e '' Xmin) := by
        exact topologicalRank_le_mk_of_topologicallyGenerates
          (G := H)
          (topologicallyGenerates_continuousMulEquiv_image
            (G := G) e hXmin)
      _ ≤ Cardinal.mk Xmin := Cardinal.mk_image_le
      _ = topologicalRank G := hXcard


end Generators

end ProCGroups.Generation
