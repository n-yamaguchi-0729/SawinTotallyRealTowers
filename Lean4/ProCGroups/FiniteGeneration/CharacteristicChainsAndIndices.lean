import ProCGroups.FiniteGeneration.Basic
import ProCGroups.Topologies.ContinuousMonoidHom

set_option autoImplicit false

/-!
# Characteristic chains from bounded-index intersections

For a topologically finitely generated profinite group, the intersection of
all open subgroups of index at most \(n\) is open and topologically
characteristic.  These intersections form a descending countable basis at the
identity.
-/

open Set
open scoped Topology Pointwise

namespace ProCGroups.FiniteGeneration

universe u v w

open ProCGroups.Generation
open ProCGroups.ProC

section IndexFamilies

variable {G : Type u} [Group G] [TopologicalSpace G]

/--
The open subgroups of index at most \(n\). This is the bounded-index family whose intersection
defines the characteristic core.
-/
def OpenSubgroupsOfIndexLE (G : Type u) [Group G] [TopologicalSpace G]
    (n : ℕ) : Set (Subgroup G) :=
  { H | IsOpen (H : Set G) ∧ Finite (G ⧸ H) ∧ Nat.card (G ⧸ H) ≤ n }

/-- The family of open normal subgroups of index exactly \(n\). -/
def OpenNormalSubgroupsOfIndex (G : Type u) [Group G] [TopologicalSpace G]
    (n : ℕ) : Set (Subgroup G) :=
  { U | U.Normal ∧ IsOpen (U : Set G) ∧ Finite (G ⧸ U) ∧ Nat.card (G ⧸ U) = n }



variable {G : Type u} [Group G] [TopologicalSpace G]

/-- Membership criterion for the finite set of open subgroups of index at most `n`. -/
@[simp] theorem mem_openSubgroupsOfIndexLE {n : ℕ} {H : Subgroup G} :
    H ∈ OpenSubgroupsOfIndexLE (G := G) n ↔
      IsOpen (H : Set G) ∧ Finite (G ⧸ H) ∧ Nat.card (G ⧸ H) ≤ n :=
  Iff.rfl

/-- Membership criterion for the finite set of open normal subgroups of a fixed index. -/
@[simp] theorem mem_openNormalSubgroupsOfIndex {n : ℕ} {U : Subgroup G} :
    U ∈ OpenNormalSubgroupsOfIndex (G := G) n ↔
      U.Normal ∧ IsOpen (U : Set G) ∧ Finite (G ⧸ U) ∧ Nat.card (G ⧸ U) = n :=
  Iff.rfl

/--
The canonical bounded-index intersection
`Vₙ = ⋂ {H ≤ G | H open and [G : H] ≤ n}`.
-/
def CharacteristicIndexIntersection (G : Type u) [Group G] [TopologicalSpace G]
    (n : ℕ) : Subgroup G :=
  sInf (OpenSubgroupsOfIndexLE (G := G) n)

/-- The characteristic index intersection is the infimum of all open subgroups of bounded index. -/
@[simp] theorem characteristicIndexIntersection_def (n : ℕ) :
    CharacteristicIndexIntersection (G := G) n =
      sInf (OpenSubgroupsOfIndexLE (G := G) n) :=
  rfl

/-- A group has only finitely many open subgroups of each prescribed index. -/
def HasFiniteOpenSubgroupsOfIndex (G : Type u) [Group G] [TopologicalSpace G]
    : Prop :=
  ∀ n, Set.Finite
    { H : Subgroup G | IsOpen (H : Set G) ∧ Finite (G ⧸ H) ∧ Nat.card (G ⧸ H) = n }

/-- Normal-subgroup version of fixed-index finiteness. -/
def HasFiniteOpenNormalSubgroupsOfIndex (G : Type u) [Group G] [TopologicalSpace G]
    : Prop :=
  ∀ n,
    Set.Finite
      { U : Subgroup G |
        U.Normal ∧ IsOpen (U : Set G) ∧ Finite (G ⧸ U) ∧ Nat.card (G ⧸ U) = n }

/--
Finiteness of open subgroups of each index implies finiteness of open normal subgroups of each
index.
-/
theorem HasFiniteOpenSubgroupsOfIndex.toHasFiniteOpenNormalSubgroupsOfIndex
    (h : HasFiniteOpenSubgroupsOfIndex G) :
    HasFiniteOpenNormalSubgroupsOfIndex G := by
  intro n
  refine (h n).subset ?_
  intro U hU
  exact ⟨hU.2.1, hU.2.2.1, hU.2.2.2⟩

/-- Continuous homomorphisms are equal when they agree on a topological generating set. -/
theorem continuousMonoidHom_eq_of_eqOn_topologicalGenerators
    [IsTopologicalGroup G]
    {R : Type v} [Group R] [TopologicalSpace R] [T2Space R]
    {s : Finset G} (hsgen : TopologicallyGenerates (G := G) (↑s : Set G))
    {f g : ContinuousMonoidHom G R}
    (hfg : ∀ x ∈ (↑s : Set G), f x = g x) :
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
  have hsub : Subgroup.closure (↑s : Set G) ≤ K := by
    rw [Subgroup.closure_le]
    intro x hx
    exact hfg x hx
  have htop : (⊤ : Subgroup G) ≤ K := by
    have hcl :
        (Subgroup.closure (↑s : Set G)).topologicalClosure ≤ K :=
      Subgroup.topologicalClosure_minimal _ hsub hKclosed
    rw [TopologicallyGenerates] at hsgen
    simpa [hsgen] using hcl
  ext x
  simpa [K] using htop (show x ∈ (⊤ : Subgroup G) from by simp only [Subgroup.mem_top])

/--
A finitely generated profinite group admits only finitely many continuous homomorphisms into a
fixed finite discrete target.
-/
theorem finite_continuousMonoidHom_to_finite_of_topologicallyFinitelyGenerated
    [IsTopologicalGroup G]
    {R : Type v} [Group R] [TopologicalSpace R] [T2Space R] [Finite R]
    (hG : TopologicallyFinitelyGenerated G) :
    Finite (ContinuousMonoidHom G R) := by
  classical
  rcases hG with ⟨s, hsgen⟩
  let eval : ContinuousMonoidHom G R → ((↑s : Set G) → R) := fun φ x => φ x.1
  have heval : Function.Injective eval := by
    intro φ ψ hφψ
    apply continuousMonoidHom_eq_of_eqOn_topologicalGenerators (G := G) hsgen
    intro x hx
    exact congrArg (fun k => k ⟨x, hx⟩) hφψ
  exact Finite.of_injective eval heval

/-- The chosen identification `G ⧸ H ≃ Fin n` for an index-`n` subgroup. -/
noncomputable def openSubgroupIndexEquiv
    (H : Subgroup G) (hHfinite : Finite (G ⧸ H)) {n : ℕ}
    (hn : Nat.card (G ⧸ H) = n) :
    (G ⧸ H) ≃ Fin n := by
  classical
  letI : Finite (G ⧸ H) := hHfinite
  exact Finite.equivFinOfCardEq hn

/-- The coset action of `G` on the `n` cosets of an index-`n` subgroup, transported to `Fin n`. -/
noncomputable def openSubgroupIndexAction
    (H : Subgroup G) (hHfinite : Finite (G ⧸ H)) {n : ℕ}
    (hn : Nat.card (G ⧸ H) = n) :
    G →* Equiv.Perm (Fin n) := by
  classical
  let e := openSubgroupIndexEquiv (G := G) H hHfinite hn
  exact e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom G (G ⧸ H))

/-- The image of the identity coset under the chosen `Fin n` identification. -/
noncomputable def openSubgroupIndexBasepoint
    (H : Subgroup G) (hHfinite : Finite (G ⧸ H)) {n : ℕ}
    (hn : Nat.card (G ⧸ H) = n) : Fin n :=
  openSubgroupIndexEquiv (G := G) H hHfinite hn (QuotientGroup.mk 1)

/-- The finite permutation type has its canonical topological space structure. -/
instance instTopologicalSpaceFinitePerm (n : ℕ) : TopologicalSpace (Equiv.Perm (Fin n)) :=
  ⊥

/-- The finite permutation type carries the discrete topology. -/
instance instDiscreteTopologyFinitePerm (n : ℕ) : DiscreteTopology (Equiv.Perm (Fin n)) :=
  ⟨rfl⟩

/-- The finite permutation group is a topological group with the discrete topology. -/
instance instIsTopologicalGroupFinitePerm (n : ℕ) : IsTopologicalGroup (Equiv.Perm (Fin n)) := by
  infer_instance

/-- The finite permutation type is finite. -/
instance instFiniteFinitePerm (n : ℕ) : Finite (Equiv.Perm (Fin n)) := by
  infer_instance

/-- The finite coset action, viewed as a continuous homomorphism into a discrete permutation
group. -/
noncomputable def openSubgroupIndexContinuousHom
    [IsTopologicalGroup G] [CompactSpace G]
    (H : Subgroup G) (hH : IsOpen (H : Set G)) {n : ℕ}
    (hHfinite : Finite (G ⧸ H)) (hn : Nat.card (G ⧸ H) = n) :
    G →ₜ* Equiv.Perm (Fin n) := by
  classical
  let φ : G →* Equiv.Perm (Fin n) := openSubgroupIndexAction (G := G) H hHfinite hn
  have hφker :
      IsOpen ((φ.ker : Subgroup G) : Set G) := by
    let e := openSubgroupIndexEquiv (G := G) H hHfinite hn
    have hker :
        φ.ker = (MulAction.toPermHom G (G ⧸ H)).ker := by
      ext g
      change e.permCongr (MulAction.toPerm g) = 1 ↔ MulAction.toPerm g = 1
      have hperm_one :
          e.permCongr (1 : Equiv.Perm (G ⧸ H)) = (1 : Equiv.Perm (Fin n)) := by
        ext x
        simp only [Equiv.permCongr_apply, Equiv.Perm.coe_one, id_eq, Equiv.apply_symm_apply]
      rw [← hperm_one]
      exact e.permCongr.injective.eq_iff
    have : Finite (G ⧸ H) := hHfinite
    have : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient (H := H)
    have hHclosed : IsClosed ((H : Subgroup G) : Set G) :=
      Subgroup.isClosed_of_isOpen H hH
    have hopenCore : IsOpen (((H.normalCore : Subgroup G) : Set G)) :=
      H.normalCore.isOpen_of_isClosed_of_finiteIndex (H.normalCore_isClosed hHclosed)
    simpa [hker, Subgroup.normalCore_eq_ker (H := H)] using hopenCore
  have hφcont : Continuous φ :=
    ProCGroups.MonoidHom.continuous_of_isOpen_ker_to_discrete φ hφker
  exact
    { toMonoidHom := φ
      continuous_toFun := hφcont }

omit [TopologicalSpace G] in
/-- Membership in an open subgroup is equivalent to fixing the basepoint in its coset action. -/
theorem mem_openSubgroup_iff_indexAction_fix_basepoint
    {H : Subgroup G} (hHfinite : Finite (G ⧸ H)) {n : ℕ}
    (hn : Nat.card (G ⧸ H) = n) {g : G} :
    g ∈ H ↔
      openSubgroupIndexAction (G := G) H hHfinite hn g
          (openSubgroupIndexBasepoint (G := G) H hHfinite hn) =
        openSubgroupIndexBasepoint (G := G) H hHfinite hn := by
  classical
  let e := openSubgroupIndexEquiv (G := G) H hHfinite hn
  constructor
  · intro hg
    have hq : QuotientGroup.mk (s := H) g = QuotientGroup.mk (s := H) 1 := by
      simpa [QuotientGroup.eq] using hg
    simpa [openSubgroupIndexAction, openSubgroupIndexBasepoint, e] using congrArg e hq
  · intro hg
    have hq :
        QuotientGroup.mk (s := H) g = QuotientGroup.mk (s := H) 1 := by
      apply e.injective
      simpa [openSubgroupIndexAction, openSubgroupIndexBasepoint, e] using hg
    simpa [QuotientGroup.eq] using hq

/-- Finitely generated profinite groups have only finitely many open subgroups of each index. -/
theorem hasFiniteOpenSubgroupsOfIndex_of_topologicallyFinitelyGenerated
    [IsTopologicalGroup G] [CompactSpace G]
    (hG : TopologicallyFinitelyGenerated G) :
    HasFiniteOpenSubgroupsOfIndex G := by
  intro n
  classical
  let S : Type u :=
    { H : Subgroup G // IsOpen (H : Set G) ∧ Finite (G ⧸ H) ∧ Nat.card (G ⧸ H) = n }
  let code : S → ContinuousMonoidHom G (Equiv.Perm (Fin n)) × Fin n := fun H =>
    let φ := openSubgroupIndexAction (G := G) H.1 H.2.2.1 H.2.2.2
    let e := openSubgroupIndexEquiv (G := G) H.1 H.2.2.1 H.2.2.2
    let hφker :
        IsOpen ((φ.ker : Subgroup G) : Set G) := by
      have : Finite (G ⧸ H.1) := H.2.2.1
      have : H.1.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient (H := H.1)
      have hHclosed : IsClosed ((H.1 : Subgroup G) : Set G) :=
        Subgroup.isClosed_of_isOpen H.1 H.2.1
      have hker :
          φ.ker = (MulAction.toPermHom G (G ⧸ H.1)).ker := by
        ext g
        change
          e.permCongr (MulAction.toPerm g) = 1 ↔ MulAction.toPerm g = 1
        have hperm_one : e.permCongr (1 : Equiv.Perm (G ⧸ H.1)) = (1 : Equiv.Perm (Fin n)) := by
          ext x
          simp only [Equiv.permCongr_apply, Equiv.Perm.coe_one, id_eq, Equiv.apply_symm_apply]
        rw [← hperm_one]
        exact e.permCongr.injective.eq_iff
      have hopenCore : IsOpen (((H.1).normalCore : Subgroup G) : Set G) :=
        (H.1).normalCore.isOpen_of_isClosed_of_finiteIndex ((H.1).normalCore_isClosed hHclosed)
      simpa [hker, Subgroup.normalCore_eq_ker (H := H.1)] using hopenCore
    have hφcont : Continuous φ :=
      ProCGroups.MonoidHom.continuous_of_isOpen_ker_to_discrete φ hφker
    ({ toMonoidHom := φ
       continuous_toFun := hφcont },
      openSubgroupIndexBasepoint (G := G) H.1 H.2.2.1 H.2.2.2)
  have hhomfinite : Finite (ContinuousMonoidHom G (Equiv.Perm (Fin n))) :=
    finite_continuousMonoidHom_to_finite_of_topologicallyFinitelyGenerated
      (G := G) hG
  have hcode : Function.Injective code := by
    intro H K hHK
    apply Subtype.ext
    ext g
    rw [mem_openSubgroup_iff_indexAction_fix_basepoint (G := G) (H := H.1) H.2.2.1 H.2.2.2
        (g := g),
      mem_openSubgroup_iff_indexAction_fix_basepoint (G := G) (H := K.1) K.2.2.1 K.2.2.2
        (g := g)]
    have hφg := DFunLike.congr_fun
      (congrArg ContinuousMonoidHom.toMonoidHom (congrArg Prod.fst hHK)) g
    have hb := congrArg Prod.snd hHK
    dsimp only [code] at hφg hb
    exact Iff.of_eq <| by simp [hφg, hb]
  have hSfinite :
      Finite
        { H : Subgroup G //
          IsOpen (H : Set G) ∧ Finite (G ⧸ H) ∧ Nat.card (G ⧸ H) = n } := by
    simpa [S] using (Finite.of_injective code hcode)
  exact (Set.finite_coe_iff
    (s := { H : Subgroup G |
      IsOpen (H : Set G) ∧ Finite (G ⧸ H) ∧ Nat.card (G ⧸ H) = n })).mp hSfinite

/-- Bounding the index by \(n\) still yields only finitely many open subgroups. -/
theorem finite_openSubgroupsOfIndexLE_of_hasFiniteOpenSubgroupsOfIndex
    (hfin : HasFiniteOpenSubgroupsOfIndex G) (n : ℕ) :
    Set.Finite (OpenSubgroupsOfIndexLE (G := G) n) := by
  classical
  refine Set.Finite.subset ((Set.finite_le_nat n).biUnion fun m hm => hfin m) ?_
  intro H hH
  exact Set.mem_iUnion.2
    ⟨Nat.card (G ⧸ H), Set.mem_iUnion.2 ⟨hH.2.2, ⟨hH.1, hH.2.1, rfl⟩⟩⟩

/-- The infimum of a finite family of open subgroups is open. -/
theorem Subgroup.isOpen_sInf_of_finite
    {S : Set (Subgroup G)} (hS : S.Finite)
    (hopen : ∀ H ∈ S, IsOpen (H : Set G)) :
    IsOpen ((sInf S : Subgroup G) : Set G) := by
  classical
  induction S, hS using Set.Finite.induction_on with
  | empty =>
      simp only [sInf_empty, Subgroup.coe_top, isOpen_univ]
  | @insert H S hHS hS ih =>
      rw [sInf_insert]
      exact (hopen H (by simp only [mem_insert_iff, true_or])).inter (ih fun K hK => hopen K (by
          simp only [mem_insert_iff, hK, or_true]))

/--
The bounded-index characteristic intersection is open once the bounded-index family is finite.
-/
theorem characteristicIndexIntersection_isOpen_of_hasFiniteOpenSubgroupsOfIndex
    (hfin : HasFiniteOpenSubgroupsOfIndex G) (n : ℕ) :
    IsOpen ((CharacteristicIndexIntersection (G := G) n : Set G)) := by
  apply Subgroup.isOpen_sInf_of_finite
  · exact finite_openSubgroupsOfIndexLE_of_hasFiniteOpenSubgroupsOfIndex (G := G) hfin n
  · intro H hH
    exact hH.1

/-- The bounded-index characteristic intersections form a descending chain. -/
theorem characteristicIndexIntersection_antitone :
    Antitone (CharacteristicIndexIntersection (G := G)) := by
  intro m n hmn x hx
  simp only [CharacteristicIndexIntersection, Subgroup.mem_sInf] at hx ⊢
  intro H hH
  exact hx H ⟨hH.1, hH.2.1, le_trans hH.2.2 hmn⟩

/-- The finite-index characteristic intersection is characteristic. -/
theorem characteristicIndexIntersection_isTopologicallyCharacteristic
    [IsTopologicalGroup G] [CompactSpace G]
    (n : ℕ) :
    IsTopologicallyCharacteristic G (CharacteristicIndexIntersection (G := G) n) := by
  have hforward :
      ∀ φ : G ≃ₜ* G, ∀ g : G,
        g ∈ CharacteristicIndexIntersection (G := G) n →
          φ g ∈ CharacteristicIndexIntersection (G := G) n := by
    intro φ g hg
    simp only [CharacteristicIndexIntersection, Subgroup.mem_sInf] at hg ⊢
    intro H hH
    have hcomap :
        Subgroup.comap φ.toMonoidHom H ∈ OpenSubgroupsOfIndexLE (G := G) n := by
      have hcomapOpen : IsOpen ((Subgroup.comap φ.toMonoidHom H : Subgroup G) : Set G) :=
        hH.1.preimage φ.continuous_toFun
      have hcomapFinite : Finite (G ⧸ Subgroup.comap φ.toMonoidHom H) :=
        Subgroup.quotient_finite_of_isOpen (Subgroup.comap φ.toMonoidHom H) hcomapOpen
      refine ⟨hcomapOpen, hcomapFinite, ?_⟩
      simpa [Subgroup.index_eq_card] using
        (Subgroup.index_comap_of_surjective (H := H) φ.surjective).le.trans hH.2.2
    exact hg _ hcomap
  intro φ g
  constructor
  · intro hg
    simpa using hforward φ.symm (φ g) hg
  · exact hforward φ g

/-- Characteristic index intersections are cofinal among open subgroups. -/
theorem characteristicIndexIntersection_cofinal_of_openSubgroup
    [IsTopologicalGroup G] [CompactSpace G]
    (U : Subgroup G) (hU : IsOpen (U : Set G)) :
    ∃ n, CharacteristicIndexIntersection (G := G) n ≤ U := by
  have hUfinite : Finite (G ⧸ U) :=
    Subgroup.quotient_finite_of_isOpen U hU
  refine ⟨Nat.card (G ⧸ U), ?_⟩
  intro x hx
  simp only [CharacteristicIndexIntersection, Subgroup.mem_sInf] at hx
  exact hx U ⟨hU, hUfinite, le_rfl⟩

/--
Topologically finitely generated profinite groups have a countable characteristic open basis at
the identity.
-/
theorem exists_characteristicOpenBasis_of_topologicallyFinitelyGenerated
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    : TopologicallyFinitelyGenerated G →
        ∃ V : ℕ → Subgroup G,
          V 0 = ⊤ ∧
          Antitone V ∧
          (∀ n, IsOpen ((V n : Subgroup G) : Set G)) ∧
          (∀ n, IsTopologicallyCharacteristic G (V n)) ∧
          ∀ U : Set G, U ∈ 𝓝 (1 : G) → ∃ n, ((V n : Subgroup G) : Set G) ⊆ U := by
  intro hG
  have hfin : HasFiniteOpenSubgroupsOfIndex G :=
    hasFiniteOpenSubgroupsOfIndex_of_topologicallyFinitelyGenerated (G := G) hG
  let V : ℕ → Subgroup G
    | 0 => ⊤
    | n + 1 => CharacteristicIndexIntersection (G := G) n
  refine ⟨V, rfl, ?_, ?_, ?_, ?_⟩
  · intro m n hmn
    cases m with
    | zero =>
        exact le_top
    | succ m =>
        cases n with
        | zero =>
            cases Nat.not_succ_le_zero m hmn
        | succ n =>
            exact characteristicIndexIntersection_antitone (G := G)
              (Nat.succ_le_succ_iff.mp hmn)
  · intro n
    cases n with
    | zero =>
        exact isOpen_univ
    | succ n =>
        exact characteristicIndexIntersection_isOpen_of_hasFiniteOpenSubgroupsOfIndex
          (G := G) hfin n
  · intro n
    cases n with
    | zero =>
        exact IsTopologicallyCharacteristic.top
    | succ n =>
        exact characteristicIndexIntersection_isTopologicallyCharacteristic
          (G := G) n
  · intro U hU
    rcases mem_nhds_iff.mp hU with ⟨W, hWU, hWopen, h1W⟩
    rcases exists_openNormalSubgroup_sub_open_nhds_of_one
        (G := G) hWopen h1W with ⟨N, hNW⟩
    rcases characteristicIndexIntersection_cofinal_of_openSubgroup
        (G := G) (N : Subgroup G) (openNormalSubgroup_isOpen (G := G) N) with
      ⟨n, hn⟩
    exact ⟨n + 1, Set.Subset.trans hn (Set.Subset.trans hNW hWU)⟩

/--
Finitely generated profinite groups have finite fixed-index open-subgroup sets and a countable
characteristic open basis at the identity.
-/
theorem finiteIndexOpenSubgroups_and_charBasis_of_tfg
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    (hG : TopologicallyFinitelyGenerated G) :
    HasFiniteOpenSubgroupsOfIndex G ∧
      ∃ V : ℕ → Subgroup G,
        V 0 = ⊤ ∧
        Antitone V ∧
        (∀ n, IsOpen ((V n : Subgroup G) : Set G)) ∧
        (∀ n, IsTopologicallyCharacteristic G (V n)) ∧
        ∀ U : Set G, U ∈ 𝓝 (1 : G) → ∃ n, ((V n : Subgroup G) : Set G) ⊆ U := by
  exact ⟨hasFiniteOpenSubgroupsOfIndex_of_topologicallyFinitelyGenerated (G := G) hG,
    exists_characteristicOpenBasis_of_topologicallyFinitelyGenerated (G := G) hG⟩

end IndexFamilies


section HopfianStep

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace Set

/-- An injective self-map of a finite set is automatically surjective on that set. -/
theorem Finite.surjOn_of_injOn_mapsTo {α : Type*} {s : Set α}
    (hs : s.Finite) {f : α → α}
    (hf : MapsTo f s s) (hinj : InjOn f s) :
    SurjOn f s s := by
  classical
  let g : s → s := fun x => ⟨f x.1, hf x.2⟩
  have hg_inj : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    exact hinj x.2 y.2 (congrArg Subtype.val hxy)
  have : Finite s := hs.to_subtype
  have hg_surj : Function.Surjective g := Finite.surjective_of_injective hg_inj
  intro y hy
  rcases hg_surj ⟨y, hy⟩ with ⟨x, hx⟩
  refine ⟨x.1, x.2, ?_⟩
  exact congrArg Subtype.val hx

end Set

/-- Open normal subgroups separate the identity from every nontrivial element. -/
def OpenNormalSeparatesPoints (G : Type u) [Group G] [TopologicalSpace G]
    : Prop :=
  ∀ x : G, x ≠ 1 → ∃ U : Subgroup G, U.Normal ∧ IsOpen (U : Set G) ∧ x ∉ U

/--
If every kernel element lies in every open normal subgroup and open normal subgroups separate
points, then the endomorphism is injective.
-/
theorem injective_of_ker_le_every_openNormal
    {φ : ContinuousMonoidHom G G}
    (hker : ∀ U : Subgroup G, U.Normal → IsOpen (U : Set G) → φ.ker ≤ U)
    (hsep : OpenNormalSeparatesPoints G) :
    Function.Injective φ := by
  intro x y hxy
  have hmem : x * y⁻¹ ∈ φ.ker := by
    simp only [ContinuousMonoidHom.coe_toMonoidHom, MonoidHom.mem_ker, MonoidHom.coe_coe,
        map_mul, hxy, map_inv,
  mul_inv_cancel]
  have hone : x * y⁻¹ = 1 := by
    by_contra hne
    obtain ⟨U, hU_normal, hU_open, hnotU⟩ := hsep (x * y⁻¹) hne
    exact hnotU (hker U hU_normal hU_open hmem)
  have hmul := congrArg (fun z => z * y) hone
  simpa [mul_assoc] using hmul

/-- The preimage operator preserves the fixed-index family of open normal subgroups. -/
def PreimagePreservesOpenNormalSubgroupsOfIndex
    (φ : ContinuousMonoidHom G G) : Prop :=
  ∀ n,
    Set.MapsTo (fun U : Subgroup G => Subgroup.comap φ.toMonoidHom U)
      (OpenNormalSubgroupsOfIndex (G := G) n)
      (OpenNormalSubgroupsOfIndex (G := G) n)

omit [TopologicalSpace G] in
/-- Comap along a surjective homomorphism is injective on subgroups. -/
theorem subgroupComap_injective_of_surjective
    {H : Type v} [Group H]
    (f : G →* H) (hf : Function.Surjective f) :
    Function.Injective (Subgroup.comap f) := by
  intro U V hUV
  ext y
  constructor <;> intro hy
  · rcases hf y with ⟨x, rfl⟩
    change x ∈ Subgroup.comap f V
    have hx : x ∈ Subgroup.comap f U := hy
    simpa [hUV] using hx
  · rcases hf y with ⟨x, rfl⟩
    change x ∈ Subgroup.comap f U
    have hx : x ∈ Subgroup.comap f V := hy
    simpa [hUV] using hx

/-- Preimage under a surjective endomorphism is injective on each fixed-index open-normal family. -/
theorem preimage_injectiveOn_openNormalSubgroupsOfIndex
    {φ : ContinuousMonoidHom G G}
    (hφsurj : Function.Surjective φ) (n : ℕ) :
    Set.InjOn (fun U : Subgroup G => Subgroup.comap φ.toMonoidHom U)
      (OpenNormalSubgroupsOfIndex (G := G) n) := by
  intro U hU V hV hEq
  exact subgroupComap_injective_of_surjective (G := G) φ.toMonoidHom hφsurj hEq

/--
Surjectivity of the preimage operator on each family of open normal subgroups of index \(n\).
This is exactly the conclusion obtained from the finiteness of the family \(U_n\).
-/
def PreimageSurjectiveOnOpenNormalSubgroupsOfIndex
    (φ : ContinuousMonoidHom G G) : Prop :=
  ∀ n,
    Set.SurjOn (fun U : Subgroup G => Subgroup.comap φ.toMonoidHom U)
      (OpenNormalSubgroupsOfIndex (G := G) n)
      (OpenNormalSubgroupsOfIndex (G := G) n)

/--
For finite groups, preimage along a surjective endomorphism is surjective on open normal
subgroups of fixed index.
-/
theorem preimageSurjectiveOn_openNormalSubgroupsOfIndex_of_finite
    {φ : ContinuousMonoidHom G G}
    (hfin : HasFiniteOpenNormalSubgroupsOfIndex G)
    (hφsurj : Function.Surjective φ)
    (hpres : PreimagePreservesOpenNormalSubgroupsOfIndex (G := G) φ) :
    PreimageSurjectiveOnOpenNormalSubgroupsOfIndex (G := G) φ := by
  intro n
  exact Set.Finite.surjOn_of_injOn_mapsTo
    (hs := hfin n)
    (f := fun U : Subgroup G => Subgroup.comap φ.toMonoidHom U)
    (hpres n)
    (preimage_injectiveOn_openNormalSubgroupsOfIndex (G := G) hφsurj n)

/--
If the preimage map is surjective on every fixed-index open-normal family, then \(\ker \varphi
\le U\) for every open normal subgroup \(U\).
-/
theorem ker_le_every_openNormal_of_preimageSurjectiveOn_index
    [IsTopologicalGroup G] [CompactSpace G]
    {φ : ContinuousMonoidHom G G}
    (hφ : PreimageSurjectiveOnOpenNormalSubgroupsOfIndex (G := G) φ) :
    ∀ U : Subgroup G, U.Normal → IsOpen (U : Set G) → φ.ker ≤ U := by
  intro U hU_normal hU_open
  have hUfinite : Finite (G ⧸ U) :=
    Subgroup.quotient_finite_of_isOpen U hU_open
  let n : ℕ := Nat.card (G ⧸ U)
  have hU : U ∈ OpenNormalSubgroupsOfIndex (G := G) n := by
    exact ⟨hU_normal, hU_open, hUfinite, rfl⟩
  rcases hφ n hU with ⟨V, hV, hEq⟩
  rw [← hEq]
  intro x hx
  change φ x ∈ V
  have hx1 : φ x = 1 := by
    change φ x = 1 at hx
    exact hx
  rw [hx1]
  exact V.one_mem

/-- The fixed-index Hopfian kernel-separation hypotheses imply injectivity. -/
theorem injective_of_preimageSurjectiveOn_openNormalIndex
    [IsTopologicalGroup G] [CompactSpace G]
    {φ : ContinuousMonoidHom G G}
    (hφ : PreimageSurjectiveOnOpenNormalSubgroupsOfIndex (G := G) φ)
    (hsep : OpenNormalSeparatesPoints G) :
    Function.Injective φ := by
  apply injective_of_ker_le_every_openNormal
  · exact ker_le_every_openNormal_of_preimageSurjectiveOn_index (G := G) hφ
  · exact hsep

/--
A topological group is continuously Hopfian if every surjective continuous endomorphism is
injective.
-/
def ContinuousHopfian (G : Type u) [Group G] [TopologicalSpace G] : Prop :=
  ∀ φ : ContinuousMonoidHom G G, Function.Surjective φ → Function.Injective φ

/-- Every surjective continuous endomorphism is induced by a continuous automorphism. -/
def SurjectiveContinuousEndomorphismsAreAutomorphisms
    (G : Type u) [Group G] [TopologicalSpace G] : Prop :=
  ∀ φ : ContinuousMonoidHom G G, Function.Surjective φ →
    ∃ e : G ≃ₜ* G, ∀ x : G, e x = φ x

/--
Upgrade a continuous bijective endomorphism of a compact Hausdorff topological group to a
continuous automorphism.
-/
noncomputable def ContinuousMonoidHom.toContinuousMulEquivOfBijective
    [CompactSpace G] [T2Space G]
    (φ : ContinuousMonoidHom G G) (hφ : Function.Bijective φ) :
    G ≃ₜ* G := by
  let e : G ≃ G := Equiv.ofBijective φ hφ
  let eh : G ≃ₜ G :=
    e.toHomeomorphOfContinuousClosed φ.continuous_toFun
      (Continuous.isClosedMap φ.continuous_toFun)
  exact ContinuousMulEquiv.mk' eh (by
    intro x y
    exact φ.map_mul x y)

/-- A continuously Hopfian group has all surjective continuous endomorphisms invertible. -/
theorem surjectiveContinuousEndomorphismsAreAutomorphisms_of_continuousHopfian
    [CompactSpace G] [T2Space G]
    (hhopf : ContinuousHopfian G) :
    SurjectiveContinuousEndomorphismsAreAutomorphisms G := by
  intro φ hφsurj
  let e := ContinuousMonoidHom.toContinuousMulEquivOfBijective
    (G := G) φ ⟨hhopf φ hφsurj, hφsurj⟩
  refine ⟨e, ?_⟩
  intro x
  rfl

/--
Once the preimage-surjectivity statement on fixed-index open normal subgroups is available for
all surjective continuous endomorphisms, the Hopfian conclusion follows mathematically.
-/
theorem continuousHopfian_of_preimageSurjectiveOn_openNormalIndex
    [IsTopologicalGroup G] [CompactSpace G]
    (hsep : OpenNormalSeparatesPoints G)
    (hpre : ∀ φ : ContinuousMonoidHom G G, Function.Surjective φ →
      PreimageSurjectiveOnOpenNormalSubgroupsOfIndex (G := G) φ) :
    ContinuousHopfian G := by
  intro φ hφsurj
  exact injective_of_preimageSurjectiveOn_openNormalIndex (G := G) (hpre φ hφsurj) hsep

/-- Finiteness of open normal subgroups of each index implies the continuous Hopfian property. -/
theorem continuousHopfian_of_finiteOpenNormalSubgroupsOfIndex
    [IsTopologicalGroup G] [CompactSpace G]
    (hsep : OpenNormalSeparatesPoints G)
    (hfin : HasFiniteOpenNormalSubgroupsOfIndex G)
    (hpres :
      ∀ φ : ContinuousMonoidHom G G, Function.Surjective φ →
        PreimagePreservesOpenNormalSubgroupsOfIndex (G := G) φ) :
    ContinuousHopfian G := by
  apply continuousHopfian_of_preimageSurjectiveOn_openNormalIndex (G := G) hsep
  intro φ hφsurj
  exact preimageSurjectiveOn_openNormalSubgroupsOfIndex_of_finite
    (G := G) hfin hφsurj (hpres φ hφsurj)

/-- Fixed-index finiteness of open normal subgroups implies the profinite Hopfian conclusion. -/
theorem surjContinuousEndomorphismsAreAutomorphisms_of_finiteOpenNormalSubgroupsOfIndex
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (hsep : OpenNormalSeparatesPoints G)
    (hfin : HasFiniteOpenNormalSubgroupsOfIndex G)
    (hpres :
      ∀ φ : ContinuousMonoidHom G G, Function.Surjective φ →
        PreimagePreservesOpenNormalSubgroupsOfIndex (G := G) φ) :
    SurjectiveContinuousEndomorphismsAreAutomorphisms G := by
  apply surjectiveContinuousEndomorphismsAreAutomorphisms_of_continuousHopfian
  exact continuousHopfian_of_finiteOpenNormalSubgroupsOfIndex (G := G) hsep hfin hpres

/--
In a profinite group, open normal subgroups separate the identity from every nontrivial element.
-/
theorem openNormalSeparatesPoints_of_profinite
    [IsTopologicalGroup G] [CompactSpace G] [T1Space G] [TotallyDisconnectedSpace G] :
    OpenNormalSeparatesPoints G := by
  intro x hx
  let U : Set G := ({x} : Set G)ᶜ
  have hUopen : IsOpen U := isClosed_singleton.isOpen_compl
  have h1U : (1 : G) ∈ U := by
    simpa [U, eq_comm] using hx
  rcases exists_openNormalSubgroup_sub_open_nhds_of_one (G := G) hUopen h1U with ⟨N, hNU⟩
  refine ⟨N, N.isNormal', openNormalSubgroup_isOpen (G := G) N, ?_⟩
  intro hxN
  have hxU : x ∈ U := hNU hxN
  simp only [mem_compl_iff, mem_singleton_iff, not_true_eq_false, U] at hxU

/--
Preimage along a surjective continuous endomorphism preserves open normal subgroups of fixed
index.
-/
theorem preimagePreservesOpenNormalSubgroupsOfIndex_of_surjective
    [IsTopologicalGroup G] [CompactSpace G]
    {φ : ContinuousMonoidHom G G} (hφsurj : Function.Surjective φ) :
    PreimagePreservesOpenNormalSubgroupsOfIndex (G := G) φ := by
  intro n U hU
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hU.1.comap φ.toMonoidHom
  · exact hU.2.1.preimage φ.continuous_toFun
  · exact Subgroup.quotient_finite_of_isOpen
      (Subgroup.comap φ.toMonoidHom U) (hU.2.1.preimage φ.continuous_toFun)
  · simpa [Subgroup.index_eq_card] using
      (Subgroup.index_comap_of_surjective (H := U) hφsurj).trans hU.2.2.2

/--
A surjective continuous endomorphism of a topologically finitely generated profinite group is
automatically a continuous automorphism.
-/
theorem surjContinuousEndomorphismsAreAutomorphisms_of_topologicallyFinitelyGenerated
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    : TopologicallyFinitelyGenerated G →
        ∀ φ : ContinuousMonoidHom G G, Function.Surjective φ →
          ∃ e : G ≃ₜ* G, ∀ x : G, e x = φ x := by
  intro hG
  apply surjContinuousEndomorphismsAreAutomorphisms_of_finiteOpenNormalSubgroupsOfIndex
  · exact openNormalSeparatesPoints_of_profinite (G := G)
  · exact HasFiniteOpenSubgroupsOfIndex.toHasFiniteOpenNormalSubgroupsOfIndex
      (h := hasFiniteOpenSubgroupsOfIndex_of_topologicallyFinitelyGenerated (G := G) hG)
  · intro φ hφsurj
    exact preimagePreservesOpenNormalSubgroupsOfIndex_of_surjective (G := G) hφsurj

end HopfianStep


end ProCGroups.FiniteGeneration
