import ProCGroups.Generation.Basic

set_option autoImplicit false

/-!
# Pro C Groups / Group Theory / Centralizers

Centralizer lemmas and closed-cyclic-subgroup results used by the profinite applications.
-/

open scoped Pointwise

namespace ProCGroups.GroupTheory

universe u

variable {G : Type u} [Group G]

/-- The centralizer of a set of elements. -/
abbrev centralizer (S : Set G) : Subgroup G :=
  Subgroup.centralizer S

/-- The centralizer of a single element. -/
abbrev centralizerOf (g : G) : Subgroup G :=
  centralizer ({g} : Set G)

/-- Membership in the centralizer is equivalent to the displayed commutation condition. -/
@[simp] theorem mem_centralizer_iff {S : Set G} {g : G} :
    g ∈ centralizer S ↔ ∀ h ∈ S, h * g = g * h :=
  Iff.rfl


/--
Membership in the centralizer of a subset is equivalent to the displayed commutation condition.
-/
@[simp] theorem mem_centralizerOf_iff {x g : G} :
    x ∈ centralizerOf g ↔ x * g = g * x := by
  simpa [centralizerOf, centralizer] using
    (Subgroup.mem_centralizer_singleton_iff (g := g) (k := x))

/-- Centralizing an element implies centralizing each of its natural powers. -/
theorem mem_centralizerOf_pow_of_mem {x y : G} (hy : y ∈ centralizerOf x) (n : ℕ) :
    y ∈ centralizerOf (x ^ n) := by
  rw [mem_centralizerOf_iff] at hy ⊢
  induction n with
  | zero =>
      simp only [pow_zero, mul_one, one_mul]
  | succ n ih =>
      calc
        y * x ^ (n + 1) = (y * x ^ n) * x := by rw [pow_succ, mul_assoc]
        _ = (x ^ n * y) * x := by rw [ih]
        _ = x ^ n * (y * x) := by rw [mul_assoc]
        _ = x ^ n * (x * y) := by rw [hy]
        _ = x ^ (n + 1) * y := by rw [pow_succ, mul_assoc]

/--
Membership of an inverse in the centralizer of a subset is equivalent to the displayed
commutation condition.
-/
theorem mem_centralizerOf_inv_iff {x y : G} :
    y ∈ centralizerOf x⁻¹ ↔ y ∈ centralizerOf x := by
  rw [mem_centralizerOf_iff, mem_centralizerOf_iff]
  constructor
  · intro h
    have h' := congrArg (fun z => x * z * x) h
    simpa [mul_assoc] using h'.symm
  · intro h
    have h' := congrArg (fun z => x⁻¹ * z * x⁻¹) h
    simpa [mul_assoc] using h'.symm

/--
Replacing a nonzero integer power by its positive absolute value does not change the
centralizer.
-/
theorem centralizerOf_zpow_eq_natAbs (x : G) {n : ℤ} (_hn : n ≠ 0) :
    centralizerOf (x ^ n) = centralizerOf (x ^ (n.natAbs : ℤ)) := by
  cases n with
  | ofNat k =>
      simp only [Int.ofNat_eq_natCast, zpow_natCast, Int.natAbs_natCast]
  | negSucc k =>
      ext y
      simp only [Int.natAbs, zpow_negSucc, zpow_natCast]
      exact mem_centralizerOf_inv_iff

/--
Centralizing a nonzero integer power is equivalent, for membership purposes, to centralizing the
corresponding positive absolute power.
-/
theorem mem_centralizerOf_zpow_natAbs_of_mem_zpow {x y : G} {n : ℤ} (hn : n ≠ 0)
    (hy : y ∈ centralizerOf (x ^ n)) :
    y ∈ centralizerOf (x ^ (n.natAbs : ℤ)) := by
  rwa [← centralizerOf_zpow_eq_natAbs x hn]


/-- If c and \(c * d\) centralize x, then d centralizes x. -/
theorem right_factor_mem_centralizerOf_of_mul_mem_and_left_mem {x c d : G}
    (hc : c ∈ centralizerOf x) (hcd : c * d ∈ centralizerOf x) :
    d ∈ centralizerOf x := by
  rw [mem_centralizerOf_iff] at hc hcd ⊢
  calc
    d * x = c⁻¹ * (c * d * x) := by simp [mul_assoc]
    _ = c⁻¹ * (x * (c * d)) := by rw [hcd]
    _ = c⁻¹ * ((x * c) * d) := by simp [mul_assoc]
    _ = c⁻¹ * ((c * x) * d) := by rw [← hc]
    _ = x * d := by simp [mul_assoc]


/-- In a Hausdorff topological group, the centralizer of one element is closed. -/
theorem centralizerOf_isClosed
    [TopologicalSpace G] [ContinuousMul G] [T2Space G] (g : G) :
    IsClosed ((centralizerOf g : Subgroup G) : Set G) := by
  change IsClosed ({g} : Set G).centralizer
  exact Set.isClosed_centralizer (M := G) ({g} : Set G)


/-- Topological generation preserves containment in a closed centralizer. -/
theorem closedSubgroupGenerated_le_centralizer_of_subset
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    {S T : Set G} (hS : S ⊆ (centralizer T : Set G)) :
    (ProCGroups.Generation.closedSubgroupGenerated (G := G) S : Subgroup G) ≤ centralizer T := by
  have hclosure : Subgroup.closure S ≤ centralizer T := by
    rw [Subgroup.closure_le]
    exact hS
  exact
    Subgroup.topologicalClosure_minimal
      _
      hclosure
      (by
        change IsClosed T.centralizer
        exact Set.isClosed_centralizer (M := G) T)

/-- A subgroup and its topological closure have the same centralizer. -/
theorem centralizer_eq_centralizer_topologicalClosure
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] (S : Subgroup G) :
    centralizer ((S.topologicalClosure : Subgroup G) : Set G) = centralizer (S : Set G) := by
  apply le_antisymm
  · exact Subgroup.centralizer_le (G := G) (Subgroup.le_topologicalClosure (s := S))
  · intro g hg
    rw [mem_centralizer_iff] at hg ⊢
    have hclosure : (S.topologicalClosure : Subgroup G) ≤ centralizerOf g := by
      exact
        Subgroup.topologicalClosure_minimal
          S
          (by
            intro x hx
            exact mem_centralizerOf_iff.mpr (hg x hx))
          (centralizerOf_isClosed (G := G) g)
    intro x hx
    exact mem_centralizerOf_iff.mp (hclosure hx)

/--
The closed subgroup topologically generated by \(g\) centralizes every integer power of \(g\).
-/
theorem closedSubgroupGenerated_singleton_le_centralizerOf_zpow
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    (g : G) (n : ℤ) :
    (ProCGroups.Generation.closedSubgroupGenerated (G := G) ({g} : Set G) : Subgroup G) ≤
      centralizerOf (g ^ n) := by
  have hclosure :
      Subgroup.closure ({g} : Set G) ≤ centralizerOf (g ^ n) := by
    rw [Subgroup.closure_le]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    exact mem_centralizerOf_iff.mpr
      (by simpa using (Commute.zpow_zpow_self g (1 : ℤ) n).eq)
  exact
    Subgroup.topologicalClosure_minimal
      _
      hclosure
      (centralizerOf_isClosed (G := G) (g ^ n))

/--
Every element in the closed subgroup topologically generated by \(x\) centralizes each integer
power of \(x\).
-/
theorem mem_centralizerOf_zpow_of_mem_closedSubgroupGenerated
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    {x c : G} (n : ℤ)
    (hc : c ∈ (ProCGroups.Generation.closedSubgroupGenerated (G := G) ({x} : Set G) :
      Subgroup G)) :
    c ∈ centralizerOf (x ^ n) :=
  (closedSubgroupGenerated_singleton_le_centralizerOf_zpow (G := G) x n) hc

/--
If a single element topologically generates the group, the centralizer of any of its powers is
the corresponding closed cyclic subgroup.
-/
theorem centralizerOf_zpow_eq_closedSubgroupGenerated_of_topologicallyGenerates
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    (x : G) (n : ℤ)
    (hgen : ProCGroups.Generation.TopologicallyGenerates (G := G) ({x} : Set G)) :
    centralizerOf (x ^ n) =
      (ProCGroups.Generation.closedSubgroupGenerated (G := G) ({x} : Set G) : Subgroup G) := by
  have hcyc :
      (ProCGroups.Generation.closedSubgroupGenerated (G := G) ({x} : Set G) : Subgroup G) =
        ⊤ := by
    unfold ProCGroups.Generation.TopologicallyGenerates at hgen
    simpa [ProCGroups.Generation.closedSubgroupGenerated] using hgen
  have hcent_top : centralizerOf (x ^ n) = ⊤ := by
    apply top_unique
    rw [← hcyc]
    exact closedSubgroupGenerated_singleton_le_centralizerOf_zpow (G := G) x n
  simpa [hcyc] using hcent_top

end ProCGroups.GroupTheory
