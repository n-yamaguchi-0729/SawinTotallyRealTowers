import ProCGroups.ProP.Zassenhaus.Functoriality

set_option autoImplicit false
/-!
# Zassenhaus depth predicates

Depth is exposed through `at least`, `exactly`, and `infinite` predicates.
This avoids assigning an arbitrary finite value to elements lying in every
filtration layer, and gives the later relation-counting API a decidable
finite-index predicate without installing new data instances.
-/

open scoped Topology

namespace ClassFieldTower.ProP

noncomputable section

universe u

variable (p : ℕ) [Fact p.Prime]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- An element has Zassenhaus depth at least `n` when it belongs to `Dₙ`. -/
def ZassenhausDepthAtLeast (n : ℕ) (g : G) : Prop :=
  g ∈ zassenhausSubgroup p G n

/-- An element has exact finite depth `n` when it belongs to `Dₙ` but not
`Dₙ₊₁`. -/
def ZassenhausDepthExactly (n : ℕ) (g : G) : Prop :=
  ZassenhausDepthAtLeast p n g ∧ ¬ ZassenhausDepthAtLeast p (n + 1) g

/-- An element has infinite depth when it belongs to every Zassenhaus layer. -/
def ZassenhausDepthInfinite (g : G) : Prop :=
  ∀ n, ZassenhausDepthAtLeast p n g

/-- A lower depth bound can be weakened. -/
theorem zassenhausDepthAtLeast_mono {m n : ℕ} (hmn : m ≤ n) {g : G}
    (hg : ZassenhausDepthAtLeast p n g) :
    ZassenhausDepthAtLeast p m g :=
  zassenhausSubgroup_antitone p G hmn hg

/-- Every group element has depth at least one. -/
@[simp] theorem zassenhausDepthAtLeast_one (g : G) :
    ZassenhausDepthAtLeast p 1 g := by
  simp [ZassenhausDepthAtLeast]

/-- The identity lies in every Zassenhaus layer. -/
@[simp] theorem zassenhausDepthInfinite_one :
    ZassenhausDepthInfinite p (1 : G) := by
  intro n
  change (1 : G) ∈ zassenhausSubgroup p G n
  exact (zassenhausSubgroup p G n).one_mem

/-- Exact finite Zassenhaus depth is unique. -/
theorem zassenhausDepthExactly_unique {m n : ℕ} {g : G}
    (hm : ZassenhausDepthExactly p m g)
    (hn : ZassenhausDepthExactly p n g) : m = n := by
  apply le_antisymm
  · by_contra h
    have hnm : n + 1 ≤ m := Nat.add_one_le_iff.mpr (Nat.lt_of_not_ge h)
    exact hn.2 (zassenhausDepthAtLeast_mono p hnm hm.1)
  · by_contra h
    have hmn : m + 1 ≤ n := Nat.add_one_le_iff.mpr (Nat.lt_of_not_ge h)
    exact hm.2 (zassenhausDepthAtLeast_mono p hmn hn.1)

/-- Continuous homomorphisms do not decrease a proved lower depth bound. -/
theorem zassenhausDepthAtLeast_map (f : G →ₜ* H) (n : ℕ) {g : G}
    (hg : ZassenhausDepthAtLeast p n g) :
    ZassenhausDepthAtLeast p n (f g) :=
  map_mem_zassenhausSubgroup p f n hg

/-- Continuous homomorphisms preserve infinite depth. -/
theorem zassenhausDepthInfinite_map (f : G →ₜ* H) {g : G}
    (hg : ZassenhausDepthInfinite p g) :
    ZassenhausDepthInfinite p (f g) := by
  intro n
  exact zassenhausDepthAtLeast_map p f n (hg n)

end

end ClassFieldTower.ProP
