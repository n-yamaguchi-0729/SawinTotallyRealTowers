import Mathlib.GroupTheory.Frattini
import Mathlib.Topology.Algebra.Group.ClosedSubgroup

set_option autoImplicit false

/-!
# Pro C Groups / Frattini

This module formalizes Frattini-type constructions for profinite groups.
-/

open Set
open scoped Topology Pointwise

namespace ProCGroups.Frattini

universe u

section MaximalSubgroups

variable {G : Type u} [Group G]

/--
A subgroup is maximal with respect to a predicate P if it satisfies P, is proper, and every
proper overgroup satisfying P is equal to it.
-/
def Subgroup.IsMaximalWithProperty (P : Subgroup G → Prop) (H : Subgroup G) : Prop :=
  P H ∧
    H ≠ ⊤ ∧
    ∀ K : Subgroup G, H ≤ K → P K → K ≠ ⊤ → K = H

namespace Subgroup.IsMaximalWithProperty

variable {P : Subgroup G → Prop} {H K : Subgroup G}

/-- A maximal subgroup with property P satisfies the property P. -/
theorem property (hH : Subgroup.IsMaximalWithProperty (G := G) P H) :
    P H :=
  hH.1

/-- A maximal subgroup in the given class is a proper subgroup. -/
theorem ne_top (hH : Subgroup.IsMaximalWithProperty (G := G) P H) :
    H ≠ ⊤ :=
  hH.2.1

/-- Maximality forces a larger proper subgroup in the same class to be equal. -/
theorem eq_of_le (hH : Subgroup.IsMaximalWithProperty (G := G) P H)
    (hHK : H ≤ K) (hK : P K) (hKne : K ≠ ⊤) :
    K = H :=
  hH.2.2 K hHK hK hKne

end Subgroup.IsMaximalWithProperty

namespace Subgroup.IsMaximalOpen

variable [TopologicalSpace G] {H K : Subgroup G}

/-- A subgroup that is maximal among open subgroups is open. -/
theorem isOpen
    (hH : Subgroup.IsMaximalWithProperty (G := G) (fun K => IsOpen (K : Set G)) H) :
    IsOpen (H : Set G) :=
  hH.1

/-- A maximal subgroup in the given class is a proper subgroup. -/
theorem ne_top
    (hH : Subgroup.IsMaximalWithProperty (G := G) (fun K => IsOpen (K : Set G)) H) :
    H ≠ ⊤ :=
  hH.2.1

/-- Maximality forces a larger proper subgroup in the same class to be equal. -/
theorem eq_of_le
    (hH : Subgroup.IsMaximalWithProperty (G := G) (fun K => IsOpen (K : Set G)) H)
    (hHK : H ≤ K)
    (hKopen : IsOpen (K : Set G)) (hKne : K ≠ ⊤) :
    K = H :=
  hH.2.2 K hHK hKopen hKne

end Subgroup.IsMaximalOpen

namespace Subgroup.IsMaximalClosed

variable [TopologicalSpace G] {H K : Subgroup G}

/-- A maximal closed subgroup is closed. -/
theorem isClosed
    (hH : Subgroup.IsMaximalWithProperty (G := G) (fun K => IsClosed (K : Set G)) H) :
    IsClosed (H : Set G) :=
  hH.1

/-- A maximal subgroup in the given class is a proper subgroup. -/
theorem ne_top
    (hH : Subgroup.IsMaximalWithProperty (G := G) (fun K => IsClosed (K : Set G)) H) :
    H ≠ ⊤ :=
  hH.2.1

/-- Maximality forces a larger proper subgroup in the same class to be equal. -/
theorem eq_of_le
    (hH : Subgroup.IsMaximalWithProperty (G := G) (fun K => IsClosed (K : Set G)) H)
    (hHK : H ≤ K)
    (hKclosed : IsClosed (K : Set G)) (hKne : K ≠ ⊤) :
    K = H :=
  hH.2.2 K hHK hKclosed hKne

end Subgroup.IsMaximalClosed

end MaximalSubgroups

section FrattiniWithin

variable {G : Type u} [Group G]

/-- The Frattini subgroup of \(H\), viewed back inside the ambient group \(G\). -/
def frattiniWithin (H : Subgroup G) : Subgroup G :=
  (frattini H).map H.subtype

/-- The Frattini subgroup within a class is contained in every subgroup from that class. -/
theorem frattiniWithin_le (H : Subgroup G) :
    frattiniWithin (G := G) H ≤ H := by
  intro x hx
  rcases hx with ⟨y, hy, rfl⟩
  exact y.2

/--
Membership in the Frattini subgroup within a class means membership in every subgroup from that
class.
-/
@[simp] theorem mem_frattiniWithin {H : Subgroup G} {x : H} :
    (x : G) ∈ frattiniWithin (G := G) H ↔ x ∈ frattini H := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact (Subtype.ext hxy) ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

end FrattiniWithin

end ProCGroups.Frattini
