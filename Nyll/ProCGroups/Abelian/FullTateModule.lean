/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Torsion
import Mathlib.Data.PNat.Basic
import Mathlib.Topology.Algebra.Group.Subgroup
import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# The full Tate module of an additive commutative group

The full Tate module consists of actual torsion points indexed by positive
integers, compatible under multiplication. It is torsion-free: if a positive
integer annihilates a compatible family, compatibility with the levels
multiplied by that integer makes every coordinate zero.

Each torsion level is given the discrete topology. The induced product
subspace topology on the limit is Hausdorff and totally disconnected, and
is compact when every actual torsion subgroup is finite.
-/

namespace ProCGroups

universe u

variable (M : Type u) [AddCommGroup M]

/-- The actual subgroup of points annihilated by a positive integer. -/
def torsionLevel (n : ℕ+) : AddSubgroup M where
  carrier := {x : M | (n : ℕ) • x = 0}
  zero_mem' := nsmul_zero (n : ℕ)
  add_mem' := by
    intro x y hx hy
    change (n : ℕ) • (x + y) = 0
    rw [nsmul_add, hx, hy, zero_add]
  neg_mem' := by
    intro x hx
    change (n : ℕ) • (-x) = 0
    rw [smul_neg, hx, neg_zero]

/-- Multiplication by `m` maps the actual `(n*m)`-torsion into the `n`-torsion. -/
def torsionTransition (n m : ℕ+) : torsionLevel M (n * m) →+ torsionLevel M n where
  toFun x := ⟨(m : ℕ) • x.val, by
    change (n : ℕ) • ((m : ℕ) • x.val) = 0
    rw [← mul_nsmul, Nat.mul_comm]
    exact x.property⟩
  map_zero' := by
    apply Subtype.ext
    exact nsmul_zero (m : ℕ)
  map_add' := by
    intro x y
    apply Subtype.ext
    exact nsmul_add x.val y.val (m : ℕ)

/-- The subgroup of the product satisfying every multiplication transition. -/
def compatibleTorsionFamilies : AddSubgroup (∀ n : ℕ+, torsionLevel M n) where
  carrier := {x | ∀ n m : ℕ+, torsionTransition M n m (x (n * m)) = x n}
  zero_mem' := by
    intro n m
    exact (torsionTransition M n m).map_zero
  add_mem' := by
    intro x y hx hy n m
    change torsionTransition M n m (x (n * m) + y (n * m)) = x n + y n
    rw [map_add, hx n m, hy n m]
  neg_mem' := by
    intro x hx n m
    change torsionTransition M n m (-x (n * m)) = -x n
    rw [map_neg, hx n m]

/-- The full Tate module, realized as compatible actual torsion families. -/
def FullTateModule : Type u := ↥(compatibleTorsionFamilies M)

namespace FullTateModule

instance : AddCommGroup (FullTateModule M) :=
  inferInstanceAs (AddCommGroup ↥(compatibleTorsionFamilies M))

/-- The canonical projection to an actual torsion subgroup. -/
def projection (n : ℕ+) : FullTateModule M →+ torsionLevel M n where
  toFun x := x.val n
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The `n`-th torsion point, viewed in the original group. -/
def evaluation (n : ℕ+) : FullTateModule M →+ M :=
  (torsionLevel M n).subtype.comp (projection M n)

variable {M}

/-- Two full Tate elements agree when their actual torsion points agree. -/
@[ext] theorem ext {x y : FullTateModule M}
    (h : ∀ n : ℕ+, evaluation M n x = evaluation M n y) : x = y := by
  apply Subtype.ext
  funext n
  apply Subtype.ext
  exact h n

/-- Every projected point is annihilated by its index. -/
theorem evaluation_annihilated (x : FullTateModule M) (n : ℕ+) :
    (n : ℕ) • evaluation M n x = 0 :=
  (projection M n x).property

/-- The compatibility equation holds in the original additive group. -/
theorem evaluation_compatible (x : FullTateModule M) (n m : ℕ+) :
    (m : ℕ) • evaluation M (n * m) x = evaluation M n x :=
  congrArg (fun z : torsionLevel M n => z.val) (x.property n m)

/-- No nonzero positive-integer torsion occurs in the constructed full Tate module. -/
theorem eq_zero_of_nsmul_eq_zero (x : FullTateModule M) {n : ℕ}
    (hn : 0 < n) (hx : n • x = 0) : x = 0 := by
  apply ext
  intro k
  let np : ℕ+ := ⟨n, hn⟩
  have hCoordinate : n • evaluation M (k * np) x = 0 := by
    have h := congrArg (evaluation M (k * np)) hx
    rw [map_nsmul, map_zero] at h
    exact h
  rw [map_zero]
  exact (evaluation_compatible x k np).symm.trans hCoordinate

instance : IsAddTorsionFree (FullTateModule M) where
  nsmul_right_injective := by
    intro n hn x y hxy
    change n • x = n • y at hxy
    apply sub_eq_zero.mp
    apply eq_zero_of_nsmul_eq_zero (x - y) (Nat.pos_of_ne_zero hn)
    rw [nsmul_sub, hxy, sub_self]

variable (M)

/-- The chosen topology at a torsion level is discrete, independently of any
topology on the original group. It is installed only locally in this module. -/
@[instance_reducible]
def torsionLevelTopology (n : ℕ+) : TopologicalSpace (torsionLevel M n) := ⊥

attribute [local instance] torsionLevelTopology

local instance (n : ℕ+) : DiscreteTopology (torsionLevel M n) := ⟨rfl⟩

/-- The full Tate topology is the subspace topology of the product of the
discrete actual torsion levels. -/
instance : TopologicalSpace (FullTateModule M) :=
  inferInstanceAs (TopologicalSpace ↥(compatibleTorsionFamilies M))

instance : IsTopologicalAddGroup (FullTateModule M) :=
  inferInstanceAs (IsTopologicalAddGroup ↥(compatibleTorsionFamilies M))

instance : T2Space (FullTateModule M) :=
  inferInstanceAs (T2Space ↥(compatibleTorsionFamilies M))

instance : TotallyDisconnectedSpace (FullTateModule M) :=
  inferInstanceAs (TotallyDisconnectedSpace ↥(compatibleTorsionFamilies M))

/-- Projection to every discrete torsion level is continuous. -/
theorem continuous_projection (n : ℕ+) : Continuous (projection M n) :=
  (continuous_apply n).comp continuous_subtype_val

/-- Compatibility cuts out a closed subspace of the discrete-level product. -/
theorem isClosed_compatibleTorsionFamilies :
    IsClosed (compatibleTorsionFamilies M : Set (∀ n : ℕ+, torsionLevel M n)) := by
  change IsClosed {x : ∀ n : ℕ+, torsionLevel M n |
    ∀ n m : ℕ+, torsionTransition M n m (x (n * m)) = x n}
  simp only [Set.ofPred_forall]
  refine isClosed_iInter fun n => isClosed_iInter fun m => ?_
  exact isClosed_eq
    ((continuous_of_discreteTopology : Continuous (torsionTransition M n m)).comp
      (continuous_apply (n * m))) (continuous_apply n)

/-- Finite actual torsion levels make the full Tate module compact. -/
instance [∀ n : ℕ+, Finite (torsionLevel M n)] : CompactSpace (FullTateModule M) :=
  (isClosed_compatibleTorsionFamilies M).isClosedEmbedding_subtypeVal.compactSpace

end FullTateModule

end ProCGroups
