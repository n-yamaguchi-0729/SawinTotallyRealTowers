/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RepresentationTheory.Invariants

/-!
# Divisibility of the augmentation part of a finite-group action

If every action difference is divisible by a scalar, averaging and then
projecting away from the invariants makes the augmentation part divisible
by the same scalar. No finite generation or topology is required.
-/

namespace LocalFieldTheory.DiscreteValuationField

open scoped BigOperators

variable {R Λ M : Type*} [CommRing R] [Group Λ] [Fintype Λ]
  [AddCommGroup M] [Module R M] [Invertible (Fintype.card Λ : R)]

/-- If the action is trivial modulo `c`, the kernel of its averaging
projection is `c`-divisible. This is the actual augmentation submodule:
averaging is a projection, so its kernel is the image of `1 - average`. -/
theorem averageMap_ker_divisible_of_action_sub_divisible
    (ρ : Representation R Λ M) (c : R)
    (hdiv : ∀ (g : Λ) (x : M), ∃ y : M, ρ g x - x = c • y)
    (x : M) (hx : ρ.averageMap x = 0) :
    ∃ y : M, ρ.averageMap y = 0 ∧ c • y = x := by
  classical
  choose z hz using fun g : Λ => hdiv g x
  have hsum : (∑ g : Λ, (ρ g x - x)) = c • ∑ g : Λ, z g := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl (fun g _ => hz g)
  have havg : ρ.averageMap x - x =
      ⅟(Fintype.card Λ : R) • ∑ g : Λ, (ρ g x - x) := by
    rw [Finset.sum_sub_distrib, smul_sub, Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul R, smul_smul, invOf_mul_self, one_smul]
    apply congrArg (fun a : M => a - x)
    simp only [Representation.averageMap, GroupAlgebra.average, map_smul, map_sum,
      Representation.asAlgebraHom_of, LinearMap.smul_apply, LinearMap.sum_apply]
  let b : M := ⅟(Fintype.card Λ : R) • ∑ g : Λ, z g
  have hb : c • b = -x := by
    change c • (⅟(Fintype.card Λ : R) • ∑ g : Λ, z g) = -x
    rw [smul_comm c (⅟(Fintype.card Λ : R)), ← hsum, ← havg, hx, zero_sub]
  have hneg : c • (-b) = x := by
    rw [smul_neg, hb, neg_neg]
  refine ⟨-b - ρ.averageMap (-b), ?_, ?_⟩
  · rw [map_sub,
      ρ.averageMap_id (ρ.averageMap (-b)) (ρ.averageMap_invariant (-b)), sub_self]
  · rw [smul_sub, hneg, ← map_smul, hneg, hx, sub_zero]

end LocalFieldTheory.DiscreteValuationField
