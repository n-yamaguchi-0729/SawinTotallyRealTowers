/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.Abelian.FullTateModule

/-!
# Finite-exponent characters of the actual full Tate module

The kernel of evaluation at n is exactly n times the full Tate module.
Division inside that kernel is given by shifting the compatible family to
the levels multiplied by n. Thus every character killed by n factors
through the actual n-torsion projection when that projection is surjective.
-/

namespace ProCGroups.FullTateModule

variable {M : Type*} [AddCommGroup M]

/-- A compatible family vanishing at n can be divided by n by shifting
its coordinates; no divisibility assumption on M is needed. -/
theorem exists_nsmul_eq_of_evaluation_eq_zero (n : ℕ+)
    (x : FullTateModule M) (hx : evaluation M n x = 0) :
    ∃ y : FullTateModule M, (n : ℕ) • y = x := by
  let y : FullTateModule M := ⟨fun k => ⟨evaluation M (k * n) x, by
    have h := evaluation_compatible x n k
    rw [mul_comm n k] at h
    exact h.trans hx⟩, by
    intro k m
    apply Subtype.ext
    change (m : ℕ) • evaluation M ((k * m) * n) x = evaluation M (k * n) x
    simpa only [mul_assoc, mul_comm, mul_left_comm] using
      evaluation_compatible x (k * n) m⟩
  refine ⟨y, ?_⟩
  apply ext
  intro k
  change (n : ℕ) • evaluation M (k * n) x = evaluation M k x
  exact evaluation_compatible x k n

/-- The kernel of the n-th evaluation is precisely the subgroup of
n-multiples in the full Tate module. -/
theorem evaluation_eq_zero_iff_exists_nsmul (n : ℕ+) (x : FullTateModule M) :
    evaluation M n x = 0 ↔ ∃ y : FullTateModule M, (n : ℕ) • y = x := by
  constructor
  · exact exists_nsmul_eq_of_evaluation_eq_zero n x
  · rintro ⟨y, rfl⟩
    rw [map_nsmul]
    exact evaluation_annihilated y n

/-- Characters annihilated by n agree on fibres of the n-th projection. -/
theorem character_eq_of_projection_eq
    {H : Type*} [AddCommGroup H] (n : ℕ+)
    (φ : FullTateModule M →+ H) (hH : ∀ a : H, (n : ℕ) • a = 0)
    {x y : FullTateModule M}
    (hxy : projection M n x = projection M n y) : φ x = φ y := by
  have hz : evaluation M n (x - y) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr (congrArg Subtype.val hxy)
  obtain ⟨z, hz⟩ := exists_nsmul_eq_of_evaluation_eq_zero n (x - y) hz
  apply sub_eq_zero.mp
  rw [← map_sub, ← hz, map_nsmul]
  exact hH (φ z)

/-- Every finite-exponent character factors through the same torsion level
if the actual projection is surjective. Continuity is not needed here. -/
theorem character_factors_through_projection
    {H : Type*} [AddCommGroup H] (n : ℕ+)
    (hsurj : Function.Surjective (projection M n))
    (φ : FullTateModule M →+ H) (hH : ∀ a : H, (n : ℕ) • a = 0) :
    ∃ ψ : torsionLevel M n →+ H, ψ.comp (projection M n) = φ := by
  classical
  let q : torsionLevel M n → FullTateModule M := fun a => (hsurj a).choose
  have hq (a : torsionLevel M n) : projection M n (q a) = a :=
    (hsurj a).choose_spec
  let ψ : torsionLevel M n →+ H :=
    { toFun := fun a => φ (q a)
      map_zero' := by
        have h := character_eq_of_projection_eq n φ hH
          ((hq 0).trans (projection M n).map_zero.symm)
        exact h.trans φ.map_zero
      map_add' := by
        intro a b
        have hproj : projection M n (q (a + b)) =
            projection M n (q a + q b) := by
          rw [map_add, hq, hq, hq]
        exact (character_eq_of_projection_eq n φ hH hproj).trans (φ.map_add _ _) }
  refine ⟨ψ, ?_⟩
  ext x
  exact character_eq_of_projection_eq n φ hH (hq (projection M n x))

end ProCGroups.FullTateModule
