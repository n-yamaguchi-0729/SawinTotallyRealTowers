/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Global.EverywhereUnramifiedBridge
import Mathlib.GroupTheory.PGroup

set_option autoImplicit false
/-!
# The maximal everywhere-unramified pro-p subextension

Inside a fixed algebraic closure of a number field, this file forms the
compositum of all finite Galois everywhere-unramified intermediate fields
whose automorphism group is a `p`-group. The results here are the lattice
universal properties of that compositum; finite-support and Galois properties
of the resulting infinite extension belong to later leaves.
-/

open scoped NumberField

noncomputable section

universe u

namespace ClassFieldTower.Martinet

/-- The compositum, inside `AlgebraicClosure F`, of all finite Galois
everywhere-unramified extensions of `F` with `p`-group Galois group.

The binder order matches the corresponding trusted LeanEval definition. -/
def maximalEverywhereUnramifiedProP
    (F : Type u) [Field F] [NumberField F]
    (p : ℕ) [Fact (Nat.Prime p)] :
    IntermediateField F (AlgebraicClosure F) :=
  ⨆ (M : IntermediateField F (AlgebraicClosure F))
      (_ : FiniteDimensional F M)
      (_ : IsGalois F M)
      (_ : IsPGroup p (M ≃ₐ[F] M))
      (_ : NumberField M)
      (_ : IsEverywhereUnramified F M),
    M

/-- Every finite Galois everywhere-unramified `p`-extension contained in the
chosen algebraic closure lies in the maximal compositum. -/
theorem le_maximalEverywhereUnramifiedProP
    (F : Type u) [Field F] [NumberField F]
    (p : ℕ) [Fact (Nat.Prime p)]
    (M : IntermediateField F (AlgebraicClosure F))
    [FiniteDimensional F M]
    [IsGalois F M]
    (hP : IsPGroup p (M ≃ₐ[F] M))
    [NumberField M]
    (hM : IsEverywhereUnramified F M) :
    M ≤ maximalEverywhereUnramifiedProP F p := by
  apply le_iSup_of_le M
  apply le_iSup_of_le (inferInstance : FiniteDimensional F M)
  apply le_iSup_of_le (inferInstance : IsGalois F M)
  apply le_iSup_of_le hP
  apply le_iSup_of_le (inferInstance : NumberField M)
  exact le_iSup_of_le hM le_rfl

/-- The maximal compositum lies in an intermediate field exactly when every
candidate used to form it lies in that field. -/
theorem maximalEverywhereUnramifiedProP_le_iff
    (F : Type u) [Field F] [NumberField F]
    (p : ℕ) [Fact (Nat.Prime p)]
    (N : IntermediateField F (AlgebraicClosure F)) :
    maximalEverywhereUnramifiedProP F p ≤ N ↔
      ∀ (M : IntermediateField F (AlgebraicClosure F))
        [FiniteDimensional F M]
        [IsGalois F M]
        (_ : IsPGroup p (M ≃ₐ[F] M))
        [NumberField M],
        IsEverywhereUnramified F M → M ≤ N := by
  simp only [maximalEverywhereUnramifiedProP, iSup_le_iff]

/-- The maximal compositum is the least upper bound of all finite Galois
everywhere-unramified `p`-extensions in the chosen algebraic closure. -/
theorem maximalEverywhereUnramifiedProP_le_of_forall_le
    (F : Type u) [Field F] [NumberField F]
    (p : ℕ) [Fact (Nat.Prime p)]
    (N : IntermediateField F (AlgebraicClosure F))
    (hN : ∀ (M : IntermediateField F (AlgebraicClosure F))
      [FiniteDimensional F M]
      [IsGalois F M]
      (_ : IsPGroup p (M ≃ₐ[F] M))
      [NumberField M],
      IsEverywhereUnramified F M → M ≤ N) :
    maximalEverywhereUnramifiedProP F p ≤ N :=
  (maximalEverywhereUnramifiedProP_le_iff F p N).2 hN

/-- An intermediate field is the maximal compositum exactly when it is an
upper bound for every candidate and is itself contained in the compositum. -/
theorem maximalEverywhereUnramifiedProP_eq_iff
    (F : Type u) [Field F] [NumberField F]
    (p : ℕ) [Fact (Nat.Prime p)]
    (N : IntermediateField F (AlgebraicClosure F)) :
    maximalEverywhereUnramifiedProP F p = N ↔
      (∀ (M : IntermediateField F (AlgebraicClosure F))
        [FiniteDimensional F M]
        [IsGalois F M]
        (_ : IsPGroup p (M ≃ₐ[F] M))
        [NumberField M],
        IsEverywhereUnramified F M → M ≤ N) ∧
      N ≤ maximalEverywhereUnramifiedProP F p := by
  constructor
  · intro h
    subst N
    exact
      ⟨fun M _ _ hP _ hM ↦
          le_maximalEverywhereUnramifiedProP F p M hP hM,
        le_rfl⟩
  · rintro ⟨hUpper, hLower⟩
    exact le_antisymm
      (maximalEverywhereUnramifiedProP_le_of_forall_le F p N hUpper)
      hLower

end ClassFieldTower.Martinet
