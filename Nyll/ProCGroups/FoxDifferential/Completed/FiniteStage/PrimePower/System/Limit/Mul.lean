/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.FiniteStage.PrimePower.System.Limit.Basic

/-!
# Fox differential: prime power — system — limit — mul

The principal declarations in this module are:

- `foxAlgebraicStagePrimePowerSourceLimitToFamily_one`
  The source-limit family of one is the one family.
- `foxAlgebraicStagePrimePowerSourceLimitToFamily_mul`
  The source-limit family map preserves multiplication.
- `foxAlgebraicStagePrimePowerTargetLimitToFamily_one`
  The target-limit family of one is the one family.
- `foxAlgebraicStagePrimePowerTargetLimitToFamily_mul`
  The target-limit family map preserves multiplication.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u v

variable (ℓ : ℕ)
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]


variable {X : Type u} [DecidableEq X]
variable (N : Subgroup (FreeGroup X)) [N.Normal] (n : ℕ)


/-- The prime-power finite Fox source inverse limit has a coordinatewise multiplicative identity. -/
instance instOneFoxAlgebraicStagePrimePowerSourceLimit
    (N : Subgroup (FreeGroup X)) :
    One (FoxAlgebraicStagePrimePowerSourceLimit (ℓ := ℓ) (X := X) N) where
  one := ⟨fun a => (1 : foxAlgebraicStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N a),
    by
      intro a b hab
      change foxAlgebraicStagePrimePowerSourceTransition (ℓ := ℓ) (X := X) N hab
          (1 : foxAlgebraicStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N b) = 1
      exact map_one _⟩

/--
Multiplication on the prime-power source inverse limit is defined coordinatewise through
finite-stage group-algebra products.
-/
instance instMulFoxAlgebraicStagePrimePowerSourceLimit
    (N : Subgroup (FreeGroup X)) :
    Mul (FoxAlgebraicStagePrimePowerSourceLimit (ℓ := ℓ) (X := X) N) where
  mul x y := ⟨fun a =>
      (show foxAlgebraicStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N a from x.1 a) *
        (show foxAlgebraicStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N a from y.1 a),
    by
      intro a b hab
      change foxAlgebraicStagePrimePowerSourceTransition (ℓ := ℓ) (X := X) N hab
          ((show foxAlgebraicStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N b from x.1 b) *
            (show foxAlgebraicStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N b from y.1 b)) =
        (show foxAlgebraicStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N a from x.1 a) *
          (show foxAlgebraicStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N a from y.1 a)
      rw [map_mul]
      exact congrArg₂ HMul.hMul (x.2 a b hab) (y.2 a b hab)⟩

/-- The prime-power finite Fox target inverse limit has a coordinatewise multiplicative identity. -/
instance instOneFoxAlgebraicStagePrimePowerTargetLimit
    (N : Subgroup (FreeGroup X)) [N.Normal] :
    One (FoxAlgebraicStagePrimePowerTargetLimit (ℓ := ℓ) (X := X) N) where
  one := ⟨fun a => (1 : foxAlgebraicStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N a),
    by
      intro a b hab
      change foxAlgebraicStagePrimePowerTargetTransition (ℓ := ℓ) (X := X) N hab
          (1 : foxAlgebraicStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N b) = 1
      exact map_one _⟩

/--
Multiplication on the prime-power target inverse limit is defined coordinatewise through
finite-stage group-algebra products.
-/
instance instMulFoxAlgebraicStagePrimePowerTargetLimit
    (N : Subgroup (FreeGroup X)) [N.Normal] :
    Mul (FoxAlgebraicStagePrimePowerTargetLimit (ℓ := ℓ) (X := X) N) where
  mul x y := ⟨fun a =>
      (show foxAlgebraicStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N a from x.1 a) *
        (show foxAlgebraicStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N a from y.1 a),
    by
      intro a b hab
      change foxAlgebraicStagePrimePowerTargetTransition (ℓ := ℓ) (X := X) N hab
          ((show foxAlgebraicStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N b from x.1 b) *
            (show foxAlgebraicStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N b from y.1 b)) =
        (show foxAlgebraicStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N a from x.1 a) *
          (show foxAlgebraicStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N a from y.1 a)
      rw [map_mul]
      exact congrArg₂ HMul.hMul (x.2 a b hab) (y.2 a b hab)⟩

omit [DecidableEq X] in
/-- The source-limit family of one is the one family. -/
@[simp]
theorem foxAlgebraicStagePrimePowerSourceLimitToFamily_one
    (N : Subgroup (FreeGroup X)) :
    foxAlgebraicStagePrimePowerSourceLimitToFamily (ℓ := ℓ) (X := X) N 1 = 1 := by
  funext a
  rfl

omit [DecidableEq X] in
/-- The source-limit family map preserves multiplication. -/
@[simp]
theorem foxAlgebraicStagePrimePowerSourceLimitToFamily_mul
    (N : Subgroup (FreeGroup X))
    (x y : FoxAlgebraicStagePrimePowerSourceLimit (ℓ := ℓ) (X := X) N) :
    foxAlgebraicStagePrimePowerSourceLimitToFamily (ℓ := ℓ) (X := X) N (x * y) =
      foxAlgebraicStagePrimePowerSourceLimitToFamily (ℓ := ℓ) (X := X) N x *
        foxAlgebraicStagePrimePowerSourceLimitToFamily (ℓ := ℓ) (X := X) N y := by
  funext a
  rfl

omit [DecidableEq X] in
/-- The target-limit family of one is the one family. -/
@[simp]
theorem foxAlgebraicStagePrimePowerTargetLimitToFamily_one
    (N : Subgroup (FreeGroup X)) [N.Normal] :
    foxAlgebraicStagePrimePowerTargetLimitToFamily (ℓ := ℓ) (X := X) N 1 = 1 := by
  funext a
  rfl

omit [DecidableEq X] in
/-- The target-limit family map preserves multiplication. -/
@[simp]
theorem foxAlgebraicStagePrimePowerTargetLimitToFamily_mul
    (N : Subgroup (FreeGroup X)) [N.Normal]
    (x y : FoxAlgebraicStagePrimePowerTargetLimit (ℓ := ℓ) (X := X) N) :
    foxAlgebraicStagePrimePowerTargetLimitToFamily (ℓ := ℓ) (X := X) N (x * y) =
      foxAlgebraicStagePrimePowerTargetLimitToFamily (ℓ := ℓ) (X := X) N x *
        foxAlgebraicStagePrimePowerTargetLimitToFamily (ℓ := ℓ) (X := X) N y := by
  funext a
  rfl




end

end FoxDifferential
