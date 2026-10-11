/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraPrimePower.InClass.System.Ring.Multiplicative

/-!
# Fox differential: in class — system — ring — projection

The principal declarations in this module are:

- `primePowerCompletedGroupAlgebraProjectionInClass_one`
  The finite-stage projection sends \(1\) to \(1\).
- `primePowerCompletedGroupAlgebraProjectionInClass_mul`
  The finite-stage projection preserves multiplication.
- `primePowerCompletedGroupAlgebraProjectionInClass_zero`
  The finite-stage projection sends \(0\) to \(0\).
- `primePowerCompletedGroupAlgebraProjectionInClass_add`
  The prime-power finite-stage projection preserves addition.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u

variable (ℓ : ℕ) [Fact (0 < ℓ)]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [Fact (0 < ℓ)] in
/-- The finite-stage projection sends \(1\) to \(1\). -/
@[simp]
theorem primePowerCompletedGroupAlgebraProjectionInClass_one
    (C : ProCGroups.FiniteGroupClass.{u}) (i : PrimePowerCompletedGroupAlgebraIndexInClass G C) :
    primePowerCompletedGroupAlgebraProjectionInClass (ℓ := ℓ) (G := G) C i
        (1 : PrimePowerCompletedGroupAlgebraInClass ℓ G C) = 1 := by
  rfl

omit [Fact (0 < ℓ)] in
/-- The finite-stage projection preserves multiplication. -/
@[simp]
theorem primePowerCompletedGroupAlgebraProjectionInClass_mul
    (C : ProCGroups.FiniteGroupClass.{u}) (i : PrimePowerCompletedGroupAlgebraIndexInClass G C)
    (x y : PrimePowerCompletedGroupAlgebraInClass ℓ G C) :
    primePowerCompletedGroupAlgebraProjectionInClass (ℓ := ℓ) (G := G) C i (x * y) =
      primePowerCompletedGroupAlgebraProjectionInClass (ℓ := ℓ) (G := G) C i x *
        primePowerCompletedGroupAlgebraProjectionInClass (ℓ := ℓ) (G := G) C i y := by
  rfl

omit [Fact (0 < ℓ)] in
/-- The finite-stage projection sends \(0\) to \(0\). -/
@[simp]
theorem primePowerCompletedGroupAlgebraProjectionInClass_zero
    (C : ProCGroups.FiniteGroupClass.{u}) (i : PrimePowerCompletedGroupAlgebraIndexInClass G C) :
    primePowerCompletedGroupAlgebraProjectionInClass (ℓ := ℓ) (G := G) C i
      (0 : PrimePowerCompletedGroupAlgebraInClass ℓ G C) = 0 := by
  rfl

omit [Fact (0 < ℓ)] in
/-- The prime-power finite-stage projection preserves addition. -/
@[simp]
theorem primePowerCompletedGroupAlgebraProjectionInClass_add
    (C : ProCGroups.FiniteGroupClass.{u}) (i : PrimePowerCompletedGroupAlgebraIndexInClass G C)
    (x y : PrimePowerCompletedGroupAlgebraInClass ℓ G C) :
    primePowerCompletedGroupAlgebraProjectionInClass (ℓ := ℓ) (G := G) C i (x + y) =
      primePowerCompletedGroupAlgebraProjectionInClass (ℓ := ℓ) (G := G) C i x +
        primePowerCompletedGroupAlgebraProjectionInClass (ℓ := ℓ) (G := G) C i y := by
  rfl

omit [Fact (0 < ℓ)] in
/-- The prime-power finite-stage projection preserves negation. -/
@[simp]
theorem primePowerCompletedGroupAlgebraProjectionInClass_neg
    (C : ProCGroups.FiniteGroupClass.{u}) (i : PrimePowerCompletedGroupAlgebraIndexInClass G C)
    (x : PrimePowerCompletedGroupAlgebraInClass ℓ G C) :
    primePowerCompletedGroupAlgebraProjectionInClass (ℓ := ℓ) (G := G) C i (-x) =
      -primePowerCompletedGroupAlgebraProjectionInClass (ℓ := ℓ) (G := G) C i x := by
  rfl

omit [Fact (0 < ℓ)] in
/-- The prime-power finite-stage projection preserves subtraction. -/
@[simp]
theorem primePowerCompletedGroupAlgebraProjectionInClass_sub
    (C : ProCGroups.FiniteGroupClass.{u}) (i : PrimePowerCompletedGroupAlgebraIndexInClass G C)
    (x y : PrimePowerCompletedGroupAlgebraInClass ℓ G C) :
    primePowerCompletedGroupAlgebraProjectionInClass (ℓ := ℓ) (G := G) C i (x - y) =
      primePowerCompletedGroupAlgebraProjectionInClass (ℓ := ℓ) (G := G) C i x -
        primePowerCompletedGroupAlgebraProjectionInClass (ℓ := ℓ) (G := G) C i y := by
  rfl

omit [Fact (0 < ℓ)] in
/-- The finite-stage projection is compatible with natural-number scalar multiplication. -/
@[simp]
theorem primePowerCompletedGroupAlgebraProjectionInClass_nsmul
    (C : ProCGroups.FiniteGroupClass.{u}) (i : PrimePowerCompletedGroupAlgebraIndexInClass G C)
    (m : ℕ) (x : PrimePowerCompletedGroupAlgebraInClass ℓ G C) :
    primePowerCompletedGroupAlgebraProjectionInClass (ℓ := ℓ) (G := G) C i (m • x) =
      m • primePowerCompletedGroupAlgebraProjectionInClass (ℓ := ℓ) (G := G) C i x := by
  rfl

omit [Fact (0 < ℓ)] in
/-- The finite-stage projection is compatible with integer scalar multiplication. -/
@[simp]
theorem primePowerCompletedGroupAlgebraProjectionInClass_zsmul
    (C : ProCGroups.FiniteGroupClass.{u}) (i : PrimePowerCompletedGroupAlgebraIndexInClass G C)
    (m : ℤ) (x : PrimePowerCompletedGroupAlgebraInClass ℓ G C) :
    primePowerCompletedGroupAlgebraProjectionInClass (ℓ := ℓ) (G := G) C i (m • x) =
      m • primePowerCompletedGroupAlgebraProjectionInClass (ℓ := ℓ) (G := G) C i x := by
  rfl

end

end FoxDifferential
