/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.FiniteStage.PrimePower.System.Limit.Basic

/-!
# Fox differential: prime power — system — limit — add comm group

The principal declarations in this module are:

- `foxAlgebraicStagePrimePowerSourceLimitToFamily_zero`
  The source-limit family of zero is the zero family.
- `foxAlgebraicStagePrimePowerSourceLimitToFamily_add`
  The source-limit family map preserves addition.
- `foxAlgebraicStagePrimePowerSourceLimitToFamily_neg`
  The source-limit family map preserves negation.
- `foxAlgebraicStagePrimePowerSourceLimitToFamily_sub`
  The source-limit family map preserves subtraction.
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


/--
The zero element is defined coordinatewise as the compatible family of zero elements at all
finite stages.
-/
instance instZeroFoxAlgebraicStagePrimePowerSourceLimit
    (N : Subgroup (FreeGroup X)) :
    Zero (FoxAlgebraicStagePrimePowerSourceLimit (ℓ := ℓ) (X := X) N) where
  zero := ⟨fun a => (0 : foxAlgebraicStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N a),
    by
      intro a b hab
      change foxAlgebraicStagePrimePowerSourceTransition (ℓ := ℓ) (X := X) N hab
          (0 : foxAlgebraicStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N b) = 0
      exact map_zero _⟩

/--
Addition in the finite Fox prime-power source limit is defined coordinatewise through finite
stages.
-/
instance instAddFoxAlgebraicStagePrimePowerSourceLimit
    (N : Subgroup (FreeGroup X)) :
    Add (FoxAlgebraicStagePrimePowerSourceLimit (ℓ := ℓ) (X := X) N) where
  add x y := ⟨fun a =>
      (show foxAlgebraicStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N a from x.1 a) +
        (show foxAlgebraicStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N a from y.1 a),
    by
      intro a b hab
      change foxAlgebraicStagePrimePowerSourceTransition (ℓ := ℓ) (X := X) N hab
          ((show foxAlgebraicStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N b from x.1 b) +
            (show foxAlgebraicStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N b from y.1 b)) =
        (show foxAlgebraicStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N a from x.1 a) +
          (show foxAlgebraicStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N a from y.1 a)
      rw [map_add]
      exact congrArg₂ HAdd.hAdd (x.2 a b hab) (y.2 a b hab)⟩

/--
Negation on the prime-power source inverse limit is defined coordinatewise through finite-stage
source negations.
-/
instance instNegFoxAlgebraicStagePrimePowerSourceLimit
    (N : Subgroup (FreeGroup X)) :
    Neg (FoxAlgebraicStagePrimePowerSourceLimit (ℓ := ℓ) (X := X) N) where
  neg x := ⟨fun a =>
      -(show foxAlgebraicStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N a from x.1 a),
    by
      intro a b hab
      change foxAlgebraicStagePrimePowerSourceTransition (ℓ := ℓ) (X := X) N hab
          (-(show foxAlgebraicStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N b from x.1 b)) =
        -(show foxAlgebraicStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N a from x.1 a)
      rw [map_neg]
      exact congrArg Neg.neg (x.2 a b hab)⟩

/--
Subtraction on the prime-power source inverse limit is defined coordinatewise through
finite-stage source subtractions.
-/
instance instSubFoxAlgebraicStagePrimePowerSourceLimit
    (N : Subgroup (FreeGroup X)) :
    Sub (FoxAlgebraicStagePrimePowerSourceLimit (ℓ := ℓ) (X := X) N) where
  sub x y := ⟨fun a =>
      (show foxAlgebraicStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N a from x.1 a) -
        (show foxAlgebraicStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N a from y.1 a),
    by
      intro a b hab
      change foxAlgebraicStagePrimePowerSourceTransition (ℓ := ℓ) (X := X) N hab
          ((show foxAlgebraicStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N b from x.1 b) -
            (show foxAlgebraicStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N b from y.1 b)) =
        (show foxAlgebraicStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N a from x.1 a) -
          (show foxAlgebraicStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N a from y.1 a)
      rw [map_sub]
      exact congrArg₂ HSub.hSub (x.2 a b hab) (y.2 a b hab)⟩

/--
The prime-power source inverse limit carries natural-number scalar multiplication
coordinatewise.
-/
instance instSMulNatFoxAlgebraicStagePrimePowerSourceLimit
    (N : Subgroup (FreeGroup X)) :
    SMul ℕ (FoxAlgebraicStagePrimePowerSourceLimit (ℓ := ℓ) (X := X) N) where
  smul m x := ⟨fun a =>
      m • (show foxAlgebraicStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N a from x.1 a),
    by
      intro a b hab
      change foxAlgebraicStagePrimePowerSourceTransition (ℓ := ℓ) (X := X) N hab
          (m • (show foxAlgebraicStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N b from
              x.1 b)) =
        m • (show foxAlgebraicStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N a from x.1 a)
      rw [map_nsmul]
      exact congrArg (m • ·) (x.2 a b hab)⟩

/-- The prime-power source inverse limit carries integer scalar multiplication coordinatewise. -/
instance instSMulIntFoxAlgebraicStagePrimePowerSourceLimit
    (N : Subgroup (FreeGroup X)) :
    SMul ℤ (FoxAlgebraicStagePrimePowerSourceLimit (ℓ := ℓ) (X := X) N) where
  smul m x := ⟨fun a =>
      m • (show foxAlgebraicStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N a from x.1 a),
    by
      intro a b hab
      change foxAlgebraicStagePrimePowerSourceTransition (ℓ := ℓ) (X := X) N hab
          (m • (show foxAlgebraicStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N b from
              x.1 b)) =
        m • (show foxAlgebraicStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N a from x.1 a)
      rw [map_zsmul]
      exact congrArg (m • ·) (x.2 a b hab)⟩

omit [DecidableEq X] in
/-- The source-limit family of zero is the zero family. -/
@[simp] theorem foxAlgebraicStagePrimePowerSourceLimitToFamily_zero
    (N : Subgroup (FreeGroup X)) :
    foxAlgebraicStagePrimePowerSourceLimitToFamily (ℓ := ℓ) (X := X) N 0 = 0 := by
  funext a
  rfl

omit [DecidableEq X] in
/-- The source-limit family map preserves addition. -/
@[simp] theorem foxAlgebraicStagePrimePowerSourceLimitToFamily_add
    (N : Subgroup (FreeGroup X))
    (x y : FoxAlgebraicStagePrimePowerSourceLimit (ℓ := ℓ) (X := X) N) :
    foxAlgebraicStagePrimePowerSourceLimitToFamily (ℓ := ℓ) (X := X) N (x + y) =
      foxAlgebraicStagePrimePowerSourceLimitToFamily (ℓ := ℓ) (X := X) N x +
        foxAlgebraicStagePrimePowerSourceLimitToFamily (ℓ := ℓ) (X := X) N y := by
  funext a
  rfl

omit [DecidableEq X] in
/-- The source-limit family map preserves negation. -/
@[simp] theorem foxAlgebraicStagePrimePowerSourceLimitToFamily_neg
    (N : Subgroup (FreeGroup X))
    (x : FoxAlgebraicStagePrimePowerSourceLimit (ℓ := ℓ) (X := X) N) :
    foxAlgebraicStagePrimePowerSourceLimitToFamily (ℓ := ℓ) (X := X) N (-x) =
      -foxAlgebraicStagePrimePowerSourceLimitToFamily (ℓ := ℓ) (X := X) N x := by
  funext a
  rfl

omit [DecidableEq X] in
/-- The source-limit family map preserves subtraction. -/
@[simp] theorem foxAlgebraicStagePrimePowerSourceLimitToFamily_sub
    (N : Subgroup (FreeGroup X))
    (x y : FoxAlgebraicStagePrimePowerSourceLimit (ℓ := ℓ) (X := X) N) :
    foxAlgebraicStagePrimePowerSourceLimitToFamily (ℓ := ℓ) (X := X) N (x - y) =
      foxAlgebraicStagePrimePowerSourceLimitToFamily (ℓ := ℓ) (X := X) N x -
        foxAlgebraicStagePrimePowerSourceLimitToFamily (ℓ := ℓ) (X := X) N y := by
  funext a
  rfl

omit [DecidableEq X] in
/-- The source-limit family map preserves natural-number scalar multiplication. -/
@[simp] theorem foxAlgebraicStagePrimePowerSourceLimitToFamily_nsmul
    (N : Subgroup (FreeGroup X)) (m : ℕ)
    (x : FoxAlgebraicStagePrimePowerSourceLimit (ℓ := ℓ) (X := X) N) :
    foxAlgebraicStagePrimePowerSourceLimitToFamily (ℓ := ℓ) (X := X) N (m • x) =
      m • foxAlgebraicStagePrimePowerSourceLimitToFamily (ℓ := ℓ) (X := X) N x := by
  funext a
  rfl

omit [DecidableEq X] in
/-- The source-limit family map preserves integer scalar multiplication. -/
@[simp] theorem foxAlgebraicStagePrimePowerSourceLimitToFamily_zsmul
    (N : Subgroup (FreeGroup X)) (m : ℤ)
    (x : FoxAlgebraicStagePrimePowerSourceLimit (ℓ := ℓ) (X := X) N) :
    foxAlgebraicStagePrimePowerSourceLimitToFamily (ℓ := ℓ) (X := X) N (m • x) =
      m • foxAlgebraicStagePrimePowerSourceLimitToFamily (ℓ := ℓ) (X := X) N x := by
  funext a
  rfl

/--
The prime-power source limit inherits an additive commutative group structure from its injective
map into the family of source stages.
-/
instance instAddCommGroupFoxAlgebraicStagePrimePowerSourceLimit
    (N : Subgroup (FreeGroup X)) :
    AddCommGroup (FoxAlgebraicStagePrimePowerSourceLimit (ℓ := ℓ) (X := X) N) :=
  Function.Injective.addCommGroup
    (foxAlgebraicStagePrimePowerSourceLimitToFamily (ℓ := ℓ) (X := X) N)
    (foxAlgebraicStagePrimePowerSourceLimitToFamily_injective (ℓ := ℓ) (X := X) N)
    (foxAlgebraicStagePrimePowerSourceLimitToFamily_zero (ℓ := ℓ) (X := X) N)
    (foxAlgebraicStagePrimePowerSourceLimitToFamily_add (ℓ := ℓ) (X := X) N)
    (foxAlgebraicStagePrimePowerSourceLimitToFamily_neg (ℓ := ℓ) (X := X) N)
    (foxAlgebraicStagePrimePowerSourceLimitToFamily_sub (ℓ := ℓ) (X := X) N)
    (fun z m => foxAlgebraicStagePrimePowerSourceLimitToFamily_nsmul
      (ℓ := ℓ) (X := X) N m z)
    (fun z m => foxAlgebraicStagePrimePowerSourceLimitToFamily_zsmul
      (ℓ := ℓ) (X := X) N m z)

/--
The zero element is defined coordinatewise as the compatible family of zero elements at all
finite stages.
-/
instance instZeroFoxAlgebraicStagePrimePowerTargetLimit
    (N : Subgroup (FreeGroup X)) [N.Normal] :
    Zero (FoxAlgebraicStagePrimePowerTargetLimit (ℓ := ℓ) (X := X) N) where
  zero := ⟨fun a => (0 : foxAlgebraicStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N a),
    by
      intro a b hab
      change foxAlgebraicStagePrimePowerTargetTransition (ℓ := ℓ) (X := X) N hab
          (0 : foxAlgebraicStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N b) = 0
      exact map_zero _⟩

/--
Addition in the finite Fox prime-power target limit is defined coordinatewise through finite
stages.
-/
instance instAddFoxAlgebraicStagePrimePowerTargetLimit
    (N : Subgroup (FreeGroup X)) [N.Normal] :
    Add (FoxAlgebraicStagePrimePowerTargetLimit (ℓ := ℓ) (X := X) N) where
  add x y := ⟨fun a =>
      (show foxAlgebraicStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N a from x.1 a) +
        (show foxAlgebraicStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N a from y.1 a),
    by
      intro a b hab
      change foxAlgebraicStagePrimePowerTargetTransition (ℓ := ℓ) (X := X) N hab
          ((show foxAlgebraicStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N b from x.1 b) +
            (show foxAlgebraicStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N b from y.1 b)) =
        (show foxAlgebraicStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N a from x.1 a) +
          (show foxAlgebraicStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N a from y.1 a)
      rw [map_add]
      exact congrArg₂ HAdd.hAdd (x.2 a b hab) (y.2 a b hab)⟩

/--
Negation on the prime-power target inverse limit is defined coordinatewise through finite-stage
target negations.
-/
instance instNegFoxAlgebraicStagePrimePowerTargetLimit
    (N : Subgroup (FreeGroup X)) [N.Normal] :
    Neg (FoxAlgebraicStagePrimePowerTargetLimit (ℓ := ℓ) (X := X) N) where
  neg x := ⟨fun a =>
      -(show foxAlgebraicStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N a from x.1 a),
    by
      intro a b hab
      change foxAlgebraicStagePrimePowerTargetTransition (ℓ := ℓ) (X := X) N hab
          (-(show foxAlgebraicStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N b from x.1 b)) =
        -(show foxAlgebraicStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N a from x.1 a)
      rw [map_neg]
      exact congrArg Neg.neg (x.2 a b hab)⟩

/--
Subtraction on the prime-power target inverse limit is defined coordinatewise through
finite-stage target subtractions.
-/
instance instSubFoxAlgebraicStagePrimePowerTargetLimit
    (N : Subgroup (FreeGroup X)) [N.Normal] :
    Sub (FoxAlgebraicStagePrimePowerTargetLimit (ℓ := ℓ) (X := X) N) where
  sub x y := ⟨fun a =>
      (show foxAlgebraicStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N a from x.1 a) -
        (show foxAlgebraicStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N a from y.1 a),
    by
      intro a b hab
      change foxAlgebraicStagePrimePowerTargetTransition (ℓ := ℓ) (X := X) N hab
          ((show foxAlgebraicStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N b from x.1 b) -
            (show foxAlgebraicStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N b from y.1 b)) =
        (show foxAlgebraicStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N a from x.1 a) -
          (show foxAlgebraicStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N a from y.1 a)
      rw [map_sub]
      exact congrArg₂ HSub.hSub (x.2 a b hab) (y.2 a b hab)⟩

/--
The prime-power target inverse limit carries natural-number scalar multiplication
coordinatewise.
-/
instance instSMulNatFoxAlgebraicStagePrimePowerTargetLimit
    (N : Subgroup (FreeGroup X)) [N.Normal] :
    SMul ℕ (FoxAlgebraicStagePrimePowerTargetLimit (ℓ := ℓ) (X := X) N) where
  smul m x := ⟨fun a =>
      m • (show foxAlgebraicStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N a from x.1 a),
    by
      intro a b hab
      change foxAlgebraicStagePrimePowerTargetTransition (ℓ := ℓ) (X := X) N hab
          (m • (show foxAlgebraicStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N b from
              x.1 b)) =
        m • (show foxAlgebraicStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N a from x.1 a)
      rw [map_nsmul]
      exact congrArg (m • ·) (x.2 a b hab)⟩

/-- The prime-power target inverse limit carries integer scalar multiplication coordinatewise. -/
instance instSMulIntFoxAlgebraicStagePrimePowerTargetLimit
    (N : Subgroup (FreeGroup X)) [N.Normal] :
    SMul ℤ (FoxAlgebraicStagePrimePowerTargetLimit (ℓ := ℓ) (X := X) N) where
  smul m x := ⟨fun a =>
      m • (show foxAlgebraicStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N a from x.1 a),
    by
      intro a b hab
      change foxAlgebraicStagePrimePowerTargetTransition (ℓ := ℓ) (X := X) N hab
          (m • (show foxAlgebraicStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N b from
              x.1 b)) =
        m • (show foxAlgebraicStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N a from x.1 a)
      rw [map_zsmul]
      exact congrArg (m • ·) (x.2 a b hab)⟩

omit [DecidableEq X] in
/-- The target-limit family of zero is the zero family. -/
@[simp] theorem foxAlgebraicStagePrimePowerTargetLimitToFamily_zero
    (N : Subgroup (FreeGroup X)) [N.Normal] :
    foxAlgebraicStagePrimePowerTargetLimitToFamily (ℓ := ℓ) (X := X) N 0 = 0 := by
  funext a
  rfl

omit [DecidableEq X] in
/-- The target-limit family map preserves addition. -/
@[simp] theorem foxAlgebraicStagePrimePowerTargetLimitToFamily_add
    (N : Subgroup (FreeGroup X)) [N.Normal]
    (x y : FoxAlgebraicStagePrimePowerTargetLimit (ℓ := ℓ) (X := X) N) :
    foxAlgebraicStagePrimePowerTargetLimitToFamily (ℓ := ℓ) (X := X) N (x + y) =
      foxAlgebraicStagePrimePowerTargetLimitToFamily (ℓ := ℓ) (X := X) N x +
        foxAlgebraicStagePrimePowerTargetLimitToFamily (ℓ := ℓ) (X := X) N y := by
  funext a
  rfl

omit [DecidableEq X] in
/-- The target-limit family map preserves negation. -/
@[simp] theorem foxAlgebraicStagePrimePowerTargetLimitToFamily_neg
    (N : Subgroup (FreeGroup X)) [N.Normal]
    (x : FoxAlgebraicStagePrimePowerTargetLimit (ℓ := ℓ) (X := X) N) :
    foxAlgebraicStagePrimePowerTargetLimitToFamily (ℓ := ℓ) (X := X) N (-x) =
      -foxAlgebraicStagePrimePowerTargetLimitToFamily (ℓ := ℓ) (X := X) N x := by
  funext a
  rfl

omit [DecidableEq X] in
/-- The target-limit family map preserves subtraction. -/
@[simp] theorem foxAlgebraicStagePrimePowerTargetLimitToFamily_sub
    (N : Subgroup (FreeGroup X)) [N.Normal]
    (x y : FoxAlgebraicStagePrimePowerTargetLimit (ℓ := ℓ) (X := X) N) :
    foxAlgebraicStagePrimePowerTargetLimitToFamily (ℓ := ℓ) (X := X) N (x - y) =
      foxAlgebraicStagePrimePowerTargetLimitToFamily (ℓ := ℓ) (X := X) N x -
        foxAlgebraicStagePrimePowerTargetLimitToFamily (ℓ := ℓ) (X := X) N y := by
  funext a
  rfl

omit [DecidableEq X] in
/-- The target-limit family map preserves natural-number scalar multiplication. -/
@[simp] theorem foxAlgebraicStagePrimePowerTargetLimitToFamily_nsmul
    (N : Subgroup (FreeGroup X)) [N.Normal] (m : ℕ)
    (x : FoxAlgebraicStagePrimePowerTargetLimit (ℓ := ℓ) (X := X) N) :
    foxAlgebraicStagePrimePowerTargetLimitToFamily (ℓ := ℓ) (X := X) N (m • x) =
      m • foxAlgebraicStagePrimePowerTargetLimitToFamily (ℓ := ℓ) (X := X) N x := by
  funext a
  rfl

omit [DecidableEq X] in
/-- The target-limit family map preserves integer scalar multiplication. -/
@[simp] theorem foxAlgebraicStagePrimePowerTargetLimitToFamily_zsmul
    (N : Subgroup (FreeGroup X)) [N.Normal] (m : ℤ)
    (x : FoxAlgebraicStagePrimePowerTargetLimit (ℓ := ℓ) (X := X) N) :
    foxAlgebraicStagePrimePowerTargetLimitToFamily (ℓ := ℓ) (X := X) N (m • x) =
      m • foxAlgebraicStagePrimePowerTargetLimitToFamily (ℓ := ℓ) (X := X) N x := by
  funext a
  rfl

/--
The prime-power target limit inherits an additive commutative group structure from its injective
map into the family of target stages.
-/
instance instAddCommGroupFoxAlgebraicStagePrimePowerTargetLimit
    (N : Subgroup (FreeGroup X)) [N.Normal] :
    AddCommGroup (FoxAlgebraicStagePrimePowerTargetLimit (ℓ := ℓ) (X := X) N) :=
  Function.Injective.addCommGroup
    (foxAlgebraicStagePrimePowerTargetLimitToFamily (ℓ := ℓ) (X := X) N)
    (foxAlgebraicStagePrimePowerTargetLimitToFamily_injective (ℓ := ℓ) (X := X) N)
    (foxAlgebraicStagePrimePowerTargetLimitToFamily_zero (ℓ := ℓ) (X := X) N)
    (foxAlgebraicStagePrimePowerTargetLimitToFamily_add (ℓ := ℓ) (X := X) N)
    (foxAlgebraicStagePrimePowerTargetLimitToFamily_neg (ℓ := ℓ) (X := X) N)
    (foxAlgebraicStagePrimePowerTargetLimitToFamily_sub (ℓ := ℓ) (X := X) N)
    (fun z m => foxAlgebraicStagePrimePowerTargetLimitToFamily_nsmul
      (ℓ := ℓ) (X := X) N m z)
    (fun z m => foxAlgebraicStagePrimePowerTargetLimitToFamily_zsmul
      (ℓ := ℓ) (X := X) N m z)




end

end FoxDifferential
