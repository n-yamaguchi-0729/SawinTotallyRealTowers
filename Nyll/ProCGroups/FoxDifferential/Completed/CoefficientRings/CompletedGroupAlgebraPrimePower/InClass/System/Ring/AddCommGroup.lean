/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraPrimePower.InClass.System.Basic

/-!
# Fox differential: in class — system — ring — add comm group

The principal declarations in this module are:

- `instAddCommGroupPrimePowerCompletedGroupAlgebraInClass`
  The class-indexed prime-power completion inherits an additive commutative group structure from its
  injective inclusion into the family of finite stages.
- `coe_zero_primePowerCompletedGroupAlgebraInClass`
  The inclusion of the class-indexed prime-power completed group algebra preserves zero.
- `coe_add_primePowerCompletedGroupAlgebraInClass`
  The inclusion of the class-indexed prime-power completed group algebra preserves addition.
- `coe_neg_primePowerCompletedGroupAlgebraInClass`
  The inclusion of the class-indexed prime-power completed group algebra preserves negation.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u

variable (ℓ : ℕ) [Fact (0 < ℓ)]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/--
The zero element is defined coordinatewise as the compatible family of zero elements at all
finite stages.
-/
instance instZeroPrimePowerCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    Zero (PrimePowerCompletedGroupAlgebraInClass ℓ G C) where
  zero := ⟨fun i => (0 : PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i), by
    intro i j hij
    change primePowerCompletedGroupAlgebraTransitionInClass (ℓ := ℓ) (G := G) C hij
      (0 : PrimePowerCompletedGroupAlgebraStageInClass ℓ G C j) = 0
    exact map_zero _⟩

/--
Addition in the prime-power completed group algebra is defined coordinatewise through
finite-stage group-algebra additions.
-/
instance instAddPrimePowerCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    Add (PrimePowerCompletedGroupAlgebraInClass ℓ G C) where
  add x y := ⟨fun i =>
      (show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i from x.1 i) +
        (show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i from y.1 i), by
    intro i j hij
    calc
      primePowerCompletedGroupAlgebraTransitionInClass (ℓ := ℓ) (G := G) C hij
          ((show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C j from x.1 j) +
            (show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C j from y.1 j))
        =
      primePowerCompletedGroupAlgebraTransitionInClass (ℓ := ℓ) (G := G) C hij
          (show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C j from x.1 j) +
        primePowerCompletedGroupAlgebraTransitionInClass (ℓ := ℓ) (G := G) C hij
          (show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C j from y.1 j) := by
            rw [map_add]
      _ =
      (show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i from x.1 i) +
        (show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i from y.1 i) := by
            exact congrArg₂ HAdd.hAdd (x.2 i j hij) (y.2 i j hij)⟩

/--
Coordinatewise zero and addition on the class-indexed prime-power completed group algebra satisfy
the left and right zero laws.
-/
instance instAddZeroClassPrimePowerCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    AddZeroClass (PrimePowerCompletedGroupAlgebraInClass ℓ G C) where
  zero := 0
  add := (· + ·)
  zero_add x := by
    apply Subtype.ext
    funext i
    change (0 : PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i) +
      (show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i from x.1 i) =
        (show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i from x.1 i)
    simp only [zero_add]
  add_zero x := by
    apply Subtype.ext
    funext i
    change (show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i from x.1 i) +
      (0 : PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i) =
        (show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i from x.1 i)
    simp only [add_zero]

/--
Negation on the \(C\)-indexed prime-power completed group algebra is defined coordinatewise
through finite-stage group-algebra negations.
-/
instance instNegPrimePowerCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    Neg (PrimePowerCompletedGroupAlgebraInClass ℓ G C) where
  neg x := ⟨fun i => -(show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i from x.1 i), by
    intro i j hij
    change primePowerCompletedGroupAlgebraTransitionInClass (ℓ := ℓ) (G := G) C hij
        (-(show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C j from x.1 j)) =
      -(show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i from x.1 i)
    rw [map_neg]
    exact congrArg Neg.neg (x.2 i j hij)⟩

/--
Subtraction on the completed group algebra is defined coordinatewise through the finite-stage
group-algebra subtractions.
-/
instance instSubPrimePowerCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    Sub (PrimePowerCompletedGroupAlgebraInClass ℓ G C) where
  sub x y := ⟨fun i =>
      (show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i from x.1 i) -
        (show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i from y.1 i), by
    intro i j hij
    change primePowerCompletedGroupAlgebraTransitionInClass (ℓ := ℓ) (G := G) C hij
        ((show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C j from x.1 j) -
          (show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C j from y.1 j)) =
      (show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i from x.1 i) -
        (show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i from y.1 i)
    rw [map_sub]
    exact congrArg₂ HSub.hSub (x.2 i j hij) (y.2 i j hij)⟩

/--
The completed group algebra carries coefficient-ring scalar multiplication by applying the
scalar action at every finite quotient stage.
-/
instance instSMulNatPrimePowerCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    SMul ℕ (PrimePowerCompletedGroupAlgebraInClass ℓ G C) where
  smul m x := ⟨fun i =>
      m • (show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i from x.1 i), by
    intro i j hij
    change primePowerCompletedGroupAlgebraTransitionInClass (ℓ := ℓ) (G := G) C hij
        (m • (show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C j from x.1 j)) =
      m • (show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i from x.1 i)
    rw [map_nsmul]
    exact congrArg (m • ·) (x.2 i j hij)⟩

/--
The completed group algebra carries coefficient-ring scalar multiplication by applying the
scalar action at every finite quotient stage.
-/
instance instSMulIntPrimePowerCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    SMul ℤ (PrimePowerCompletedGroupAlgebraInClass ℓ G C) where
  smul m x := ⟨fun i =>
      m • (show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i from x.1 i), by
    intro i j hij
    change primePowerCompletedGroupAlgebraTransitionInClass (ℓ := ℓ) (G := G) C hij
        (m • (show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C j from x.1 j)) =
      m • (show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i from x.1 i)
    rw [map_zsmul]
    exact congrArg (m • ·) (x.2 i j hij)⟩

omit [Fact (0 < ℓ)] in
/-- The inclusion of the class-indexed prime-power completed group algebra preserves zero. -/
@[simp]
theorem coe_zero_primePowerCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    ((0 : PrimePowerCompletedGroupAlgebraInClass ℓ G C) :
      (i : PrimePowerCompletedGroupAlgebraIndexInClass G C) →
        PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i) = 0 := by
  funext i
  rfl

omit [Fact (0 < ℓ)] in
/-- The inclusion of the class-indexed prime-power completed group algebra preserves addition. -/
@[simp]
theorem coe_add_primePowerCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u})
    (x y : PrimePowerCompletedGroupAlgebraInClass ℓ G C) :
    ((x + y : PrimePowerCompletedGroupAlgebraInClass ℓ G C) :
      (i : PrimePowerCompletedGroupAlgebraIndexInClass G C) →
        PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i) = x + y := by
  funext i
  rfl

omit [Fact (0 < ℓ)] in
/-- The inclusion of the class-indexed prime-power completed group algebra preserves negation. -/
@[simp]
theorem coe_neg_primePowerCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u})
    (x : PrimePowerCompletedGroupAlgebraInClass ℓ G C) :
    ((-x : PrimePowerCompletedGroupAlgebraInClass ℓ G C) :
      (i : PrimePowerCompletedGroupAlgebraIndexInClass G C) →
        PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i) = -x := by
  funext i
  rfl

omit [Fact (0 < ℓ)] in
/--
Subtraction in the \(C\)-indexed prime-power completed group algebra is computed coordinatewise.
-/
@[simp]
theorem coe_sub_primePowerCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u})
    (x y : PrimePowerCompletedGroupAlgebraInClass ℓ G C) :
    ((x - y : PrimePowerCompletedGroupAlgebraInClass ℓ G C) :
      (i : PrimePowerCompletedGroupAlgebraIndexInClass G C) →
        PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i) = x - y := by
  funext i
  rfl

omit [Fact (0 < ℓ)] in
/--
The inclusion of the class-indexed prime-power completed group algebra preserves natural-number
scalar multiplication.
-/
@[simp]
theorem coe_nsmul_primePowerCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u})
    (m : ℕ) (x : PrimePowerCompletedGroupAlgebraInClass ℓ G C) :
    ((m • x : PrimePowerCompletedGroupAlgebraInClass ℓ G C) :
      (i : PrimePowerCompletedGroupAlgebraIndexInClass G C) →
        PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i) = m • x := by
  funext i
  rfl

omit [Fact (0 < ℓ)] in
/--
The inclusion of the class-indexed prime-power completed group algebra preserves integer scalar
multiplication.
-/
@[simp]
theorem coe_zsmul_primePowerCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u})
    (m : ℤ) (x : PrimePowerCompletedGroupAlgebraInClass ℓ G C) :
    ((m • x : PrimePowerCompletedGroupAlgebraInClass ℓ G C) :
      (i : PrimePowerCompletedGroupAlgebraIndexInClass G C) →
        PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i) = m • x := by
  funext i
  rfl

/--
The class-indexed prime-power completion inherits an additive commutative group structure from
its injective inclusion into the family of finite stages.
-/
@[reducible] def instAddCommGroupPrimePowerCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    AddCommGroup (PrimePowerCompletedGroupAlgebraInClass ℓ G C) :=
  Function.Injective.addCommGroup
    (fun x : PrimePowerCompletedGroupAlgebraInClass ℓ G C =>
      (x :
        (i : PrimePowerCompletedGroupAlgebraIndexInClass G C) →
          PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i))
    Subtype.val_injective
    (coe_zero_primePowerCompletedGroupAlgebraInClass (ℓ := ℓ) (G := G) C)
    (coe_add_primePowerCompletedGroupAlgebraInClass (ℓ := ℓ) (G := G) C)
    (coe_neg_primePowerCompletedGroupAlgebraInClass (ℓ := ℓ) (G := G) C)
    (coe_sub_primePowerCompletedGroupAlgebraInClass (ℓ := ℓ) (G := G) C)
    (fun x m => coe_nsmul_primePowerCompletedGroupAlgebraInClass (ℓ := ℓ) (G := G) C m x)
    (fun x m => coe_zsmul_primePowerCompletedGroupAlgebraInClass (ℓ := ℓ) (G := G) C m x)

attribute [local instance] instAddCommGroupPrimePowerCompletedGroupAlgebraInClass

end

end FoxDifferential
