/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraPrimePower.InClass.System.Ring.AddCommGroup

/-!
# Fox differential: in class — system — ring — multiplicative

The principal declarations in this module are:

- `coe_one_primePowerCompletedGroupAlgebraInClass`
  The multiplicative identity in the class-indexed prime-power completed group algebra is computed
  coordinatewise.
- `coe_mul_primePowerCompletedGroupAlgebraInClass`
  Multiplication in the class-indexed prime-power completed group algebra is computed
  coordinatewise.
- `coe_natCast_primePowerCompletedGroupAlgebraInClass`
  Natural number casts in the class-indexed prime-power completed group algebra are computed
  coordinatewise.
- `coe_intCast_primePowerCompletedGroupAlgebraInClass`
  Integer casts in the class-indexed prime-power completed group algebra are computed
  coordinatewise.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u

variable (ℓ : ℕ) [Fact (0 < ℓ)]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

attribute [local instance] instAddCommGroupPrimePowerCompletedGroupAlgebraInClass

/--
The in-class prime-power completed group algebra has a coordinatewise multiplicative identity.
-/
instance instOnePrimePowerCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    One (PrimePowerCompletedGroupAlgebraInClass ℓ G C) where
  one := ⟨fun i => (1 : PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i), by
    intro i j hij
    change primePowerCompletedGroupAlgebraTransitionInClass (ℓ := ℓ) (G := G) C hij
      (1 : PrimePowerCompletedGroupAlgebraStageInClass ℓ G C j) = 1
    exact map_one _⟩

/--
Multiplication on the completed group algebra is defined coordinatewise through the finite-stage
group-algebra products.
-/
instance instMulPrimePowerCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    Mul (PrimePowerCompletedGroupAlgebraInClass ℓ G C) where
  mul x y := ⟨fun i =>
      (show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i from x.1 i) *
        (show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i from y.1 i), by
    intro i j hij
    calc
      primePowerCompletedGroupAlgebraTransitionInClass (ℓ := ℓ) (G := G) C hij
          ((show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C j from x.1 j) *
            (show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C j from y.1 j))
        =
      primePowerCompletedGroupAlgebraTransitionInClass (ℓ := ℓ) (G := G) C hij
          (show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C j from x.1 j) *
        primePowerCompletedGroupAlgebraTransitionInClass (ℓ := ℓ) (G := G) C hij
          (show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C j from y.1 j) := by
            rw [map_mul]
      _ =
      (show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i from x.1 i) *
        (show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i from y.1 i) := by
            exact congrArg₂ HMul.hMul (x.2 i j hij) (y.2 i j hij)⟩

/--
Natural number casts in the class-indexed prime-power completed group algebra are computed
coordinatewise.
-/
instance instNatCastPrimePowerCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    NatCast (PrimePowerCompletedGroupAlgebraInClass ℓ G C) where
  natCast n := ⟨fun i => (n : PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i), by
    intro i j hij
    change primePowerCompletedGroupAlgebraTransitionInClass (ℓ := ℓ) (G := G) C hij
      (n : PrimePowerCompletedGroupAlgebraStageInClass ℓ G C j) = n
    exact map_natCast _ _⟩

/--
Integer casts in the class-indexed prime-power completed group algebra are computed
coordinatewise.
-/
instance instIntCastPrimePowerCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    IntCast (PrimePowerCompletedGroupAlgebraInClass ℓ G C) where
  intCast n := ⟨fun i => (n : PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i), by
    intro i j hij
    change primePowerCompletedGroupAlgebraTransitionInClass (ℓ := ℓ) (G := G) C hij
      (n : PrimePowerCompletedGroupAlgebraStageInClass ℓ G C j) = n
    exact map_intCast _ _⟩

/-- Powers in the class-indexed prime-power completed group algebra are computed coordinatewise. -/
instance instPowPrimePowerCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    Pow (PrimePowerCompletedGroupAlgebraInClass ℓ G C) ℕ where
  pow x n := ⟨fun i =>
      (show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i from x.1 i) ^ n, by
    intro i j hij
    change primePowerCompletedGroupAlgebraTransitionInClass (ℓ := ℓ) (G := G) C hij
        ((show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C j from x.1 j) ^ n) =
      (show PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i from x.1 i) ^ n
    rw [map_pow]
    exact congrArg (fun t => t ^ n) (x.2 i j hij)⟩

omit [Fact (0 < ℓ)] in
/--
The multiplicative identity in the class-indexed prime-power completed group algebra is computed
coordinatewise.
-/
@[simp]
theorem coe_one_primePowerCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    ((1 : PrimePowerCompletedGroupAlgebraInClass ℓ G C) :
      (i : PrimePowerCompletedGroupAlgebraIndexInClass G C) →
        PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i) =
      (1 :
        (i : PrimePowerCompletedGroupAlgebraIndexInClass G C) →
          PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i) := by
  funext i
  rfl

omit [Fact (0 < ℓ)] in
/--
Multiplication in the class-indexed prime-power completed group algebra is computed
coordinatewise.
-/
@[simp]
theorem coe_mul_primePowerCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u})
    (x y : PrimePowerCompletedGroupAlgebraInClass ℓ G C) :
    ((x * y : PrimePowerCompletedGroupAlgebraInClass ℓ G C) :
      (i : PrimePowerCompletedGroupAlgebraIndexInClass G C) →
        PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i) =
      (x * y :
        (i : PrimePowerCompletedGroupAlgebraIndexInClass G C) →
          PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i) := by
  funext i
  rfl

omit [Fact (0 < ℓ)] in
/--
Natural number casts in the class-indexed prime-power completed group algebra are computed
coordinatewise.
-/
@[simp]
theorem coe_natCast_primePowerCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u}) (n : ℕ) :
    ((n : PrimePowerCompletedGroupAlgebraInClass ℓ G C) :
      (i : PrimePowerCompletedGroupAlgebraIndexInClass G C) →
        PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i) =
      (n :
        (i : PrimePowerCompletedGroupAlgebraIndexInClass G C) →
          PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i) := by
  funext i
  rfl

omit [Fact (0 < ℓ)] in
/--
Integer casts in the class-indexed prime-power completed group algebra are computed
coordinatewise.
-/
@[simp]
theorem coe_intCast_primePowerCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u}) (n : ℤ) :
    ((n : PrimePowerCompletedGroupAlgebraInClass ℓ G C) :
      (i : PrimePowerCompletedGroupAlgebraIndexInClass G C) →
        PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i) =
      (n :
        (i : PrimePowerCompletedGroupAlgebraIndexInClass G C) →
          PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i) := by
  funext i
  rfl

omit [Fact (0 < ℓ)] in
/-- Powers in the class-indexed prime-power completed group algebra are computed coordinatewise. -/
@[simp]
theorem coe_pow_primePowerCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u})
    (x : PrimePowerCompletedGroupAlgebraInClass ℓ G C) (n : ℕ) :
    ((x ^ n : PrimePowerCompletedGroupAlgebraInClass ℓ G C) :
      (i : PrimePowerCompletedGroupAlgebraIndexInClass G C) →
        PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i) =
      (x ^ n :
        (i : PrimePowerCompletedGroupAlgebraIndexInClass G C) →
          PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i) := by
  funext i
  rfl

/--
The completed group algebra is a ring because all ring operations and ring axioms are inherited
coordinatewise from the finite-stage group algebras.
-/
instance instRingPrimePowerCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    Ring (PrimePowerCompletedGroupAlgebraInClass ℓ G C) :=
  Function.Injective.ring
    (fun x : PrimePowerCompletedGroupAlgebraInClass ℓ G C =>
      (x :
        (i : PrimePowerCompletedGroupAlgebraIndexInClass G C) →
          PrimePowerCompletedGroupAlgebraStageInClass ℓ G C i))
    Subtype.val_injective
    (coe_zero_primePowerCompletedGroupAlgebraInClass (ℓ := ℓ) (G := G) C)
    (coe_one_primePowerCompletedGroupAlgebraInClass (ℓ := ℓ) (G := G) C)
    (coe_add_primePowerCompletedGroupAlgebraInClass (ℓ := ℓ) (G := G) C)
    (coe_mul_primePowerCompletedGroupAlgebraInClass (ℓ := ℓ) (G := G) C)
    (coe_neg_primePowerCompletedGroupAlgebraInClass (ℓ := ℓ) (G := G) C)
    (coe_sub_primePowerCompletedGroupAlgebraInClass (ℓ := ℓ) (G := G) C)
    (fun n x => coe_nsmul_primePowerCompletedGroupAlgebraInClass (ℓ := ℓ) (G := G) C n x)
    (fun n x => coe_zsmul_primePowerCompletedGroupAlgebraInClass (ℓ := ℓ) (G := G) C n x)
    (fun x n => coe_pow_primePowerCompletedGroupAlgebraInClass (ℓ := ℓ) (G := G) C x n)
    (by
      intro n
      exact coe_natCast_primePowerCompletedGroupAlgebraInClass (ℓ := ℓ) (G := G) C n)
    (by
      intro z
      exact coe_intCast_primePowerCompletedGroupAlgebraInClass (ℓ := ℓ) (G := G) C z)

end

end FoxDifferential
