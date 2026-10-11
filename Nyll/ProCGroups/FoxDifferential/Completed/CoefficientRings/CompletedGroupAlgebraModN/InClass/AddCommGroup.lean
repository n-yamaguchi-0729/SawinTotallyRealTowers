/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraModN.InClass.Basic

/-!
# Fox differential: coefficient rings — mod-\(n\) completed group algebra — in class — add
comm group

The principal declarations in this module are:

- `coe_zero_modNCompletedGroupAlgebraInClass`
  The inclusion of the \(C\)-indexed mod-\(n\) completed group algebra into the ambient completed
  group algebra preserves zero.
- `coe_add_modNCompletedGroupAlgebraInClass`
  The inclusion of the \(C\)-indexed mod-\(n\) completed group algebra into the ambient completed
  group algebra preserves addition.
- `coe_neg_modNCompletedGroupAlgebraInClass`
  The inclusion of the \(C\)-indexed mod-\(n\) completed group algebra into the ambient completed
  group algebra preserves negation.
- `coe_sub_modNCompletedGroupAlgebraInClass`
  The inclusion of the \(C\)-indexed mod-\(n\) completed group algebra into the ambient completed
  group algebra preserves subtraction.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u

variable (n : ℕ) [Fact (0 < n)]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/--
The zero element is defined coordinatewise as the compatible family of zero elements at all
finite stages.
-/
instance instZeroModNCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    Zero (ModNCompletedGroupAlgebraInClass n G C) where
  zero := ⟨fun U => (0 : ModNCompletedGroupAlgebraStageInClass n G C U), by
    intro U V hUV
    change modNCompletedGroupAlgebraTransitionInClass n G C hUV
      (0 : ModNCompletedGroupAlgebraStageInClass n G C V) = 0
    exact map_zero _⟩

/--
Addition in the mod-\(n\) completed group algebra is defined coordinatewise through finite-stage
group-algebra additions.
-/
instance instAddModNCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    Add (ModNCompletedGroupAlgebraInClass n G C) where
  add x y := ⟨fun U =>
      (show ModNCompletedGroupAlgebraStageInClass n G C U from x.1 U) +
        (show ModNCompletedGroupAlgebraStageInClass n G C U from y.1 U), by
    intro U V hUV
    calc
      modNCompletedGroupAlgebraTransitionInClass n G C hUV
          ((show ModNCompletedGroupAlgebraStageInClass n G C V from x.1 V) +
            (show ModNCompletedGroupAlgebraStageInClass n G C V from y.1 V))
        =
          modNCompletedGroupAlgebraTransitionInClass n G C hUV
            (show ModNCompletedGroupAlgebraStageInClass n G C V from x.1 V) +
          modNCompletedGroupAlgebraTransitionInClass n G C hUV
            (show ModNCompletedGroupAlgebraStageInClass n G C V from y.1 V) := by
            rw [map_add]
      _ =
          (show ModNCompletedGroupAlgebraStageInClass n G C U from x.1 U) +
            (show ModNCompletedGroupAlgebraStageInClass n G C U from y.1 U) := by
            exact congrArg₂ HAdd.hAdd (x.2 U V hUV) (y.2 U V hUV)⟩

/--
Coordinatewise zero and addition on the class-indexed mod-\(n\) completed group algebra satisfy
the left and right zero laws.
-/
instance instAddZeroClassModNCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    AddZeroClass (ModNCompletedGroupAlgebraInClass n G C) where
  zero := 0
  add := (· + ·)
  zero_add x := by
    apply Subtype.ext
    funext U
    change (0 : ModNCompletedGroupAlgebraStageInClass n G C U) +
      (show ModNCompletedGroupAlgebraStageInClass n G C U from x.1 U) =
        (show ModNCompletedGroupAlgebraStageInClass n G C U from x.1 U)
    simp only [zero_add]
  add_zero x := by
    apply Subtype.ext
    funext U
    change (show ModNCompletedGroupAlgebraStageInClass n G C U from x.1 U) +
      (0 : ModNCompletedGroupAlgebraStageInClass n G C U) =
        (show ModNCompletedGroupAlgebraStageInClass n G C U from x.1 U)
    simp only [add_zero]

/--
Negation on the \(C\)-indexed mod-\(n\) completed group algebra is defined coordinatewise
through finite-stage group-algebra negations.
-/
instance instNegModNCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    Neg (ModNCompletedGroupAlgebraInClass n G C) where
  neg x := ⟨fun U => -(show ModNCompletedGroupAlgebraStageInClass n G C U from x.1 U), by
    intro U V hUV
    change modNCompletedGroupAlgebraTransitionInClass n G C hUV
        (-(show ModNCompletedGroupAlgebraStageInClass n G C V from x.1 V)) =
      -(show ModNCompletedGroupAlgebraStageInClass n G C U from x.1 U)
    rw [map_neg]
    exact congrArg Neg.neg (x.2 U V hUV)⟩

/--
Subtraction on the completed group algebra is defined coordinatewise through the finite-stage
group-algebra subtractions.
-/
instance instSubModNCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    Sub (ModNCompletedGroupAlgebraInClass n G C) where
  sub x y := ⟨fun U =>
      (show ModNCompletedGroupAlgebraStageInClass n G C U from x.1 U) -
        (show ModNCompletedGroupAlgebraStageInClass n G C U from y.1 U), by
    intro U V hUV
    change modNCompletedGroupAlgebraTransitionInClass n G C hUV
        ((show ModNCompletedGroupAlgebraStageInClass n G C V from x.1 V) -
          (show ModNCompletedGroupAlgebraStageInClass n G C V from y.1 V)) =
      (show ModNCompletedGroupAlgebraStageInClass n G C U from x.1 U) -
        (show ModNCompletedGroupAlgebraStageInClass n G C U from y.1 U)
    rw [map_sub]
    exact congrArg₂ HSub.hSub (x.2 U V hUV) (y.2 U V hUV)⟩

/--
The completed group algebra carries coefficient-ring scalar multiplication by applying the
scalar action at every finite quotient stage.
-/
instance instSMulNatModNCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    SMul ℕ (ModNCompletedGroupAlgebraInClass n G C) where
  smul m x := ⟨fun U =>
      m • (show ModNCompletedGroupAlgebraStageInClass n G C U from x.1 U), by
    intro U V hUV
    change modNCompletedGroupAlgebraTransitionInClass n G C hUV
        (m • (show ModNCompletedGroupAlgebraStageInClass n G C V from x.1 V)) =
      m • (show ModNCompletedGroupAlgebraStageInClass n G C U from x.1 U)
    rw [map_nsmul]
    exact congrArg (m • ·) (x.2 U V hUV)⟩

/--
The completed group algebra carries coefficient-ring scalar multiplication by applying the
scalar action at every finite quotient stage.
-/
instance instSMulIntModNCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    SMul ℤ (ModNCompletedGroupAlgebraInClass n G C) where
  smul m x := ⟨fun U =>
      m • (show ModNCompletedGroupAlgebraStageInClass n G C U from x.1 U), by
    intro U V hUV
    change modNCompletedGroupAlgebraTransitionInClass n G C hUV
        (m • (show ModNCompletedGroupAlgebraStageInClass n G C V from x.1 V)) =
      m • (show ModNCompletedGroupAlgebraStageInClass n G C U from x.1 U)
    rw [map_zsmul]
    exact congrArg (m • ·) (x.2 U V hUV)⟩

omit [Fact (0 < n)] in
/--
The inclusion of the \(C\)-indexed mod-\(n\) completed group algebra into the ambient completed
group algebra preserves zero.
-/
@[simp]
theorem coe_zero_modNCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    ((0 : ModNCompletedGroupAlgebraInClass n G C) :
      (U : CompletedGroupAlgebraIndexInClass G C) →
        ModNCompletedGroupAlgebraStageInClass n G C U) = 0 := by
  funext U
  rfl

omit [Fact (0 < n)] in
/--
The inclusion of the \(C\)-indexed mod-\(n\) completed group algebra into the ambient completed
group algebra preserves addition.
-/
@[simp]
theorem coe_add_modNCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u})
    (x y : ModNCompletedGroupAlgebraInClass n G C) :
    ((x + y : ModNCompletedGroupAlgebraInClass n G C) :
      (U : CompletedGroupAlgebraIndexInClass G C) →
        ModNCompletedGroupAlgebraStageInClass n G C U) = x + y := by
  funext U
  rfl

omit [Fact (0 < n)] in
/--
The inclusion of the \(C\)-indexed mod-\(n\) completed group algebra into the ambient completed
group algebra preserves negation.
-/
@[simp]
theorem coe_neg_modNCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u})
    (x : ModNCompletedGroupAlgebraInClass n G C) :
    ((-x : ModNCompletedGroupAlgebraInClass n G C) :
      (U : CompletedGroupAlgebraIndexInClass G C) →
        ModNCompletedGroupAlgebraStageInClass n G C U) = -x := by
  funext U
  rfl

omit [Fact (0 < n)] in
/--
The inclusion of the \(C\)-indexed mod-\(n\) completed group algebra into the ambient completed
group algebra preserves subtraction.
-/
@[simp]
theorem coe_sub_modNCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u})
    (x y : ModNCompletedGroupAlgebraInClass n G C) :
    ((x - y : ModNCompletedGroupAlgebraInClass n G C) :
      (U : CompletedGroupAlgebraIndexInClass G C) →
        ModNCompletedGroupAlgebraStageInClass n G C U) = x - y := by
  funext U
  rfl

omit [Fact (0 < n)] in
/--
The inclusion of the \(C\)-indexed mod-\(n\) completed group algebra into the ambient completed
group algebra preserves natural-number scalar multiplication.
-/
@[simp]
theorem coe_nsmul_modNCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u})
    (m : ℕ) (x : ModNCompletedGroupAlgebraInClass n G C) :
    ((m • x : ModNCompletedGroupAlgebraInClass n G C) :
      (U : CompletedGroupAlgebraIndexInClass G C) →
        ModNCompletedGroupAlgebraStageInClass n G C U) = m • x := by
  funext U
  rfl

omit [Fact (0 < n)] in
/--
The inclusion of the \(C\)-indexed mod-\(n\) completed group algebra into the ambient completed
group algebra preserves integer scalar multiplication.
-/
@[simp]
theorem coe_zsmul_modNCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u})
    (m : ℤ) (x : ModNCompletedGroupAlgebraInClass n G C) :
    ((m • x : ModNCompletedGroupAlgebraInClass n G C) :
      (U : CompletedGroupAlgebraIndexInClass G C) →
        ModNCompletedGroupAlgebraStageInClass n G C U) = m • x := by
  funext U
  rfl

/--
The class-indexed mod-\(n\) completion inherits an additive commutative group structure from its
injective inclusion into the family of finite stages.
-/
instance instAddCommGroupModNCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    AddCommGroup (ModNCompletedGroupAlgebraInClass n G C) :=
  Function.Injective.addCommGroup
    (fun x : ModNCompletedGroupAlgebraInClass n G C =>
      (x :
        (U : CompletedGroupAlgebraIndexInClass G C) →
          ModNCompletedGroupAlgebraStageInClass n G C U))
    Subtype.val_injective
    (coe_zero_modNCompletedGroupAlgebraInClass (n := n) (G := G) C)
    (coe_add_modNCompletedGroupAlgebraInClass (n := n) (G := G) C)
    (coe_neg_modNCompletedGroupAlgebraInClass (n := n) (G := G) C)
    (coe_sub_modNCompletedGroupAlgebraInClass (n := n) (G := G) C)
    (fun x m => coe_nsmul_modNCompletedGroupAlgebraInClass (n := n) (G := G) C m x)
    (fun x m => coe_zsmul_modNCompletedGroupAlgebraInClass (n := n) (G := G) C m x)

omit [Fact (0 < n)] in
/-- The finite-stage projection sends \(0\) to \(0\). -/
@[simp]
theorem modNCompletedGroupAlgebraProjectionInClass_zero
    (C : ProCGroups.FiniteGroupClass.{u}) (U : CompletedGroupAlgebraIndexInClass G C) :
    modNCompletedGroupAlgebraProjectionInClass n G C U
      (0 : ModNCompletedGroupAlgebraInClass n G C) = 0 := by
  rfl

omit [Fact (0 < n)] in
/-- The mod-\(n\) finite-stage projection preserves addition. -/
@[simp]
theorem modNCompletedGroupAlgebraProjectionInClass_add
    (C : ProCGroups.FiniteGroupClass.{u}) (U : CompletedGroupAlgebraIndexInClass G C)
    (x y : ModNCompletedGroupAlgebraInClass n G C) :
    modNCompletedGroupAlgebraProjectionInClass n G C U (x + y) =
      modNCompletedGroupAlgebraProjectionInClass n G C U x +
        modNCompletedGroupAlgebraProjectionInClass n G C U y := by
  rfl

omit [Fact (0 < n)] in
/-- The mod-\(n\) finite-stage projection preserves negation. -/
@[simp]
theorem modNCompletedGroupAlgebraProjectionInClass_neg
    (C : ProCGroups.FiniteGroupClass.{u}) (U : CompletedGroupAlgebraIndexInClass G C)
    (x : ModNCompletedGroupAlgebraInClass n G C) :
    modNCompletedGroupAlgebraProjectionInClass n G C U (-x) =
      -modNCompletedGroupAlgebraProjectionInClass n G C U x := by
  rfl

omit [Fact (0 < n)] in
/-- The mod-\(n\) finite-stage projection preserves subtraction. -/
@[simp]
theorem modNCompletedGroupAlgebraProjectionInClass_sub
    (C : ProCGroups.FiniteGroupClass.{u}) (U : CompletedGroupAlgebraIndexInClass G C)
    (x y : ModNCompletedGroupAlgebraInClass n G C) :
    modNCompletedGroupAlgebraProjectionInClass n G C U (x - y) =
      modNCompletedGroupAlgebraProjectionInClass n G C U x -
        modNCompletedGroupAlgebraProjectionInClass n G C U y := by
  rfl

omit [Fact (0 < n)] in
/-- The finite-stage projection is compatible with natural-number scalar multiplication. -/
@[simp]
theorem modNCompletedGroupAlgebraProjectionInClass_nsmul
    (C : ProCGroups.FiniteGroupClass.{u}) (U : CompletedGroupAlgebraIndexInClass G C)
    (m : ℕ) (x : ModNCompletedGroupAlgebraInClass n G C) :
    modNCompletedGroupAlgebraProjectionInClass n G C U (m • x) =
      m • modNCompletedGroupAlgebraProjectionInClass n G C U x := by
  rfl

omit [Fact (0 < n)] in
/-- The finite-stage projection is compatible with integer scalar multiplication. -/
@[simp]
theorem modNCompletedGroupAlgebraProjectionInClass_zsmul
    (C : ProCGroups.FiniteGroupClass.{u}) (U : CompletedGroupAlgebraIndexInClass G C)
    (m : ℤ) (x : ModNCompletedGroupAlgebraInClass n G C) :
    modNCompletedGroupAlgebraProjectionInClass n G C U (m • x) =
      m • modNCompletedGroupAlgebraProjectionInClass n G C U x := by
  rfl

end

end FoxDifferential
