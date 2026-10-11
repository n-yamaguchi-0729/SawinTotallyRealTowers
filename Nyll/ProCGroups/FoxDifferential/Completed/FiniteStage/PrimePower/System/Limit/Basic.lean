/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.FiniteStage.PrimePower.System.Basic

/-!
# Fox differential: prime power — system — limit — basic

The principal declarations in this module are:

- `FoxAlgebraicStagePrimePowerSourceLimit`
  Inverse limit of the prime-power finite Fox source group-algebra system.
- `FoxAlgebraicStagePrimePowerTargetLimit`
  Inverse limit of the prime-power finite Fox target group-algebra system.
- `foxAlgebraicStagePrimePowerSourceLimitToFamily_injective`
  The family map out of the source inverse limit is injective.
- `foxAlgebraicStagePrimePowerTargetLimitToFamily_injective`
  The family map out of the target inverse limit is injective.
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


/-- Inverse limit of the prime-power finite Fox source group-algebra system. -/
abbrev FoxAlgebraicStagePrimePowerSourceLimit
    (N : Subgroup (FreeGroup X)) : Type u :=
  (foxAlgebraicStagePrimePowerSourceSystem (ℓ := ℓ) (X := X) N).inverseLimit

/-- Inverse limit of the prime-power finite Fox target group-algebra system. -/
abbrev FoxAlgebraicStagePrimePowerTargetLimit
    (N : Subgroup (FreeGroup X)) [N.Normal] : Type u :=
  (foxAlgebraicStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).inverseLimit

/-- Forget a source inverse-limit element to its compatible family of source stages. -/
def foxAlgebraicStagePrimePowerSourceLimitToFamily
    (N : Subgroup (FreeGroup X)) :
    FoxAlgebraicStagePrimePowerSourceLimit (ℓ := ℓ) (X := X) N →
      ((a : ℕ) → foxAlgebraicStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N a) :=
  fun z a => z.1 a

/-- Forget a target inverse-limit element to its compatible family of target stages. -/
def foxAlgebraicStagePrimePowerTargetLimitToFamily
    (N : Subgroup (FreeGroup X)) [N.Normal] :
    FoxAlgebraicStagePrimePowerTargetLimit (ℓ := ℓ) (X := X) N →
      ((a : ℕ) → foxAlgebraicStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N a) :=
  fun z a => z.1 a

omit [DecidableEq X] in
/-- The family map out of the source inverse limit is injective. -/
theorem foxAlgebraicStagePrimePowerSourceLimitToFamily_injective
    (N : Subgroup (FreeGroup X)) :
    Function.Injective
      (foxAlgebraicStagePrimePowerSourceLimitToFamily (ℓ := ℓ) (X := X) N) := by
  intro x y h
  apply Subtype.ext
  funext a
  exact congrFun h a

omit [DecidableEq X] in
/-- The family map out of the target inverse limit is injective. -/
theorem foxAlgebraicStagePrimePowerTargetLimitToFamily_injective
    (N : Subgroup (FreeGroup X)) [N.Normal] :
    Function.Injective
      (foxAlgebraicStagePrimePowerTargetLimitToFamily (ℓ := ℓ) (X := X) N) := by
  intro x y h
  apply Subtype.ext
  funext a
  exact congrFun h a




end

end FoxDifferential
