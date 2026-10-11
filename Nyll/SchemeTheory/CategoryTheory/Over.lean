/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Based on pi1 source (comparison revision; exact copied commit unverified):
https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/Mathlib/CategoryTheory/Limits/MorphismProperty.lean
Original mathlib source:
https://github.com/leanprover-community/mathlib4/blob/53f8a93a7739dd4eb33926f645811ebb6cee21bf/Mathlib/CategoryTheory/Limits/MorphismProperty.lean
-/

module

public import Mathlib.CategoryTheory.Limits.MorphismProperty

/-!
# Finite limits in over categories of a morphism property

Under stability and cancellation hypotheses, the forgetful functor from the over category
creates finite limits, and pullback along a morphism preserves them.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.MorphismProperty.Over

noncomputable
instance {C : Type*} [Category C] (P : MorphismProperty C) (X : C)
    [HasPullbacks C] [P.IsStableUnderComposition] [P.ContainsIdentities]
    [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P] :
    CreatesFiniteLimits (Over.forget P ⊤ X) :=
  createsFiniteLimitsOfCreatesTerminalAndPullbacks _

instance {C : Type*} [Category C] (P : MorphismProperty C) (X : C)
    [HasPullbacks C] [P.IsStableUnderComposition] [P.ContainsIdentities]
    [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P] :
    PreservesFiniteLimits (Over.forget P ⊤ X) :=
  preservesFiniteLimits_of_preservesTerminal_and_pullbacks (Over.forget P ⊤ X)

variable {C : Type*} [Category C] (P Q : MorphismProperty C)
variable [HasPullbacks C] [P.IsStableUnderBaseChange] [Q.IsStableUnderBaseChange]
  [Q.IsMultiplicative]

instance {X Y : C} (f : X ⟶ Y) [P.HasOfPostcompProperty P]
    [P.IsStableUnderComposition] [P.ContainsIdentities] :
    PreservesFiniteLimits (MorphismProperty.Over.pullback P ⊤ f) := by
  constructor
  intro J _ _
  have heq : MorphismProperty.Over.pullback P ⊤ f ⋙ MorphismProperty.Over.forget _ _ _ =
      MorphismProperty.Over.forget _ _ _ ⋙ CategoryTheory.Over.pullback f :=
    rfl
  have : PreservesLimitsOfShape J
      (MorphismProperty.Over.pullback P ⊤ f ⋙ MorphismProperty.Over.forget _ _ _) := by
    rw [heq]
    infer_instance
  apply preservesLimitsOfShape_of_reflects_of_preserves
    (MorphismProperty.Over.pullback P ⊤ f) (MorphismProperty.Over.forget _ _ _)

end CategoryTheory.MorphismProperty.Over
