/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
public import Mathlib.CategoryTheory.Limits.MorphismProperty
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Exactness of the finite étale forgetful functor

This file records the limit-preservation part of Stacks Project, Tag `0BNA`,
directly for the canonical forgetful functor from finite étale schemes.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.FiniteEtale

variable (X : Scheme.{u})

/-- The canonical forgetful functor from finite étale schemes over `X` to
schemes over `X` preserves finite limits. -/
instance forgetPreservesFiniteLimits :
    PreservesFiniteLimits (forget X) := by
  let : HasPullbacks Scheme.{u} := inferInstance
  let : MorphismProperty.IsStableUnderComposition
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) := inferInstance
  let : MorphismProperty.ContainsIdentities
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) := inferInstance
  let : MorphismProperty.IsStableUnderBaseChange
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) := inferInstance
  let : MorphismProperty.HasOfPostcompProperty
      (@IsFiniteEtale : MorphismProperty Scheme.{u})
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) := inferInstance
  let : MorphismProperty.RespectsIso
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) := by
    apply MorphismProperty.RespectsIso.mk
    · intro _ _ _ _ f hf
      let : IsFinite f := hf.toIsFinite
      let : Etale f := hf.toEtale
      exact @IsFiniteEtale.mk _ _ _ inferInstance inferInstance
    · intro _ _ _ _ f hf
      let : IsFinite f := hf.toIsFinite
      let : Etale f := hf.toEtale
      exact @IsFiniteEtale.mk _ _ _ inferInstance inferInstance
  let : Category (MorphismProperty.Over
      (@IsFiniteEtale : MorphismProperty Scheme.{u})
      (⊤ : MorphismProperty Scheme.{u}) X) := FiniteEtale.instCategory X
  let : HasTerminal (MorphismProperty.Over
      (@IsFiniteEtale : MorphismProperty Scheme.{u})
      (⊤ : MorphismProperty Scheme.{u}) X) :=
    (MorphismProperty.Over.mkIdTerminal
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) X).hasTerminal
  let : HasTerminal (Over X) := Over.mkIdTerminal.hasTerminal
  let : CreatesLimitsOfShape (Discrete PEmpty.{1})
      (MorphismProperty.Over.forget
        (@IsFiniteEtale : MorphismProperty Scheme.{u}) ⊤ X) := by
    apply +allowSynthFailures
      MorphismProperty.Comma.forgetCreatesLimitsOfShapeOfClosed
    · exact inferInstanceAs (HasLimitsOfShape _ (Over X))
    · apply Over.closedUnderLimitsOfShape_discrete_empty _
  let : HasPullbacks (MorphismProperty.Over
      (@IsFiniteEtale : MorphismProperty Scheme.{u})
      (⊤ : MorphismProperty Scheme.{u}) X) :=
    MorphismProperty.Over.hasPullbacks
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) X
  let : CreatesLimitsOfShape WalkingCospan
      (MorphismProperty.Over.forget
        (@IsFiniteEtale : MorphismProperty Scheme.{u}) ⊤ X) :=
    MorphismProperty.Over.createsLimitsOfShape_walkingCospan
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) X
  change PreservesFiniteLimits
    (MorphismProperty.Over.forget (@IsFiniteEtale : MorphismProperty Scheme.{u}) ⊤ X)
  exact preservesFiniteLimits_of_preservesTerminal_and_pullbacks _

/-- Forgetting a finite étale scheme all the way to schemes preserves
pullbacks. -/
instance forgetCompOverForgetPreservesPullbacks :
    PreservesLimitsOfShape WalkingCospan
      (forget X ⋙ CategoryTheory.Over.forget X) :=
  inferInstance

/-- Forgetting a finite étale scheme all the way to schemes preserves
equalizers. -/
instance forgetCompOverForgetPreservesEqualizers :
    PreservesLimitsOfShape WalkingParallelPair
      (forget X ⋙ CategoryTheory.Over.forget X) :=
  inferInstance

end AlgebraicGeometry.FiniteEtale
