/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RingTheory.Extension.Presentation.Submersive
public import Mathlib.RingTheory.Extension.Presentation.Basic
public import Mathlib.RingTheory.Smooth.StandardSmooth
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Localizing a presentation at its Jacobian

A presubmersive presentation has an injective assignment of relations to
variables, without any assumption that its Jacobian is invertible. Composing
with the presentation of the localization at that Jacobian gives a submersive
presentation of the same relative dimension. In relative dimension zero the
localized algebra is therefore étale.
-/

@[expose] public section

noncomputable section

universe u v w t

open Algebra

namespace Algebra.PreSubmersivePresentation

variable {R : Type u} {S : Type v} {ι : Type w} {σ : Type t}
  [CommRing R] [CommRing S] [Algebra R S] [Finite σ]
  (P : PreSubmersivePresentation R S ι σ)

/-- Inverting the Jacobian makes a presubmersive presentation submersive. -/
def jacobianLocalizationPresentation :
    SubmersivePresentation R (Localization.Away P.jacobian) (Unit ⊕ ι) (Unit ⊕ σ) where
  toPreSubmersivePresentation :=
    (PreSubmersivePresentation.localizationAway (Localization.Away P.jacobian) P.jacobian).comp P
  jacobian_isUnit := by
    rw [PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
      PreSubmersivePresentation.localizationAway_jacobian, Algebra.smul_def]
    exact (IsLocalization.Away.algebraMap_isUnit P.jacobian).mul
      (IsLocalization.Away.algebraMap_isUnit P.jacobian)

/-- The Jacobian localization preserves the relative dimension of the presentation. -/
lemma jacobianLocalizationPresentation_dimension [Finite ι] :
    (jacobianLocalizationPresentation P).dimension = P.dimension := by
  change ((PreSubmersivePresentation.localizationAway
    (Localization.Away P.jacobian) P.jacobian).comp P).dimension = P.dimension
  rw [PreSubmersivePresentation.dimension_comp_eq_dimension_add_dimension]
  change (Presentation.localizationAway (Localization.Away P.jacobian) P.jacobian).dimension +
    P.dimension = P.dimension
  rw [Presentation.localizationAway_dimension_zero, zero_add]

/-- A presentation of relative dimension zero becomes étale after inverting its Jacobian. -/
lemma jacobianLocalization_etale [Finite ι] (h : P.dimension = 0) :
    Algebra.Etale R (Localization.Away P.jacobian) := by
  have : IsStandardSmoothOfRelativeDimension 0 R (Localization.Away P.jacobian) :=
    (jacobianLocalizationPresentation P).isStandardSmoothOfRelativeDimension
      ((jacobianLocalizationPresentation_dimension P).trans h)
  infer_instance

end Algebra.PreSubmersivePresentation
