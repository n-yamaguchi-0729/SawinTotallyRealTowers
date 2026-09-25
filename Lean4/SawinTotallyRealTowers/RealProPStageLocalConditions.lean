/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.FiniteRealPExtension
import ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.LocalBlocks
import ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.IdealToCompletion

set_option autoImplicit false
/-!
# Local conditions of actual finite real p-layers

The global ramification certificates on an admissible finite layer imply
the actual chosen-completion conditions used by finite H² localization.
-/

open scoped NumberField
open NumberField IsDedekindDomain

namespace ClassFieldTower.Sawin

private local instance stageNumberField (p : ℕ)
    (T : Set (HeightOneSpectrum (𝓞 ℚ))) (E : FiniteRealPExtension p T) : NumberField E.val :=
  NumberField.of_module_finite ℚ E.val

private local instance stageIsGalois (p : ℕ)
    (T : Set (HeightOneSpectrum (𝓞 ℚ))) (E : FiniteRealPExtension p T) :
    IsGalois ℚ E.val.toIntermediateField := E.val.isGalois

/-- The actual chosen completion of an admissible layer is unramified
at every finite place outside its allowed support. -/
theorem finiteRealPExtension_chosenFinitePlaceIsUnramified
    (p : ℕ) (T : Set (HeightOneSpectrum (𝓞 ℚ))) (E : FiniteRealPExtension p T)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : v ∉ T) :
    ChosenFinitePlaceIsUnramified (K := ℚ) (L := E.val) v := by
  apply chosenFinitePlaceIsUnramified_of_isUnramifiedAt
  apply E.property.2.1
  simpa only [finitePlaceBelow_finitePlaceExtensionCentre] using hv

/-- Every chosen infinite place of an admissible layer is unramified. -/
theorem finiteRealPExtension_chosenInfinitePlaceIsUnramified
    (p : ℕ) (T : Set (HeightOneSpectrum (𝓞 ℚ))) (E : FiniteRealPExtension p T)
    (v : InfinitePlace ℚ) :
    (chosenInfinitePlaceAbove (L := E.val) v).IsUnramified ℚ := by
  let : IsUnramifiedAtInfinitePlaces ℚ E.val := E.property.2.2
  exact IsUnramifiedAtInfinitePlaces.isUnramified _

end ClassFieldTower.Sawin
