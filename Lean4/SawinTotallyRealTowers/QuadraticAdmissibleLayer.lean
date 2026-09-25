/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.FiniteRealPExtension
import SawinTotallyRealTowers.QuadraticClosure
import SawinTotallyRealTowers.QuadraticFieldDiscriminant
import SawinTotallyRealTowers.QuadraticReality
import SawinTotallyRealTowers.RationalRamificationSupport
import Mathlib.Algebra.Order.Ring.Cast
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.PGroup

set_option autoImplicit false

/-!
# Admissible quadratic layers from supported radicands

A positive squarefree integer congruent to one modulo four determines an
actual quadratic field in the fixed algebraic closure. Its Galois group
has order two, its embeddings are real, and its discriminant is the given
integer. Restricting its prime divisors therefore makes this constructed
field an admissible finite layer of the real pro-two tower.
-/

open scoped NumberField
open NumberField IsDedekindDomain

namespace ClassFieldTower.Sawin

/-- A positive squarefree nonsquare radicand congruent to one modulo four
and supported on `T` produces an actual admissible quadratic layer. -/
theorem isAdmissibleFiniteLayer_quadraticClosure
    (d : ℤ) (hdPos : 0 < d) (hdSquarefree : Squarefree d.natAbs)
    (hMod : d % 4 = 1) (hdNonsquare : ¬ IsSquare (d : ℚ))
    (T : Set (HeightOneSpectrum (𝓞 ℚ)))
    (hSupport : ∀ q : Nat.Primes, (q : ℤ) ∣ d →
      (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm q ∈ T) :
    IsAdmissibleFiniteLayer 2 T (quadraticClosure (d : ℚ) hdNonsquare) := by
  let E : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ) :=
    quadraticClosure (d : ℚ) hdNonsquare
  let : NumberField E := NumberField.of_module_finite ℚ E
  let : Algebra.IsQuadraticExtension ℚ E :=
    quadraticClosure_isQuadraticExtension (d : ℚ) hdNonsquare
  let β : E := quadraticClosureGenerator (d : ℚ) hdNonsquare
  have hSquare : β ^ 2 = algebraMap ℚ E (d : ℚ) :=
    quadraticClosureGenerator_sq (d : ℚ) hdNonsquare
  have hGenerate : IntermediateField.adjoin ℚ ({β} : Set E) = ⊤ :=
    quadraticClosureGenerator_adjoin (d : ℚ) hdNonsquare
  change IsAdmissibleFiniteLayer 2 T E
  refine ⟨?_, ?_, ?_⟩
  · apply IsPGroup.of_card (n := 1)
    exact (IsGalois.card_aut_eq_finrank ℚ E).trans
      ((quadraticClosure_finrank (d : ℚ) hdNonsquare).trans (pow_one 2).symm)
  · apply (isUnramifiedAtFinitePlacesOutside_rat_iff_discr E T).mpr
    rw [numberField_discr_of_mod_four_eq_one E d hdSquarefree β hSquare hGenerate hMod]
    exact hSupport
  · apply (isUnramifiedAtInfinitePlaces_rat_iff_isTotallyReal E).mpr
    exact isTotallyReal_of_sq_nonneg_adjoin E hSquare hGenerate
      (Int.cast_nonneg hdPos.le)

end ClassFieldTower.Sawin
