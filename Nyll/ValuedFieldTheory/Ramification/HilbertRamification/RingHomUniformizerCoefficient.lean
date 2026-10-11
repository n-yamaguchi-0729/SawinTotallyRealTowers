/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.GroupWithZero.Units.Basic

/-!
# Coefficients of a mapped uniformizer

The coefficient in `π * c = s(π)` is constructed from the ring map and the element.
Existence and nonzero-factor cancellation identify it with any actual unit ratio,
without using a ramification character.
-/

noncomputable section

namespace RamificationTheory.HilbertRamification.DiscreteValuationRing

universe u

/-- Extract the coefficient in the literal equation `π * c = s(π)` when
it exists. This construction uses only the ring map and the chosen element;
it does not use a character, residue action, or character evaluation. -/
def ringHomUniformizerCoefficient
    (R : Type u) [CommRing R] (s : R →+* R) (π : R) : R := by
  classical
  exact if h : ∃ c : R, π * c = s.toFun π then h.choose else 0

/-- An actual coefficient witness makes the extracted coefficient solve
the prescribed equation. -/
theorem ringHomUniformizerCoefficient_spec
    (R : Type u) [CommRing R] (s : R →+* R) (π : R)
    (h : ∃ c : R, π * c = s.toFun π) :
    π * ringHomUniformizerCoefficient R s π = s.toFun π := by
  classical
  unfold ringHomUniformizerCoefficient
  rw [dite_eq_left h]
  exact h.choose_spec

/-- In a domain, the coefficient of a nonzero element is unique. In
particular, any actual uniformizer-ratio witness gives this same coefficient. -/
theorem ringHomUniformizerCoefficient_eq_of_mul_eq
    (R : Type u) [CommRing R] [IsDomain R]
    (s : R →+* R) (π : R) (hπ : π ≠ 0)
    (c : R) (hc : π * c = s.toFun π) :
    ringHomUniformizerCoefficient R s π = c := by
  exact mul_left_cancel₀ hπ
    ((ringHomUniformizerCoefficient_spec R s π ⟨c, hc⟩).trans hc.symm)

/-- A constructed unit ratio supplies both properties of the extracted
coefficient, with no chosen character or comparison in its definition. -/
theorem ringHomUniformizerCoefficient_unit_spec
    (R : Type u) [CommRing R] [IsDomain R]
    (s : R →+* R) (π : R) (hπ : π ≠ 0)
    (h : ∃ c : R, IsUnit c ∧ π * c = s.toFun π) :
    IsUnit (ringHomUniformizerCoefficient R s π) ∧
      π * ringHomUniformizerCoefficient R s π = s.toFun π := by
  obtain ⟨c, hunit, hc⟩ := h
  have heq := ringHomUniformizerCoefficient_eq_of_mul_eq R s π hπ c hc
  exact ⟨heq.symm ▸ hunit, (congrArg (fun x : R => π * x) heq).trans hc⟩

end RamificationTheory.HilbertRamification.DiscreteValuationRing

end
