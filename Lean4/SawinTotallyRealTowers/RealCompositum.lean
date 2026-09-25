/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

set_option autoImplicit false

/-!
# Real places in composita over the rationals

The initial Sawin tower has base field `ℚ`. Over this base, being unramified
at infinite places is exactly total reality. Total reality is preserved by
composita inside an algebraic extension, so this supplies the real-place
condition independently of the finite ramification support and the prime `p`.
-/

open NumberField

universe u

namespace ClassFieldTower.Sawin

/-- Since every infinite place of `ℚ` is real, an extension of `ℚ` is
unramified at infinite places exactly when its infinite places are all real. -/
theorem isUnramifiedAtInfinitePlaces_rat_iff_isTotallyReal
    (K : Type u) [Field K] [CharZero K] :
    IsUnramifiedAtInfinitePlaces ℚ K ↔ IsTotallyReal K := by
  constructor
  · intro h
    refine ⟨fun w ↦ ?_⟩
    exact (InfinitePlace.isUnramified_iff.mp (h.isUnramified w)).resolve_right
      (InfinitePlace.not_isComplex_iff_isReal.mpr
        (IsTotallyReal.isReal (w.comap (algebraMap ℚ K))))
  · intro h
    refine ⟨fun w ↦ ?_⟩
    exact InfinitePlace.isUnramified_iff.mpr (Or.inl (h.isReal w))

/-- The compositum of two subextensions of an algebraic extension of `ℚ`
retains the real-place condition. No odd-degree or Galois hypothesis is needed. -/
theorem isUnramifiedAtInfinitePlaces_rat_sup
    {E : Type u} [Field E] [CharZero E] [Algebra.IsAlgebraic ℚ E]
    (A B : IntermediateField ℚ E)
    (hA : IsUnramifiedAtInfinitePlaces ℚ A)
    (hB : IsUnramifiedAtInfinitePlaces ℚ B) :
    IsUnramifiedAtInfinitePlaces ℚ (A ⊔ B : IntermediateField ℚ E) := by
  let : IsTotallyReal A.toSubfield :=
    (isUnramifiedAtInfinitePlaces_rat_iff_isTotallyReal A).mp hA
  let : IsTotallyReal B.toSubfield :=
    (isUnramifiedAtInfinitePlaces_rat_iff_isTotallyReal B).mp hB
  have hSup : IsTotallyReal (A.toSubfield ⊔ B.toSubfield : Subfield E) :=
    NumberField.isTotallyReal_sup
  rw [← IntermediateField.sup_toSubfield A B] at hSup
  exact (isUnramifiedAtInfinitePlaces_rat_iff_isTotallyReal
    (A ⊔ B : IntermediateField ℚ E)).mpr hSup

end ClassFieldTower.Sawin
