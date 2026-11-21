/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.NumberField.FiniteUnramifiedTower
public import Nyll.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsEverywhereUnramified
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification

/-!
# Everywhere-unramified towers of number fields

This file combines finite-prime and infinite-place unramifiedness and
records its tower and intermediate-field properties.
-/



@[expose] public section

open scoped NumberField

universe u v w

namespace ClassFieldTheory.IsEverywhereUnramified

/-- The identity extension is everywhere unramified. -/
theorem refl
    (K : Type u) [Field K] [NumberField K] :
    IsEverywhereUnramified K K where
  left :=
    IsUnramifiedAtFinitePlaces.refl K
  right :=
    inferInstance

variable
    {k : Type u} {K : Type v} {F : Type w}
    [Field k] [NumberField k]
    [Field K] [NumberField K]
    [Field F] [NumberField F]
    [Algebra k K] [Algebra k F] [Algebra K F]
    [IsScalarTower k K F]

/-- Everywhere-unramified extensions are transitive in towers. -/
theorem trans
    (hkK : IsEverywhereUnramified k K)
    (hKF : IsEverywhereUnramified K F) :
    IsEverywhereUnramified k F where
  left :=
    IsUnramifiedAtFinitePlaces.trans
      hkK.1 hKF.1
  right := by
    let : IsUnramifiedAtInfinitePlaces k K :=
      hkK.2
    let : IsUnramifiedAtInfinitePlaces K F :=
      hKF.2
    exact
      IsUnramifiedAtInfinitePlaces.trans k K F

/-- If the top of a number-field tower is everywhere unramified over
the bottom, then it is everywhere unramified over the intermediate
field. -/
theorem top
    (hkF : IsEverywhereUnramified k F) :
    IsEverywhereUnramified K F where
  left :=
    IsUnramifiedAtFinitePlaces.top hkF.1
  right := by
    let : IsUnramifiedAtInfinitePlaces k F :=
      hkF.2
    exact
      IsUnramifiedAtInfinitePlaces.top k K F

/-- If the top of a number-field tower is everywhere unramified over
the bottom, then the intermediate field is everywhere unramified over
the bottom. -/
theorem bot
    (hkF : IsEverywhereUnramified k F) :
    IsEverywhereUnramified k K where
  left :=
    IsUnramifiedAtFinitePlaces.bot hkF.1
  right := by
    let : IsUnramifiedAtInfinitePlaces k F :=
      hkF.2
    exact
      IsUnramifiedAtInfinitePlaces.bot k K F

end ClassFieldTheory.IsEverywhereUnramified
