/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.OreLocalization.Ring

/-!
# Principal localization as a commutative algebra

Bundles localization away from an element as a commutative algebra over the coefficient ring and
proves its localization witness.
-/


noncomputable section

namespace SchemeTheory

universe u w

/-- The principal localization with its native commutative ring and
coefficient algebra, bundled once as a commutative algebra. The constructor
works with abstract ring inputs before specializing to normalization stages. -/
def localizationAwayCommAlgCat (A : Type u) (R : Type w)
    [CommRing A] [CommRing R] [Algebra A R] (f : R) : CommAlgCat.{w} A := by
  letI : CommRing (Localization.Away f) :=
    inferInstanceAs (CommRing (OreLocalization (Submonoid.powers f) R))
  exact CommAlgCat.of A (Localization.Away f)

/-- The coefficient algebra stored by the native principal-localization
owner has its canonical localization witness. -/
theorem localizationAwayCommAlgCat_isLocalization (R : Type w) [CommRing R] (f : R) :
    IsLocalization.Away f (localizationAwayCommAlgCat R R f) := by
  change IsLocalization.Away f (Localization.Away f)
  infer_instance

end SchemeTheory
