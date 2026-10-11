/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Normalization.NativeNormalizationRingMap
import Nyll.SchemeTheory.Normalization.SubalgebraPreimage
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Ring.Hom.Defs

/-!
# Maps in subalgebra normalization towers

Constructs the ring map between normalizations of nested subalgebras. It proves compatibility
with the ambient inclusion and injectivity of the tower map.
-/

noncomputable section

namespace SchemeTheory

universe u v

variable {A : Type u} {L : Type v}
  [CommRing A] [CommRing L] [Algebra A L]

/-- The actual map between nested native subalgebra normalizations. -/
def subalgebraNormalizationTowerRingMap
    (S T : Subalgebra A L) (h : S ≤ T) :
    subalgebraNormalizationCommAlgCat S →+* subalgebraNormalizationCommAlgCat T :=
  nativeNormalizationRingMap (subalgebraCommAlgCat S) (subalgebraCommAlgCat T)
    (Subalgebra.inclusion h)

/-- The normalization tower is the literal triangle of subtype inclusions. -/
theorem subalgebraNormalizationTowerRingMap_comp
    (S T : Subalgebra A L) (h : S ≤ T) :
    (subalgebraNormalizationRingMap T).comp
      (subalgebraNormalizationTowerRingMap S T h) = subalgebraNormalizationRingMap S := rfl

/-- The tower map is injective because its composite is the native ambient inclusion. -/
theorem subalgebraNormalizationTowerRingMap_injective
    (S T : Subalgebra A L) (h : S ≤ T) :
    Function.Injective (subalgebraNormalizationTowerRingMap S T h).toFun := by
  intro x y hxy
  apply subalgebraNormalizationRingMap_injective S
  exact congrArg (subalgebraNormalizationRingMap T).toFun hxy

end SchemeTheory

end
