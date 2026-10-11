/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.RingTheory.RingHom.Surjective

/-!
# Surjectivity in an actual ring-section pushout

This applies native stability of surjective ring maps to the actual
categorical pushout, retaining all four supplied maps.
-/

open CategoryTheory CategoryTheory.Limits

namespace CommRingCat

universe u

/-- In an actual ring pushout, the cobase change of a surjective map is surjective. -/
theorem surjective_pushout_inr_of_surjective
    {R S A B : CommRingCat.{u}} (f : R ⟶ S) (g : R ⟶ A)
    (i : S ⟶ B) (j : A ⟶ B) (h : IsPushout f g i j)
    (hf : Function.Surjective f) : Function.Surjective j := by
  let : Algebra R S := f.hom.toAlgebra
  let : Algebra R A := g.hom.toAlgebra
  let : Algebra S B := i.hom.toAlgebra
  let : Algebra A B := j.hom.toAlgebra
  let : Algebra R B := (g ≫ j).hom.toAlgebra
  have : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R S B :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom h.w).symm
  have hAlgebra : Algebra.IsPushout R S A B :=
    CommRingCat.isPushout_iff_isPushout.mp h
  exact RingHom.surjective_isStableUnderBaseChange R S A B hf

end CommRingCat
