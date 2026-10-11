/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.ImageSubmodule
import Nyll.SchemeTheory.Modules.SubmoduleGluingQuasicoherent
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.Shapes.StrongEpi

/-!
# The actual image on an open where its source generates

If a morphism into a prescribed native submodule becomes epimorphic on an
open, the image of its composite into the ambient sheaf restricts to that
exact prescribed submodule. The reverse inclusion is constructed by the
epimorphism--monomorphism lifting property in the actual sheaf category.
-/

noncomputable section

universe u v

open CategoryTheory

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}

private theorem overSheafIso_inv_ι {M : SheafOfModules.{u} R}
    (N : M.Submodule) (U : C) :
    (Submodule.overSheafIso N U).inv ≫ (N.over U).ι = N.ι.over U := by
  rw [← Submodule.overSheafIso_hom_ι, Iso.inv_hom_id_assoc]

variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{u}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- An actual local epimorphism onto `P` gives literal equality between `P`
and the restriction of its image in the ambient sheaf. -/
theorem imageSubmodule_over_eq_of_epi {A M : SheafOfModules.{u} R}
    (P : M.Submodule) (f : A ⟶ P.toSheafOfModules) (U : C) [Epi (f.over U)] :
    (imageSubmodule (f ≫ P.ι)).over U = P.over U := by
  let N : M.Submodule := imageSubmodule (f ≫ P.ι)
  have hNP : N ≤ P := imageSubmodule_le (f ≫ P.ι) P f rfl
  apply le_antisymm
  · intro X
    exact hNP (Opposite.op X.unop.left)
  · let a : A.over U ⟶ (P.over U).toSheafOfModules :=
      f.over U ≫ (Submodule.overSheafIso P U).inv
    let b : A.over U ⟶ (N.over U).toSheafOfModules :=
      (toImageSubmodule (f ≫ P.ι)).over U ≫ (Submodule.overSheafIso N U).inv
    have : Epi a := inferInstanceAs
      (Epi (f.over U ≫ (Submodule.overSheafIso P U).inv))
    have : StrongEpi a := strongEpi_of_epi a
    let sq : CommSq b a (N.over U).ι (P.over U).ι := ⟨by
      dsimp only [a, b]
      rw [Category.assoc, overSheafIso_inv_ι, Category.assoc, overSheafIso_inv_ι]
      change (overFunctor R U).map (toImageSubmodule (f ≫ P.ι)) ≫
          (overFunctor R U).map N.ι =
        (overFunctor R U).map f ≫ (overFunctor R U).map P.ι
      rw [← Functor.map_comp, toImageSubmodule_ι, ← Functor.map_comp]⟩
    exact Submodule.le_of_hom_ι (P.over U) (N.over U) sq.lift sq.fac_right

end SheafOfModules
