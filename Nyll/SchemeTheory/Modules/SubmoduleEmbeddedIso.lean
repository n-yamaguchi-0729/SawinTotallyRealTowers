/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule

/-!
# Literal equality from embedded submodule comparisons

An actual morphism commuting with the native inclusions gives pointwise
containment. An actual isomorphism commuting with the inclusions therefore
gives equality of the original native submodules. In particular, the
embedded restriction comparison in the quasicoherent extension theorem
can be used by submodule gluing without an assumed section comparison.
-/

noncomputable section

universe v v₁ u₁ u

open CategoryTheory

namespace SheafOfModules.Submodule

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}} {M : SheafOfModules.{v} R}

/-- A map of actual submodules commuting with their inclusions gives containment. -/
theorem le_of_hom_ι (N P : M.Submodule)
    (f : N.toSheafOfModules ⟶ P.toSheafOfModules) (hf : f ≫ P.ι = N.ι) :
    N ≤ P := by
  intro X s hs
  let sN : N.toSubmodule.obj X := ⟨s, hs⟩
  have h := congrArg
    (fun g : N.toSheafOfModules ⟶ M => (g.val.app X).hom sN) hf
  change ((f.val.app X).hom sN).val = s at h
  rw [← h]
  exact ((f.val.app X).hom sN).property

/-- An isomorphism of submodules respecting their native embeddings gives
equality of the actual submodules, including every section submodule. -/
theorem eq_of_iso_ι (N P : M.Submodule)
    (e : N.toSheafOfModules ≅ P.toSheafOfModules) (he : e.hom ≫ P.ι = N.ι) :
    N = P := by
  apply le_antisymm (le_of_hom_ι N P e.hom he)
  apply le_of_hom_ι P N e.inv
  rw [← he, Iso.inv_hom_id_assoc]

end SheafOfModules.Submodule
