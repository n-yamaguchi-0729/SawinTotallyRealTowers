/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.FiniteTypeLocality
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# Recovering finite type from restriction to the top open

The singleton family consisting of the top open covers every open.
The existing finite-type locality theorem therefore recovers global
finite type from the actual top-slice module used by the open induction.
-/

noncomputable section

universe u

open CategoryTheory TopologicalSpace

namespace SheafOfModules

/-- Finite type on the top slice is finite type on the original open-set site. -/
theorem IsFiniteType.of_over_top {X : Type u} [TopologicalSpace X]
    {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}
    (M : SheafOfModules.{u} R) (hM : (M.over (⊤ : Opens X)).IsFiniteType) :
    M.IsFiniteType := by
  apply IsFiniteType.of_coversTop M (fun _i : PUnit.{u + 1} => (⊤ : Opens X))
  · intro U
    apply (Opens.grothendieckTopology X).covering_of_eq_top
    apply le_antisymm le_top
    intro V f _hf
    exact ⟨PUnit.unit, ⟨homOfLE le_top⟩⟩
  · intro _i
    exact hM

end SheafOfModules
