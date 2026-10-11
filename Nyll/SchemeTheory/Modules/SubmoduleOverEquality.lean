/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.SubmoduleGluingQuasicoherent

/-!
# Exact restriction equalities for the finite-open induction

Equality on a slice gives equality of every actual section submodule
below that slice. It is therefore inherited by smaller slices, and the
native gluing has the exact prescribed restrictions on both opens.
-/

noncomputable section

universe v v₁ u₁ u

open CategoryTheory Opposite

namespace SheafOfModules.Submodule

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}} {M : SheafOfModules.{v} R}

/-- Exact equality on a slice identifies every section submodule below it. -/
theorem obj_eq_of_over_eq {N P : M.Submodule} {U : C}
    (h : N.over U = P.over U) (V : C) (f : V ⟶ U) :
    N.toSubmodule.obj (op V) = P.toSubmodule.obj (op V) :=
  congrArg (fun Q : (M.over U).Submodule => Q.toSubmodule.obj (op (Over.mk f))) h

/-- Literal equality of native submodules persists under further restriction. -/
theorem over_eq_of_over_eq {N P : M.Submodule} {U V : C}
    (h : N.over V = P.over V) (f : U ⟶ V) : N.over U = P.over U := by
  apply over_eq_of_obj_eq N P U
  intro W g
  exact obj_eq_of_over_eq h W (g ≫ f)

/-- The constructed gluing has exactly the first prescribed native restriction. -/
theorem glueOn_over_eq_left (N P : M.Submodule) (U V : C)
    (h : ∀ (Z : C) (_a : Z ⟶ U) (_b : Z ⟶ V),
      N.toSubmodule.obj (op Z) = P.toSubmodule.obj (op Z)) :
    (glueOn N P U V).over U = N.over U := by
  apply over_eq_of_obj_eq (glueOn N P U V) N U
  intro W i
  exact glueOn_obj_eq_left N P U V W i h

/-- The constructed gluing has exactly the second prescribed native restriction. -/
theorem glueOn_over_eq_right (N P : M.Submodule) (U V : C)
    (h : ∀ (Z : C) (_a : Z ⟶ U) (_b : Z ⟶ V),
      N.toSubmodule.obj (op Z) = P.toSubmodule.obj (op Z)) :
    (glueOn N P U V).over V = P.over V := by
  apply over_eq_of_obj_eq (glueOn N P U V) P V
  intro W i
  exact glueOn_obj_eq_right N P U V W i h

end SheafOfModules.Submodule
