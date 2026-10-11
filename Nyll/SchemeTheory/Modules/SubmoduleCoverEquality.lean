/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.SubmoduleGluingQuasicoherent
import Mathlib.CategoryTheory.Sites.Spaces

/-!
# Equality of actual submodules from an open cover

Containment of the actual restricted submodules is local on an open
cover. The proof uses the native membership locality axiom on the
intersections of each test open with the cover. This turns the finite
principal-open equalities of affine extraction into equality on their
quasi-compact union.
-/

noncomputable section

universe u v w t

open CategoryTheory Opposite TopologicalSpace

namespace SheafOfModules.Submodule

variable {X : Type u} [TopologicalSpace X]
  {R : Sheaf (Opens.grothendieckTopology X) RingCat.{v}}
  {M : SheafOfModules.{w} R}

/-- Native submodule containment on a union follows from containment
on every member of its actual open cover. -/
theorem le_over_of_iSup_eq (N P : M.Submodule) (U : Opens X)
    {ι : Type t} (V : ι → Opens X) (hCover : (⨆ i, V i) = U)
    (h : ∀ i : ι, N.over (V i) ≤ P.over (V i)) : N.over U ≤ P.over U := by
  intro A s hs
  change s ∈ P.toSubmodule.obj (op A.unop.left)
  change s ∈ N.toSubmodule.obj (op A.unop.left) at hs
  apply P.isSheaf (X := op A.unop.left) s
  apply (Opens.mem_grothendieckTopology (T := X)).mpr
  intro x hx
  have hxCover : x ∈ ⨆ i, V i := by
    rw [hCover]
    exact leOfHom A.unop.hom hx
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hxCover
  let W : Opens X := A.unop.left ⊓ V i
  let a : W ⟶ A.unop.left := homOfLE inf_le_left
  let b : W ⟶ V i := homOfLE inf_le_right
  refine ⟨W, a, ?_, ⟨hx, hi⟩⟩
  change M.val.map a.op s ∈ P.toSubmodule.obj (op W)
  exact h i (op (Over.mk b)) (N.toSubmodule.map_mem a.op hs)

/-- Literal equality of native restrictions can be checked on any
actual open cover of the given open. -/
theorem over_eq_of_iSup_eq (N P : M.Submodule) (U : Opens X)
    {ι : Type t} (V : ι → Opens X) (hCover : (⨆ i, V i) = U)
    (h : ∀ i : ι, N.over (V i) = P.over (V i)) : N.over U = P.over U := by
  apply le_antisymm
  · exact le_over_of_iSup_eq N P U V hCover (fun i => (h i).le)
  · exact le_over_of_iSup_eq P N U V hCover (fun i => (h i).ge)

end SheafOfModules.Submodule
