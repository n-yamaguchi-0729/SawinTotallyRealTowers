/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
import Mathlib.CategoryTheory.Sites.Grothendieck

/-!
# Gluing actual submodules from local membership conditions

The construction imposes membership in a given native submodule only on
objects mapping to a specified object of the site. Intersecting two such
submodules glues their prescribed local values when those values agree on
the overlap. This constructs the sheaf itself, rather than postulating a
gluing object or an identification with one.

For an open-cover induction in Stacks Tag 01PF, the input submodules are
the actual extensions supplied by Tag 01PE. The overlap equality still
has to be proved using their embedded restriction identifications.
-/

noncomputable section

universe v v₁ u₁ u

open CategoryTheory Opposite

namespace SheafOfModules.Submodule

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}} {M : SheafOfModules.{v} R}

/-- Impose membership in `N` only after restriction to objects mapping to `U`.
On the site of opens this is the largest submodule agreeing with `N` on `U`. -/
def imposeOn (N : M.Submodule) (U : C) : M.Submodule where
  toSubmodule :=
    { obj X :=
        { carrier := {s | ∀ (V : C) (i : V ⟶ X.unop) (_j : V ⟶ U),
            M.val.map i.op s ∈ N.toSubmodule.obj (op V)}
          zero_mem' := by
            intro V i j
            rw [map_zero]
            exact (N.toSubmodule.obj (op V)).zero_mem
          add_mem' := by
            intro s t hs ht V i j
            rw [map_add]
            exact (N.toSubmodule.obj (op V)).add_mem (hs V i j) (ht V i j)
          smul_mem' := by
            intro r s hs V i j
            rw [M.val.map_smul]
            exact (N.toSubmodule.obj (op V)).smul_mem _ (hs V i j) }
      map := by
        intro X Y f s hs V i j
        change M.val.map i.op (M.val.map f s) ∈ N.toSubmodule.obj (op V)
        have h := hs V (i ≫ f.unop) j
        rw [op_comp, M.val.map_comp_apply] at h
        exact h }
  isSheaf := by
    intro X s hs V i j
    apply N.isSheaf (X := op V) (M.val.map i.op s)
    apply J.superset_covering _ (J.pullback_stable i hs)
    intro W f hf
    change ∀ (Z : C) (k : Z ⟶ W) (l : Z ⟶ U),
      M.val.map k.op (M.val.map (f ≫ i).op s) ∈ N.toSubmodule.obj (op Z) at hf
    have h := hf W (𝟙 W) (f ≫ j)
    change M.val.map f.op (M.val.map i.op s) ∈ N.toSubmodule.obj (op W)
    rw [op_id, ← M.val.map_comp_apply, op_comp,
      Category.comp_id (i.op ≫ f.op), M.val.map_comp_apply] at h
    exact h

/-- The original submodule satisfies all of its local membership conditions. -/
theorem le_imposeOn (N : M.Submodule) (U : C) : N ≤ imposeOn N U := by
  intro X s hs V i j
  exact N.toSubmodule.map_mem i.op hs

/-- Below `U`, imposing the local condition recovers the literal section submodule. -/
theorem imposeOn_obj_eq (N : M.Submodule) (U V : C) (i : V ⟶ U) :
    (imposeOn N U).toSubmodule.obj (op V) = N.toSubmodule.obj (op V) := by
  apply le_antisymm
  · intro s hs
    have h := hs V (𝟙 V) i
    change M.val.presheaf.map (𝟙 (op V)) s ∈ N.toSubmodule.obj (op V) at h
    rw [M.val.presheaf.map_id] at h
    exact h
  · exact le_imposeOn N U (op V)

/-- Actual gluing of two prescribed submodules, by their local section conditions. -/
def glueOn (N P : M.Submodule) (U V : C) : M.Submodule :=
  imposeOn N U ⊓ imposeOn P V

/-- Agreement on the overlap gives the exact first local section submodule
of the constructed gluing. -/
theorem glueOn_obj_eq_left (N P : M.Submodule) (U V W : C) (i : W ⟶ U)
    (h : ∀ (Z : C) (_a : Z ⟶ U) (_b : Z ⟶ V),
      N.toSubmodule.obj (op Z) = P.toSubmodule.obj (op Z)) :
    (glueOn N P U V).toSubmodule.obj (op W) = N.toSubmodule.obj (op W) := by
  apply le_antisymm
  · intro s hs
    have hleft : s ∈ (imposeOn N U).toSubmodule.obj (op W) := hs.1
    rw [imposeOn_obj_eq N U W i] at hleft
    exact hleft
  · intro s hs
    refine ⟨le_imposeOn N U (op W) hs, ?_⟩
    intro Z a b
    rw [← h Z (a ≫ i) b]
    exact N.toSubmodule.map_mem a.op hs

/-- Agreement on the overlap gives the exact second local section submodule
of the constructed gluing. -/
theorem glueOn_obj_eq_right (N P : M.Submodule) (U V W : C) (i : W ⟶ V)
    (h : ∀ (Z : C) (_a : Z ⟶ U) (_b : Z ⟶ V),
      N.toSubmodule.obj (op Z) = P.toSubmodule.obj (op Z)) :
    (glueOn N P U V).toSubmodule.obj (op W) = P.toSubmodule.obj (op W) := by
  have hswap : glueOn N P U V = glueOn P N V U :=
    inf_comm (imposeOn N U) (imposeOn P V)
  rw [hswap]
  exact glueOn_obj_eq_left P N V U W i (fun Z a b => (h Z b a).symm)

end SheafOfModules.Submodule
