/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.SubmoduleGluing
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.Over

/-!
# Quasicoherence of the actual gluing of submodules

Restriction of a native submodule to the slice site is computed on its
actual section submodules. The local section equalities of `glueOn` thus
identify its restrictions with the two given quasicoherent modules. The
native cover-locality theorem supplies quasicoherence of the glued object.
-/

noncomputable section

universe v v₁ u₁ u

open CategoryTheory Opposite

namespace SheafOfModules.Submodule

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}} {M : SheafOfModules.{v} R}

/-- Restrict an actual submodule to the slice site. -/
def over (N : M.Submodule) (U : C) : (M.over U).Submodule where
  toSubmodule :=
    { obj X := N.toSubmodule.obj (op X.unop.left)
      map f := N.toSubmodule.map f.unop.left.op }
  isSheaf := by
    intro X s hs
    apply N.isSheaf s
    apply J.superset_covering _ ((J.mem_over_iff _).mp hs)
    intro V i hi
    exact (Sieve.overEquiv_iff _ i).mp hi

/-- The module of the restricted native submodule is the restriction of its module. -/
def overSheafIso (N : M.Submodule) (U : C) :
    (N.over U).toSheafOfModules ≅ N.toSheafOfModules.over U :=
  (SheafOfModules.fullyFaithfulForget (R.over U)).preimageIso
    (PresheafOfModules.isoMk (fun _ => Iso.refl _) (fun {_ _} _ => rfl))

/-- The comparison of the actual restricted modules respects their embeddings. -/
theorem overSheafIso_hom_ι (N : M.Submodule) (U : C) :
    (overSheafIso N U).hom ≫ N.ι.over U = (N.over U).ι := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  rfl

/-- Local section equalities give equality of the actual restricted submodules. -/
theorem over_eq_of_obj_eq (N P : M.Submodule) (U : C)
    (h : ∀ (V : C) (_i : V ⟶ U),
      N.toSubmodule.obj (op V) = P.toSubmodule.obj (op V)) :
    N.over U = P.over U := by
  apply SheafOfModules.Submodule.ext
  apply PresheafOfModules.Submodule.ext
  intro V
  exact h V.unop.left V.unop.hom

/-- The two local sheaves of a glued submodule are the actual prescribed sheaves. -/
def glueOnOverIsoLeft (N P : M.Submodule) (U V : C)
    (h : ∀ (Z : C) (_a : Z ⟶ U) (_b : Z ⟶ V),
      N.toSubmodule.obj (op Z) = P.toSubmodule.obj (op Z)) :
    (glueOn N P U V).toSheafOfModules.over U ≅ N.toSheafOfModules.over U :=
  (overSheafIso (glueOn N P U V) U).symm ≪≫
    eqToIso (congrArg SheafOfModules.Submodule.toSheafOfModules
      (over_eq_of_obj_eq (glueOn N P U V) N U
        (fun W i => glueOn_obj_eq_left N P U V W i h))) ≪≫
    overSheafIso N U

/-- The second local sheaf of a glued submodule is its prescribed actual sheaf. -/
def glueOnOverIsoRight (N P : M.Submodule) (U V : C)
    (h : ∀ (Z : C) (_a : Z ⟶ U) (_b : Z ⟶ V),
      N.toSubmodule.obj (op Z) = P.toSubmodule.obj (op Z)) :
    (glueOn N P U V).toSheafOfModules.over V ≅ P.toSheafOfModules.over V :=
  (overSheafIso (glueOn N P U V) V).symm ≪≫
    eqToIso (congrArg SheafOfModules.Submodule.toSheafOfModules
      (over_eq_of_obj_eq (glueOn N P U V) P V
        (fun W i => glueOn_obj_eq_right N P U V W i h))) ≪≫
    overSheafIso P V

section Quasicoherent

variable [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X Y, HasSheafify ((J.over X).over Y) AddCommGrpCat.{u}]
  [∀ X Y, ((J.over X).over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The actual gluing is quasicoherent if its two prescribed local modules
are quasicoherent and the two objects cover the site. -/
theorem isQuasicoherent_glueOn {M' : SheafOfModules.{u} R}
    (N P : M'.Submodule) (U V : C)
    (hCover : J.CoversTop (fun b : ULift.{u} Bool => cond b.down U V))
    (h : ∀ (Z : C) (_a : Z ⟶ U) (_b : Z ⟶ V),
      N.toSubmodule.obj (op Z) = P.toSubmodule.obj (op Z))
    (hN : (N.toSheafOfModules.over U).IsQuasicoherent)
    (hP : (P.toSheafOfModules.over V).IsQuasicoherent) :
    (glueOn N P U V).toSheafOfModules.IsQuasicoherent := by
  have hLocal : ∀ b : ULift.{u} Bool,
      ((glueOn N P U V).toSheafOfModules.over (cond b.down U V)).IsQuasicoherent := by
    intro b
    rcases b with ⟨b⟩
    cases b
    · exact (SheafOfModules.isQuasicoherent (R.over V)).prop_of_iso
        (glueOnOverIsoRight N P U V h).symm hP
    · exact (SheafOfModules.isQuasicoherent (R.over U)).prop_of_iso
        (glueOnOverIsoLeft N P U V h).symm hN
  exact SheafOfModules.IsQuasicoherent.of_coversTop
    (glueOn N P U V).toSheafOfModules
    (fun b : ULift.{u} Bool => cond b.down U V) hCover

end Quasicoherent

end SheafOfModules.Submodule
