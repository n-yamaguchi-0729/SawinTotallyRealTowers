/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Actual kernel subsheaves of modules

The kernel is the native submodule consisting, on each object, of the
sections killed by the actual component morphism. Membership is local by
separatedness of the target sheaf. Evaluation identifies its kernel fork
with the ordinary linear-map kernel, giving the actual categorical comparison.
-/

noncomputable section

universe v u

open CategoryTheory Limits Opposite

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{u}}

/-- The actual sectionwise kernel submodule of a morphism of presheaves
of modules. Its restriction compatibility is the naturality of the morphism. -/
def kernelSubmodule {M N : PresheafOfModules.{u} R} (φ : M ⟶ N) : M.Submodule where
  obj X := (φ.app X).hom.ker
  map {X Y} i := by
    intro x hx
    change (φ.app X).hom x = 0 at hx
    change (φ.app Y).hom (M.map i x) = 0
    exact (PresheafOfModules.naturality_apply φ i x).trans
      ((congrArg (fun y : N.obj X => N.map i y) hx).trans
        (map_zero (N.map i).hom))

end PresheafOfModules

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}

/-- The native kernel subsheaf, constructed from local vanishing of
the actual target section. -/
def kernelSubmodule {M N : SheafOfModules.{u} R} (φ : M ⟶ N) : M.Submodule where
  toSubmodule := PresheafOfModules.kernelSubmodule φ.val
  isSheaf {X} s hs := by
    have hN : Presieve.IsSheaf J
        (N.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{u}) := by
      rw [← isSheaf_iff_isSheaf_of_type]
      exact GrothendieckTopology.HasSheafCompose.isSheaf _ N.isSheaf
    apply LinearMap.mem_ker.mpr
    apply (hN _ hs).isSeparatedFor.ext
    intro V i hi
    change (φ.val.app (op V)).hom (M.val.map i.op s) = 0 at hi
    change N.val.map i.op ((φ.val.app X).hom s) = N.val.map i.op (0 : N.val.obj X)
    exact (PresheafOfModules.naturality_apply φ.val i.op s).symm.trans
      (hi.trans (map_zero (N.val.map i.op).hom).symm)

theorem kernelSubmodule_ι_comp
    {M N : SheafOfModules.{u} R} (φ : M ⟶ N) :
    (kernelSubmodule φ).ι ≫ φ = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  exact s.property

/-- The inclusion of the actual kernel subsheaf is a kernel fork. -/
def kernelSubmoduleIsLimit
    {M N : SheafOfModules.{u} R} (φ : M ⟶ N) :
    IsLimit (KernelFork.ofι (kernelSubmodule φ).ι (kernelSubmodule_ι_comp φ)) := by
  apply isLimitOfReflects (SheafOfModules.forget R)
  apply PresheafOfModules.evaluationJointlyReflectsLimits
  intro X
  let E : SheafOfModules.{u} R ⥤ ModuleCat.{u} (R.obj.obj X) :=
    SheafOfModules.forget R ⋙ PresheafOfModules.evaluation R.obj X
  change IsLimit (E.mapCone
    (KernelFork.ofι (kernelSubmodule φ).ι (kernelSubmodule_ι_comp φ)))
  refine (isLimitMapConeForkEquiv' E (kernelSubmodule_ι_comp φ)).symm ?_
  exact ModuleCat.kernelIsLimit (φ.val.app X)

/-- The native sectionwise kernel subsheaf is the actual categorical kernel. -/
def kernelSubmoduleIso
    {M N : SheafOfModules.{u} R} (φ : M ⟶ N) :
    (kernelSubmodule φ).toSheafOfModules ≅ kernel φ :=
  (kernelSubmoduleIsLimit φ).conePointUniqueUpToIso (limit.isLimit (parallelPair φ 0))

theorem kernelSubmoduleIso_hom_ι
    {M N : SheafOfModules.{u} R} (φ : M ⟶ N) :
    (kernelSubmoduleIso φ).hom ≫ kernel.ι φ = (kernelSubmodule φ).ι :=
  IsLimit.conePointUniqueUpToIso_hom_comp
    (kernelSubmoduleIsLimit φ) (limit.isLimit (parallelPair φ 0)) WalkingParallelPair.zero

end SheafOfModules
