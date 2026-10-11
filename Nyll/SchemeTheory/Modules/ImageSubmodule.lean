/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.KernelSubmodule
import Nyll.SchemeTheory.Modules.SubmoduleEmbeddedIso
import Nyll.SchemeTheory.Modules.FiniteTypeQuotient
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Actual image subsheaves

The image is the native kernel submodule of the actual cokernel projection.
Its comparison with the abelian image gives an epimorphic corestriction,
and the categorical image universal property gives its least-submodule property.
-/

noncomputable section

universe u v

open CategoryTheory Limits

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The actual image subsheaf, including its local membership condition. -/
def imageSubmodule {M N : SheafOfModules.{u} R} (f : M ⟶ N) : N.Submodule :=
  kernelSubmodule (cokernel.π f)

/-- The actual image subsheaf agrees with the abelian image. -/
def imageSubmoduleIso {M N : SheafOfModules.{u} R} (f : M ⟶ N) :
    (imageSubmodule f).toSheafOfModules ≅ Abelian.image f :=
  kernelSubmoduleIso (cokernel.π f)

/-- The abelian-image comparison respects the actual inclusion into the target. -/
theorem imageSubmoduleIso_hom_ι {M N : SheafOfModules.{u} R} (f : M ⟶ N) :
    (imageSubmoduleIso f).hom ≫ Abelian.image.ι f = (imageSubmodule f).ι :=
  kernelSubmoduleIso_hom_ι (cokernel.π f)

/-- The actual epimorphism from the source onto its native image subsheaf. -/
def toImageSubmodule {M N : SheafOfModules.{u} R} (f : M ⟶ N) :
    M ⟶ (imageSubmodule f).toSheafOfModules :=
  Abelian.factorThruImage f ≫ (imageSubmoduleIso f).inv

instance {M N : SheafOfModules.{u} R} (f : M ⟶ N) :
    Epi (toImageSubmodule f) :=
  inferInstanceAs (Epi (Abelian.factorThruImage f ≫ (imageSubmoduleIso f).inv))

/-- The corestriction retains the original map into the ambient sheaf. -/
theorem toImageSubmodule_ι {M N : SheafOfModules.{u} R} (f : M ⟶ N) :
    toImageSubmodule f ≫ (imageSubmodule f).ι = f := by
  rw [← imageSubmoduleIso_hom_ι, toImageSubmodule, Category.assoc,
    Iso.inv_hom_id_assoc, Abelian.image.fac]

/-- Every actual factorization through a native submodule contains the image. -/
theorem imageSubmodule_le {M N : SheafOfModules.{u} R} (f : M ⟶ N)
    (P : N.Submodule) (g : M ⟶ P.toSheafOfModules) (hg : g ≫ P.ι = f) :
    imageSubmodule f ≤ P := by
  let F : MonoFactorisation f := { I := P.toSheafOfModules, m := P.ι, e := g, fac := hg }
  let e : (imageSubmodule f).toSheafOfModules ≅ Limits.image f :=
    imageSubmoduleIso f ≪≫ Abelian.imageIsoImage f
  apply Submodule.le_of_hom_ι (imageSubmodule f) P (e.hom ≫ Limits.image.lift F)
  rw [Category.assoc, Limits.image.lift_fac, Iso.trans_hom, Category.assoc,
    Abelian.imageIsoImage_hom_comp_image_ι, imageSubmoduleIso_hom_ι]

variable [HasBinaryProducts C]
  [∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- An actual image of a finite-type sheaf is finite type. -/
theorem isFiniteType_imageSubmodule {M N : SheafOfModules.{u} R}
    (f : M ⟶ N) [M.IsFiniteType] : (imageSubmodule f).toSheafOfModules.IsFiniteType :=
  isFiniteType_of_epi (toImageSubmodule f)

end SheafOfModules
