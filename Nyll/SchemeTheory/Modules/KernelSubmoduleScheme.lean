/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.KernelSubmodule
import Nyll.SchemeTheory.Modules.QuasicoherentLocal
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Actual kernel submodules on schemes

The native sectionwise kernel subsheaf is transported through the identity-action
equivalence with the category of scheme modules. The comparison with the actual
categorical kernel respects the inclusion into the original module.
-/

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

private instance sheafOfModulesEquivalence_functor_preservesZeroMorphisms
    (X : Scheme.{u}) :
    (sheafOfModulesEquivalence X).functor.PreservesZeroMorphisms where
  map_zero _ _ := rfl

/-- The native submodule of sections killed by a morphism of scheme modules. -/
def kernelSubmodule {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) :
    M.Submodule :=
  SheafOfModules.kernelSubmodule ((sheafOfModulesEquivalence X).functor.map φ)

/-- The actual module of the sectionwise kernel submodule is the image of the
categorical kernel under the identity-action native sheaf equivalence. -/
def kernelSubmoduleIso {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) :
    (kernelSubmodule φ).toSheafOfModules ≅
      (sheafOfModulesEquivalence X).functor.obj (kernel φ) :=
  SheafOfModules.kernelSubmoduleIso
      ((sheafOfModulesEquivalence X).functor.map φ) ≪≫
    (PreservesKernel.iso (sheafOfModulesEquivalence X).functor φ).symm

/-- The categorical-kernel comparison identifies its inclusion with the actual
inclusion of the pointwise kernel submodule. -/
theorem kernelSubmoduleIso_hom_ι {X : Scheme.{u}} {M N : X.Modules}
    (φ : M ⟶ N) :
    (kernelSubmoduleIso φ).hom ≫
      (sheafOfModulesEquivalence X).functor.map (kernel.ι φ) =
      (kernelSubmodule φ).ι := by
  change
    (SheafOfModules.kernelSubmoduleIso
      ((sheafOfModulesEquivalence X).functor.map φ) ≪≫
      (PreservesKernel.iso (sheafOfModulesEquivalence X).functor φ).symm).hom ≫
      (sheafOfModulesEquivalence X).functor.map (kernel.ι φ) =
      (kernelSubmodule φ).ι
  rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, PreservesKernel.iso_inv_ι,
    SheafOfModules.kernelSubmoduleIso_hom_ι]
  rfl

end AlgebraicGeometry.Scheme.Modules
