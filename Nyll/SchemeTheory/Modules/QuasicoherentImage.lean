/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.ImageSubmodule
import Nyll.SchemeTheory.Modules.QuasicoherentKernelGlobal
import Nyll.SchemeTheory.Modules.QuasicoherentCokernel
import Nyll.SchemeTheory.Modules.QuasicoherentLocal
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Quasicoherence of native image subsheaves

The identity-action equivalence transports the actual kernel and cokernel
theorems for scheme modules to native sheaves. The native image is then
the actual kernel of the actual cokernel projection.
-/

noncomputable section

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace SheafOfModules

private instance schemeEquivalence_preservesZeroMorphisms (X : Scheme.{u}) :
    (Scheme.Modules.sheafOfModulesEquivalence X).functor.PreservesZeroMorphisms where
  map_zero _ _ := rfl

/-- Native categorical kernels of quasicoherent sheaves on schemes are quasicoherent. -/
theorem isQuasicoherent_kernel_native {X : Scheme.{u}}
    {M N : SheafOfModules.{u} X.ringCatSheaf}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) :
    (kernel f).IsQuasicoherent := by
  let E : X.Modules ≌ SheafOfModules.{u} X.ringCatSheaf :=
    Scheme.Modules.sheafOfModulesEquivalence X
  let f' : E.inverse.obj M ⟶ E.inverse.obj N := E.inverse.map f
  have : (E.inverse.obj M).IsQuasicoherent := inferInstanceAs M.IsQuasicoherent
  have : (E.inverse.obj N).IsQuasicoherent := inferInstanceAs N.IsQuasicoherent
  have h : (kernel f').IsQuasicoherent := Scheme.Modules.isQuasicoherent_kernel f'
  let e : E.functor.obj (kernel f') ≅ kernel f := PreservesKernel.iso E.functor f'
  exact (isQuasicoherent X.ringCatSheaf).prop_of_iso e h

/-- Native categorical cokernels of quasicoherent sheaves on schemes are quasicoherent. -/
theorem isQuasicoherent_cokernel_native {X : Scheme.{u}}
    {M N : SheafOfModules.{u} X.ringCatSheaf}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) :
    (cokernel f).IsQuasicoherent := by
  let E : X.Modules ≌ SheafOfModules.{u} X.ringCatSheaf :=
    Scheme.Modules.sheafOfModulesEquivalence X
  let f' : E.inverse.obj M ⟶ E.inverse.obj N := E.inverse.map f
  have : (E.inverse.obj M).IsQuasicoherent := inferInstanceAs M.IsQuasicoherent
  have : (E.inverse.obj N).IsQuasicoherent := inferInstanceAs N.IsQuasicoherent
  have h : (cokernel f').IsQuasicoherent := Scheme.Modules.isQuasicoherent_cokernel f'
  let e : E.functor.obj (cokernel f') ≅ cokernel f := PreservesCokernel.iso E.functor f'
  exact (isQuasicoherent X.ringCatSheaf).prop_of_iso e h

/-- The actual native image submodule of a map of quasicoherent sheaves is quasicoherent. -/
theorem isQuasicoherent_imageSubmodule {X : Scheme.{u}}
    {M N : SheafOfModules.{u} X.ringCatSheaf}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) :
    (imageSubmodule f).toSheafOfModules.IsQuasicoherent := by
  have : (cokernel f).IsQuasicoherent := isQuasicoherent_cokernel_native f
  have h : (kernel (cokernel.π f)).IsQuasicoherent :=
    isQuasicoherent_kernel_native (cokernel.π f)
  exact (isQuasicoherent X.ringCatSheaf).prop_of_iso (imageSubmoduleIso f).symm h

end SheafOfModules
