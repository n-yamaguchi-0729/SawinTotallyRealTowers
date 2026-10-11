/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.DirectImageAlgebra
import Nyll.SchemeTheory.Modules.QuasicoherentPushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Quasicoherence of the actual affine direct-image algebra

The unit sheaf is the one-generator free sheaf. Affine pushforward preserves
its quasicoherence, and the actual direct-image algebra/module comparison
identifies the resulting module with the algebra's underlying module.
-/

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- The actual structure-sheaf unit module is quasicoherent, by its
isomorphism with the one-generator free sheaf. -/
theorem Modules.isQuasicoherent_unit (T : Scheme.{u}) :
    (show T.Modules from SheafOfModules.unit T.ringCatSheaf).IsQuasicoherent := by
  let M : T.Modules := SheafOfModules.free (R := T.ringCatSheaf) PUnit.{u + 1}
  have hM : M.IsQuasicoherent := inferInstance
  let e : M ≅ SheafOfModules.unit T.ringCatSheaf :=
    coproductUniqueIso (fun _ : PUnit.{u + 1} => SheafOfModules.unit T.ringCatSheaf)
  exact (SheafOfModules.isQuasicoherent T.ringCatSheaf).prop_of_iso e hM

namespace DirectImageAlgebra

/-- An affine morphism's actual direct-image ring algebra has a
quasicoherent underlying module. No direct-image QC premise is required. -/
theorem isQuasicoherent_underlyingModule {T X : Scheme.{u}}
    (g : T ⟶ X) [IsAffineHom g] :
    (RelativeSpec.underlyingModule (structureMap g)).IsQuasicoherent := by
  have : (show T.Modules from SheafOfModules.unit T.ringCatSheaf).IsQuasicoherent :=
    Modules.isQuasicoherent_unit T
  have hPushforward : ((Modules.pushforward g).obj
      (SheafOfModules.unit T.ringCatSheaf)).IsQuasicoherent :=
    Modules.isQuasicoherent_pushforward_of_isAffineHom g (SheafOfModules.unit T.ringCatSheaf)
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (underlyingModuleIso g).symm hPushforward

end DirectImageAlgebra

end AlgebraicGeometry.Scheme
