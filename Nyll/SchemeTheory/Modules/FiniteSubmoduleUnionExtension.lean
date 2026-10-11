/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.QuasicoherentSubmoduleOverExtension
import Nyll.SchemeTheory.Modules.SubmoduleGluingUnion
import Nyll.SchemeTheory.Modules.SubmoduleGluingQuasicoherent
import Nyll.SchemeTheory.Modules.SubmoduleOverEquality
import Nyll.SchemeTheory.Modules.FiniteTypeLocality
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Global representatives of finite submodules glued on a union

The two actual submodules are glued on the union of their prescribed
opens. The native quasicoherent extension construction then produces a
global representative with both exact restrictions and finite type on
the union. Global finite type is not asserted outside that union.
-/

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace
open SheafOfModules.Submodule

namespace AlgebraicGeometry.Scheme.Modules

/-- Glue the prescribed finite restrictions on two compact opens, and extend
the actual glued submodule to a global quasicoherent representative. -/
theorem exists_finiteType_union_extension {X : Scheme.{u}} [QuasiSeparatedSpace X]
    (F : X.Modules) [F.IsQuasicoherent] (N P : F.Submodule)
    [N.toSheafOfModules.IsQuasicoherent] [P.toSheafOfModules.IsQuasicoherent]
    (U V : X.Opens) (hU : IsCompact (U : Set X)) (hV : IsCompact (V : Set X))
    (h : ∀ (Z : X.Opens) (_a : Z ⟶ U) (_b : Z ⟶ V),
      N.toSubmodule.obj (op Z) = P.toSubmodule.obj (op Z))
    (hNft : (N.toSheafOfModules.over U).IsFiniteType)
    (hPft : (P.toSheafOfModules.over V).IsFiniteType) :
    ∃ L : F.Submodule, L.toSheafOfModules.IsQuasicoherent ∧
      (L.toSheafOfModules.over (U ⊔ V)).IsFiniteType ∧
      L.over U = N.over U ∧ L.over V = P.over V := by
  let K : F.Submodule := glueOn N P U V
  have hKqcOver : (K.toSheafOfModules.over (U ⊔ V)).IsQuasicoherent :=
    isQuasicoherent_glueOn_over_sup N P U V h
      (SheafOfModules.isQuasicoherent_over N.toSheafOfModules U)
      (SheafOfModules.isQuasicoherent_over P.toSheafOfModules V)
  have hKftOver : (K.toSheafOfModules.over (U ⊔ V)).IsFiniteType :=
    isFiniteType_glueOn_over_sup N P U V h hNft hPft
  have hKqc : (K.over (U ⊔ V)).toSheafOfModules.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (X.ringCatSheaf.over (U ⊔ V))).prop_of_iso
      (overSheafIso K (U ⊔ V)).symm hKqcOver
  have hUnion : IsCompact ((U ⊔ V : X.Opens) : Set X) := hU.union hV
  have : CompactSpace (U ⊔ V : X.Opens) := isCompact_iff_compactSpace.mp hUnion
  have : QuasiCompact (U ⊔ V : X.Opens).ι := inferInstance
  let L : F.Submodule := extendQuasicoherentSubmoduleOver F (U ⊔ V) (K.over (U ⊔ V))
  have hLqc : L.toSheafOfModules.IsQuasicoherent :=
    isQuasicoherent_extendQuasicoherentSubmoduleOver F (U ⊔ V) (K.over (U ⊔ V)) hKqc
  have hLover : L.over (U ⊔ V) = K.over (U ⊔ V) :=
    extendQuasicoherentSubmoduleOver_over F (U ⊔ V) (K.over (U ⊔ V))
  have hLft : (L.over (U ⊔ V)).toSheafOfModules.IsFiniteType := by
    rw [hLover]
    exact SheafOfModules.IsFiniteType.of_iso
      (C := Over (U ⊔ V)) (R := X.ringCatSheaf.over (U ⊔ V))
      (M := K.toSheafOfModules.over (U ⊔ V))
      (N := (K.over (U ⊔ V)).toSheafOfModules)
      (overSheafIso K (U ⊔ V)).symm hKftOver
  have hLftOver : (L.toSheafOfModules.over (U ⊔ V)).IsFiniteType :=
    SheafOfModules.IsFiniteType.of_iso
      (C := Over (U ⊔ V)) (R := X.ringCatSheaf.over (U ⊔ V))
      (M := (L.over (U ⊔ V)).toSheafOfModules)
      (N := L.toSheafOfModules.over (U ⊔ V))
      (overSheafIso L (U ⊔ V)) hLft
  refine ⟨L, hLqc, hLftOver, ?_, ?_⟩
  · exact (over_eq_of_over_eq hLover (homOfLE le_sup_left)).trans
      (glueOn_over_eq_left N P U V h)
  · exact (over_eq_of_over_eq hLover (homOfLE le_sup_right)).trans
      (glueOn_over_eq_right N P U V h)

end AlgebraicGeometry.Scheme.Modules
