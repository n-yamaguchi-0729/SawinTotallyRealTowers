/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.FiniteTypeIteratedSlice
import Nyll.SchemeTheory.Modules.FiniteTypeRestriction
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Finite type on subopens

Restriction to a smaller open is obtained within the larger slice site,
then transported by the actual equivalence of iterated slice sites.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace SheafOfModules

/-- The iterated restriction has finite type when the direct restriction does. -/
theorem IsFiniteType.iterated_over {X : Scheme.{u}}
    (M : SheafOfModules.{u} X.ringCatSheaf) {U V : X.Opens}
    (hUV : U ≤ V) (hM : (M.over U).IsFiniteType) :
    ((M.over V).over (Over.mk (homOfLE hUV))).IsFiniteType :=
  IsFiniteType.iteratedSlice_forward M (Over.mk (homOfLE hUV)) hM

/-- Finite type on an open is inherited by every smaller open. -/
theorem IsFiniteType.over_of_le {X : Scheme.{u}}
    (M : SheafOfModules.{u} X.ringCatSheaf) {U V : X.Opens}
    (hUV : U ≤ V) (hM : (M.over V).IsFiniteType) : (M.over U).IsFiniteType :=
  IsFiniteType.iteratedSlice_backward M (Over.mk (homOfLE hUV))
    (IsFiniteType.over (M.over V) (Over.mk (homOfLE hUV)) hM)

/-- The iterated restriction is quasicoherent when the direct restriction is. -/
theorem isQuasicoherent_iterated_over {X : Scheme.{u}}
    (M : SheafOfModules.{u} X.ringCatSheaf) {U V : X.Opens}
    (hUV : U ≤ V) (hM : (M.over U).IsQuasicoherent) :
    ((M.over V).over (Over.mk (homOfLE hUV))).IsQuasicoherent :=
  isQuasicoherent_iteratedSlice_forward M (Over.mk (homOfLE hUV)) hM

end SheafOfModules
