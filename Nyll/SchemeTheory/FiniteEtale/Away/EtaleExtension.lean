/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.RingHom.Etale

/-!
# Boundary Away maps through an etale extension

The boundary Away property is stable under a genuinely etale extension of
the target.  This elementary map-level statement is useful after a Tag/ETag
comparison has produced the primitive Away map on one local factor and a
retained unit factor supplies an etale algebra over that same factor.

Unlike the formally-etale localization bridge, no module-finiteness or
Noetherian hypothesis is needed: after localizing both targets at the same
source element, the second map is etale by localization and restriction of
scalars, and the two literal Away maps compose.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe uA uC uD

/-- A literal boundary Away map remains etale after a genuinely etale target
extension.

This is deliberately stated for the actual composite algebra map.  It does
not replace either target by an abstractly equivalent algebra, and it does
not require the intermediate or final algebra to be finite over the original
base. -/
theorem localization_awayMap_etale_of_etale_extension
    {A : Type uA} {C : Type uC} {D : Type uD}
    [CommRing A] [CommRing C] [CommRing D]
    [Algebra A C] [Algebra C D] [Algebra A D]
    [IsScalarTower A C D]
    [Algebra.Etale C D]
    (f : A)
    (hAway : (Localization.awayMap (algebraMap A C) f).Etale) :
    (Localization.awayMap (algebraMap A D) f).Etale := by
  let fC : C := algebraMap A C f
  let fD : D := algebraMap A D f
  let S := Localization.Away f
  let T := Localization.Away fC
  let U := Localization.Away fD
  let mapST : S →+* T :=
    Localization.awayMap (algebraMap A C) f
  let mapCDU : C →+* U := algebraMap C U
  have hfCUnit : IsUnit (mapCDU fC) := by
    change IsUnit
      (algebraMap D U (algebraMap C D (algebraMap A C f)))
    rw [← IsScalarTower.algebraMap_apply A C D f]
    exact IsLocalization.Away.algebraMap_isUnit fD
  let mapTU : T →+* U :=
    Localization.awayLift mapCDU fC hfCUnit
  let mapSU : S →+* U :=
    Localization.awayMap (algebraMap A D) f
  let : Algebra S T := mapST.toAlgebra
  let : Algebra T U := mapTU.toAlgebra
  let : IsScalarTower C T U :=
    IsScalarTower.of_algebraMap_eq fun c ↦ by
      change mapCDU c = mapTU (algebraMap C T c)
      simp [mapTU]
  have hcomp : mapTU.comp mapST = mapSU := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    ext a
    simp only [RingHom.comp_apply]
    calc
      mapTU (mapST (algebraMap A S a)) =
          mapTU (algebraMap C T (algebraMap A C a)) := by
        rw [show mapST (algebraMap A S a) =
            algebraMap C T (algebraMap A C a) by
          simp [mapST, S, T, fC, IsLocalization.Away.map]]
      _ = mapCDU (algebraMap A C a) := by simp [mapTU]
      _ = algebraMap D U
          (algebraMap C D (algebraMap A C a)) := rfl
      _ = algebraMap D U (algebraMap A D a) := by
        rw [IsScalarTower.algebraMap_apply A C D a]
      _ = mapSU (algebraMap A S a) := by
        simp [mapSU, S, U, fD, IsLocalization.Away.map]
  let : Algebra S U := mapSU.toAlgebra
  let : IsScalarTower S T U :=
    IsScalarTower.of_algebraMap_eq fun x ↦
      (DFunLike.congr_fun hcomp x).symm
  let : Algebra.Etale S T := hAway.toAlgebra
  let : Algebra.Etale C T :=
    Algebra.Etale.of_isLocalizationAway fC
  let : Algebra.Etale C U := inferInstance
  let : Algebra.Etale T U :=
    Algebra.Etale.of_restrictScalars C T U
  exact (show Algebra.Etale S U from Algebra.Etale.comp S T U)

end EtaleFundamentalGroups

end
