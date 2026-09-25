/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Global.MaximalEverywhereUnramifiedProPGroup

set_option autoImplicit false
/-!
# Arithmetic fields attached to open normal quotients

An open normal quotient of the maximal everywhere-unramified pro-`p`
Galois group is realized by the Galois group of a concrete finite
everywhere-unramified `p`-extension.  This is the finite-stage arithmetic
bridge used before introducing any cohomological local--global map.
-/

open scoped NumberField

noncomputable section

universe u

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.Martinet
open ProCGroups

variable (F : Type u) [Field F] [NumberField F]
variable (p : ℕ) [Fact p.Prime]

private noncomputable def openNormalClosedSubgroup
    (U : OpenNormalSubgroup
      (MaxEverywhereUnramifiedProPGaloisGroup F p)) :
    ClosedSubgroup (MaxEverywhereUnramifiedProPGaloisGroup F p) :=
  ⟨(U : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F p)),
    ProCGroups.openNormalSubgroup_isClosed U⟩

private noncomputable def openNormalFixedFieldInMaximal
    (U : OpenNormalSubgroup
      (MaxEverywhereUnramifiedProPGaloisGroup F p)) :
    IntermediateField F (maximalEverywhereUnramifiedProP F p) :=
  IntermediateField.fixedField
    (openNormalClosedSubgroup F p U :
      Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F p))

/-- The fixed field of an open normal subgroup, transported from the maximal
compositum into the chosen algebraic closure. -/
noncomputable def openNormalFixedField
    (U : OpenNormalSubgroup
      (MaxEverywhereUnramifiedProPGaloisGroup F p)) :
    IntermediateField F (AlgebraicClosure F) :=
  IntermediateField.lift (openNormalFixedFieldInMaximal F p U)

/-- For odd `p`, the fixed field of an open normal subgroup is a bundled
finite Galois everywhere-unramified `p`-extension. -/
noncomputable def openNormalArithmeticStage
    (hpOdd : Odd p)
    (U : OpenNormalSubgroup
      (MaxEverywhereUnramifiedProPGaloisGroup F p)) :
    FiniteEverywhereUnramifiedProPExtension F p := by
  let Uc : ClosedSubgroup
      (MaxEverywhereUnramifiedProPGaloisGroup F p) :=
    ⟨(U : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F p)),
      ProCGroups.openNormalSubgroup_isClosed U⟩
  let L := openNormalFixedFieldInMaximal F p U
  have hfix :
      L.fixingSubgroup =
        (Uc : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F p)) := by
    dsimp only [L, openNormalFixedFieldInMaximal,
      openNormalClosedSubgroup, Uc]
    exact InfiniteGalois.fixingSubgroup_fixedField Uc
  have hUcNormal : Subgroup.Normal
      (G := maximalEverywhereUnramifiedProP F p ≃ₐ[F]
        maximalEverywhereUnramifiedProP F p) Uc.toSubgroup :=
    U.isNormal'
  let : Uc.toSubgroup.Normal := hUcNormal
  let : FiniteDimensional F L :=
    (InfiniteGalois.isOpen_iff_finite L).1 (by
      rw [hfix]
      exact U.toOpenSubgroup.isOpen)
  let : IsGalois F L :=
    (InfiniteGalois.normal_iff_isGalois L).1 (by
      rw [hfix]
      exact hUcNormal)
  have hFiniteLift : FiniteDimensional F (IntermediateField.lift L) :=
    (IntermediateField.liftAlgEquiv L).toLinearEquiv.finiteDimensional
  let : FiniteDimensional F (IntermediateField.lift L) := hFiniteLift
  have hGaloisLift : IsGalois F (IntermediateField.lift L) :=
    IsGalois.of_algEquiv (IntermediateField.liftAlgEquiv L)
  let : IsGalois F (IntermediateField.lift L) := hGaloisLift
  have hNumberLift : NumberField (IntermediateField.lift L) :=
    NumberField.of_module_finite F (IntermediateField.lift L)
  let : NumberField (IntermediateField.lift L) := hNumberLift
  have hQuotientClass :
      FiniteGroupClass.pGroup p
        (MaxEverywhereUnramifiedProPGaloisGroup F p ⧸
          (U : Subgroup
            (MaxEverywhereUnramifiedProPGaloisGroup F p))) :=
    (maxEverywhereUnramifiedProPGaloisGroup_hasPGroupOpenNormalBasis
      F p hpOdd).quotient_mem
        (FiniteGroupClass.pGroup_formation p) U
  let eQuotientFixed :
      (MaxEverywhereUnramifiedProPGaloisGroup F p ⧸
          (U : Subgroup
            (MaxEverywhereUnramifiedProPGaloisGroup F p))) ≃*
        (L ≃ₐ[F] L) :=
    normalAutEquivQuotientWithNormal (k := F)
      (K := maximalEverywhereUnramifiedProP F p) (H := Uc)
      (hNormal := hUcNormal)
  let eLift :
      (L ≃ₐ[F] L) ≃*
        (IntermediateField.lift L ≃ₐ[F] IntermediateField.lift L) :=
    AlgEquiv.autCongr (IntermediateField.liftAlgEquiv L)
  exact
    { field := IntermediateField.lift L
      finiteDimensional := hFiniteLift
      isGalois := hGaloisLift
      numberField := hNumberLift
      isPGroup := hQuotientClass.2.of_equiv
        (eQuotientFixed.trans eLift)
      everywhereUnramified := by
        exact isEverywhereUnramified_of_le_maximalEverywhereUnramifiedProP
          F p hpOdd (IntermediateField.lift L)
            (IntermediateField.lift_le L) }

@[simp]
theorem openNormalArithmeticStage_field
    (hpOdd : Odd p)
    (U : OpenNormalSubgroup
      (MaxEverywhereUnramifiedProPGaloisGroup F p)) :
    (openNormalArithmeticStage F p hpOdd U).field =
      openNormalFixedField F p U :=
  rfl

/-- The quotient by an open normal subgroup is the Galois group of its
concrete finite everywhere-unramified arithmetic stage. -/
noncomputable def openNormalQuotientEquivArithmeticStageGalois
    (hpOdd : Odd p)
    (U : OpenNormalSubgroup
      (MaxEverywhereUnramifiedProPGaloisGroup F p)) :
    (MaxEverywhereUnramifiedProPGaloisGroup F p ⧸
        (U : Subgroup
          (MaxEverywhereUnramifiedProPGaloisGroup F p))) ≃*
      ((openNormalArithmeticStage F p hpOdd U).field ≃ₐ[F]
        (openNormalArithmeticStage F p hpOdd U).field) := by
  let Uc : ClosedSubgroup
      (MaxEverywhereUnramifiedProPGaloisGroup F p) :=
    ⟨(U : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F p)),
      ProCGroups.openNormalSubgroup_isClosed U⟩
  let L := openNormalFixedFieldInMaximal F p U
  have hfix :
      L.fixingSubgroup =
        (Uc : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F p)) := by
    dsimp only [L, openNormalFixedFieldInMaximal,
      openNormalClosedSubgroup, Uc]
    exact InfiniteGalois.fixingSubgroup_fixedField Uc
  have hUcNormal : Subgroup.Normal
      (G := maximalEverywhereUnramifiedProP F p ≃ₐ[F]
        maximalEverywhereUnramifiedProP F p) Uc.toSubgroup :=
    U.isNormal'
  let : Uc.toSubgroup.Normal := hUcNormal
  let : FiniteDimensional F L :=
    (InfiniteGalois.isOpen_iff_finite L).1 (by
      rw [hfix]
      exact U.toOpenSubgroup.isOpen)
  let : IsGalois F L :=
    (InfiniteGalois.normal_iff_isGalois L).1 (by
      rw [hfix]
      exact hUcNormal)
  let eQuotientFixed :
      (MaxEverywhereUnramifiedProPGaloisGroup F p ⧸
          (U : Subgroup
            (MaxEverywhereUnramifiedProPGaloisGroup F p))) ≃*
        (L ≃ₐ[F] L) :=
    normalAutEquivQuotientWithNormal (k := F)
      (K := maximalEverywhereUnramifiedProP F p) (H := Uc)
      (hNormal := hUcNormal)
  rw [openNormalArithmeticStage_field]
  exact eQuotientFixed.trans
    (AlgEquiv.autCongr (IntermediateField.liftAlgEquiv L))

end ClassFieldTower.Martinet.Shafarevich
