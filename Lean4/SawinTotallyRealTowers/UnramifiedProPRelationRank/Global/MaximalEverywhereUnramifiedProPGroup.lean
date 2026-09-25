/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Global.MaximalEverywhereUnramifiedProPGalois
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Global.MaximalEverywhereUnramifiedProPCofinality
import ProCGroups.ProC.InverseLimits.Predicates
import ProCGroups.Profinite.OpenSubgroups

set_option autoImplicit false
/-!
# The maximal everywhere-unramified pro-p Galois group

For odd `p`, every open normal quotient of the Galois group of the maximal
compositum is a finite `p`-group.  The corresponding fixed field is finite
Galois, hence lies in one bundled finite `p`-extension by cofinality; restriction
from that extension supplies the required quotient `p`-group structure.
-/

open scoped NumberField

noncomputable section

universe u

namespace ClassFieldTower.Martinet

/-- The fixed-field quotient equivalence with a named normality argument. -/
noncomputable def normalAutEquivQuotientWithNormal
    {k K : Type u} [Field k] [Field K] [Algebra k K] [IsGalois k K]
    (H : ClosedSubgroup (K ≃ₐ[k] K)) [hNormal : H.toSubgroup.Normal] :
    ((K ≃ₐ[k] K) ⧸ H.toSubgroup) ≃*
      (IntermediateField.fixedField H.toSubgroup ≃ₐ[k]
        IntermediateField.fixedField H.toSubgroup) :=
  InfiniteGalois.normalAutEquivQuotient (k := k) (K := K) (H := H)

/-- For odd `p`, the Galois group of the maximal everywhere-unramified
pro-`p` compositum has an open-normal basis with finite `p`-group quotients. -/
theorem maxEverywhereUnramifiedProPGaloisGroup_hasPGroupOpenNormalBasis
    (F : Type u) [Field F] [NumberField F]
    (p : ℕ) [Fact p.Prime]
    (hpOdd : Odd p) :
    ProCGroups.ProC.HasPGroupOpenNormalBasis p
      (MaxEverywhereUnramifiedProPGaloisGroup F p) := by
  rw [ProCGroups.ProC.HasPGroupOpenNormalBasis]
  apply ProCGroups.ProC.HasOpenNormalBasisInClass.of_allOpenNormalQuotients
  intro U
  refine ⟨inferInstance, ?_⟩
  let Uc : ClosedSubgroup
      (MaxEverywhereUnramifiedProPGaloisGroup F p) :=
    ⟨(U : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F p)),
      ProCGroups.openNormalSubgroup_isClosed U⟩
  have hUcNormal : Subgroup.Normal
      (G := maximalEverywhereUnramifiedProP F p ≃ₐ[F]
        maximalEverywhereUnramifiedProP F p) Uc.toSubgroup :=
    U.isNormal'
  let L : IntermediateField F (maximalEverywhereUnramifiedProP F p) :=
    IntermediateField.fixedField (Uc : Subgroup
      (MaxEverywhereUnramifiedProPGaloisGroup F p))
  have hfix : L.fixingSubgroup = (Uc : Subgroup
      (MaxEverywhereUnramifiedProPGaloisGroup F p)) := by
    dsimp only [L]
    exact InfiniteGalois.fixingSubgroup_fixedField Uc
  let : FiniteDimensional F L :=
    (InfiniteGalois.isOpen_iff_finite L).1 (by
      rw [hfix]
      exact U.toOpenSubgroup.isOpen)
  let : IsGalois F L :=
    (InfiniteGalois.normal_iff_isGalois L).1 (by
      rw [hfix]
      exact hUcNormal)
  let : FiniteDimensional F (IntermediateField.lift L) :=
    (IntermediateField.liftAlgEquiv L).toLinearEquiv.finiteDimensional
  obtain ⟨C, hLC⟩ :=
    finiteDimensional_le_maximalEverywhereUnramifiedProP_exists_extension
      F p hpOdd (IntermediateField.lift L) (IntermediateField.lift_le L)
  let : IsGalois F (IntermediateField.lift L) :=
    IsGalois.of_algEquiv (IntermediateField.liftAlgEquiv L)
  let : Algebra (IntermediateField.lift L) C.field :=
    RingHom.toAlgebra (IntermediateField.inclusion hLC).toRingHom
  let : IsScalarTower F (IntermediateField.lift L) C.field :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hLift : IsPGroup p
      (IntermediateField.lift L ≃ₐ[F] IntermediateField.lift L) :=
    C.isPGroup.of_surjective
      (AlgEquiv.restrictNormalHom (IntermediateField.lift L))
      (AlgEquiv.restrictNormalHom_surjective C.field)
  have hL : IsPGroup p (L ≃ₐ[F] L) :=
    hLift.of_equiv
      (AlgEquiv.autCongr (IntermediateField.liftAlgEquiv L)).symm
  let e : (MaxEverywhereUnramifiedProPGaloisGroup F p ⧸
      (Uc : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F p))) ≃*
      (L ≃ₐ[F] L) :=
    normalAutEquivQuotientWithNormal (k := F)
      (K := maximalEverywhereUnramifiedProP F p) (H := Uc)
      (hNormal := hUcNormal)
  have hquot : IsPGroup p
      (MaxEverywhereUnramifiedProPGaloisGroup F p ⧸
        (Uc : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F p))) :=
    hL.of_equiv e.symm
  simpa only [Uc] using hquot

end ClassFieldTower.Martinet
