/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.FiniteRealPExtensionSupport
import SawinTotallyRealTowers.MaximalRealProPOutside
import ProCGroups.ProC.InverseLimits.Predicates
import ProCGroups.Profinite.OpenSubgroups
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.Profinite

set_option autoImplicit false

/-!
# The Galois group of the maximal real pro-p compositum

Every finite normal subextension of the constructed compositum is contained
in an admissible finite layer. Restriction therefore makes its Galois group
a quotient of a p-group. Applying this to fixed fields of open normal
subgroups gives a basis of open normal subgroups with finite p-group
quotients. The argument applies to `p = 2` as well as odd primes.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTower.Sawin

/-- A finite normal subextension of the maximal real compositum has a
p-group Galois group, by restriction from one admissible finite layer. -/
theorem isPGroup_galois_of_le_maximalRealProPOutside
    (p : ℕ) (T : Set (HeightOneSpectrum (𝓞 ℚ)))
    (L : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ L] [Normal ℚ L]
    (hL : L ≤ maximalRealProPOutside p T) :
    IsPGroup p (L ≃ₐ[ℚ] L) := by
  obtain ⟨C, hLC⟩ :=
    finiteDimensional_le_iSup_realPExtension_exists_extension p T L hL
  let : Algebra L C.val :=
    RingHom.toAlgebra (IntermediateField.inclusion hLC).toRingHom
  let : IsScalarTower ℚ L C.val := IsScalarTower.of_algebraMap_eq' rfl
  let : Normal ℚ C.val.toIntermediateField := C.val.isGalois.to_normal
  exact C.property.1.of_surjective
    (AlgEquiv.restrictNormalHom L)
    (AlgEquiv.restrictNormalHom_surjective C.val)

/-- The actual Galois group of the maximal real compositum has an
open-normal basis whose finite quotients are p-groups. -/
theorem maximalRealProPOutside_galoisGroup_hasPGroupOpenNormalBasis
    (p : ℕ) [Fact p.Prime] (T : Set (HeightOneSpectrum (𝓞 ℚ))) :
    ProCGroups.ProC.HasPGroupOpenNormalBasis p
      (maximalRealProPOutside p T ≃ₐ[ℚ] maximalRealProPOutside p T) := by
  let : IsGalois ℚ (maximalRealProPOutside p T) :=
    maximalRealProPOutside_isGalois p T
  rw [ProCGroups.ProC.HasPGroupOpenNormalBasis]
  apply ProCGroups.ProC.HasOpenNormalBasisInClass.of_allOpenNormalQuotients
  intro U
  refine ⟨inferInstance, ?_⟩
  let Uc : ClosedSubgroup
      (maximalRealProPOutside p T ≃ₐ[ℚ] maximalRealProPOutside p T) :=
    ⟨(U : Subgroup
      (maximalRealProPOutside p T ≃ₐ[ℚ] maximalRealProPOutside p T)),
      ProCGroups.openNormalSubgroup_isClosed U⟩
  let hUcNormal : Uc.toSubgroup.Normal := U.isNormal'
  let L : IntermediateField ℚ (maximalRealProPOutside p T) :=
    IntermediateField.fixedField Uc.toSubgroup
  have hfix : L.fixingSubgroup = Uc.toSubgroup := by
    dsimp only [L]
    exact InfiniteGalois.fixingSubgroup_fixedField Uc
  let : FiniteDimensional ℚ L :=
    (InfiniteGalois.isOpen_iff_finite L).mp (by
      rw [hfix]
      exact U.toOpenSubgroup.isOpen)
  let hLNormal : Normal ℚ L :=
    ((InfiniteGalois.normal_iff_isGalois L).mp (by
      rw [hfix]
      exact hUcNormal)).to_normal
  have hL : IsPGroup p (L ≃ₐ[ℚ] L) := by
    let : FiniteDimensional ℚ (IntermediateField.lift L) :=
      (IntermediateField.liftAlgEquiv L).toLinearEquiv.finiteDimensional
    let : Normal ℚ (IntermediateField.lift L) :=
      Normal.of_algEquiv (h := hLNormal) (IntermediateField.liftAlgEquiv L)
    have hLift : IsPGroup p
        (IntermediateField.lift L ≃ₐ[ℚ] IntermediateField.lift L) :=
      isPGroup_galois_of_le_maximalRealProPOutside p T
        (IntermediateField.lift L) (IntermediateField.lift_le L)
    exact hLift.of_equiv
      (AlgEquiv.autCongr (IntermediateField.liftAlgEquiv L)).symm
  let e :
      ((maximalRealProPOutside p T ≃ₐ[ℚ] maximalRealProPOutside p T) ⧸
        Uc.toSubgroup) ≃* (L ≃ₐ[ℚ] L) :=
    InfiniteGalois.normalAutEquivQuotient
      (k := ℚ) (K := maximalRealProPOutside p T) Uc
  have hquot : IsPGroup p
      ((maximalRealProPOutside p T ≃ₐ[ℚ] maximalRealProPOutside p T) ⧸
        Uc.toSubgroup) := hL.of_equiv e.symm
  simpa only [Uc] using hquot

end ClassFieldTower.Sawin
