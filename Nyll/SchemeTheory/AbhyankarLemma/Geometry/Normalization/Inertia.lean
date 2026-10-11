/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.AbhyankarLemma.Geometry.Inertia.IdealTower
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Inertia in a tower of normalization rings

This file instantiates the ideal-theoretic inertia tower for the integral
closures of a Dedekind domain in a finite Galois tower of fields.
-/

noncomputable section

universe uV uK uE

namespace TameAbhyankar
namespace SGA1

attribute [local instance] Ideal.Quotient.field Module.Free.of_divisionRing

variable {V : Type uV} {K : Type uK} {E : Type uE}
variable [CommRing V] [Field K] [Field E]
variable [Algebra V K] [IsFractionRing V K]
variable [Algebra K E] [Algebra V E] [IsScalarTower V K E]
variable (M : IntermediateField K E)
variable [Algebra V M] [IsScalarTower V K M] [IsScalarTower V M E]

/-- The canonical map from the normalization in `M` to the normalization in
`E`, induced by the inclusion `M ⊆ E`. -/
noncomputable def normalizationMap :
    integralClosure V M →ₐ[V] integralClosure V E :=
  (IsScalarTower.toAlgHom V M E).mapIntegralClosure

omit [Algebra V K] [IsFractionRing V K] [IsScalarTower V K E]
  [IsScalarTower V K M] in
@[simp] theorem normalizationMap_coe (x : integralClosure V M) :
    ((normalizationMap (V := V) (K := K) (E := E) M x :
      integralClosure V E) : E) = ((x : M) : E) :=
  rfl

/-- Contraction of a top normalization prime to the normalization in `M`. -/
def normalizationLowerPrime (Q : Ideal (integralClosure V E)) :
    Ideal (integralClosure V M) :=
  Q.comap (normalizationMap (V := V) (K := K) (E := E) M).toRingHom

/-- Further contraction of a top normalization prime to the base ring. -/
def normalizationBasePrime (Q : Ideal (integralClosure V E)) : Ideal V :=
  (normalizationLowerPrime (V := V) (K := K) (E := E) M Q).comap
    (algebraMap V (integralClosure V M))

section GaloisTower

variable [IsDedekindDomain V]
variable [FiniteDimensional K E] [IsGalois K E] [IsGalois K M]

local instance normalizationAlgebra :
    Algebra (integralClosure V M) (integralClosure V E) :=
  (normalizationMap (V := V) (K := K) (E := E) M).toRingHom.toAlgebra

local instance normalizationScalarTower :
    IsScalarTower V (integralClosure V M) (integralClosure V E) := by
  apply IsScalarTower.of_algebraMap_eq
  intro x
  apply IsIntegralClosure.algebraMap_injective (integralClosure V E) V E
  change algebraMap V E x = algebraMap M E (algebraMap V M x)
  exact IsScalarTower.algebraMap_apply V M E x

local instance normalizationLowerPrime_liesOver
    (Q : Ideal (integralClosure V E)) :
    Q.LiesOver
      (normalizationLowerPrime (V := V) (K := K) (E := E) M Q) where
  over := rfl

local instance normalizationBasePrime_liesOver
    (Q : Ideal (integralClosure V E)) :
    (normalizationLowerPrime (V := V) (K := K) (E := E) M Q).LiesOver
      (normalizationBasePrime (V := V) (K := K) (E := E) M Q) where
  over := rfl

local instance lowerNormalizationToTopFieldAlgebra :
    Algebra (integralClosure V M) E :=
  ((algebraMap M E).comp
    (algebraMap (integralClosure V M) M)).toAlgebra

local instance lowerNormalizationToFractionFieldTower :
    IsScalarTower V (integralClosure V M) M :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance topNormalizationToFractionFieldTower :
    IsScalarTower V (integralClosure V E) E :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance lowerNormalizationToTopFieldTower :
    IsScalarTower (integralClosure V M) M E :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance baseNormalizationToTopFieldTower :
    IsScalarTower V (integralClosure V M) E := by
  apply IsScalarTower.of_algebraMap_eq
  intro x
  change algebraMap V E x = algebraMap M E (algebraMap V M x)
  exact IsScalarTower.algebraMap_apply V M E x

local instance normalizationToTopFieldTower :
    IsScalarTower (integralClosure V M) (integralClosure V E) E := by
  apply IsScalarTower.of_algebraMap_eq
  intro x
  rfl

local instance topOverLowerNormalization :
    IsIntegralClosure (integralClosure V E) (integralClosure V M) E := by
  exact @IsIntegralClosure.tower_top
    V (integralClosure V M) _ _ _ E (integralClosure V E)
    _ _ _ _ _ (baseNormalizationToTopFieldTower (V := V) M) _ _

local instance topOverLowerIntegral :
    Algebra.IsIntegral (integralClosure V M) (integralClosure V E) := by
  exact @IsIntegralClosure.isIntegral_algebra
    (integralClosure V M) (integralClosure V E) E
    _ _ _ _ _ _ _ (normalizationToTopFieldTower (V := V) M)

local instance normalizationLowerPrime_isMaximal
    (Q : Ideal (integralClosure V E)) [Q.IsMaximal] :
    (normalizationLowerPrime (V := V) (K := K) (E := E) M Q).IsMaximal := by
  change (Q.comap
    (algebraMap (integralClosure V M) (integralClosure V E))).IsMaximal
  exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
    (algebraMap (integralClosure V M) (integralClosure V E))
    (fun x ↦ Algebra.IsIntegral.isIntegral x) Q

local instance normalizationBasePrime_isMaximal
    (Q : Ideal (integralClosure V E)) [Q.IsMaximal] :
    (normalizationBasePrime (V := V) (K := K) (E := E) M Q).IsMaximal := by
  change ((normalizationLowerPrime (V := V) (K := K) (E := E) M Q).comap
    (algebraMap V (integralClosure V M))).IsMaximal
  exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
    (algebraMap V (integralClosure V M)) (fun x ↦ Algebra.IsIntegral.isIntegral x)
    (normalizationLowerPrime (V := V) (K := K) (E := E) M Q)

noncomputable local instance topNormalizationAction :
    MulSemiringAction Gal(E/K) (integralClosure V E) :=
  IsIntegralClosure.MulSemiringAction V K E (integralClosure V E)

noncomputable local instance lowerNormalizationAction :
    MulSemiringAction Gal(M/K) (integralClosure V M) :=
  IsIntegralClosure.MulSemiringAction V K M (integralClosure V M)

/-- Restriction from the top Galois group to the normal intermediate field. -/
noncomputable def normalizationRestrictionHom : Gal(E/K) →* Gal(M/K) :=
  AlgEquiv.restrictNormalHom M

omit [IsDedekindDomain V] [FiniteDimensional K E] in
/-- The normalization map is equivariant for restriction of Galois
automorphisms. -/
theorem normalizationMap_smul_restriction
    (sigma : Gal(E/K)) (x : integralClosure V M) :
    normalizationMap (V := V) (K := K) (E := E) M
        (normalizationRestrictionHom M sigma • x) =
      sigma • normalizationMap (V := V) (K := K) (E := E) M x := by
  apply IsIntegralClosure.algebraMap_injective (integralClosure V E) V E
  change
    ((normalizationMap (V := V) (K := K) (E := E) M
      (normalizationRestrictionHom M sigma • x) : integralClosure V E) : E) =
      ((sigma • normalizationMap (V := V) (K := K) (E := E) M x :
        integralClosure V E) : E)
  rw [normalizationMap_coe]
  change
    algebraMap M E
        (algebraMap (integralClosure V M) M
          (galRestrict V K M (integralClosure V M)
            (normalizationRestrictionHom M sigma) x)) =
      algebraMap (integralClosure V E) E
        (galRestrict V K E (integralClosure V E) sigma
          (normalizationMap (V := V) (K := K) (E := E) M x))
  rw [algebraMap_galRestrict_apply, algebraMap_galRestrict_apply]
  change
    algebraMap M E
        (normalizationRestrictionHom M sigma
          (algebraMap (integralClosure V M) M x)) =
      sigma
        (((normalizationMap (V := V) (K := K) (E := E) M x :
          integralClosure V E) : E))
  rw [normalizationMap_coe]
  exact AlgEquiv.restrictNormalHom_apply M sigma (x : M)

/-- Restriction on the inertia groups attached to a top normalization prime
and its contraction to the normalization in `M`. -/
noncomputable def normalizationInertiaRestriction
    (Q : Ideal (integralClosure V E)) :
    Q.toAddSubgroup.inertia Gal(E/K) →*
      (normalizationLowerPrime (V := V) (K := K) (E := E) M Q).toAddSubgroup.inertia
        Gal(M/K) :=
  idealInertiaRestriction
    (normalizationRestrictionHom M)
    (normalizationLowerPrime (V := V) (K := K) (E := E) M Q) Q
    (normalizationMap_smul_restriction (V := V) M)

omit [IsDedekindDomain V] [FiniteDimensional K E] in
/-- For every top normalization prime, the kernel of inertia restriction is
the relative inertia group of `E / M`. -/
theorem normalizationInertiaRestriction_ker_eq_range_relative
    (Q : Ideal (integralClosure V E)) :
    MonoidHom.ker (normalizationInertiaRestriction (V := V) M Q) =
      (idealRelativeInertiaInclusion (Q := Q)
        (normalizationRestrictionHom M)).range :=
  idealInertiaRestriction_ker_eq_range_relative
    (normalizationRestrictionHom M)
    (normalizationLowerPrime (V := V) (K := K) (E := E) M Q) Q
    (normalizationMap_smul_restriction (V := V) M)

/-- For every maximal prime of the top normalization, restriction on inertia
to its contraction in the normalization in `M` is surjective, provided the
two residue-field steps are separable. -/
theorem normalizationInertiaRestriction_surjective
    (Q : Ideal (integralClosure V E)) [Q.IsMaximal]
    (hV : ¬ IsField V)
    [Algebra.IsSeparable
      (V ⧸ normalizationBasePrime (V := V) (K := K) (E := E) M Q)
      (integralClosure V M ⧸
        normalizationLowerPrime (V := V) (K := K) (E := E) M Q)]
    [Algebra.IsSeparable
      (integralClosure V M ⧸
        normalizationLowerPrime (V := V) (K := K) (E := E) M Q)
      (integralClosure V E ⧸ Q)] :
    Function.Surjective (normalizationInertiaRestriction (V := V) M Q) := by
  let : IsDedekindDomain (integralClosure V M) :=
    IsIntegralClosure.isDedekindDomain V K M (integralClosure V M)
  let : IsDedekindDomain (integralClosure V E) :=
    IsIntegralClosure.isDedekindDomain V K E (integralClosure V E)
  let : Module.Finite V (integralClosure V M) :=
    IsIntegralClosure.finite V K M (integralClosure V M)
  let : Module.Finite V (integralClosure V E) :=
    IsIntegralClosure.finite V K E (integralClosure V E)
  let : IsFractionRing (integralClosure V M) M :=
    IsIntegralClosure.isFractionRing_of_finite_extension
      V K M (integralClosure V M)
  let : IsFractionRing (integralClosure V E) E :=
    IsIntegralClosure.isFractionRing_of_finite_extension
      V K E (integralClosure V E)
  let : Module.Finite (integralClosure V M) (integralClosure V E) :=
    @IsIntegralClosure.finite
      (integralClosure V M) M _ _ _ _ E _ (integralClosure V E)
      _ _ _ (lowerNormalizationToTopFieldTower (V := V) M)
      _ _ _ (normalizationToTopFieldTower (V := V) M) _ _ _ _ _
  have hVM : Function.Injective (algebraMap V M) := by
    intro x y hxy
    apply IsFractionRing.injective V K
    apply (algebraMap K M).injective
    calc
      algebraMap K M (algebraMap V K x) = algebraMap V M x :=
        (IsScalarTower.algebraMap_apply V K M x).symm
      _ = algebraMap V M y := hxy
      _ = algebraMap K M (algebraMap V K y) :=
        IsScalarTower.algebraMap_apply V K M y
  let : Module.IsTorsionFree V (integralClosure V M) :=
    @IsIntegralClosure.isTorsionFree
      V (integralClosure V M) M _ _ _ _ _ _ _
      (lowerNormalizationToFractionFieldTower (V := V) M)
      (Module.isTorsionFree_iff_algebraMap_injective.mpr hVM)
  let : Module.IsTorsionFree V (integralClosure V E) :=
    @IsIntegralClosure.isTorsionFree
      V (integralClosure V E) E _ _ _ _ _ _ _
      (topNormalizationToFractionFieldTower (V := V) (E := E))
      (Module.IsTorsionFree.trans_faithfulSMul V K E)
  let : Module.IsTorsionFree
      (integralClosure V M) (integralClosure V E) :=
    @IsIntegralClosure.isTorsionFree
      (integralClosure V M) (integralClosure V E) E _ _ _ _ _ _ _
      (normalizationToTopFieldTower (V := V) M)
      (Module.IsTorsionFree.trans_faithfulSMul (integralClosure V M) M E)
  let : Finite Gal(M/K) :=
    IsGaloisGroup.finite Gal(M/K) K M
  let : Finite Gal(E/K) :=
    IsGaloisGroup.finite Gal(E/K) K E
  let : IsGaloisGroup Gal(M/K) V (integralClosure V M) :=
    IsGaloisGroup.of_isFractionRing Gal(M/K)
      V (integralClosure V M) K M
  let : IsGaloisGroup Gal(E/K) V (integralClosure V E) :=
    IsGaloisGroup.of_isFractionRing Gal(E/K)
      V (integralClosure V E) K E
  let res := normalizationRestrictionHom M
  let : IsGaloisGroup res.ker M E := by
    apply IsGaloisGroup.of_fixedPoints_eq Gal(E/K) K E res.ker M
    change IntermediateField.fixedField res.ker = M
    rw [show res.ker = M.fixingSubgroup by
      exact IntermediateField.restrictNormalHom_ker M]
    exact IsGalois.fixedField_fixingSubgroup M
  let : SMulDistribClass res.ker (integralClosure V E) E := {
    smul_distrib_smul := fun sigma x y =>
      smul_distrib_smul (sigma : Gal(E/K)) x y }
  let : IsGaloisGroup res.ker
      (integralClosure V M) (integralClosure V E) :=
    @IsGaloisGroup.of_isFractionRing
      res.ker (integralClosure V M) (integralClosure V E) M E
      _ _ _ _ _ _ _ _ _ _ _ _ _
      (lowerNormalizationToTopFieldTower (V := V) M)
      (normalizationToTopFieldTower (V := V) M) _ _ _ _ _
  have hp :
      normalizationBasePrime (V := V) (K := K) (E := E) M Q ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField
      (normalizationBasePrime_isMaximal (V := V) M Q) hV
  exact idealInertiaRestriction_surjective
    (res := res)
    (p := normalizationBasePrime (V := V) (K := K) (E := E) M Q)
    (P := normalizationLowerPrime (V := V) (K := K) (E := E) M Q)
    (Q := Q) hp
    (normalizationMap_smul_restriction (V := V) M)

end GaloisTower

end SGA1
end TameAbhyankar
