/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.AbhyankarLemma.Geometry.Normalization.Inertia
import Nyll.SchemeTheory.AbhyankarLemma.Geometry.Inertia.FieldCompositum
import Nyll.SchemeTheory.AbhyankarLemma.Geometry.Inertia.IdealCompositum
import Nyll.SchemeTheory.AbhyankarLemma.Geometry.Inertia.TrivialImpliesUnramified

/-!
# Abhyankar's cyclic argument for normalization rings

This file combines the two restriction maps from a compositum with the
ideal-theoretic cyclic projection argument.  The resulting relative inertia
group is trivial, and hence the right normalization is unramified in the top
normalization at every chosen maximal prime.
-/

noncomputable section


universe uV uK uE

namespace TameAbhyankar.SGA1

attribute [local instance] Ideal.Quotient.field Module.Free.of_divisionRing

variable {V : Type uV} {K : Type uK} {E : Type uE}
variable [CommRing V] [Field K] [Field E]
variable [Algebra V K] [IsFractionRing V K]
variable [Algebra K E] [Algebra V E] [IsScalarTower V K E]
variable (M N : IntermediateField K E)
variable [Algebra V M] [IsScalarTower V K M] [IsScalarTower V M E]
variable [Algebra V N] [IsScalarTower V K N] [IsScalarTower V N E]

section GaloisCompositum

variable [IsDedekindDomain V]
variable [FiniteDimensional K E] [IsGalois K E]
variable [IsGalois K M] [IsGalois K N]

local instance leftNormalizationAlgebra :
    Algebra (integralClosure V M) (integralClosure V E) :=
  normalizationAlgebra (V := V) (K := K) (E := E) M

local instance rightNormalizationAlgebra :
    Algebra (integralClosure V N) (integralClosure V E) :=
  normalizationAlgebra (V := V) (K := K) (E := E) N

local instance leftPrime_liesOver (Q : Ideal (integralClosure V E)) :
    Q.LiesOver
      (normalizationLowerPrime (V := V) (K := K) (E := E) M Q) :=
  normalizationLowerPrime_liesOver (V := V) M Q

local instance rightPrime_liesOver (Q : Ideal (integralClosure V E)) :
    Q.LiesOver
      (normalizationLowerPrime (V := V) (K := K) (E := E) N Q) :=
  normalizationLowerPrime_liesOver (V := V) N Q

local instance leftBasePrime_liesOver (Q : Ideal (integralClosure V E)) :
    (normalizationLowerPrime (V := V) (K := K) (E := E) M Q).LiesOver
      (normalizationBasePrime (V := V) (K := K) (E := E) M Q) :=
  normalizationBasePrime_liesOver (V := V) M Q

local instance rightBasePrime_liesOver (Q : Ideal (integralClosure V E)) :
    (normalizationLowerPrime (V := V) (K := K) (E := E) N Q).LiesOver
      (normalizationBasePrime (V := V) (K := K) (E := E) N Q) :=
  normalizationBasePrime_liesOver (V := V) N Q

local instance leftPrime_isMaximal
    (Q : Ideal (integralClosure V E)) [Q.IsMaximal] :
    (normalizationLowerPrime (V := V) (K := K) (E := E) M Q).IsMaximal :=
  normalizationLowerPrime_isMaximal (V := V) M Q

local instance rightPrime_isMaximal
    (Q : Ideal (integralClosure V E)) [Q.IsMaximal] :
    (normalizationLowerPrime (V := V) (K := K) (E := E) N Q).IsMaximal :=
  normalizationLowerPrime_isMaximal (V := V) N Q

local instance leftBasePrime_isMaximal
    (Q : Ideal (integralClosure V E)) [Q.IsMaximal] :
    (normalizationBasePrime (V := V) (K := K) (E := E) M Q).IsMaximal :=
  normalizationBasePrime_isMaximal (V := V) M Q

local instance rightBasePrime_isMaximal
    (Q : Ideal (integralClosure V E)) [Q.IsMaximal] :
    (normalizationBasePrime (V := V) (K := K) (E := E) N Q).IsMaximal :=
  normalizationBasePrime_isMaximal (V := V) N Q

noncomputable local instance compositumTopNormalizationAction :
    MulSemiringAction Gal(E/K) (integralClosure V E) :=
  IsIntegralClosure.MulSemiringAction V K E (integralClosure V E)

noncomputable local instance compositumLeftNormalizationAction :
    MulSemiringAction Gal(M/K) (integralClosure V M) :=
  IsIntegralClosure.MulSemiringAction V K M (integralClosure V M)

noncomputable local instance compositumRightNormalizationAction :
    MulSemiringAction Gal(N/K) (integralClosure V N) :=
  IsIntegralClosure.MulSemiringAction V K N (integralClosure V N)

/-- The cyclic step of Abhyankar's lemma for the normalizations in two
normal subextensions which generate the top field.  Separability of the four
residue-field steps supplies both restriction surjections.  Thus no
surjectivity or joint-injectivity hypothesis remains in the statement. -/
theorem normalizationRelativeInertia_card_eq_one_and_isUnramifiedAt
    (hsup : M ⊔ N = ⊤)
    (Q : Ideal (integralClosure V E)) [Q.IsMaximal]
    (hV : ¬ IsField V)
    [IsCyclic (Q.toAddSubgroup.inertia Gal(E/K))]
    [Algebra.IsSeparable
      (V ⧸ normalizationBasePrime (V := V) (K := K) (E := E) M Q)
      (integralClosure V M ⧸
        normalizationLowerPrime (V := V) (K := K) (E := E) M Q)]
    [Algebra.IsSeparable
      (integralClosure V M ⧸
        normalizationLowerPrime (V := V) (K := K) (E := E) M Q)
      (integralClosure V E ⧸ Q)]
    [Algebra.IsSeparable
      (V ⧸ normalizationBasePrime (V := V) (K := K) (E := E) N Q)
      (integralClosure V N ⧸
        normalizationLowerPrime (V := V) (K := K) (E := E) N Q)]
    [Algebra.IsSeparable
      (integralClosure V N ⧸
        normalizationLowerPrime (V := V) (K := K) (E := E) N Q)
      (integralClosure V E ⧸ Q)]
    (hcard :
      Nat.card
          ((normalizationLowerPrime (V := V) (K := K) (E := E) M Q).toAddSubgroup.inertia
            Gal(M/K)) ∣
        Nat.card
          ((normalizationLowerPrime (V := V) (K := K) (E := E) N Q).toAddSubgroup.inertia
            Gal(N/K))) :
    Nat.card
          (Q.toAddSubgroup.inertia
            (normalizationRestrictionHom N).ker) = 1 ∧
      Algebra.IsUnramifiedAt (integralClosure V N) Q := by
  -- Pin the two normalization towers used below.  Keeping these instances
  -- inside the proof prevents fraction-ring instances from making search
  -- reconstruct competing Algebra/tower graphs.
  let : IsScalarTower V (integralClosure V M) (integralClosure V E) :=
    normalizationScalarTower (V := V) (K := K) (E := E) M
  let : IsScalarTower V (integralClosure V N) (integralClosure V E) :=
    normalizationScalarTower (V := V) (K := K) (E := E) N
  let : Algebra (integralClosure V N) E :=
    lowerNormalizationToTopFieldAlgebra (V := V) N
  let : IsScalarTower (integralClosure V N) N E :=
    lowerNormalizationToTopFieldTower (V := V) N
  let : IsScalarTower V (integralClosure V N) E :=
    baseNormalizationToTopFieldTower (V := V) N
  let : IsScalarTower
      (integralClosure V N) (integralClosure V E) E :=
    normalizationToTopFieldTower (V := V) N
  let : IsIntegralClosure
      (integralClosure V E) (integralClosure V N) E :=
    topOverLowerNormalization (V := V) N
  let : Algebra.IsIntegral
      (integralClosure V N) (integralClosure V E) :=
    topOverLowerIntegral (V := V) N
  let : Finite Gal(E/K) :=
    IsGaloisGroup.finite Gal(E/K) K E
  let : Finite Gal(M/K) :=
    IsGaloisGroup.finite Gal(M/K) K M
  let : Finite Gal(N/K) :=
    IsGaloisGroup.finite Gal(N/K) K N
  have hleft :
      Function.Surjective (normalizationInertiaRestriction (V := V) M Q) :=
    normalizationInertiaRestriction_surjective (V := V) M Q hV
  have hright :
      Function.Surjective (normalizationInertiaRestriction (V := V) N Q) :=
    normalizationInertiaRestriction_surjective (V := V) N Q hV
  let : IsCyclic
      ((normalizationLowerPrime (V := V) (K := K) (E := E) M Q).toAddSubgroup.inertia
        Gal(M/K)) :=
    isCyclic_of_surjective
      (normalizationInertiaRestriction (V := V) M Q) hleft
  have hpair : Function.Injective
      ((normalizationRestrictionHom M).prod
        (normalizationRestrictionHom N)) := by
    simpa only [normalizationRestrictionHom] using
      restrictNormalHom_prod_injective_of_sup_eq_top K M N hsup
  have hrelative :
      Nat.card
          (Q.toAddSubgroup.inertia
            (normalizationRestrictionHom N).ker) = 1 := by
    exact (idealRelativeInertia_card_eq_one_of_cyclic_of_card_dvd
      (resLeft := normalizationRestrictionHom M)
      (resRight := normalizationRestrictionHom N)
      (PLeft := normalizationLowerPrime
        (V := V) (K := K) (E := E) M Q)
      (PRight := normalizationLowerPrime
        (V := V) (K := K) (E := E) N Q)
      (Q := Q)
      (normalizationMap_smul_restriction (V := V) M)
      (normalizationMap_smul_restriction (V := V) N)
      hpair hright hcard).2
  let : IsDedekindDomain (integralClosure V N) :=
    IsIntegralClosure.isDedekindDomain V K N (integralClosure V N)
  let : IsDedekindDomain (integralClosure V E) :=
    IsIntegralClosure.isDedekindDomain V K E (integralClosure V E)
  let : IsFractionRing (integralClosure V N) N :=
    IsIntegralClosure.isFractionRing_of_finite_extension
      V K N (integralClosure V N)
  let : IsFractionRing (integralClosure V E) E :=
    IsIntegralClosure.isFractionRing_of_finite_extension
      V K E (integralClosure V E)
  let : Module.Finite (integralClosure V N) (integralClosure V E) :=
    @IsIntegralClosure.finite
      (integralClosure V N) N _ _ _ _ E _ (integralClosure V E)
      _ _ _ (lowerNormalizationToTopFieldTower (V := V) N)
      _ _ _ (normalizationToTopFieldTower (V := V) N) _ _ _ _ _
  have hVN : Function.Injective (algebraMap V N) := by
    intro x y hxy
    apply IsFractionRing.injective V K
    apply (algebraMap K N).injective
    calc
      algebraMap K N (algebraMap V K x) = algebraMap V N x :=
        (IsScalarTower.algebraMap_apply V K N x).symm
      _ = algebraMap V N y := hxy
      _ = algebraMap K N (algebraMap V K y) :=
        IsScalarTower.algebraMap_apply V K N y
  let : Module.IsTorsionFree V (integralClosure V N) :=
    @IsIntegralClosure.isTorsionFree
      V (integralClosure V N) N _ _ _ _ _ _ _
      (lowerNormalizationToFractionFieldTower (V := V) N)
      (Module.isTorsionFree_iff_algebraMap_injective.mpr hVN)
  let : Module.IsTorsionFree
      (integralClosure V N) (integralClosure V E) :=
    @IsIntegralClosure.isTorsionFree
      (integralClosure V N) (integralClosure V E) E _ _ _ _ _ _ _
      (normalizationToTopFieldTower (V := V) N)
      (Module.IsTorsionFree.trans_faithfulSMul (integralClosure V N) N E)
  let resRight := normalizationRestrictionHom N
  let : IsGaloisGroup resRight.ker N E := by
    apply IsGaloisGroup.of_fixedPoints_eq Gal(E/K) K E resRight.ker N
    change IntermediateField.fixedField resRight.ker = N
    rw [show resRight.ker = N.fixingSubgroup by
      exact IntermediateField.restrictNormalHom_ker N]
    exact IsGalois.fixedField_fixingSubgroup N
  let : SMulDistribClass resRight.ker (integralClosure V E) E := {
    smul_distrib_smul := fun sigma x y =>
      smul_distrib_smul (sigma : Gal(E/K)) x y }
  let : IsGaloisGroup resRight.ker
      (integralClosure V N) (integralClosure V E) :=
    @IsGaloisGroup.of_isFractionRing
      resRight.ker (integralClosure V N) (integralClosure V E) N E
      _ _ _ _ _ _ _ _ _ _ _ _ _
      (lowerNormalizationToTopFieldTower (V := V) N)
      (normalizationToTopFieldTower (V := V) N) _ _ _ _ _
  have hp :
      normalizationBasePrime (V := V) (K := K) (E := E) N Q ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField
      (rightBasePrime_isMaximal (V := V) N Q) hV
  have hP :
      normalizationLowerPrime (V := V) (K := K) (E := E) N Q ≠ ⊥ :=
    Ideal.ne_bot_of_liesOver_of_ne_bot hp
      (normalizationLowerPrime (V := V) (K := K) (E := E) N Q)
  refine ⟨hrelative, ?_⟩
  exact isUnramifiedAt_of_inertia_card_eq_one
    (A := integralClosure V N) (B := integralClosure V E)
    (G := resRight.ker)
    (normalizationLowerPrime (V := V) (K := K) (E := E) N Q)
    hP Q hrelative

end GaloisCompositum

end TameAbhyankar.SGA1
