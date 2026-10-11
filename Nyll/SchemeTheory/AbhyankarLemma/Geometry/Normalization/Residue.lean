/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.AbhyankarLemma.Geometry.Normalization.Inertia
import Nyll.SchemeTheory.AbhyankarLemma.Geometry.Residue.Tame

/-!
# Residue separability in a tower of normalization rings

This file specializes the tame-inertia residue criterion to the integral
closures of a Dedekind domain in a finite Galois tower.  It supplies the two
residue-separability inputs used by the normalization form of Abhyankar's
lemma.
-/

noncomputable section


universe uV uK uE

namespace TameAbhyankar.SGA1

attribute [local instance] Ideal.Quotient.field Module.Free.of_divisionRing

variable {V : Type uV} {K : Type uK} {E : Type uE}
variable [CommRing V] [Field K] [Field E]
variable [Algebra V K] [IsFractionRing V K]
variable [Algebra K E] [Algebra V E] [IsScalarTower V K E]
variable (M : IntermediateField K E)
variable [Algebra V M] [IsScalarTower V K M] [IsScalarTower V M E]

section GaloisTower

variable [IsDedekindDomain V]
variable [FiniteDimensional K E] [IsGalois K E] [IsGalois K M]

local instance residueNormalizationAlgebra :
    Algebra (integralClosure V M) (integralClosure V E) :=
  normalizationAlgebra (V := V) (K := K) (E := E) M

local instance residueNormalizationScalarTower :
    IsScalarTower V (integralClosure V M) (integralClosure V E) :=
  normalizationScalarTower (V := V) M

local instance residueLowerPrime_liesOver
    (Q : Ideal (integralClosure V E)) :
    Q.LiesOver
      (normalizationLowerPrime (V := V) (K := K) (E := E) M Q) where
  over := rfl

local instance residueBasePrime_liesOver
    (Q : Ideal (integralClosure V E)) :
    (normalizationLowerPrime (V := V) (K := K) (E := E) M Q).LiesOver
      (normalizationBasePrime (V := V) (K := K) (E := E) M Q) where
  over := rfl

local instance residueTopPrime_liesOverBase
    (Q : Ideal (integralClosure V E)) :
    Q.LiesOver
      (normalizationBasePrime (V := V) (K := K) (E := E) M Q) :=
  Ideal.LiesOver.trans Q
    (normalizationLowerPrime (V := V) (K := K) (E := E) M Q)
    (normalizationBasePrime (V := V) (K := K) (E := E) M Q)

local instance residueLowerPrime_isMaximal
    (Q : Ideal (integralClosure V E)) [Q.IsMaximal] :
    (normalizationLowerPrime (V := V) (K := K) (E := E) M Q).IsMaximal :=
  normalizationLowerPrime_isMaximal (V := V) M Q

local instance residueBasePrime_isMaximal
    (Q : Ideal (integralClosure V E)) [Q.IsMaximal] :
    (normalizationBasePrime (V := V) (K := K) (E := E) M Q).IsMaximal :=
  normalizationBasePrime_isMaximal (V := V) M Q

local instance residueLowerToTopFieldAlgebra :
    Algebra (integralClosure V M) E :=
  lowerNormalizationToTopFieldAlgebra (V := V) M

local instance residueLowerToTopFieldTower :
    IsScalarTower (integralClosure V M) M E :=
  lowerNormalizationToTopFieldTower (V := V) M

local instance residueNormalizationToTopFieldTower :
    IsScalarTower (integralClosure V M) (integralClosure V E) E :=
  normalizationToTopFieldTower (V := V) M

local instance residueLowerDedekind :
    IsDedekindDomain (integralClosure V M) :=
  IsIntegralClosure.isDedekindDomain V K M (integralClosure V M)

local instance residueLowerFinite :
    Module.Finite V (integralClosure V M) :=
  IsIntegralClosure.finite V K M (integralClosure V M)

local instance residueLowerFractionRing :
    IsFractionRing (integralClosure V M) M :=
  IsIntegralClosure.isFractionRing_of_finite_extension
    V K M (integralClosure V M)

local instance residueLowerTorsionFree :
    Module.IsTorsionFree V (integralClosure V M) := by
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
  exact @IsIntegralClosure.isTorsionFree
    V (integralClosure V M) M _ _ _ _ _ _ _
    (lowerNormalizationToFractionFieldTower (V := V) M)
    (Module.isTorsionFree_iff_algebraMap_injective.mpr hVM)

local instance residueLowerGaloisFinite : Finite Gal(M/K) :=
  IsGaloisGroup.finite Gal(M/K) K M

local instance residueTopGaloisFinite : Finite Gal(E/K) :=
  IsGaloisGroup.finite Gal(E/K) K E

noncomputable local instance residueTopNormalizationAction :
    MulSemiringAction Gal(E/K) (integralClosure V E) :=
  IsIntegralClosure.MulSemiringAction V K E (integralClosure V E)

noncomputable local instance residueLowerNormalizationAction :
    MulSemiringAction Gal(M/K) (integralClosure V M) :=
  IsIntegralClosure.MulSemiringAction V K M (integralClosure V M)

local instance residueLowerIsGaloisGroup :
    IsGaloisGroup Gal(M/K) V (integralClosure V M) :=
  IsGaloisGroup.of_isFractionRing Gal(M/K)
    V (integralClosure V M) K M

omit [IsScalarTower V K E] in
/-- If lower inertia is prime to the exponential characteristic of the base
residue field, then the residue extension from the base to the contraction in
the normalization in `M` is separable. -/
theorem normalizationLowerResidue_isSeparable_of_inertia_card_coprime
    (Q : Ideal (integralClosure V E)) [Q.IsMaximal]
    (hV : ¬ IsField V)
    (hcop : Nat.Coprime
      (Nat.card
        ((normalizationLowerPrime (V := V) (K := K) (E := E) M Q).toAddSubgroup.inertia
          Gal(M/K)))
      (ringExpChar
        (V ⧸ normalizationBasePrime (V := V) (K := K) (E := E) M Q))) :
    Algebra.IsSeparable
      (V ⧸ normalizationBasePrime (V := V) (K := K) (E := E) M Q)
      (integralClosure V M ⧸
        normalizationLowerPrime (V := V) (K := K) (E := E) M Q) := by
  have hp :
      normalizationBasePrime (V := V) (K := K) (E := E) M Q ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField
      (residueBasePrime_isMaximal (V := V) M Q) hV
  exact residue_isSeparable_of_inertia_card_coprime_ringExpChar
    (A := V) (B := integralClosure V M) (G := Gal(M/K))
    (normalizationBasePrime (V := V) (K := K) (E := E) M Q) hp
    (normalizationLowerPrime (V := V) (K := K) (E := E) M Q) hcop

omit [IsScalarTower V K M] [IsGalois K M] in
/-- If top inertia is prime to the exponential characteristic of the base
residue field, then the residue extension from the base directly to the top
normalization prime is separable. -/
theorem normalizationTopResidue_isSeparable_of_inertia_card_coprime
    (Q : Ideal (integralClosure V E)) [Q.IsMaximal]
    (hV : ¬ IsField V)
    (hcop : Nat.Coprime
      (Nat.card (Q.toAddSubgroup.inertia Gal(E/K)))
      (ringExpChar
        (V ⧸ normalizationBasePrime (V := V) (K := K) (E := E) M Q))) :
    Algebra.IsSeparable
      (V ⧸ normalizationBasePrime (V := V) (K := K) (E := E) M Q)
      (integralClosure V E ⧸ Q) := by
  let : IsDedekindDomain (integralClosure V E) :=
    IsIntegralClosure.isDedekindDomain V K E (integralClosure V E)
  let : Module.Finite V (integralClosure V E) :=
    IsIntegralClosure.finite V K E (integralClosure V E)
  let : IsFractionRing (integralClosure V E) E :=
    IsIntegralClosure.isFractionRing_of_finite_extension
      V K E (integralClosure V E)
  let hVE : Module.IsTorsionFree V E :=
    Module.IsTorsionFree.trans_faithfulSMul V K E
  let : Module.IsTorsionFree V (integralClosure V E) :=
    @IsIntegralClosure.isTorsionFree
      V (integralClosure V E) E _ _ _ _ _ _ _
      (topNormalizationToFractionFieldTower (V := V) (E := E)) hVE
  let : IsGaloisGroup Gal(E/K) V (integralClosure V E) :=
    IsGaloisGroup.of_isFractionRing Gal(E/K)
      V (integralClosure V E) K E
  have hp :
      normalizationBasePrime (V := V) (K := K) (E := E) M Q ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField
      (residueBasePrime_isMaximal (V := V) M Q) hV
  exact residue_isSeparable_of_inertia_card_coprime_ringExpChar
    (A := V) (B := integralClosure V E) (G := Gal(E/K))
    (normalizationBasePrime (V := V) (K := K) (E := E) M Q) hp Q hcop

omit [IsScalarTower V K M] [IsGalois K M] in
/-- The same coprimality condition on top inertia also makes the upper step
of the residue tower, from the contraction in `M` to `Q`, separable. -/
theorem normalizationRelativeResidue_isSeparable_of_top_inertia_card_coprime
    (Q : Ideal (integralClosure V E)) [Q.IsMaximal]
    (hV : ¬ IsField V)
    (hcop : Nat.Coprime
      (Nat.card (Q.toAddSubgroup.inertia Gal(E/K)))
      (ringExpChar
        (V ⧸ normalizationBasePrime (V := V) (K := K) (E := E) M Q))) :
    Algebra.IsSeparable
      (integralClosure V M ⧸
        normalizationLowerPrime (V := V) (K := K) (E := E) M Q)
      (integralClosure V E ⧸ Q) := by
  let : IsScalarTower
      (V ⧸ normalizationBasePrime (V := V) (K := K) (E := E) M Q)
      (integralClosure V M ⧸
        normalizationLowerPrime (V := V) (K := K) (E := E) M Q)
      (integralClosure V E ⧸ Q) :=
    IsScalarTower.of_algebraMap_eq
      (R := V ⧸ normalizationBasePrime (V := V) (K := K) (E := E) M Q)
      (S := integralClosure V M ⧸
        normalizationLowerPrime (V := V) (K := K) (E := E) M Q)
      (A := integralClosure V E ⧸ Q) <| by
      intro x
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      change Ideal.Quotient.mk Q (algebraMap V (integralClosure V E) y) =
        Ideal.Quotient.mk Q (algebraMap (integralClosure V M) (integralClosure V E)
          (algebraMap V (integralClosure V M) y))
      exact congrArg (Ideal.Quotient.mk Q)
        (IsScalarTower.algebraMap_apply
          V (integralClosure V M) (integralClosure V E) y)
  let : Algebra.IsSeparable
      (V ⧸ normalizationBasePrime (V := V) (K := K) (E := E) M Q)
      (integralClosure V E ⧸ Q) :=
    normalizationTopResidue_isSeparable_of_inertia_card_coprime
      (V := V) M Q hV hcop
  exact Algebra.isSeparable_tower_top_of_isSeparable
    (V ⧸ normalizationBasePrime (V := V) (K := K) (E := E) M Q)
    (integralClosure V M ⧸
      normalizationLowerPrime (V := V) (K := K) (E := E) M Q)
    (integralClosure V E ⧸ Q)

end GaloisTower

end TameAbhyankar.SGA1
