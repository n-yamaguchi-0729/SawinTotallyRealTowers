/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.AbhyankarLemma.Geometry.Normalization.DVR
import Nyll.SchemeTheory.AbhyankarLemma.Geometry.Inertia.IdealLocalization
import Nyll.SchemeTheory.AbhyankarLemma.Geometry.Normalization.Compositum
import Nyll.SchemeTheory.AbhyankarLemma.Geometry.Normalization.Residue
import Nyll.SchemeTheory.AbhyankarLemma.Geometry.Normalization.Tame

/-!
# Abhyankar's lemma over an arbitrary discrete valuation ring

This file packages the SGA 1 inertia-group argument prime by prime.  The
base DVR is neither assumed complete nor henselian.  All maximal ideals of
the normalization in the compositum are quantified, and the conclusion
records both inertia restriction exact sequences as well as unramifiedness
over the right-hand normalization.
-/

noncomputable section


universe uV uK uE

namespace TameAbhyankar.SGA1

attribute [local instance] Ideal.Quotient.field Module.Free.of_divisionRing

variable {V : Type uV} {K : Type uK} {E : Type uE}
variable [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
variable [Field K] [Field E]
variable [Algebra V K] [IsFractionRing V K]
variable [Algebra K E] [Algebra V E] [IsScalarTower V K E]
variable [FiniteDimensional K E] [IsGalois K E]

variable (M N : IntermediateField K E)
variable [Normal K M] [Normal K N]
variable [Algebra V M] [IsScalarTower V K M] [IsScalarTower V M E]
variable [Algebra V N] [IsScalarTower V K N] [IsScalarTower V N E]

local instance abhyankarDVRDedekind : IsDedekindDomain V :=
  isDedekindDomain_of_isDiscreteValuationRing V

local instance abhyankarLeftSeparable : Algebra.IsSeparable K M :=
  Algebra.isSeparable_tower_bot_of_isSeparable (F := K) M E

local instance abhyankarRightSeparable : Algebra.IsSeparable K N :=
  Algebra.isSeparable_tower_bot_of_isSeparable (F := K) N E

local instance abhyankarLeftGalois : IsGalois K M :=
  isGalois_iff.mpr ⟨inferInstance, inferInstance⟩

local instance abhyankarRightGalois : IsGalois K N :=
  isGalois_iff.mpr ⟨inferInstance, inferInstance⟩

local instance abhyankarLeftNormalizationAlgebra :
    Algebra (integralClosure V M) (integralClosure V E) :=
  normalizationAlgebra (V := V) (K := K) (E := E) M

local instance abhyankarRightNormalizationAlgebra :
    Algebra (integralClosure V N) (integralClosure V E) :=
  normalizationAlgebra (V := V) (K := K) (E := E) N

local instance abhyankarLeftPrimeLiesOver
    (Q : Ideal (integralClosure V E)) :
    Q.LiesOver
      (normalizationLowerPrime (V := V) (K := K) (E := E) M Q) where
  over := rfl

local instance abhyankarRightPrimeLiesOver
    (Q : Ideal (integralClosure V E)) :
    Q.LiesOver
      (normalizationLowerPrime (V := V) (K := K) (E := E) N Q) where
  over := rfl

local instance abhyankarLeftBasePrimeLiesOver
    (Q : Ideal (integralClosure V E)) :
    (normalizationLowerPrime (V := V) (K := K) (E := E) M Q).LiesOver
      (normalizationBasePrime (V := V) (K := K) (E := E) M Q) where
  over := rfl

local instance abhyankarRightBasePrimeLiesOver
    (Q : Ideal (integralClosure V E)) :
    (normalizationLowerPrime (V := V) (K := K) (E := E) N Q).LiesOver
      (normalizationBasePrime (V := V) (K := K) (E := E) N Q) where
  over := rfl

local instance abhyankarLeftPrimeIsMaximal
    (Q : Ideal (integralClosure V E)) [Q.IsMaximal] :
    (normalizationLowerPrime (V := V) (K := K) (E := E) M Q).IsMaximal :=
  normalizationLowerPrime_isMaximal (V := V) M Q

local instance abhyankarRightPrimeIsMaximal
    (Q : Ideal (integralClosure V E)) [Q.IsMaximal] :
    (normalizationLowerPrime (V := V) (K := K) (E := E) N Q).IsMaximal :=
  normalizationLowerPrime_isMaximal (V := V) N Q

local instance abhyankarLeftBasePrimeIsMaximal
    (Q : Ideal (integralClosure V E)) [Q.IsMaximal] :
    (normalizationBasePrime (V := V) (K := K) (E := E) M Q).IsMaximal :=
  normalizationBasePrime_isMaximal (V := V) M Q

local instance abhyankarRightBasePrimeIsMaximal
    (Q : Ideal (integralClosure V E)) [Q.IsMaximal] :
    (normalizationBasePrime (V := V) (K := K) (E := E) N Q).IsMaximal :=
  normalizationBasePrime_isMaximal (V := V) N Q

noncomputable local instance abhyankarTopNormalizationAction :
    MulSemiringAction Gal(E/K) (integralClosure V E) :=
  IsIntegralClosure.MulSemiringAction V K E (integralClosure V E)

noncomputable local instance abhyankarLeftNormalizationAction :
    MulSemiringAction Gal(M/K) (integralClosure V M) :=
  IsIntegralClosure.MulSemiringAction V K M (integralClosure V M)

noncomputable local instance abhyankarRightNormalizationAction :
    MulSemiringAction Gal(N/K) (integralClosure V N) :=
  IsIntegralClosure.MulSemiringAction V K N (integralClosure V N)

/-- Prime-to-residue-characteristic tameness of the inertia group obtained by
contracting a top normalization prime to an intermediate normalization. -/
def NormalizationInertia.IsTameAt
    (M : IntermediateField K E)
    [Algebra V M] [IsScalarTower V K M] [IsScalarTower V M E]
    (Q : Ideal (integralClosure V E)) : Prop :=
  Nat.Coprime
    (Nat.card
      ((normalizationLowerPrime (V := V) (K := K) (E := E) M Q).toAddSubgroup.inertia
        Gal(M/K)))
    (ringExpChar (V ⧸ IsLocalRing.maximalIdeal V))

/-- SGA 1, Expose X, Lemma 3.6, in its inertia-group form over an arbitrary
DVR.  Tameness is expressed intrinsically: at every maximal prime above the
base, each factor inertia order is prime to the fixed exponential residue
characteristic.  If the left inertia order divides the right one, then the
compositum is unramified over the right factor at that prime.

The conclusion also exposes the two surjective inertia restriction maps and
identifies both kernels with their relative inertia groups. -/
theorem abhyankar_for_all_maximalIdeals_of_dvr
    (hsup : M ⊔ N = ⊤)
    (hleftTame : ∀ (Q : Ideal (integralClosure V E)), [Q.IsMaximal] →
      NormalizationInertia.IsTameAt M Q)
    (hrightTame : ∀ (Q : Ideal (integralClosure V E)), [Q.IsMaximal] →
      NormalizationInertia.IsTameAt N Q)
    (hcard : ∀ (Q : Ideal (integralClosure V E)), [Q.IsMaximal] →
      Nat.card
          ((normalizationLowerPrime (V := V) (K := K) (E := E) M Q).toAddSubgroup.inertia
            Gal(M/K)) ∣
        Nat.card
          ((normalizationLowerPrime (V := V) (K := K) (E := E) N Q).toAddSubgroup.inertia
            Gal(N/K)))
    (Q : Ideal (integralClosure V E)) [Q.IsMaximal] :
      Function.Surjective (normalizationInertiaRestriction (V := V) M Q) ∧
      MonoidHom.ker (normalizationInertiaRestriction (V := V) M Q) =
        (idealRelativeInertiaInclusion (Q := Q)
          (normalizationRestrictionHom M)).range ∧
      Function.Surjective (normalizationInertiaRestriction (V := V) N Q) ∧
      MonoidHom.ker (normalizationInertiaRestriction (V := V) N Q) =
        (idealRelativeInertiaInclusion (Q := Q)
          (normalizationRestrictionHom N)).range ∧
      Nat.card
          (Q.toAddSubgroup.inertia
            (normalizationRestrictionHom N).ker) = 1 ∧
      Algebra.IsUnramifiedAt (integralClosure V N) Q := by
  let : IsDedekindDomain (integralClosure V E) :=
    IsIntegralClosure.isDedekindDomain V K E (integralClosure V E)
  let : IsFractionRing (integralClosure V E) E :=
    IsIntegralClosure.isFractionRing_of_finite_extension
      V K E (integralClosure V E)
  have hV : ¬ IsField V := IsDiscreteValuationRing.not_isField V
  let q := ringExpChar (V ⧸ IsLocalRing.maximalIdeal V)
  have hleft : Nat.Coprime
      (Nat.card
        ((normalizationLowerPrime (V := V) (K := K) (E := E) M Q).toAddSubgroup.inertia
          Gal(M/K))) q :=
    hleftTame Q
  have hright : Nat.Coprime
      (Nat.card
        ((normalizationLowerPrime (V := V) (K := K) (E := E) N Q).toAddSubgroup.inertia
          Gal(N/K))) q :=
    hrightTame Q
  have htop : Nat.Coprime
      (Nat.card (Q.toAddSubgroup.inertia Gal(E/K))) q :=
    normalizationTopInertia_card_coprime (V := V) M N hsup Q q hleft hright
  have hleftBase : Nat.Coprime
      (Nat.card
        ((normalizationLowerPrime (V := V) (K := K) (E := E) M Q).toAddSubgroup.inertia
          Gal(M/K)))
      (ringExpChar
        (V ⧸ normalizationBasePrime (V := V) (K := K) (E := E) M Q)) := by
    rw [normalizationBasePrime_eq_maximalIdeal (V := V) M Q]
    exact hleft
  have hrightBase : Nat.Coprime
      (Nat.card
        ((normalizationLowerPrime (V := V) (K := K) (E := E) N Q).toAddSubgroup.inertia
          Gal(N/K)))
      (ringExpChar
        (V ⧸ normalizationBasePrime (V := V) (K := K) (E := E) N Q)) := by
    rw [normalizationBasePrime_eq_maximalIdeal (V := V) N Q]
    exact hright
  have htopLeftBase : Nat.Coprime
      (Nat.card (Q.toAddSubgroup.inertia Gal(E/K)))
      (ringExpChar
        (V ⧸ normalizationBasePrime (V := V) (K := K) (E := E) M Q)) := by
    rw [normalizationBasePrime_eq_maximalIdeal (V := V) M Q]
    exact htop
  have htopRightBase : Nat.Coprime
      (Nat.card (Q.toAddSubgroup.inertia Gal(E/K)))
      (ringExpChar
        (V ⧸ normalizationBasePrime (V := V) (K := K) (E := E) N Q)) := by
    rw [normalizationBasePrime_eq_maximalIdeal (V := V) N Q]
    exact htop
  let : Algebra.IsSeparable
      (V ⧸ normalizationBasePrime (V := V) (K := K) (E := E) M Q)
      (integralClosure V M ⧸
        normalizationLowerPrime (V := V) (K := K) (E := E) M Q) :=
    normalizationLowerResidue_isSeparable_of_inertia_card_coprime
      (V := V) M Q hV hleftBase
  let : Algebra.IsSeparable
      (integralClosure V M ⧸
        normalizationLowerPrime (V := V) (K := K) (E := E) M Q)
      (integralClosure V E ⧸ Q) :=
    normalizationRelativeResidue_isSeparable_of_top_inertia_card_coprime
      (V := V) M Q hV htopLeftBase
  let : Algebra.IsSeparable
      (V ⧸ normalizationBasePrime (V := V) (K := K) (E := E) N Q)
      (integralClosure V N ⧸
        normalizationLowerPrime (V := V) (K := K) (E := E) N Q) :=
    normalizationLowerResidue_isSeparable_of_inertia_card_coprime
      (V := V) N Q hV hrightBase
  let : Algebra.IsSeparable
      (integralClosure V N ⧸
        normalizationLowerPrime (V := V) (K := K) (E := E) N Q)
      (integralClosure V E ⧸ Q) :=
    normalizationRelativeResidue_isSeparable_of_top_inertia_card_coprime
      (V := V) N Q hV htopRightBase
  have htopResidue : Nat.Coprime
      (Nat.card (Q.toAddSubgroup.inertia Gal(E/K)))
      (ringExpChar (integralClosure V E ⧸ Q)) := by
    rw [← normalizationBase_ringExpChar_eq_top (V := V) Q]
    exact htop
  let hVE : Module.IsTorsionFree V E :=
    Module.IsTorsionFree.trans_faithfulSMul V K E
  let : Module.IsTorsionFree V (integralClosure V E) :=
    @IsIntegralClosure.isTorsionFree
      V (integralClosure V E) E _ _ _ _ _ _ _
      (topNormalizationToFractionFieldTower (V := V) (E := E)) hVE
  have hQ0 : Q ≠ ⊥ := by
    let : Q.LiesOver
        (normalizationBasePrime (V := V) (K := K) (E := E) M Q) :=
      Ideal.LiesOver.trans Q
        (normalizationLowerPrime (V := V) (K := K) (E := E) M Q)
        (normalizationBasePrime (V := V) (K := K) (E := E) M Q)
    have hbase :
        normalizationBasePrime (V := V) (K := K) (E := E) M Q ≠ ⊥ :=
      Ring.ne_bot_of_isMaximal_of_not_isField
        (normalizationBasePrime_isMaximal (V := V) M Q) hV
    exact Ideal.ne_bot_of_liesOver_of_ne_bot hbase Q
  let : IsCyclic (Q.toAddSubgroup.inertia Gal(E/K)) :=
    idealInertia_isCyclic_of_card_coprime_ringExpChar
      (A := V) (K := K) (L := E) Q hQ0 htopResidue
  have hleftSurjective :
      Function.Surjective (normalizationInertiaRestriction (V := V) M Q) :=
    normalizationInertiaRestriction_surjective (V := V) M Q hV
  have hrightSurjective :
      Function.Surjective (normalizationInertiaRestriction (V := V) N Q) :=
    normalizationInertiaRestriction_surjective (V := V) N Q hV
  have hrelative :=
    normalizationRelativeInertia_card_eq_one_and_isUnramifiedAt
      (V := V) M N hsup Q hV (hcard Q)
  exact
    ⟨hleftSurjective,
      normalizationInertiaRestriction_ker_eq_range_relative (V := V) M Q,
      hrightSurjective,
      normalizationInertiaRestriction_ker_eq_range_relative (V := V) N Q,
      hrelative.1, hrelative.2⟩

/-- The unramifiedness-only form of Abhyankar's lemma.  Its conclusion is
explicitly quantified over every maximal ideal, hence over every
localization of the right-hand normalization. -/
theorem abhyankar_isUnramifiedAt_all_maximalIdeals_of_dvr
    (hsup : M ⊔ N = ⊤)
    (hleftTame : ∀ (Q : Ideal (integralClosure V E)), [Q.IsMaximal] →
      NormalizationInertia.IsTameAt M Q)
    (hrightTame : ∀ (Q : Ideal (integralClosure V E)), [Q.IsMaximal] →
      NormalizationInertia.IsTameAt N Q)
    (hcard : ∀ (Q : Ideal (integralClosure V E)), [Q.IsMaximal] →
      Nat.card
          ((normalizationLowerPrime (V := V) (K := K) (E := E) M Q).toAddSubgroup.inertia
            Gal(M/K)) ∣
        Nat.card
          ((normalizationLowerPrime (V := V) (K := K) (E := E) N Q).toAddSubgroup.inertia
            Gal(N/K))) :
    ∀ (Q : Ideal (integralClosure V E)), [Q.IsMaximal] →
      Algebra.IsUnramifiedAt (integralClosure V N) Q := by
  intro Q _
  exact
    (abhyankar_for_all_maximalIdeals_of_dvr
      (V := V) M N hsup hleftTame hrightTame hcard Q).2.2.2.2.2

/-- SGA 1's localization formulation: for every maximal ideal `P` of the
right-hand normalization and every maximal ideal `Q` of the compositum
normalization lying over it, the localized extension is unramified at `Q`. -/
theorem abhyankar_isUnramifiedAt_all_localizations_of_dvr
    (hsup : M ⊔ N = ⊤)
    (hleftTame : ∀ (Q : Ideal (integralClosure V E)), [Q.IsMaximal] →
      NormalizationInertia.IsTameAt M Q)
    (hrightTame : ∀ (Q : Ideal (integralClosure V E)), [Q.IsMaximal] →
      NormalizationInertia.IsTameAt N Q)
    (hcard : ∀ (Q : Ideal (integralClosure V E)), [Q.IsMaximal] →
      Nat.card
          ((normalizationLowerPrime (V := V) (K := K) (E := E) M Q).toAddSubgroup.inertia
            Gal(M/K)) ∣
        Nat.card
          ((normalizationLowerPrime (V := V) (K := K) (E := E) N Q).toAddSubgroup.inertia
            Gal(N/K))) :
    ∀ (P : Ideal (integralClosure V N)), [P.IsMaximal] →
      ∀ (Q : Ideal (integralClosure V E)), [Q.IsMaximal] →
        [Q.LiesOver P] → Algebra.IsUnramifiedAt (integralClosure V N) Q := by
  intro _ _ Q _ _
  exact abhyankar_isUnramifiedAt_all_maximalIdeals_of_dvr
    (V := V) M N hsup hleftTame hrightTame hcard Q

end TameAbhyankar.SGA1

end
