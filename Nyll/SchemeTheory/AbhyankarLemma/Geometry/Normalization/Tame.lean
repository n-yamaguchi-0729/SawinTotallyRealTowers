/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.AbhyankarLemma.Geometry.GroupTheory.CoprimeProjection
import Nyll.SchemeTheory.AbhyankarLemma.Geometry.Inertia.FieldCompositum
import Nyll.SchemeTheory.AbhyankarLemma.Geometry.Normalization.Inertia

/-!
# Tameness at a prime of a normalization compositum

The inertia group at a prime of a compositum embeds in the product of the
two factor inertia groups.  Consequently, prime-to-residue-characteristic
tameness of both factors propagates to the compositum, prime by prime.
-/

noncomputable section

universe uV uK uE

namespace TameAbhyankar.SGA1

variable {V : Type uV} {K : Type uK} {E : Type uE}
variable [CommRing V] [Field K] [Field E]
variable [Algebra V K] [IsFractionRing V K]
variable [Algebra K E] [Algebra V E] [IsScalarTower V K E]
variable [IsDedekindDomain V] [FiniteDimensional K E] [IsGalois K E]

variable (M N : IntermediateField K E)
variable [Normal K M] [Normal K N]
variable [Algebra V M] [IsScalarTower V K M] [IsScalarTower V M E]
variable [Algebra V N] [IsScalarTower V K N] [IsScalarTower V N E]

noncomputable local instance normalizationTameTopAction :
    MulSemiringAction Gal(E/K) (integralClosure V E) :=
  IsIntegralClosure.MulSemiringAction V K E (integralClosure V E)

noncomputable local instance normalizationTameLeftAction :
    MulSemiringAction Gal(M/K) (integralClosure V M) :=
  IsIntegralClosure.MulSemiringAction V K M (integralClosure V M)

noncomputable local instance normalizationTameRightAction :
    MulSemiringAction Gal(N/K) (integralClosure V N) :=
  IsIntegralClosure.MulSemiringAction V K N (integralClosure V N)

omit [IsDedekindDomain V] in
/-- At every prime of the top normalization, the top inertia order is prime
to `p` if the inertia orders at both contractions are prime to `p`. -/
theorem normalizationTopInertia_card_coprime
    (hsup : M ⊔ N = ⊤)
    (Q : Ideal (integralClosure V E))
    (p : ℕ)
    (hleft : Nat.Coprime
      (Nat.card
        ((normalizationLowerPrime (V := V) (K := K) (E := E) M Q).toAddSubgroup.inertia
          Gal(M/K))) p)
    (hright : Nat.Coprime
      (Nat.card
        ((normalizationLowerPrime (V := V) (K := K) (E := E) N Q).toAddSubgroup.inertia
          Gal(N/K))) p) :
    Nat.Coprime
      (Nat.card (Q.toAddSubgroup.inertia Gal(E/K))) p := by
  let : Algebra.IsSeparable K M :=
    Algebra.isSeparable_tower_bot_of_isSeparable (F := K) M E
  let : Algebra.IsSeparable K N :=
    Algebra.isSeparable_tower_bot_of_isSeparable (F := K) N E
  let : IsGalois K M := isGalois_iff.mpr ⟨inferInstance, inferInstance⟩
  let : IsGalois K N := isGalois_iff.mpr ⟨inferInstance, inferInstance⟩
  let : Finite Gal(E/K) := IsGaloisGroup.finite Gal(E/K) K E
  let : Finite Gal(M/K) := IsGaloisGroup.finite Gal(M/K) K M
  let : Finite Gal(N/K) := IsGaloisGroup.finite Gal(N/K) K N
  let toLeft := normalizationInertiaRestriction (V := V) M Q
  let toRight := normalizationInertiaRestriction (V := V) N Q
  have hambient : Function.Injective
      ((normalizationRestrictionHom M).prod
        (normalizationRestrictionHom N)) := by
    simpa only [normalizationRestrictionHom] using
      restrictNormalHom_prod_injective_of_sup_eq_top K M N hsup
  have hjoint : Function.Injective (toLeft.prod toRight) := by
    intro sigma tau h
    apply Subtype.ext
    apply hambient
    apply Prod.ext
    · exact congrArg (fun z ↦ ((z.1 : Gal(M/K)))) h
    · exact congrArg (fun z ↦ ((z.2 : Gal(N/K)))) h
  exact card_coprime_of_prod_injective toLeft toRight hjoint p hleft hright

end TameAbhyankar.SGA1
