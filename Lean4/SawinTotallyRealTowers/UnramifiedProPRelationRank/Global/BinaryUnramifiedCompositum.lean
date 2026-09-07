import SawinTotallyRealTowers.UnramifiedProPRelationRank.Global.EverywhereUnramifiedBridge
import ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.CompositumUnramified
import Mathlib.FieldTheory.Galois.GaloisClosure

set_option autoImplicit false
/-!
# Binary everywhere-unramified composita

This file proves that the compositum of two finite Galois number-field
extensions unramified at finite places is again unramified at finite places.
An odd-degree hypothesis on the compositum then supplies the infinite-place
condition.
-/

open scoped NumberField

noncomputable section

universe u v

namespace ClassFieldTower.Martinet

private local instance finiteIntermediateFieldNumberField
    {K : Type u} {Omega : Type v}
    [Field K] [NumberField K]
    [Field Omega] [Algebra K Omega]
    (E : IntermediateField K Omega) [FiniteDimensional K E] :
    NumberField E :=
  NumberField.of_module_finite K E

/-- The two restricted factors generate their compositum. -/
private theorem restrict_left_sup_restrict_right_eq_top
    {K : Type u} {Omega : Type v}
    [Field K] [Field Omega] [Algebra K Omega]
    (E₁ E₂ : IntermediateField K Omega) :
    IntermediateField.restrict
          (show E₁ ≤ E₁ ⊔ E₂ from le_sup_left) ⊔
        IntermediateField.restrict
          (show E₂ ≤ E₁ ⊔ E₂ from le_sup_right) = ⊤ := by
  apply IntermediateField.lift_injective (E₁ ⊔ E₂)
  rw [IntermediateField.lift_sup,
    IntermediateField.lift_restrict,
    IntermediateField.lift_restrict,
    IntermediateField.lift_top]

/-- The compositum of two finite Galois extensions unramified at every finite
place is again unramified at every finite place. -/
theorem finitePlaceUnramifiedness_sup
    {K : Type u} {Omega : Type v}
    [Field K] [NumberField K]
    [Field Omega] [Algebra K Omega]
    (E₁ E₂ : IntermediateField K Omega)
    [FiniteDimensional K E₁] [FiniteDimensional K E₂]
    [IsGalois K E₁] [IsGalois K E₂]
    (h₁ : IsUnramifiedAtFinitePlaces K E₁)
    (h₂ : IsUnramifiedAtFinitePlaces K E₂) :
    IsUnramifiedAtFinitePlaces K ↥(E₁ ⊔ E₂) := by
  let S : IntermediateField K Omega := E₁ ⊔ E₂
  let A : IntermediateField K S :=
    IntermediateField.restrict
      (show E₁ ≤ E₁ ⊔ E₂ from le_sup_left)
  let B : IntermediateField K S :=
    IntermediateField.restrict
      (show E₂ ≤ E₁ ⊔ E₂ from le_sup_right)
  let eA : E₁ ≃ₐ[K] A :=
    IntermediateField.restrictAlgEquiv
      (show E₁ ≤ E₁ ⊔ E₂ from le_sup_left)
  let eB : E₂ ≃ₐ[K] B :=
    IntermediateField.restrictAlgEquiv
      (show E₂ ≤ E₁ ⊔ E₂ from le_sup_right)
  let hFiniteS : FiniteDimensional K S :=
    IntermediateField.finiteDimensional_sup E₁ E₂
  let _ := hFiniteS
  let hNumberS : NumberField S :=
    NumberField.of_module_finite K S
  let _ := hNumberS
  let hGaloisS : IsGalois K S := inferInstance
  let _ := hGaloisS
  let hGaloisA : IsGalois K A := IsGalois.of_algEquiv eA
  let _ := hGaloisA
  let hGaloisB : IsGalois K B := IsGalois.of_algEquiv eB
  let _ := hGaloisB
  have hA : IsUnramifiedAtFinitePlaces K A :=
    finitePlaceUnramifiedness_congrTop eA h₁
  have hB : IsUnramifiedAtFinitePlaces K B :=
    finitePlaceUnramifiedness_congrTop eB h₂
  intro Q
  let hQPrime : Q.asIdeal.IsPrime := Q.isPrime
  let _ := hQPrime
  let hQMaximal : Q.asIdeal.IsMaximal :=
    hQPrime.isMaximal Q.ne_bot
  let _ := hQMaximal
  apply
    HilbertRamification.Dedekind.isUnramifiedAt_of_inertiaGroup_eq_bot
      Q.asIdeal
  apply
    HilbertRamification.Dedekind.inertiaGroup_eq_bot_of_restrictNormal_of_sup_eq_top
      A B Q.asIdeal
      (restrict_left_sup_restrict_right_eq_top E₁ E₂)
  · let QA : Ideal (𝓞 A) := Q.asIdeal.under (𝓞 A)
    have hQA0 : QA ≠ ⊥ :=
      Ideal.under_ne_bot (𝓞 A) Q.ne_bot
    let hQAPrime : QA.IsPrime := inferInstance
    let _ := hQAPrime
    let hQAMaximal : QA.IsMaximal :=
      hQAPrime.isMaximal hQA0
    let _ := hQAMaximal
    apply
      HilbertRamification.Dedekind.inertiaGroup_eq_bot_of_isUnramifiedAt
    exact hA
      { asIdeal := QA
        isPrime := hQAPrime
        ne_bot := hQA0 }
  · let QB : Ideal (𝓞 B) := Q.asIdeal.under (𝓞 B)
    have hQB0 : QB ≠ ⊥ :=
      Ideal.under_ne_bot (𝓞 B) Q.ne_bot
    let hQBPrime : QB.IsPrime := inferInstance
    let _ := hQBPrime
    let hQBMaximal : QB.IsMaximal :=
      hQBPrime.isMaximal hQB0
    let _ := hQBMaximal
    apply
      HilbertRamification.Dedekind.inertiaGroup_eq_bot_of_isUnramifiedAt
    exact hB
      { asIdeal := QB
        isPrime := hQBPrime
        ne_bot := hQB0 }

/-- If the finite Galois compositum has odd degree, then finite-place
unramifiedness of both factors makes the compositum everywhere unramified. -/
theorem everywhereUnramified_sup_of_odd_finrank
    {K : Type u} {Omega : Type v}
    [Field K] [NumberField K]
    [Field Omega] [Algebra K Omega]
    (E₁ E₂ : IntermediateField K Omega)
    [FiniteDimensional K E₁] [FiniteDimensional K E₂]
    [IsGalois K E₁] [IsGalois K E₂]
    (h₁ : IsEverywhereUnramified K E₁)
    (h₂ : IsEverywhereUnramified K E₂)
    (hOdd : Odd (Module.finrank K ↥(E₁ ⊔ E₂))) :
    IsEverywhereUnramified K ↥(E₁ ⊔ E₂) := by
  let hFinite : FiniteDimensional K ↥(E₁ ⊔ E₂) :=
    IntermediateField.finiteDimensional_sup E₁ E₂
  let _ := hFinite
  let hNumber : NumberField ↥(E₁ ⊔ E₂) :=
    NumberField.of_module_finite K ↥(E₁ ⊔ E₂)
  let _ := hNumber
  let hGalois : IsGalois K ↥(E₁ ⊔ E₂) := inferInstance
  let _ := hGalois
  exact everywhereUnramified_of_finitePlaces_of_infinitePlaces
    (finitePlaceUnramifiedness_sup E₁ E₂
      h₁.finitePlaces h₂.finitePlaces)
    (IsUnramifiedAtInfinitePlaces_of_odd_finrank hOdd)

end ClassFieldTower.Martinet
