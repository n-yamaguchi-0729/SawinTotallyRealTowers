import SawinTotallyRealTowers.RamificationSupportTransport
import ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.CompositumUnramified
import Mathlib.FieldTheory.Galois.GaloisClosure

set_option autoImplicit false

/-!
# Composita with prescribed finite ramification support

Inertia at a prime outside the permitted support is trivial on each factor.
The restrictions to the factors jointly detect automorphisms of their
compositum. This argument does not require an odd extension degree.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

universe u v

namespace ClassFieldTower.Sawin

private local instance finiteIntermediateFieldNumberField
    {K : Type u} {Omega : Type v}
    [Field K] [NumberField K] [Field Omega] [Algebra K Omega]
    (E : IntermediateField K Omega) [FiniteDimensional K E] : NumberField E :=
  NumberField.of_module_finite K E

/-- The support condition kills inertia in a normal intermediate field at
every prime above a base prime outside the support. -/
private theorem inertia_eq_bot_of_outside
    {K : Type u} {M : Type v}
    [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] [FiniteDimensional K M]
    (A : IntermediateField K M) [IsGalois K A]
    (T : Set (HeightOneSpectrum (𝓞 K)))
    (hA : IsUnramifiedAtFinitePlacesOutside K A T)
    (Q : HeightOneSpectrum (𝓞 M))
    (hQ : finitePlaceBelow (K := K) Q ∉ T) :
    HilbertRamification.Dedekind.inertiaGroup
      (Q.asIdeal.under (𝓞 A)) (A ≃ₐ[K] A) = ⊥ := by
  let P : HeightOneSpectrum (𝓞 A) := finitePlaceBelow (K := A) Q
  let : P.asIdeal.IsPrime := P.isPrime
  let : P.asIdeal.IsMaximal := P.isPrime.isMaximal P.ne_bot
  have hP : finitePlaceBelow (K := K) P ∉ T := by
    simpa only [P, finitePlaceBelow_finitePlaceBelow] using hQ
  exact HilbertRamification.Dedekind.inertiaGroup_eq_bot_of_isUnramifiedAt
    (K := K) (M := A) P.asIdeal (hA P hP)

namespace IsUnramifiedAtFinitePlacesOutside

/-- Finite Galois composita preserve the permitted ramification support. -/
theorem sup
    {K : Type u} {Omega : Type v}
    [Field K] [NumberField K] [Field Omega] [Algebra K Omega]
    (E₁ E₂ : IntermediateField K Omega)
    [FiniteDimensional K E₁] [FiniteDimensional K E₂]
    [IsGalois K E₁] [IsGalois K E₂]
    (T : Set (HeightOneSpectrum (𝓞 K)))
    (h₁ : IsUnramifiedAtFinitePlacesOutside K E₁ T)
    (h₂ : IsUnramifiedAtFinitePlacesOutside K E₂ T) :
    IsUnramifiedAtFinitePlacesOutside K ↥(E₁ ⊔ E₂) T := by
  let L : IntermediateField K Omega := E₁ ⊔ E₂
  let A : IntermediateField K L := IntermediateField.restrict
    (show E₁ ≤ E₁ ⊔ E₂ from le_sup_left)
  let B : IntermediateField K L := IntermediateField.restrict
    (show E₂ ≤ E₁ ⊔ E₂ from le_sup_right)
  let eA : E₁ ≃ₐ[K] A := IntermediateField.restrictAlgEquiv
    (show E₁ ≤ E₁ ⊔ E₂ from le_sup_left)
  let eB : E₂ ≃ₐ[K] B := IntermediateField.restrictAlgEquiv
    (show E₂ ≤ E₁ ⊔ E₂ from le_sup_right)
  let : FiniteDimensional K L := IntermediateField.finiteDimensional_sup E₁ E₂
  let : NumberField L := NumberField.of_module_finite K L
  let : IsGalois K L := inferInstanceAs (IsGalois K ↥(E₁ ⊔ E₂))
  let : IsGalois K A := IsGalois.of_algEquiv eA
  let : IsGalois K B := IsGalois.of_algEquiv eB
  have hA : IsUnramifiedAtFinitePlacesOutside K A T := congrTop eA h₁
  have hB : IsUnramifiedAtFinitePlacesOutside K B T := congrTop eB h₂
  have hSup : A ⊔ B = ⊤ := by
    apply IntermediateField.lift_injective L
    rw [IntermediateField.lift_sup, IntermediateField.lift_restrict,
      IntermediateField.lift_restrict, IntermediateField.lift_top]
  intro Q hQ
  let : Q.asIdeal.IsPrime := Q.isPrime
  let : Q.asIdeal.IsMaximal := Q.isPrime.isMaximal Q.ne_bot
  apply HilbertRamification.Dedekind.isUnramifiedAt_of_inertiaGroup_eq_bot
    (K := K) (M := L) Q.asIdeal
  exact HilbertRamification.Dedekind.inertiaGroup_eq_bot_of_restrictNormal_of_sup_eq_top
    A B Q.asIdeal hSup
    (inertia_eq_bot_of_outside A T hA Q hQ)
    (inertia_eq_bot_of_outside B T hB Q hQ)

end IsUnramifiedAtFinitePlacesOutside

end ClassFieldTower.Sawin
