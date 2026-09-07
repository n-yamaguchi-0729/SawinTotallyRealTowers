import SawinTotallyRealTowers.AbsoluteCharacterRealValue
import SawinTotallyRealTowers.AbsoluteRealKernelField
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FinitePlaceH2Localization
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FinitePlaceUnramifiedH1
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.EmptySupportKummerCokernel
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.FinitePlaceH1AdicRestriction
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.FiniteSupportInertiaCorrection
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.FiniteSupportLocalReciprocityIdeleCharacter
import ProCGroups.ProP.ContinuousH1
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.PNat.Basic
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Instances.ZMod

set_option autoImplicit false

/-!
# Real values and prescribed finite inertia over the rationals

The finite-support radical kernel constructs an absolute quadratic character
with the prescribed inertia values. Multiplication by the character of
negative three then gives any specified real value while preserving inertia
outside an allowed ramification set containing three.
-/

open NumberField IsDedekindDomain
open scoped NumberField

namespace ClassFieldTower.Sawin

open ClassFieldTower.Martinet.Shafarevich ClassFieldTower.ProP

/-- Realize a finite local family in the radical kernel, with a prescribed
real value and unchanged inertia outside a set containing three. -/
theorem exists_absoluteCharacter_with_real_value_of_radical_annihilator
    (T : Set (HeightOneSpectrum (𝓞 ℚ)))
    (hThree : (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm
      (⟨3, Nat.prime_three⟩ : Nat.Primes) ∈ T)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (chi : ∀ v : ↥S, finitePlaceAbsoluteDecompositionGroup ℚ v.1 →ₜ*
      Multiplicative (ZMod 2))
    (hchi : absolutePowerClassDualRestriction ℚ 2
      (finiteSupportLocalReciprocityPowerClassFunctional ℚ 2 S
        (fun v => finitePlaceDecompositionH1ToAdic ℚ 2 v.1
          (h1OfCharacter (chi v)))) = 0)
    (ε : Multiplicative (ZMod 2)) :
    ∃ gamma : Field.absoluteGaloisGroup ℚ →ₜ* Multiplicative (ZMod 2),
      (∀ v : InfinitePlace ℚ,
        gamma (absoluteInfinitePlaceArtinNegOne ℚ v) = ε) ∧
      (∀ (v : ↥S), v.1 ∉ T →
        ∀ sigma : finitePlaceAbsoluteInertiaSubgroup ℚ v.1,
          chi v sigma.1 =
            gamma (finitePlaceAbsoluteDecompositionInclusion ℚ v.1 sigma.1)) ∧
      (∀ (v : HeightOneSpectrum (𝓞 ℚ)), v ∉ S → v ∉ T →
        ∀ sigma : finitePlaceAbsoluteInertiaSubgroup ℚ v,
          gamma (finitePlaceAbsoluteDecompositionInclusion ℚ v sigma.1) = 1) := by
  obtain ⟨gamma, hInside, hOutside⟩ :=
    exists_absoluteCharacter_of_finiteSupport_radical_annihilator
      ℚ (2 : ℕ+) S chi hchi
  refine ⟨absoluteCharacterWithRealValue gamma ε,
    absoluteCharacterWithRealValue_infinite gamma ε, ?_, ?_⟩
  · intro v hv sigma
    have hNe : v.1 ≠ (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm
        (⟨3, Nat.prime_three⟩ : Nat.Primes) := by
      intro h
      exact hv (h.symm ▸ hThree)
    have hValue : absoluteCharacterWithRealValue gamma ε
        (finitePlaceAbsoluteDecompositionInclusion ℚ v.1 sigma.1) =
        gamma (finitePlaceAbsoluteDecompositionInclusion ℚ v.1 sigma.1) :=
      absoluteCharacterWithRealValue_inertia gamma ε v.1 hNe sigma
    exact (hInside v sigma).trans hValue.symm
  · intro v hv hT sigma
    have hNe : v ≠ (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm
        (⟨3, Nat.prime_three⟩ : Nat.Primes) := by
      intro h
      exact hT (h.symm ▸ hThree)
    have hValue : absoluteCharacterWithRealValue gamma ε
        (finitePlaceAbsoluteDecompositionInclusion ℚ v sigma.1) =
        gamma (finitePlaceAbsoluteDecompositionInclusion ℚ v sigma.1) :=
      absoluteCharacterWithRealValue_inertia gamma ε v hNe sigma
    exact hValue.trans (hOutside v hv sigma)

end ClassFieldTower.Sawin
