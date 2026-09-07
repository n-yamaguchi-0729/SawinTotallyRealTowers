import SawinTotallyRealTowers.SixPrimeSupport
import Mathlib.Data.Finset.Card

set_option autoImplicit false
/-!
# Finite coordinates for the six-prime support

The finite set of allowed places is the actual six-prime support, with
cardinality six. It provides the coordinate set used by H² localization.
-/

open scoped NumberField
open IsDedekindDomain

namespace ClassFieldTower.Sawin

private def sixAllowedPrimes : Finset Nat.Primes :=
  {⟨3, by decide⟩, ⟨5, by decide⟩, ⟨7, by decide⟩,
    ⟨11, by decide⟩, ⟨13, by decide⟩, ⟨17, by decide⟩}

/-- The six allowed finite places as a finite coordinate set. -/
noncomputable def sawinFinitePrimeSupport : Finset (HeightOneSpectrum (𝓞 ℚ)) :=
  sixAllowedPrimes.map (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm.toEmbedding

/-- Finite-set and set-valued versions of the ramification support agree. -/
theorem mem_sawinFinitePrimeSupport_iff (v : HeightOneSpectrum (𝓞 ℚ)) :
    v ∈ sawinFinitePrimeSupport ↔ v ∈ sawinRationalPrimeSupport := by
  rw [sawinFinitePrimeSupport, Finset.mem_map_equiv]
  change Rat.HeightOneSpectrum.primesEquiv v ∈ sixAllowedPrimes ↔
    (Rat.HeightOneSpectrum.primesEquiv v : ℕ) ∈ sawinRationalPrimes
  let e : Nat.Primes ↪ ℕ := ⟨Subtype.val, Subtype.val_injective⟩
  have hm : sixAllowedPrimes.map e = sawinRationalPrimes := by decide
  rw [← hm]
  exact (Finset.mem_map' e).symm

/-- There are precisely six finite coordinates in the allowed support. -/
theorem sawinFinitePrimeSupport_card : sawinFinitePrimeSupport.card = 6 := by
  rw [sawinFinitePrimeSupport, Finset.card_map]
  decide

end ClassFieldTower.Sawin
