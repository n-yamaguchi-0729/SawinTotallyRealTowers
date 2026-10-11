/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.RingFiniteTameCharacter
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.RingInertiaCharacterFixedElement
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.DVRRamificationOrder
import Mathlib.Algebra.Algebra.Defs

/-!
# Tame orders and ramification indices

Proves that the finite tame order is invertible in the residue field and divides the valuation
of every nonzero fixed element. It consequently divides the ramification index of an injective
DVR algebra with a compatible action.
-/

noncomputable section

namespace RamificationTheory.HilbertRamification.DiscreteValuationRing

open IsLocalRing

universe u v w

section OneRing

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (G : Type v) [Group G] [Finite G] [MulSemiringAction G R]

/-- An actual finite tame degree is invertible in the actual residue field. -/
theorem tameOrder_isUnit_residue : IsUnit (tameOrder R G : ResidueField R) := by
  have : NeZero (tameOrder R G) := ⟨(tameOrder_pos R G).ne'⟩
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_tameOrder R G
  exact isUnit_iff_ne_zero.mpr hζ.neZero'.out

/-- Every actual nonzero fixed ring element has order divisible by the tame degree. -/
theorem tameOrder_dvd_addVal_of_fixed (x : R) (hx : x ≠ 0)
    (hfixed : ∀ g : G, g • x = x) :
    tameOrder R G ∣ (IsDiscreteValuationRing.addVal R x).toNat := by
  have : NeZero (tameOrder R G) := ⟨(tameOrder_pos R G).ne'⟩
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_tameOrder R G
  obtain ⟨σ, hσ⟩ := tameCharacter_surjective R G hζ.toRootsOfUnity
  have hζσ : (inertiaResidueCharacter R G σ : ResidueField R) = ζ :=
    congrArg (fun a : rootsOfUnity (tameOrder R G) (ResidueField R) =>
      ((a : (ResidueField R)ˣ) : ResidueField R)) hσ
  have hpow := inertiaResidueCharacter_pow_addVal_eq_one_of_fixed R G σ x hx (hfixed σ)
  have hpowRes := congrArg (fun a : (ResidueField R)ˣ => (a : ResidueField R)) hpow
  change (inertiaResidueCharacter R G σ : ResidueField R) ^
    (IsDiscreteValuationRing.addVal R x).toNat = 1 at hpowRes
  rw [hζσ] at hpowRes
  exact hζ.dvd_of_pow_eq_one _ hpowRes

end OneRing

/-- The actual tame degree divides the actual ramification index of an
injective DVR algebra on which the group acts over the base. The group/residue
calculation and the two-ring valuation comparison are closed separate suppliers. -/
theorem tameOrder_dvd_ramificationIdx
    (A : Type u) (R : Type v)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Algebra A R]
    [(maximalIdeal R).LiesOver (maximalIdeal A)]
    (G : Type w) [Group G] [Finite G] [MulSemiringAction G R] [SMulCommClass G A R]
    (hinj : Function.Injective (algebraMap A R)) :
    tameOrder R G ∣ (maximalIdeal R).ramificationIdx A := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  rw [ramificationIdx_eq_addVal_uniformizer A R hinj π hπ]
  have hx : algebraMap A R π ≠ 0 := fun h =>
    hπ.ne_zero (hinj (h.trans (map_zero (algebraMap A R)).symm))
  exact tameOrder_dvd_addVal_of_fixed R G (algebraMap A R π) hx
    (fun g => smul_algebraMap g π)

end RamificationTheory.HilbertRamification.DiscreteValuationRing

end
