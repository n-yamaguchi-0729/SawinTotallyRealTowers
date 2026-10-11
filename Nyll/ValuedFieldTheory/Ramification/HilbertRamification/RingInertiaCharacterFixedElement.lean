/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Ring.Action.Basic
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.RingInertiaCharacter
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Tactic.Ring

/-!
# Fixed elements and powers of the inertia character

Proves that fixing a unit times a uniformizer power makes the same power of the inertia
character trivial. It deduces the corresponding result using the additive valuation of a nonzero
fixed element.
-/

noncomputable section

namespace RamificationTheory.HilbertRamification.DiscreteValuationRing

open IsLocalRing

universe u v

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (G : Type v) [Group G] [MulSemiringAction G R]

/-- Fixing a unit times a uniformizer power annihilates the same power of the
actual residue character. The ratio calculation has no additive valuation in scope. -/
theorem inertiaResidueCharacter_pow_eq_one_of_fixed_factor
    (π : R) (hπ : Irreducible π) (σ : (maximalIdeal R).inertia G)
    (n : ℕ) (u : Rˣ)
    (hfixed : (σ : G) • ((u : R) * π ^ n) = (u : R) * π ^ n) :
    inertiaResidueCharacter R G σ ^ n = 1 := by
  let c : Rˣ := uniformizerRatioUnit R G π hπ (σ : G)
  let gu : Rˣ := Units.map
    (MulSemiringAction.toRingHom G R (σ : G)).toMonoidHom u
  have hc : π * (c : R) = (σ : G) • π := uniformizerRatioUnit_spec R G π hπ (σ : G)
  have hunit : gu * c ^ n = u := by
    apply Units.ext
    apply mul_left_cancel₀ (pow_ne_zero n hπ.ne_zero)
    calc
      _ = ((σ : G) • (u : R)) * (π * (c : R)) ^ n := by
        change π ^ n * (((σ : G) • (u : R)) * (c : R) ^ n) =
          ((σ : G) • (u : R)) * (π * (c : R)) ^ n
        rw [mul_pow]
        ring
      _ = (σ : G) • ((u : R) * π ^ n) := by
        rw [smul_mul', smul_pow', hc]
      _ = (u : R) * π ^ n := hfixed
      _ = _ := mul_comm _ _
  let f : Rˣ →* (ResidueField R)ˣ := Units.map (residue R).toMonoidHom
  have hgu : f gu = f u := inertia_residueUnits_fixed R G σ u
  have hres := congrArg f hunit
  rw [map_mul, map_pow, hgu] at hres
  have hpow : (f c) ^ n = 1 :=
    mul_left_cancel (hres.trans (mul_one (f u)).symm)
  rw [inertiaResidueCharacter_eq_uniformizer R G π hπ]
  exact hpow

/-- The order of every nonzero fixed element annihilates the actual inertia
character. The valuation comparison is separate from the ratio calculation. -/
theorem inertiaResidueCharacter_pow_addVal_eq_one_of_fixed
    (σ : (maximalIdeal R).inertia G) (x : R) (hx : x ≠ 0)
    (hfixed : (σ : G) • x = x) :
    inertiaResidueCharacter R G σ ^ (IsDiscreteValuationRing.addVal R x).toNat = 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hπ
  have hv : IsDiscreteValuationRing.addVal R x = (n : ℕ∞) :=
    IsDiscreteValuationRing.addVal_def x u hπ n hu
  rw [hv, ENat.toNat_natCast]
  apply inertiaResidueCharacter_pow_eq_one_of_fixed_factor R G π hπ σ n u
  rw [← hu]
  exact hfixed

end RamificationTheory.HilbertRamification.DiscreteValuationRing

end
