/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.Ideal.Span

/-!
# Ramification indices as uniformizer orders

Identifies both ideal ramification-index conventions with the additive valuation of a mapped
base uniformizer for an injective map of discrete valuation rings.
-/

namespace RamificationTheory.HilbertRamification.DiscreteValuationRing

open IsLocalRing

universe u v

variable (A : Type u) (B : Type v)
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]

/-- The literal maximal-ideal ramification index is the additive order of the
actual mapped base uniformizer. The comparison uses no group or residue field. -/
theorem ramificationIdx'_eq_addVal_uniformizer
    (hinj : Function.Injective (algebraMap A B)) (π : A) (hπ : Irreducible π) :
    Ideal.ramificationIdx' (maximalIdeal A) (maximalIdeal B) =
      (IsDiscreteValuationRing.addVal B (algebraMap A B π)).toNat := by
  have hx : algebraMap A B π ≠ 0 := fun h =>
    hπ.ne_zero (hinj (h.trans (map_zero (algebraMap A B)).symm))
  obtain ⟨ρ, hρ⟩ := IsDiscreteValuationRing.exists_irreducible B
  obtain ⟨n, unit, hfactor⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hρ
  have hmap : Ideal.map (algebraMap A B) (maximalIdeal A) = (maximalIdeal B) ^ n := by
    rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, hfactor,
      Ideal.span_singleton_mul_left_unit unit.isUnit, hρ.maximalIdeal_eq,
      Ideal.span_singleton_pow]
  have hnot : ¬ Ideal.map (algebraMap A B) (maximalIdeal A) ≤
      (maximalIdeal B) ^ (n + 1) := by
    rw [hmap]
    exact not_le_of_gt
      (Ideal.pow_succ_lt_pow (IsDiscreteValuationRing.not_a_field B) n)
  have he : Ideal.ramificationIdx' (maximalIdeal A) (maximalIdeal B) = n :=
    Ideal.ramificationIdx'_spec hmap.le hnot
  rw [he, IsDiscreteValuationRing.addVal_def (algebraMap A B π) unit hρ n hfactor,
    ENat.toNat_natCast]

/-- The current ideal ramification index has the same actual uniformizer order. -/
theorem ramificationIdx_eq_addVal_uniformizer
    [(maximalIdeal B).LiesOver (maximalIdeal A)]
    (hinj : Function.Injective (algebraMap A B)) (π : A) (hπ : Irreducible π) :
    (maximalIdeal B).ramificationIdx A =
      (IsDiscreteValuationRing.addVal B (algebraMap A B π)).toNat := by
  have hmap0 : Ideal.map (algebraMap A B) (maximalIdeal A) ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective hinj).not.mpr
      (IsDiscreteValuationRing.not_a_field A)
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx'
    (maximalIdeal A) (maximalIdeal B) hmap0]
  exact ramificationIdx'_eq_addVal_uniformizer A B hinj π hπ

end RamificationTheory.HilbertRamification.DiscreteValuationRing
