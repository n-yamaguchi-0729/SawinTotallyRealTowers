/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.DVRRamificationOrder

/-!
# Factorization of mapped uniformizers

Factors a mapped uniformizer into a target uniformizer power and a unit, with exponent given by
its additive valuation. For a local DVR algebra, the exponent is the ramification index.
-/

namespace RamificationTheory.HilbertRamification.DiscreteValuationRing

open IsLocalRing

universe u v

variable (A : Type u) (B : Type v)
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]

omit [IsDomain A] [IsDiscreteValuationRing A] in
/-- The mapped source uniformizer has its native DVR order as exponent. The
unit factor is constructed from the target DVR, with no supplied factorization. -/
theorem mappedUniformizer_factorization_addVal
    (f : A →+* B) (hinj : Function.Injective f)
    (π : A) (hπ : Irreducible π) (ρ : B) (hρ : Irreducible ρ) :
    ∃ u : Bˣ,
      f π = ρ ^ (IsDiscreteValuationRing.addVal B (f π)).toNat * (u : B) := by
  have hx : f π ≠ 0 := fun h =>
    hπ.ne_zero (hinj (h.trans (map_zero f).symm))
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hρ
  have hv : IsDiscreteValuationRing.addVal B (f π) = (n : ℕ∞) :=
    IsDiscreteValuationRing.addVal_def (f π) u hρ n hu
  refine ⟨u, ?_⟩
  rw [hv, ENat.toNat_natCast]
  exact hu.trans (mul_comm (u : B) (ρ ^ n))

/-- For a local DVR algebra, the same constructed unit factor has exponent
equal to the actual maximal-ideal ramification index. -/
theorem mappedUniformizer_factorization_ramificationIdx
    [Algebra A B] [(maximalIdeal B).LiesOver (maximalIdeal A)]
    (hinj : Function.Injective (algebraMap A B))
    (π : A) (hπ : Irreducible π) (ρ : B) (hρ : Irreducible ρ) :
    ∃ u : Bˣ,
      algebraMap A B π = ρ ^ (maximalIdeal B).ramificationIdx A * (u : B) := by
  rw [ramificationIdx_eq_addVal_uniformizer A B hinj π hπ]
  exact mappedUniformizer_factorization_addVal A B (algebraMap A B) hinj π hπ ρ hρ

end RamificationTheory.HilbertRamification.DiscreteValuationRing
