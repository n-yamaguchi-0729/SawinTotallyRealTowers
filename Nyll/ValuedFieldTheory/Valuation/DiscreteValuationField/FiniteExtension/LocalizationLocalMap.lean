/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Ideal.Over

/-!
# The local map into a localization at a prime above the maximal ideal

For a local ring `R`, localizing an `R`-algebra at a prime above the maximal
ideal gives a local map from `R`. This uses the actual localization and
lying-over data, without integrality or finiteness assumptions.
-/

namespace ValuationTheory.DiscreteValuationField

/-- The map from a local base ring into a localization at a prime above its
maximal ideal reflects units. The algebra structures form the given tower. -/
theorem localizationAtPrime_algebraMap_isLocalHom
    (R : Type*) {B : Type*} (A : Type*)
    [CommRing R] [CommRing B] [CommRing A] [IsLocalRing R]
    [Algebra R B] [Algebra B A] [Algebra R A] [IsScalarTower R B A]
    (P : Ideal B) [P.IsPrime] [P.LiesOver (IsLocalRing.maximalIdeal R)]
    [IsLocalization.AtPrime A P] :
    IsLocalHom (algebraMap R A) := by
  constructor
  intro x hx
  by_contra hunit
  have hm : x ∈ IsLocalRing.maximalIdeal R := hunit
  have hP : algebraMap R B x ∈ P :=
    (Ideal.mem_of_liesOver P (IsLocalRing.maximalIdeal R) x).mp hm
  have hx' : IsUnit (algebraMap B A (algebraMap R B x)) := by
    rw [← IsScalarTower.algebraMap_apply R B A]
    exact hx
  exact ((IsLocalization.AtPrime.isUnit_to_map_iff A P (algebraMap R B x)).mp hx') hP

end ValuationTheory.DiscreteValuationField
