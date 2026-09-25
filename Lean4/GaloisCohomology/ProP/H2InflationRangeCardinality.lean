/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import GaloisCohomology.ProP.H2InflationRangeBound
import Mathlib.FieldTheory.Finiteness

set_option autoImplicit false
/-!
# Cardinality bounds on finite-stage degree-two inflation

A uniform bound p^d on finite-stage inflation images gives finite
continuous H² of dimension at most d. Finiteness of the finite-stage
cohomology and its image is constructed, rather than assumed.
-/

open scoped Topology

namespace ClassFieldTower.Cohomology

open ProCGroups ProCGroups.ProC

noncomputable section
universe u

variable {p : ℕ} [Fact p.Prime]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- A uniform cardinality bound for finite-stage images bounds the full
continuous degree-two cohomology dimension. -/
theorem finiteDimensional_and_finrank_degree_two_le_of_inflationRange_natCard
    (d : ℕ)
    (hG : HasOpenNormalBasisInClass (FiniteGroupClass.pGroup p) G)
    (hcard : ∀ U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G,
      Nat.card (degreeTwoInflationRange (p := p) U) ≤ p ^ d) :
    FiniteDimensional (ZMod p) (continuousCohomologyZModPLifted p G 2) ∧
      Module.finrank (ZMod p) (continuousCohomologyZModPLifted p G 2) ≤ d := by
  have h := finiteDimensional_and_finrank_degree_two_le_of_inflationRange_embeddings
    (p := p) (G := G) (W := Fin d → ZMod p) hG (by
      intro U
      let Q := G ⧸ (U.1 : Subgroup G)
      let : FiniteDimensional (ZMod p) (continuousCohomologyZModPLifted p Q 2) :=
        finiteDimensional_degree_two_of_finite (p := p) (Q := Q) inferInstance
      let : FiniteDimensional (ZMod p) (degreeTwoInflationRange (p := p) U) :=
        LinearMap.finiteDimensional_range _
      have hc : p ^ Module.finrank (ZMod p) (degreeTwoInflationRange (p := p) U) ≤
          p ^ d := by
        have he : Nat.card (degreeTwoInflationRange (p := p) U) =
            p ^ Module.finrank (ZMod p) (degreeTwoInflationRange (p := p) U) := by
          simpa only [Nat.card_zmod] using
            (Module.natCard_eq_pow_finrank (K := ZMod p)
              (V := degreeTwoInflationRange (p := p) U))
        exact he ▸ hcard U
      have hd : Module.finrank (ZMod p) (degreeTwoInflationRange (p := p) U) ≤ d :=
        (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp hc
      apply finrank_le_iff_exists_linearMap.mp
      simpa using hd)
  simpa using h

end
end ClassFieldTower.Cohomology
