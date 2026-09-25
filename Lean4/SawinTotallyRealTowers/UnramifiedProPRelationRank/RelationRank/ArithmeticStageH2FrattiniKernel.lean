/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import GaloisCohomology.ProP.CentralExtensionFrattiniKernel
import SawinTotallyRealTowers.UnramifiedProPRelationRank.RelationRank.ArithmeticStageH2EmbeddingProblem

set_option autoImplicit false
/-!
# The Frattini kernel of the arithmetic degree-two embedding problem

Transporting the explicit cocycle-extension projection to its finite
everywhere-unramified arithmetic stage does not change its kernel.  A nonzero
stage class therefore has a cyclic kernel of order `p` contained in the
Frattini subgroup of the extension group.
-/

open scoped NumberField Topology

noncomputable section

universe u

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.Cohomology ClassFieldTower.Martinet
open ProCGroups ProCGroups.ProC

variable (F : Type u) [Field F] [NumberField F]
variable (p : ℕ) [Fact p.Prime]

/-- Transport to the arithmetic-stage Galois group leaves the cocycle
extension kernel unchanged. -/
theorem arithmeticStageH2Projection_ker
    (hpOdd : Odd p)
    (U : OpenNormalSubgroup
      (MaxEverywhereUnramifiedProPGaloisGroup F p))
    (xU : continuousCohomologyZModPLifted p
      (MaxEverywhereUnramifiedProPGaloisGroup F p ⧸
        (U : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F p))) 2) :
    (arithmeticStageH2Projection F p hpOdd U xU).ker =
      (ProP.H2CocycleExtension.projection
        (ProP.degreeTwoCocycleRepresentative xU)).ker := by
  ext y
  simp only [MonoidHom.mem_ker]
  change
    (openNormalQuotientContinuousEquivArithmeticStageGalois
        F p hpOdd U)
        (ProP.H2CocycleExtension.projection
          (ProP.degreeTwoCocycleRepresentative xU) y) = 1 ↔
      ProP.H2CocycleExtension.projection
          (ProP.degreeTwoCocycleRepresentative xU) y = 1
  exact (openNormalQuotientContinuousEquivArithmeticStageGalois
    F p hpOdd U).map_eq_one_iff

/-- The arithmetic embedding-problem kernel has cardinality `p`. -/
theorem arithmeticStageH2Projection_kernel_card
    (hpOdd : Odd p)
    (U : OpenNormalSubgroup
      (MaxEverywhereUnramifiedProPGaloisGroup F p))
    (xU : continuousCohomologyZModPLifted p
      (MaxEverywhereUnramifiedProPGaloisGroup F p ⧸
        (U : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F p))) 2) :
    Nat.card (arithmeticStageH2Projection F p hpOdd U xU).ker = p := by
  rw [arithmeticStageH2Projection_ker]
  exact ProP.degreeTwoCentralExtension_kernel_card xU

/-- The arithmetic embedding-problem kernel is cyclic. -/
theorem arithmeticStageH2Projection_kernel_isCyclic
    (hpOdd : Odd p)
    (U : OpenNormalSubgroup
      (MaxEverywhereUnramifiedProPGaloisGroup F p))
    (xU : continuousCohomologyZModPLifted p
      (MaxEverywhereUnramifiedProPGaloisGroup F p ⧸
        (U : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F p))) 2) :
    IsCyclic (arithmeticStageH2Projection F p hpOdd U xU).ker := by
  rw [arithmeticStageH2Projection_ker]
  exact ProP.degreeTwoCentralExtension_kernel_isCyclic xU

/-- For a nonzero stage class, the cyclic kernel is a Frattini kernel. -/
theorem arithmeticStageH2Projection_kernel_le_frattini_of_ne_zero
    (hpOdd : Odd p)
    (U : OpenNormalSubgroup
      (MaxEverywhereUnramifiedProPGaloisGroup F p))
    {xU : continuousCohomologyZModPLifted p
      (MaxEverywhereUnramifiedProPGaloisGroup F p ⧸
        (U : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F p))) 2}
    (hxU : xU ≠ 0) :
    (arithmeticStageH2Projection F p hpOdd U xU).ker ≤
      frattini (ProP.DegreeTwoCentralExtension xU) := by
  rw [arithmeticStageH2Projection_ker]
  exact ProP.degreeTwoCentralExtension_kernel_le_frattini_of_ne_zero hxU

end ClassFieldTower.Martinet.Shafarevich
