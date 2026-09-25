/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import GaloisCohomology.ProP.H2FiniteEmbeddingProblem
import SawinTotallyRealTowers.UnramifiedProPRelationRank.RelationRank.OpenNormalArithmeticStage

set_option autoImplicit false
/-!
# Finite degree-two embedding problems at arithmetic stages

A nonzero degree-two class of the maximal everywhere-unramified pro-`p`
Galois group is detected on a finite quotient.  The quotient is transported to
the Galois group of its concrete arithmetic stage, carrying the cocycle
extension to a finite nonsplit central `p`-group embedding problem there.
-/

open scoped NumberField Topology

noncomputable section

universe u

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.Cohomology ClassFieldTower.Martinet
open ProCGroups ProCGroups.ProC

variable (F : Type u) [Field F] [NumberField F]
variable (p : ℕ) [Fact p.Prime]

/-- The quotient--arithmetic-stage equivalence, with its canonical finite
topologies recorded. -/
noncomputable def openNormalQuotientContinuousEquivArithmeticStageGalois
    (hpOdd : Odd p)
    (U : OpenNormalSubgroup
      (MaxEverywhereUnramifiedProPGaloisGroup F p)) :
    (MaxEverywhereUnramifiedProPGaloisGroup F p ⧸
        (U : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F p))) ≃ₜ*
      ((openNormalArithmeticStage F p hpOdd U).field ≃ₐ[F]
        (openNormalArithmeticStage F p hpOdd U).field) :=
  { openNormalQuotientEquivArithmeticStageGalois F p hpOdd U with
    continuous_toFun := continuous_of_discreteTopology
    continuous_invFun := continuous_of_discreteTopology }

/-- The cocycle-extension projection, transported to the Galois group of the
corresponding finite arithmetic stage. -/
noncomputable def arithmeticStageH2Projection
    (hpOdd : Odd p)
    (U : OpenNormalSubgroup
      (MaxEverywhereUnramifiedProPGaloisGroup F p))
    (xU : continuousCohomologyZModPLifted p
      (MaxEverywhereUnramifiedProPGaloisGroup F p ⧸
        (U : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F p))) 2) :
    ProP.DegreeTwoCentralExtension xU →ₜ*
      ((openNormalArithmeticStage F p hpOdd U).field ≃ₐ[F]
        (openNormalArithmeticStage F p hpOdd U).field) :=
  (ContinuousMonoidHom.toContinuousMonoidHom
    (openNormalQuotientContinuousEquivArithmeticStageGalois F p hpOdd U)).comp
      (ProP.H2CocycleExtension.projection
        (ProP.degreeTwoCocycleRepresentative xU))

theorem arithmeticStageH2Projection_surjective
    (hpOdd : Odd p)
    (U : OpenNormalSubgroup
      (MaxEverywhereUnramifiedProPGaloisGroup F p))
    (xU : continuousCohomologyZModPLifted p
      (MaxEverywhereUnramifiedProPGaloisGroup F p ⧸
        (U : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F p))) 2) :
    Function.Surjective (arithmeticStageH2Projection F p hpOdd U xU) :=
  (openNormalQuotientContinuousEquivArithmeticStageGalois
      F p hpOdd U).surjective.comp
    (ProP.H2CocycleExtension.projection_surjective
      (ProP.degreeTwoCocycleRepresentative xU))

theorem arithmeticStageH2Projection_kernel_le_center
    (hpOdd : Odd p)
    (U : OpenNormalSubgroup
      (MaxEverywhereUnramifiedProPGaloisGroup F p))
    (xU : continuousCohomologyZModPLifted p
      (MaxEverywhereUnramifiedProPGaloisGroup F p ⧸
        (U : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F p))) 2) :
    (arithmeticStageH2Projection F p hpOdd U xU).ker ≤
      Subgroup.center (ProP.DegreeTwoCentralExtension xU) := by
  intro y hy
  apply ProP.H2CocycleExtension.kernel_le_center
  change ProP.H2CocycleExtension.projection
      (ProP.degreeTwoCocycleRepresentative xU) y = 1
  change (openNormalQuotientContinuousEquivArithmeticStageGalois
    F p hpOdd U)
      (ProP.H2CocycleExtension.projection
        (ProP.degreeTwoCocycleRepresentative xU) y) = 1 at hy
  apply (openNormalQuotientContinuousEquivArithmeticStageGalois
    F p hpOdd U).injective
  simpa only [map_one] using hy

theorem arithmeticStageH2Projection_no_section
    (hpOdd : Odd p)
    (U : OpenNormalSubgroup
      (MaxEverywhereUnramifiedProPGaloisGroup F p))
    {xU : continuousCohomologyZModPLifted p
      (MaxEverywhereUnramifiedProPGaloisGroup F p ⧸
        (U : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F p))) 2}
    (hnoSection : ¬ ∃ s :
      (MaxEverywhereUnramifiedProPGaloisGroup F p ⧸
          (U : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F p))) →ₜ*
        ProP.DegreeTwoCentralExtension xU,
      (ProP.H2CocycleExtension.projection
        (ProP.degreeTwoCocycleRepresentative xU)).comp s =
          ContinuousMonoidHom.id _) :
    ¬ ∃ s : ((openNormalArithmeticStage F p hpOdd U).field ≃ₐ[F]
          (openNormalArithmeticStage F p hpOdd U).field) →ₜ*
        ProP.DegreeTwoCentralExtension xU,
      (arithmeticStageH2Projection F p hpOdd U xU).comp s =
        ContinuousMonoidHom.id _ := by
  intro hsection
  apply hnoSection
  obtain ⟨s, hs⟩ := hsection
  let e := openNormalQuotientContinuousEquivArithmeticStageGalois
    F p hpOdd U
  let eHom :
      (MaxEverywhereUnramifiedProPGaloisGroup F p ⧸
          (U : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F p))) →ₜ*
        ((openNormalArithmeticStage F p hpOdd U).field ≃ₐ[F]
          (openNormalArithmeticStage F p hpOdd U).field) :=
    ContinuousMonoidHom.toContinuousMonoidHom e
  refine ⟨s.comp eHom, ?_⟩
  ext q
  apply e.injective
  have hq := DFunLike.congr_fun hs (e q)
  exact hq

/-- A nonzero ambient degree-two class produces a finite nonsplit central
`p`-group embedding problem over the Galois group of a finite everywhere-
unramified arithmetic stage. -/
theorem exists_arithmeticStage_finite_nonsplit_central_extension_of_degreeTwo_ne_zero
    (hpOdd : Odd p)
    {x : continuousCohomologyZModPLifted p
      (MaxEverywhereUnramifiedProPGaloisGroup F p) 2}
    (hx : x ≠ 0) :
    ∃ U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p)
        (MaxEverywhereUnramifiedProPGaloisGroup F p),
      ∃ xU : continuousCohomologyZModPLifted p
          (MaxEverywhereUnramifiedProPGaloisGroup F p ⧸
            (U.1 : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F p))) 2,
        continuousCohomologyZModPMapLifted p
            (OpenNormalSubgroupInClass.quotientProj U) 2 xU = x ∧
          Finite (ProP.DegreeTwoCentralExtension xU) ∧
          IsPGroup p (ProP.DegreeTwoCentralExtension xU) ∧
          Function.Surjective
            (arithmeticStageH2Projection F p hpOdd U.1 xU) ∧
          (arithmeticStageH2Projection F p hpOdd U.1 xU).ker ≤
            Subgroup.center (ProP.DegreeTwoCentralExtension xU) ∧
          ¬ ∃ s :
              ((openNormalArithmeticStage F p hpOdd U.1).field ≃ₐ[F]
                (openNormalArithmeticStage F p hpOdd U.1).field) →ₜ*
                ProP.DegreeTwoCentralExtension xU,
            (arithmeticStageH2Projection F p hpOdd U.1 xU).comp s =
              ContinuousMonoidHom.id _ := by
  obtain ⟨U, xU, hxUinflates, hxUnoSection⟩ :=
    exists_finite_nonsplit_extension_of_degree_two_ne_zero
      (maxEverywhereUnramifiedProPGaloisGroup_hasPGroupOpenNormalBasis
        F p hpOdd) hx
  refine ⟨U, xU, hxUinflates, inferInstance, ?_,
    arithmeticStageH2Projection_surjective F p hpOdd U.1 xU,
    arithmeticStageH2Projection_kernel_le_center F p hpOdd U.1 xU,
    arithmeticStageH2Projection_no_section F p hpOdd U.1 hxUnoSection⟩
  exact ProP.H2CocycleExtension.isPGroup
    (ProP.degreeTwoCocycleRepresentative xU) U.2.2

end ClassFieldTower.Martinet.Shafarevich
