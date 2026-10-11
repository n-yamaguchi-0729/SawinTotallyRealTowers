/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.ProC.MaximalQuotients.SubgroupComparison
import Nyll.ProCGroups.Topologies.Conjugation
import Nyll.ProCGroups.Abelian.TopologicalAbelianization

/-!
# Conjugation through maximal pro-`C` subgroup comparisons

Ambient conjugation descends intrinsically to the residual quotient of a closed normal
subgroup. The comparison with a subgroup of a maximal pro-`C` quotient intertwines this
action, including after topological abelianization.
-/

open scoped Topology

namespace ProCGroups.ProC

universe u

variable {C : FiniteGroupClass.{u}}
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- Conjugation on a normal subgroup descends to its intrinsic residual quotient. -/
noncomputable def residualQuotientConjugationContinuousMulEquiv
    (hC : FiniteGroupClass.FullFormation C)
    (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) (g : G) :
    N ⧸ proCResidualCore C N ≃ₜ* N ⧸ proCResidualCore C N := by
  have : CompactSpace N := hN.isClosedEmbedding_subtypeVal.compactSpace
  let e : N ≃ₜ* N := Subgroup.conjNormalContinuousMulEquiv N g
  have hmap : (proCResidualCore C N).map e.toMulEquiv.toMonoidHom =
      proCResidualCore C N :=
    map_proCResidualCore_eq_of_surjective hC e.toMulEquiv.toMonoidHom
      e.continuous_toFun e.surjective
      (proCResidualCoreQuotient_hasOpenNormalBasisInClass hC.melnikovFormation.formation)
  exact QuotientGroup.congrₜ (proCResidualCore C N) (proCResidualCore C N) e hmap

/-- The descended conjugation is computed on subgroup representatives. -/
@[simp] theorem residualQuotientConjugationContinuousMulEquiv_apply_mk
    (hC : FiniteGroupClass.FullFormation C)
    (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) (g : G) (n : N) :
    residualQuotientConjugationContinuousMulEquiv hC N hN g
      (QuotientGroup.mk' (proCResidualCore C N) n) =
        QuotientGroup.mk' (proCResidualCore C N) (MulAut.conjNormal g n) := by
  rfl

variable {Q : Type u} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
  [CompactSpace Q] [T2Space Q] [TotallyDisconnectedSpace Q]

/-- The subgroup comparison intertwines intrinsic ambient conjugation. -/
theorem residualQuotientPreimageContinuousMulEquiv_conjugation
    (hC : FiniteGroupClass.FullFormation C)
    (π : G →ₜ* Q) (hπ : IsMaximalProCQuotient C π.toMonoidHom)
    (U : Subgroup Q) [U.Normal] (hU : IsClosed (U : Set Q)) (g : G)
    (z : U.comap π.toMonoidHom ⧸ proCResidualCore C (U.comap π.toMonoidHom)) :
    residualQuotientPreimageContinuousMulEquiv hC π hπ U hU
      (residualQuotientConjugationContinuousMulEquiv hC (U.comap π.toMonoidHom)
        (hU.preimage π.continuous_toFun) g z) =
      MulAut.conjNormal (π g)
        (residualQuotientPreimageContinuousMulEquiv hC π hπ U hU z) := by
  obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective
    (proCResidualCore C (U.comap π.toMonoidHom)) z
  have hn := residualQuotientConjugationContinuousMulEquiv_apply_mk hC
    (U.comap π.toMonoidHom) (hU.preimage π.continuous_toFun) g n
  refine (congrArg (residualQuotientPreimageContinuousMulEquiv hC π hπ U hU) hn).trans ?_
  rw [residualQuotientPreimageContinuousMulEquiv_apply_mk,
    residualQuotientPreimageContinuousMulEquiv_apply_mk]
  apply Subtype.ext
  change π (g * (n : G) * g⁻¹) = π g * π (n : G) * (π g)⁻¹
  simp only [map_mul, map_inv]

open Abelian

/-- The comparison on abelianizations also preserves the conjugation action. -/
theorem residualQuotientPreimage_abelianization_conjugation
    (hC : FiniteGroupClass.FullFormation C)
    (π : G →ₜ* Q) (hπ : IsMaximalProCQuotient C π.toMonoidHom)
    (U : Subgroup Q) [U.Normal] (hU : IsClosed (U : Set Q)) (g : G)
    (a : TopologicalAbelianization
      (U.comap π.toMonoidHom ⧸ proCResidualCore C (U.comap π.toMonoidHom))) :
    TopologicalAbelianization.congr
      (residualQuotientPreimageContinuousMulEquiv hC π hπ U hU)
      (TopologicalAbelianization.congr
        (residualQuotientConjugationContinuousMulEquiv hC (U.comap π.toMonoidHom)
          (hU.preimage π.continuous_toFun) g) a) =
      TopologicalAbelianization.congr (Subgroup.conjNormalContinuousMulEquiv U (π g))
        (TopologicalAbelianization.congr
          (residualQuotientPreimageContinuousMulEquiv hC π hπ U hU) a) := by
  let e := residualQuotientPreimageContinuousMulEquiv hC π hπ U hU
  let cg := residualQuotientConjugationContinuousMulEquiv hC (U.comap π.toMonoidHom)
    (hU.preimage π.continuous_toFun) g
  let cq := Subgroup.conjNormalContinuousMulEquiv U (π g)
  change TopologicalAbelianization.congr e (TopologicalAbelianization.congr cg a) =
    TopologicalAbelianization.congr cq (TopologicalAbelianization.congr e a)
  obtain ⟨z, rfl⟩ := TopologicalAbelianization.surjective_mk _ a
  simp only [TopologicalAbelianization.congr_apply_mk]
  exact congrArg (TopologicalAbelianization.mk U)
    (residualQuotientPreimageContinuousMulEquiv_conjugation hC π hπ U hU g z)

end ProCGroups.ProC
