/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.ProC.MaximalQuotients.ConjugationComparison
import Nyll.ProCGroups.Abelian.TopologicalAbelianization
import Mathlib.Algebra.Group.End
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Quotient conjugation on abelianized residual quotients

Ambient conjugation acts on the actual residual quotient of a closed normal
subgroup. Its topological abelianization kills internal conjugation, giving
an action of the original quotient group, with a representative-wise
criterion for faithfulness.
-/

namespace ProCGroups.ProC

open ProCGroups.Abelian

universe u

variable {C : FiniteGroupClass.{u}}
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

private noncomputable def residualAbelianizationConjugationHom
    (hC : FiniteGroupClass.FullFormation C)
    (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) :
    G →* MulAut (TopologicalAbelianization (N ⧸ proCResidualCore C N)) where
  toFun g := (TopologicalAbelianization.congr
    (residualQuotientConjugationContinuousMulEquiv hC N hN g)).toMulEquiv
  map_one' := by
    apply MulEquiv.ext
    intro a
    obtain ⟨z, rfl⟩ := TopologicalAbelianization.surjective_mk
      (N ⧸ proCResidualCore C N) a
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (proCResidualCore C N) z
    change TopologicalAbelianization.congr
        (residualQuotientConjugationContinuousMulEquiv hC N hN (1 : G))
        (TopologicalAbelianization.mk (N ⧸ proCResidualCore C N)
          (QuotientGroup.mk' (proCResidualCore C N) x)) =
      TopologicalAbelianization.mk (N ⧸ proCResidualCore C N)
        (QuotientGroup.mk' (proCResidualCore C N) x)
    rw [TopologicalAbelianization.congr_apply_mk,
      residualQuotientConjugationContinuousMulEquiv_apply_mk]
    exact congrArg
      (fun y : N => TopologicalAbelianization.mk (N ⧸ proCResidualCore C N)
        (QuotientGroup.mk' (proCResidualCore C N) y))
      (DFunLike.congr_fun (map_one (MulAut.conjNormal (H := N))) x)
  map_mul' g h := by
    apply MulEquiv.ext
    intro a
    obtain ⟨z, rfl⟩ := TopologicalAbelianization.surjective_mk
      (N ⧸ proCResidualCore C N) a
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (proCResidualCore C N) z
    change TopologicalAbelianization.congr
        (residualQuotientConjugationContinuousMulEquiv hC N hN (g * h))
        (TopologicalAbelianization.mk (N ⧸ proCResidualCore C N)
          (QuotientGroup.mk' (proCResidualCore C N) x)) =
      TopologicalAbelianization.congr
        (residualQuotientConjugationContinuousMulEquiv hC N hN g)
        (TopologicalAbelianization.congr
          (residualQuotientConjugationContinuousMulEquiv hC N hN h)
          (TopologicalAbelianization.mk (N ⧸ proCResidualCore C N)
            (QuotientGroup.mk' (proCResidualCore C N) x)))
    simp only [TopologicalAbelianization.congr_apply_mk,
      residualQuotientConjugationContinuousMulEquiv_apply_mk]
    simpa only [MulAut.mul_apply] using congrArg
      (fun y : N => TopologicalAbelianization.mk (N ⧸ proCResidualCore C N)
        (QuotientGroup.mk' (proCResidualCore C N) y))
      (DFunLike.congr_fun (map_mul (MulAut.conjNormal (H := N)) g h) x)

/-- The original quotient acts by actual conjugation on the abelianized
residual quotient of its closed normal subgroup. -/
noncomputable def residualAbelianizationQuotientConjugation
    (hC : FiniteGroupClass.FullFormation C)
    (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) :
    (G ⧸ N) →* MulAut (TopologicalAbelianization (N ⧸ proCResidualCore C N)) := by
  let ρ : G →* MulAut (TopologicalAbelianization (N ⧸ proCResidualCore C N)) :=
    residualAbelianizationConjugationHom hC N hN
  have hNker : N ≤ ρ.ker := by
    intro g hg
    apply MulEquiv.ext
    intro a
    obtain ⟨z, rfl⟩ := TopologicalAbelianization.surjective_mk
      (N ⧸ proCResidualCore C N) a
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (proCResidualCore C N) z
    change TopologicalAbelianization.congr
        (residualQuotientConjugationContinuousMulEquiv hC N hN g)
        (TopologicalAbelianization.mk (N ⧸ proCResidualCore C N)
          (QuotientGroup.mk' (proCResidualCore C N) x)) =
      TopologicalAbelianization.mk (N ⧸ proCResidualCore C N)
        (QuotientGroup.mk' (proCResidualCore C N) x)
    rw [TopologicalAbelianization.congr_apply_mk,
      residualQuotientConjugationContinuousMulEquiv_apply_mk]
    let q : N →* TopologicalAbelianization (N ⧸ proCResidualCore C N) :=
      (TopologicalAbelianization.mk (N ⧸ proCResidualCore C N)).comp
        (QuotientGroup.mk' (proCResidualCore C N))
    change q (MulAut.conjNormal g x) = q x
    have hconj : MulAut.conjNormal g x = (⟨g, hg⟩ : N) * x * (⟨g, hg⟩ : N)⁻¹ := by
      apply Subtype.ext
      rfl
    rw [hconj, map_mul, map_mul, map_inv,
      mul_comm (q (⟨g, hg⟩ : N)) (q x), mul_assoc, mul_inv_cancel, mul_one]
  exact QuotientGroup.lift N ρ hNker

/-- On an ambient representative, the quotient action is the already
constructed continuous residual conjugation followed by abelianization. -/
theorem residualAbelianizationQuotientConjugation_mk
    (hC : FiniteGroupClass.FullFormation C)
    (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) (g : G) :
    residualAbelianizationQuotientConjugation hC N hN (QuotientGroup.mk' N g) =
      (TopologicalAbelianization.congr
        (residualQuotientConjugationContinuousMulEquiv hC N hN g)).toMulEquiv := by
  rfl

/-- Faithfulness is exactly nontriviality of actual conjugation for every
ambient representative outside the subgroup; no quotient finiteness is needed. -/
theorem residualAbelianizationQuotientConjugation_injective_iff
    (hC : FiniteGroupClass.FullFormation C)
    (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) :
    Function.Injective (residualAbelianizationQuotientConjugation hC N hN) ↔
      ∀ g : G, g ∉ N →
        (TopologicalAbelianization.congr
          (residualQuotientConjugationContinuousMulEquiv hC N hN g)).toMulEquiv ≠ 1 := by
  constructor
  · intro hinj g hg heq
    apply hg
    apply (QuotientGroup.eq_one_iff (N := N) g).mp
    apply hinj
    change residualAbelianizationQuotientConjugation hC N hN (QuotientGroup.mk' N g) =
      residualAbelianizationQuotientConjugation hC N hN 1
    rw [residualAbelianizationQuotientConjugation_mk, heq, map_one]
  · intro hdetect
    apply (injective_iff_map_eq_one
      (residualAbelianizationQuotientConjugation hC N hN)).mpr
    intro a ha
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N a
    apply (QuotientGroup.eq_one_iff (N := N) g).mpr
    by_contra hg
    exact hdetect g hg ((residualAbelianizationQuotientConjugation_mk hC N hN g).symm.trans ha)

end ProCGroups.ProC
