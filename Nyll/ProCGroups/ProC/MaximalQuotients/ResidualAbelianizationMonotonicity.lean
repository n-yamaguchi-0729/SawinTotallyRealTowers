/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualMonotonicity
import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualCore
import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualQuotientAction
import Nyll.ProCGroups.ProC.MaximalQuotients.ConjugationComparison
import Nyll.ProCGroups.Abelian.TopologicalAbelianization
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Class inclusion and faithful residual abelianization actions

The actual quotient map induced by an inclusion of finite-group classes
remains surjective after topological abelianization. It intertwines the
same ambient conjugation on both residual quotients. Consequently an
action detected by the smaller class is also detected by the larger class.
-/

namespace ProCGroups.ProC

open ProCGroups.Abelian

universe u

variable {C D : FiniteGroupClass.{u}}
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Inclusion of finite-group classes induces the actual continuous map
between the abelianized residual quotients. -/
noncomputable def residualAbelianizationMapOfClassInclusion
    (hCD : ∀ {Q : Type u} [Group Q], C Q → D Q) :
    TopologicalAbelianization (G ⧸ proCResidualCore D G) →ₜ*
      TopologicalAbelianization (G ⧸ proCResidualCore C G) :=
  TopologicalAbelianization.map (residualQuotientMapOfClassInclusion hCD)

/-- The abelianized class-inclusion map retains the original representative. -/
@[simp] theorem residualAbelianizationMapOfClassInclusion_apply_mk
    (hCD : ∀ {Q : Type u} [Group Q], C Q → D Q) (x : G) :
    residualAbelianizationMapOfClassInclusion hCD
        (TopologicalAbelianization.mk (G ⧸ proCResidualCore D G)
          (QuotientGroup.mk' (proCResidualCore D G) x)) =
      TopologicalAbelianization.mk (G ⧸ proCResidualCore C G)
        (QuotientGroup.mk' (proCResidualCore C G) x) := by
  rw [residualAbelianizationMapOfClassInclusion, TopologicalAbelianization.map_apply_mk,
    residualQuotientMapOfClassInclusion_apply_mk]

/-- The actual map between abelianized residual quotients is surjective. -/
theorem residualAbelianizationMapOfClassInclusion_surjective
    (hCD : ∀ {Q : Type u} [Group Q], C Q → D Q) :
    Function.Surjective (residualAbelianizationMapOfClassInclusion (G := G) hCD) :=
  TopologicalAbelianization.surjective_map_of_surjective
    (residualQuotientMapOfClassInclusion hCD)
    (residualQuotientMapOfClassInclusion_surjective hCD)

variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- Class inclusion commutes with actual conjugation by the same ambient
element on both abelianized residual quotients of a normal subgroup. -/
theorem residualAbelianizationMapOfClassInclusion_conjugation
    (hC : FiniteGroupClass.FullFormation C) (hD : FiniteGroupClass.FullFormation D)
    (hCD : ∀ {Q : Type u} [Group Q], C Q → D Q)
    (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) (g : G)
    (a : TopologicalAbelianization (N ⧸ proCResidualCore D N)) :
    residualAbelianizationMapOfClassInclusion hCD
        (TopologicalAbelianization.congr
          (residualQuotientConjugationContinuousMulEquiv hD N hN g) a) =
      TopologicalAbelianization.congr
        (residualQuotientConjugationContinuousMulEquiv hC N hN g)
        (residualAbelianizationMapOfClassInclusion hCD a) := by
  obtain ⟨q, rfl⟩ := TopologicalAbelianization.surjective_mk
    (N ⧸ proCResidualCore D N) a
  obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective (proCResidualCore D N) q
  simp only [TopologicalAbelianization.congr_apply_mk,
    residualQuotientConjugationContinuousMulEquiv_apply_mk,
    residualAbelianizationMapOfClassInclusion_apply_mk]

/-- Faithfulness detected by a finite-group class persists upon enlarging
that class, using the constructed equivariant surjection. -/
theorem residualAbelianizationQuotientConjugation_injective_of_class_inclusion
    (hC : FiniteGroupClass.FullFormation C) (hD : FiniteGroupClass.FullFormation D)
    (hCD : ∀ {Q : Type u} [Group Q], C Q → D Q)
    (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G))
    (hfaith : Function.Injective (residualAbelianizationQuotientConjugation hC N hN)) :
    Function.Injective (residualAbelianizationQuotientConjugation hD N hN) := by
  apply (residualAbelianizationQuotientConjugation_injective_iff hD N hN).mpr
  intro g hg htrivial
  apply (residualAbelianizationQuotientConjugation_injective_iff hC N hN).mp hfaith g hg
  apply MulEquiv.ext
  intro a
  obtain ⟨b, rfl⟩ := residualAbelianizationMapOfClassInclusion_surjective (G := N) hCD a
  have hcompare := residualAbelianizationMapOfClassInclusion_conjugation
    hC hD hCD N hN g b
  have hfixed := DFunLike.congr_fun htrivial b
  change TopologicalAbelianization.congr
    (residualQuotientConjugationContinuousMulEquiv hD N hN g) b = b at hfixed
  rw [hfixed] at hcompare
  exact hcompare.symm

end ProCGroups.ProC
