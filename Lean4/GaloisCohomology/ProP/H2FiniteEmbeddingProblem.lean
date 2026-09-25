/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import GaloisCohomology.ProP.H2CentralExtensionClass
import GaloisCohomology.ProP.H2FiniteStage

set_option autoImplicit false
/-!
# Finite nonsplit embedding problems detected by degree two

A nonzero lifted continuous degree-two class of a pro-`p` group descends to
a nonzero class on one finite `p`-group quotient.  Its explicit cocycle
extension is therefore a finite central `p`-extension with no continuous
group-theoretic section.
-/

open scoped Topology

namespace ClassFieldTower.Cohomology

open ProCGroups ProCGroups.ProC

noncomputable section

universe u

variable {p : ℕ} [Fact p.Prime]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- Every nonzero ambient degree-two class is witnessed by a nonsplit finite
central `p`-extension of a finite quotient. -/
theorem exists_finite_nonsplit_extension_of_degree_two_ne_zero
    (hG : HasOpenNormalBasisInClass (FiniteGroupClass.pGroup p) G)
    {x : continuousCohomologyZModPLifted p G 2}
    (hx : x ≠ 0) :
    ∃ U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G,
      ∃ xU : continuousCohomologyZModPLifted p
          (G ⧸ (U.1 : Subgroup G)) 2,
        continuousCohomologyZModPMapLifted p
            (OpenNormalSubgroupInClass.quotientProj U) 2 xU = x ∧
          ¬ ∃ s : (G ⧸ (U.1 : Subgroup G)) →ₜ*
              ProP.DegreeTwoCentralExtension xU,
            (ProP.H2CocycleExtension.projection
              (ProP.degreeTwoCocycleRepresentative xU)).comp s =
                ContinuousMonoidHom.id (G ⧸ (U.1 : Subgroup G)) := by
  obtain ⟨U, xU, hxUinflates⟩ :=
    exists_openNormalSubgroupInClass_inflation_eq_degree_two hG x
  have hxU : xU ≠ 0 := by
    intro hxUzero
    apply hx
    simpa [hxUzero] using hxUinflates.symm
  refine ⟨U, xU, hxUinflates, ?_⟩
  exact ProP.degreeTwoCentralExtension_no_section_of_ne_zero hxU

end

end ClassFieldTower.Cohomology
