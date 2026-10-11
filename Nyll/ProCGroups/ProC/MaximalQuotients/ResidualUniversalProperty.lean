/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.ProC.MaximalQuotients.Definitions
import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualCore
import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualQuotient
import Nyll.ProCGroups.ProC.MaximalQuotients.UniversalProperty
import Nyll.ProCGroups.ProC.Quotients.ClosedNormal

/-!
# The canonical residual quotient is maximal pro-C

The actual residual quotient has the required pro-C basis. Every continuous
map to a pro-C group factors through its residual core, and surjectivity of
the quotient projection gives uniqueness of this factorization.
-/

namespace ProCGroups.ProC

universe u

attribute [local instance] proCResidualCore_isClosed

private theorem residualQuotient_totallyDisconnectedSpace
    {C : FiniteGroupClass.{u}}
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    TotallyDisconnectedSpace (G ⧸ proCResidualCore C G) :=
  ProCGroups.totallyDisconnectedSpace_quotient_closedNormal
    (proCResidualCore C G) (proCResidualCore_isClosed C G)

attribute [local instance] residualQuotient_totallyDisconnectedSpace

/-- The canonical residual-core projection satisfies the maximal pro-C
universal property. The quotient's separation properties are supplied from
closedness of the actual core, rather than assumed. -/
theorem isMaximalProCQuotient_residualCore
    {C : FiniteGroupClass.{u}}
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hForm : FiniteGroupClass.Formation C) (hHer : FiniteGroupClass.Hereditary C) :
    IsMaximalProCQuotient C (QuotientGroup.mk' (proCResidualCore C G)) := by
  refine
    { hasOpenNormalBasisInClass := proCResidualCoreQuotient_hasOpenNormalBasisInClass hForm
      continuous_π := QuotientGroup.continuous_mk
      surjective_π := QuotientGroup.mk'_surjective (proCResidualCore C G)
      existsUnique_lift := ?_ }
  intro H _ _ _ _ _ _ hH φ hφ
  let f : G →ₜ* H := ⟨φ, hφ⟩
  let ψ : G ⧸ proCResidualCore C G →ₜ* H := lift_proCResidualCoreQuotient hHer f hH
  refine ⟨ψ.toMonoidHom, ⟨ψ.continuous_toFun, ?_⟩, ?_⟩
  · apply MonoidHom.ext
    intro x
    exact lift_proCResidualCoreQuotient_mk hHer f hH x
  · intro ψ' hψ'
    apply MonoidHom.ext
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (proCResidualCore C G) q
    exact (DFunLike.congr_fun hψ'.2 x).trans
      (lift_proCResidualCoreQuotient_mk hHer f hH x).symm

end ProCGroups.ProC
