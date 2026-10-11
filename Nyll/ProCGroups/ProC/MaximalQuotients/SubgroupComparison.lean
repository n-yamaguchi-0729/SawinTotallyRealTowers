/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.ProC.MaximalQuotients.Definitions
import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualIdempotence
import Nyll.ProCGroups.Topologies.ContinuousMulEquiv

/-!
# Subgroups of maximal pro-C quotients

The kernel of a maximal pro-C quotient is the concrete residual core. For a
closed subgroup of the quotient, its preimage has the same residual kernel.
Consequently its residual quotient is continuously isomorphic to the chosen
subgroup. In particular, this applies to open subgroups of maximal pro-p
quotients without making any claim about arbitrary open subgroups of the source.
-/

open scoped Topology

namespace ProCGroups.ProC

universe u

variable {C : FiniteGroupClass.{u}}
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
variable {Q : Type u} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
  [CompactSpace Q] [T2Space Q] [TotallyDisconnectedSpace Q]

/-- The universal maximal quotient has exactly the residual core as its kernel. -/
theorem IsMaximalProCQuotient.ker_eq_proCResidualCore
    (hC : FiniteGroupClass.FullFormation C)
    (π : G →ₜ* Q) (hπ : IsMaximalProCQuotient C π.toMonoidHom) :
    π.toMonoidHom.ker = proCResidualCore C G := by
  have hRclosed := proCResidualCore_isClosed C G
  have : TotallyDisconnectedSpace (G ⧸ proCResidualCore C G) :=
    ProCGroups.totallyDisconnectedSpace_quotient_closedNormal
      (proCResidualCore C G) hRclosed
  have hres : HasOpenNormalBasisInClass C (G ⧸ proCResidualCore C G) :=
    proCResidualCoreQuotient_hasOpenNormalBasisInClass hC.melnikovFormation.formation
  obtain ⟨ψ, hψ, _hunique⟩ := hπ.existsUnique_lift hres
    (QuotientGroup.mk' (proCResidualCore C G)) QuotientGroup.continuous_mk
  apply le_antisymm
  · intro x hx
    apply (QuotientGroup.eq_one_iff (N := proCResidualCore C G) x).mp
    have heq := DFunLike.congr_fun hψ.2 x
    change ψ (π x) = QuotientGroup.mk' (proCResidualCore C G) x at heq
    change π x = 1 at hx
    rw [hx, map_one] at heq
    exact heq.symm
  · exact proCResidualCore_le_ker_of_continuousMonoidHom_to_proC
      hC.hereditary π hπ.hasOpenNormalBasisInClass

/-- The residual core of a closed subgroup preimage is the kernel of the
restricted maximal quotient map. -/
theorem proCResidualCore_preimage_eq_ker
    (hC : FiniteGroupClass.FullFormation C)
    (π : G →ₜ* Q) (hπ : IsMaximalProCQuotient C π.toMonoidHom)
    (U : Subgroup Q) (hU : IsClosed (U : Set Q)) :
    proCResidualCore C (U.comap π.toMonoidHom) =
      (ContinuousMonoidHom.restrictPreimage π U).toMonoidHom.ker := by
  have hker : π.toMonoidHom.ker = proCResidualCore C G :=
    hπ.ker_eq_proCResidualCore hC π
  have hJclosed : IsClosed ((U.comap π.toMonoidHom : Subgroup G) : Set G) :=
    hU.preimage π.continuous_toFun
  have hRJ : proCResidualCore C G ≤ U.comap π.toMonoidHom := by
    intro x hx
    change π x ∈ U
    have hxker : x ∈ π.toMonoidHom.ker := hker.symm ▸ hx
    change π x = 1 at hxker
    rw [hxker]
    exact U.one_mem
  rw [proCResidualCore_eq_comap_of_le hC (U.comap π.toMonoidHom) hJclosed hRJ]
  ext x
  change x.1 ∈ proCResidualCore C G ↔
    ContinuousMonoidHom.restrictPreimage π U x = 1
  rw [← hker]
  exact ContinuousMonoidHom.restrictPreimage_eq_one_iff.symm

/-- The residual quotient of the preimage of a closed subgroup of a maximal
pro-C quotient is continuously isomorphic to that subgroup. -/
noncomputable def residualQuotientPreimageContinuousMulEquiv
    (hC : FiniteGroupClass.FullFormation C)
    (π : G →ₜ* Q) (hπ : IsMaximalProCQuotient C π.toMonoidHom)
    (U : Subgroup Q) (hU : IsClosed (U : Set Q)) :
    (U.comap π.toMonoidHom) ⧸ proCResidualCore C (U.comap π.toMonoidHom) ≃ₜ* U := by
  have hJclosed : IsClosed ((U.comap π.toMonoidHom : Subgroup G) : Set G) :=
    hU.preimage π.continuous_toFun
  have : CompactSpace (U.comap π.toMonoidHom) :=
    hJclosed.isClosedEmbedding_subtypeVal.compactSpace
  let f : U.comap π.toMonoidHom →ₜ* U := ContinuousMonoidHom.restrictPreimage π U
  have hker : proCResidualCore C (U.comap π.toMonoidHom) = f.toMonoidHom.ker :=
    proCResidualCore_preimage_eq_ker hC π hπ U hU
  let fbar : (U.comap π.toMonoidHom) ⧸
      proCResidualCore C (U.comap π.toMonoidHom) →ₜ* U :=
    QuotientGroup.liftₜ (proCResidualCore C (U.comap π.toMonoidHom)) f hker.le
  have hinj : Function.Injective fbar :=
    (QuotientGroup.injective_lift_iff
      (proCResidualCore C (U.comap π.toMonoidHom)) f.toMonoidHom hker.le).mpr hker
  have hsurj : Function.Surjective fbar :=
    QuotientGroup.lift_surjective_of_surjective
      (proCResidualCore C (U.comap π.toMonoidHom)) f.toMonoidHom
      (ContinuousMonoidHom.restrictPreimage_surjective π hπ.surjective_π U) hker.le
  exact ContinuousMulEquiv.ofBijectiveCompactToT2 fbar.toMonoidHom
    fbar.continuous_toFun ⟨hinj, hsurj⟩

/-- The comparison is the restriction of the original quotient on representatives. -/
theorem residualQuotientPreimageContinuousMulEquiv_apply_mk
    (hC : FiniteGroupClass.FullFormation C)
    (π : G →ₜ* Q) (hπ : IsMaximalProCQuotient C π.toMonoidHom)
    (U : Subgroup Q) (hU : IsClosed (U : Set Q))
    (x : U.comap π.toMonoidHom) :
    residualQuotientPreimageContinuousMulEquiv hC π hπ U hU
        (QuotientGroup.mk' (proCResidualCore C (U.comap π.toMonoidHom)) x) =
      ContinuousMonoidHom.restrictPreimage π U x := by
  rfl

/-- Restricting a maximal quotient to the preimage of a closed subgroup again
satisfies the full maximal-quotient universal property. -/
theorem IsMaximalProCQuotient.restrictPreimage
    (hC : FiniteGroupClass.FullFormation C)
    (π : G →ₜ* Q) (hπ : IsMaximalProCQuotient C π.toMonoidHom)
    (U : Subgroup Q) [CompactSpace U] :
    IsMaximalProCQuotient C (Q := U)
      (ContinuousMonoidHom.restrictPreimage π U).toMonoidHom := by
  have hU : IsClosed (U : Set Q) :=
    (isCompact_iff_compactSpace.mpr (inferInstance : CompactSpace U)).isClosed
  have hJclosed : IsClosed
      ((U.comap π.toMonoidHom : Subgroup G) : Set G) :=
    hU.preimage π.continuous_toFun
  have : CompactSpace (U.comap π.toMonoidHom) :=
    hJclosed.isClosedEmbedding_subtypeVal.compactSpace
  let f : U.comap π.toMonoidHom →ₜ* U :=
    ContinuousMonoidHom.restrictPreimage π U
  have hfsurj : Function.Surjective f :=
    ContinuousMonoidHom.restrictPreimage_surjective π hπ.surjective_π U
  refine
    { hasOpenNormalBasisInClass :=
        HasOpenNormalBasisInClass.of_isClosed_subgroup_of_fullFormation
          hC hπ.hasOpenNormalBasisInClass U hU
      continuous_π := f.continuous_toFun
      surjective_π := hfsurj
      existsUnique_lift := ?_ }
  intro H _instGroupH _instTopologyH _instTopGroupH _instCompactH _instT2H _instDisconnectedH
    hH φ hφ
  let φₜ : U.comap π.toMonoidHom →ₜ* H :=
    { toMonoidHom := φ, continuous_toFun := hφ }
  let e := residualQuotientPreimageContinuousMulEquiv hC π hπ U hU
  let l := lift_proCResidualCoreQuotient hC.hereditary φₜ hH
  let φbar : U →ₜ* H := l.comp (ContinuousMonoidHom.toContinuousMonoidHom e.symm)
  have heq : φbar.toMonoidHom.comp f.toMonoidHom = φ := by
    apply MonoidHom.ext
    intro x
    change l (e.symm (f x)) = φₜ x
    rw [← residualQuotientPreimageContinuousMulEquiv_apply_mk hC π hπ
      U hU x]
    rw [e.symm_apply_apply]
    exact lift_proCResidualCoreQuotient_mk hC.hereditary φₜ hH x
  refine ⟨φbar.toMonoidHom, ⟨φbar.continuous_toFun, heq⟩, ?_⟩
  intro ψ hψ
  apply MonoidHom.ext
  intro u
  obtain ⟨x, rfl⟩ := hfsurj u
  exact (DFunLike.congr_fun hψ.2 x).trans (DFunLike.congr_fun heq x).symm

end ProCGroups.ProC
