/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FiniteGroups.StandardClasses
import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualCore

/-!
# Pro-p subgroups in the Sigma residual core

When `p` is outside `sigma`, every continuous map from a group with an
open-normal p-group basis to a Hausdorff group with a Sigma-group basis is
trivial. Thus every pro-p subgroup lies in the actual Sigma residual core.
The subgroup need not be closed or normal, and no compactness is required.
-/

namespace ProCGroups.ProC

universe u v

/-- A continuous map from a group with a pro-p basis to a finite discrete
Sigma-group is trivial when `p` is excluded from `sigma`. -/
theorem continuousMonoidHom_eq_one_of_proP_to_finite_sigmaGroup
    {G : Type u} [Group G] [TopologicalSpace G]
    {Q : Type v} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
    (p : ℕ) [Fact p.Prime] {sigma : Set ℕ} (hp : p ∉ sigma)
    (hG : HasOpenNormalBasisInClass (FiniteGroupClass.pGroup p) G)
    (hQ : FiniteGroupClass.sigmaGroup sigma Q)
    (f : G →ₜ* Q) (x : G) : f x = 1 := by
  have : Finite Q := hQ.1
  have hquot : FiniteGroupClass.pGroup p (G ⧸ f.toMonoidHom.ker) :=
    hG.quotient_mem (FiniteGroupClass.pGroup_formation p) (OpenNormalSubgroup.ker f)
  let e : G ⧸ f.toMonoidHom.ker ≃* f.toMonoidHom.range :=
    QuotientGroup.quotientKerEquivRange f.toMonoidHom
  have hrangeP : IsPGroup p f.toMonoidHom.range :=
    hquot.2.of_surjective e.toMonoidHom e.surjective
  have hrangeSigma : FiniteGroupClass.sigmaGroup sigma f.toMonoidHom.range :=
    FiniteGroupClass.sigmaGroup_subgroupClosed sigma f.toMonoidHom.range hQ
  let y : f.toMonoidHom.range := ⟨f x, ⟨x, rfl⟩⟩
  have hy : y = 1 := by
    by_contra hne
    exact hrangeSigma.2 p (Fact.out : p.Prime) hp
      ((hrangeP.dvd_orderOf hne).trans (orderOf_dvd_natCard y))
  exact congrArg (fun a : f.toMonoidHom.range => (a : Q)) hy

/-- Finite Sigma quotients separate a Hausdorff group with a pro-Sigma basis,
so every continuous map to it from a pro-p group is trivial for excluded p. -/
theorem continuousMonoidHom_eq_one_of_proP_to_proSigma
    {G : Type u} [Group G] [TopologicalSpace G]
    {H : Type v} [Group H] [TopologicalSpace H] [ContinuousMul H] [T2Space H]
    (p : ℕ) [Fact p.Prime] {sigma : Set ℕ} (hp : p ∉ sigma)
    (hG : HasOpenNormalBasisInClass (FiniteGroupClass.pGroup p) G)
    (hH : HasOpenNormalBasisInClass (FiniteGroupClass.sigmaGroup sigma) H)
    (f : G →ₜ* H) (x : G) : f x = 1 := by
  apply hH.eq_one_of_mem_all_openNormalSubgroupInClass
  intro U
  apply (QuotientGroup.eq_one_iff (N := (U.1 : Subgroup H)) (f x)).mp
  exact continuousMonoidHom_eq_one_of_proP_to_finite_sigmaGroup p hp hG U.2
    ((OpenNormalSubgroup.quotientProj U.1).comp f) x

/-- Every subgroup with a pro-p basis lies in the actual Sigma residual core
when `p` is excluded. Neither closedness nor normality of the subgroup is needed. -/
theorem subgroup_le_sigmaResidualCore_of_proP
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (p : ℕ) [Fact p.Prime] {sigma : Set ℕ} (hp : p ∉ sigma)
    (P : Subgroup G)
    (hP : HasOpenNormalBasisInClass (FiniteGroupClass.pGroup p) P) :
    P ≤ proCResidualCore (FiniteGroupClass.sigmaGroup sigma) G := by
  change P ≤ sInf (Set.range fun N :
    ProCQuotientKernel (FiniteGroupClass.sigmaGroup sigma) G => N.toSubgroup)
  apply le_sInf
  rintro _ ⟨N, rfl⟩
  have : IsClosed (N.toSubgroup : Set G) := N.isClosed'
  intro x hx
  let f : P →ₜ* G ⧸ N.toSubgroup :=
    { toMonoidHom := (QuotientGroup.mk' N.toSubgroup).comp P.subtype
      continuous_toFun := continuous_quotient_mk'.comp continuous_subtype_val }
  exact (QuotientGroup.eq_one_iff (N := N.toSubgroup) x).mp
    (continuousMonoidHom_eq_one_of_proP_to_proSigma p hp hP
      N.quotient_hasOpenNormalBasisInClass f ⟨x, hx⟩)

end ProCGroups.ProC
