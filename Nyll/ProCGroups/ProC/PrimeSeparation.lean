/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import Nyll.ProCGroups.ProC.OpenNormalSubgroups.ProCGroup
import Nyll.ProCGroups.FiniteGroups.PGroupFormation
import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualQuotient
import Nyll.ProCGroups.ProC.Subgroups.Closed

/-!
# Separating distinct pro-prime group classes

Finite quotients of a group that is both pro-p and pro-q have trivial
order at distinct primes. Applying this to the actual residual quotient
shows that the maximal pro-q quotient of a pro-p group is trivial.
-/

namespace ProCGroups.ProC
universe u

/-- A Hausdorff group which is both pro-p and pro-q for distinct primes is trivial. -/
theorem subsingleton_of_hasOpenNormalBasisInClass_distinct_primes
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    (hp : HasOpenNormalBasisInClass (FiniteGroupClass.pGroup p) G)
    (hq : HasOpenNormalBasisInClass (FiniteGroupClass.pGroup q) G) : Subsingleton G := by
  apply subsingleton_of_forall_eq 1
  intro x
  apply hp.eq_one_of_mem_all_openNormalSubgroupInClass
  intro U
  have hQ :=
    hq.quotient_mem (FiniteGroupClass.pGroup_fullFormation q).melnikovFormation.formation U.1
  let z : G ⧸ (U.1 : Subgroup G) := QuotientGroup.mk' (U.1 : Subgroup G) x
  obtain ⟨a, ha⟩ := U.property.2 z
  obtain ⟨b, hb⟩ := hQ.2 z
  have heq : z = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes
      ((Nat.coprime_primes (Fact.out : p.Prime) (Fact.out : q.Prime)).mpr hpq |>.pow a b)
      (orderOf_dvd_of_pow_eq_one ha) (orderOf_dvd_of_pow_eq_one hb))
  exact (QuotientGroup.eq_one_iff (N := (U.1 : Subgroup G)) x).mp heq

/-- The maximal pro-q quotient of a pro-p group is trivial for distinct primes. -/
theorem residualQuotient_subsingleton_of_distinct_primes
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    (hp : HasOpenNormalBasisInClass (FiniteGroupClass.pGroup p) G) :
    Subsingleton (G ⧸ proCResidualCore (FiniteGroupClass.pGroup q) G) := by
  let R := proCResidualCore (FiniteGroupClass.pGroup q) G
  have : IsClosed (R : Set G) := proCResidualCore_isClosed _ _
  let π : G →ₜ* G ⧸ R :=
    { toMonoidHom := QuotientGroup.mk' R
      continuous_toFun := QuotientGroup.continuous_mk }
  have hp' := hp.of_surjective
    (FiniteGroupClass.pGroup_fullFormation p).melnikovFormation.formation π
    (QuotientGroup.mk'_surjective R)
  exact subsingleton_of_hasOpenNormalBasisInClass_distinct_primes p q hpq hp'
    (proCResidualCoreQuotient_hasOpenNormalBasisInClass
      (FiniteGroupClass.pGroup_fullFormation q).melnikovFormation.formation)

end ProCGroups.ProC
