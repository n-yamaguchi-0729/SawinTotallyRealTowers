/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FiniteGroups.StandardClasses
import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualQuotient
import Nyll.ProCGroups.Abelian.TopologicalAbelianization

/-!
# Prime-to-Sigma powers on actual residual abelianizations

Finite Sigma quotients have order coprime to every excluded prime. Their
power maps are injective, and separation transfers this to a pro-Sigma group.
-/

namespace ProCGroups.ProC

open ProCGroups.Abelian

universe u

/-- Raising to an excluded prime is injective on a Hausdorff group with a
pro-Sigma basis. Commutativity and compactness are unnecessary. -/
theorem HasOpenNormalBasisInClass.pow_left_injective_of_prime_not_mem
    {sigma : Set ℕ} {G : Type u}
    [Group G] [TopologicalSpace G] [T2Space G]
    (hG : HasOpenNormalBasisInClass (FiniteGroupClass.sigmaGroup sigma) G)
    (r : ℕ) [Fact r.Prime] (hr : r ∉ sigma) :
    Function.Injective (fun x : G => x ^ r) := by
  intro x y hxy
  apply hG.eq_of_forall_openNormalSubgroupInClass_quotient_eq
  intro U
  have hcop : (Nat.card (G ⧸ (U.1 : Subgroup G))).Coprime r :=
    ((Fact.out : r.Prime).coprime_iff_not_dvd.mpr
      (U.2.2 r (Fact.out : r.Prime) hr)).symm
  apply hcop.pow_left_bijective.injective
  simpa only [map_pow] using congrArg (QuotientGroup.mk' (U.1 : Subgroup G)) hxy

/-- The actual abelianization of the maximal pro-Sigma residual quotient has
injective r-th power map for every excluded prime r. -/
theorem residualAbelianization_pow_left_injective_of_prime_not_mem
    {sigma : Set ℕ} (G : Type u)
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (r : ℕ) [Fact r.Prime] (hr : r ∉ sigma) :
    Function.Injective (fun x : TopologicalAbelianization
      (G ⧸ proCResidualCore (FiniteGroupClass.sigmaGroup sigma) G) => x ^ r) := by
  let R := proCResidualCore (FiniteGroupClass.sigmaGroup sigma) G
  have : IsClosed (R : Set G) := proCResidualCore_isClosed _ _
  have : TotallyDisconnectedSpace (G ⧸ R) :=
    ProCGroups.totallyDisconnectedSpace_quotient_closedNormal R
      (proCResidualCore_isClosed _ _)
  have hQ : HasOpenNormalBasisInClass (FiniteGroupClass.sigmaGroup sigma) (G ⧸ R) :=
    proCResidualCoreQuotient_hasOpenNormalBasisInClass
      (FiniteGroupClass.sigmaGroup_formation sigma)
  have hA : HasOpenNormalBasisInClass (FiniteGroupClass.sigmaGroup sigma)
      (TopologicalAbelianization (G ⧸ R)) :=
    quotient_closedNormalSubgroup
      (FiniteGroupClass.sigmaGroup sigma).isomClosed
      (FiniteGroupClass.sigmaGroup_quotientClosed sigma) hQ
      (Subgroup.closedCommutator (G ⧸ R)) (Subgroup.isClosed_closedCommutator _)
  exact hA.pow_left_injective_of_prime_not_mem r hr

end ProCGroups.ProC
