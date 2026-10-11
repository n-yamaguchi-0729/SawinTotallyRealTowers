/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Ramification.FiniteFixedResidueLift
import Mathlib.Data.Set.Lattice.Indexed
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order

/-!
# Profinite residue lifts by compact intersection

For each open normal subgroup N, take the actual elements of G whose residue
equations hold on every N-fixed original coefficient. These sets are closed,
nonempty by the finite quotient lift, and directed downward by intersection
of open normal subgroups. Compactness supplies a common element. Open point
stabilizers then extend its equation to every original coefficient.

All equations live in B/q. No fixed-ring quotient, auxiliary lift functor,
additional target algebra, or presumed residue surjectivity is used.
-/

namespace EtaleFundamentalGroups.Inertia

private def residueLiftSet
    {B G : Type*} [CommRing B] [Group G] [MulSemiringAction G B]
    [TopologicalSpace G] (q : Ideal B) (φ : (B ⧸ q) ≃+* (B ⧸ q))
    (N : OpenNormalSubgroup G) : Set G :=
  {g | ∀ x : B, (∀ n ∈ N.toSubgroup, n • x = x) →
    (Ideal.Quotient.mk q).toFun (g • x) = φ.toRingHom.toFun ((Ideal.Quotient.mk q).toFun x)}

private theorem residueEquation_isClosed
    {B G : Type*} [CommRing B] [Group G] [MulSemiringAction G B]
    [TopologicalSpace G] [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul G B]
    (q : Ideal B) (φ : (B ⧸ q) ≃+* (B ⧸ q)) (x : B) :
    IsClosed {g : G | (Ideal.Quotient.mk q).toFun (g • x) =
      φ.toRingHom.toFun ((Ideal.Quotient.mk q).toFun x)} := by
  have hcont : Continuous (fun g : G => g • x) := continuous_id.smul continuous_const
  exact (isClosed_discrete {y : B | (Ideal.Quotient.mk q).toFun y =
    φ.toRingHom.toFun ((Ideal.Quotient.mk q).toFun x)}).preimage hcont

private theorem residueLiftSet_isClosed
    {B G : Type*} [CommRing B] [Group G] [MulSemiringAction G B]
    [TopologicalSpace G] [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul G B]
    (q : Ideal B) (φ : (B ⧸ q) ≃+* (B ⧸ q)) (N : OpenNormalSubgroup G) :
    IsClosed (residueLiftSet q φ N) := by
  simp only [residueLiftSet, Set.ofPred_forall]
  exact isClosed_iInter (fun x : B => isClosed_iInter
    (fun _hx : ∀ n ∈ N.toSubgroup, n • x = x => residueEquation_isClosed q φ x))

private theorem residueLiftSet_directed
    {B G : Type*} [CommRing B] [Group G] [MulSemiringAction G B]
    [TopologicalSpace G] (q : Ideal B) (φ : (B ⧸ q) ≃+* (B ⧸ q)) :
    Directed (fun S T : Set G => T ⊆ S) (residueLiftSet q φ) := by
  intro N M
  refine ⟨N ⊓ M, ?_, ?_⟩
  · intro g hg x hx
    exact hg x (fun n hn => hx n hn.1)
  · intro g hg x hx
    exact hg x (fun n hn => hx n hn.2)

private theorem residueLiftSet_nonempty
    (A : Type*) {B G : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
    [Algebra.IsInvariant A B G]
    [TopologicalSpace G] [CompactSpace G] [IsTopologicalGroup G]
    (q : Ideal B) [q.IsPrime] (φ : (B ⧸ q) ≃+* (B ⧸ q))
    (hφ : φ.toRingHom.comp ((Ideal.Quotient.mk q).comp (algebraMap A B)) =
      (Ideal.Quotient.mk q).comp (algebraMap A B))
    (N : OpenNormalSubgroup G) : (residueLiftSet q φ N).Nonempty := by
  have : Finite (G ⧸ N.toSubgroup) :=
    Subgroup.quotient_finite_of_isOpen N.toSubgroup N.isOpen
  exact exists_residue_lift_on_fixed_elements A B G N.toSubgroup q φ hφ

private theorem openNormal_nonempty
    (G : Type*) [Group G] [TopologicalSpace G] [CompactSpace G]
    [TotallyDisconnectedSpace G] [IsTopologicalGroup G] :
    Nonempty (OpenNormalSubgroup G) := by
  obtain ⟨N, _hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (G := G) isOpen_univ (Set.mem_univ (1 : G))
  exact ⟨N⟩

private theorem exists_openNormal_fixing
    (G : Type*) {X : Type*} [Group G] [MulAction G X]
    [TopologicalSpace G] [CompactSpace G] [TotallyDisconnectedSpace G]
    [IsTopologicalGroup G] [TopologicalSpace X] [DiscreteTopology X] [ContinuousSMul G X]
    (x : X) :
    ∃ N : OpenNormalSubgroup G, ∀ n ∈ N.toSubgroup, n • x = x := by
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (stabilizer_isOpen G x) (Subgroup.one_mem (MulAction.stabilizer G x))
  exact ⟨N, fun n hn => hN hn⟩

/-- A profinite invariant action lifts every residue automorphism fixing
its original coefficients to one original group element, on all elements. -/
theorem profiniteInvariant_exists_residue_lift
    (A : Type*) {B G : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
    [Algebra.IsInvariant A B G]
    [TopologicalSpace G] [CompactSpace G] [TotallyDisconnectedSpace G]
    [IsTopologicalGroup G] [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul G B]
    (q : Ideal B) [q.IsPrime] (φ : (B ⧸ q) ≃+* (B ⧸ q))
    (hφ : φ.toRingHom.comp ((Ideal.Quotient.mk q).comp (algebraMap A B)) =
      (Ideal.Quotient.mk q).comp (algebraMap A B)) :
    ∃ g : G, ∀ x : B, (Ideal.Quotient.mk q).toFun (g • x) =
      φ.toRingHom.toFun ((Ideal.Quotient.mk q).toFun x) := by
  have : Nonempty (OpenNormalSubgroup G) := openNormal_nonempty G
  have hclosed : ∀ N : OpenNormalSubgroup G, IsClosed (residueLiftSet q φ N) :=
    fun N => residueLiftSet_isClosed q φ N
  obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    (residueLiftSet q φ) (residueLiftSet_directed q φ)
    (residueLiftSet_nonempty A q φ hφ) (fun N => (hclosed N).isCompact) hclosed
  refine ⟨g, ?_⟩
  intro x
  obtain ⟨N, hN⟩ := exists_openNormal_fixing G x
  exact Set.mem_iInter.mp hg N x hN

end EtaleFundamentalGroups.Inertia
