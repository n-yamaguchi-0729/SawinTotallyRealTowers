/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
Statement adapted from Lean Eval:
https://github.com/leanprover/lean-eval/blob/4ae7061fe4b0b70dcb7fe24fdee067b68636226b/generated/shafarevich_relation_rank_bound/Challenge.lean
Lean Eval repository: Copyright 2026 Lean FRO, LLC; Apache 2.0.
-/

import GaloisCohomology.ProP.SmallLiftedComparison
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Global.FrattiniClassField
import ProCGroups.ProP.FiniteGeneratorRankBridge

set_option autoImplicit false
/-!
# Adapter infrastructure for the LeanEval Shafarevich statement

This file isolates the three representation differences between the
production theorem and the trusted benchmark statement: the explicit
everywhere-unramified predicate, finite-set generator rank, and small versus
universe-lifted trivial cohomology coefficients.
-/

open scoped NumberField Topology

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.Cohomology
open ClassFieldTower.ProP
open ProCGroups.Generation
open ProCGroups.FiniteGeneration

universe u v

/-- The finite-prime and real-place formula used as the trusted benchmark's
everywhere-unramified predicate. -/
def ExplicitIsEverywhereUnramified
    (F : Type u) (M : Type v)
    [Field F] [Field M] [NumberField F] [NumberField M]
    [Algebra F M] : Prop :=
  (∀ (𝔭 : Ideal (𝓞 F)) (𝔓 : Ideal (𝓞 M)),
      𝔭.IsPrime → 𝔭 ≠ ⊥ →
      𝔓 ∈ 𝔭.primesOver (𝓞 M) →
      𝔓.ramificationIdx (𝓞 F) = 1) ∧
  (∀ w : NumberField.InfinitePlace F, w.IsReal →
    ∀ w' : NumberField.InfinitePlace M,
      w'.comap (algebraMap F M) = w → w'.IsReal)

/-- The library predicate and the benchmark's explicit predicate agree. -/
theorem isEverywhereUnramified_iff_explicitPredicate
    (F : Type u) (M : Type v)
    [Field F] [Field M] [NumberField F] [NumberField M]
    [Algebra F M] :
    IsEverywhereUnramified F M ↔ ExplicitIsEverywhereUnramified F M :=
  isEverywhereUnramified_iff_explicit

/-- The maximal compositum written with the explicit benchmark predicate. -/
def explicitMaximalEverywhereUnramifiedProP
    (F : Type u) [Field F] [NumberField F]
    (p : ℕ) [Fact p.Prime] :
    IntermediateField F (AlgebraicClosure F) :=
  ⨆ (M : IntermediateField F (AlgebraicClosure F))
      (_ : FiniteDimensional F M)
      (_ : IsGalois F M)
      (_ : IsPGroup p (M ≃ₐ[F] M))
      (_ : NumberField M)
      (_ : ExplicitIsEverywhereUnramified F M),
    M

/-- Replacing the structured unramified predicate by its explicit clauses
does not change the maximal compositum. -/
theorem maximalEverywhereUnramifiedProP_eq_explicit
    (F : Type u) [Field F] [NumberField F]
    (p : ℕ) [Fact p.Prime] :
    maximalEverywhereUnramifiedProP F p =
      explicitMaximalEverywhereUnramifiedProP F p := by
  rw [maximalEverywhereUnramifiedProP,
    explicitMaximalEverywhereUnramifiedProP]
  simp_rw [isEverywhereUnramified_iff_explicitPredicate F]

/-- The maximal everywhere-unramified pro-`p` Galois group is topologically
finitely generated for odd `p`. -/
theorem maxEverywhereUnramifiedProPGaloisGroup_topologicallyFinitelyGenerated
    (F : Type) [Field F] [NumberField F]
    (p : ℕ) [Fact p.Prime] (hpOdd : Odd p) :
    TopologicallyFinitelyGenerated
      (MaxEverywhereUnramifiedProPGaloisGroup F p) := by
  classical
  let G := MaxEverywhereUnramifiedProPGaloisGroup F p
  let : (closedPowerCommutator p G).Normal :=
    closedPowerCommutator_normal p G
  let E := hilbertElementaryLayerInMaximal F p
  let e : powerCommutatorQuotient p G ≃*
      Gal(E / F) := maxPowerCommutatorEquivHilbert F p hpOdd
  let : Finite (powerCommutatorQuotient p G) :=
    Finite.of_equiv Gal(E / F) e.symm.toEquiv
  have hpG : ProCGroups.ProC.HasPGroupOpenNormalBasis p G :=
    maxEverywhereUnramifiedProPGaloisGroup_hasPGroupOpenNormalBasis
      F p hpOdd
  let : Fintype (powerCommutatorQuotient p G) := Fintype.ofFinite _
  let liftQ : powerCommutatorQuotient p G → G :=
    Function.surjInv (powerCommutatorQuotientMk_surjective p G)
  let S : Finset G := Finset.univ.image liftQ
  refine ⟨S, (topologicallyGenerates_iff_powerCommutatorQuotient_image hpG).2 ?_⟩
  have himage :
      (powerCommutatorQuotientMk p G) '' (S : Set G) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    refine ⟨liftQ z, ?_, ?_⟩
    · simp [S]
    · exact Function.surjInv_eq
        (powerCommutatorQuotientMk_surjective p G) z
  rw [himage]
  apply top_unique
  rw [Subgroup.closure_univ]
  exact Subgroup.le_topologicalClosure _

/-- A production bound for lifted cohomology converts directly to the
small-coefficient and finite-generator-rank presentation used by LeanEval. -/
theorem smallH2_and_finiteGeneratorRank_bound_of_lifted
    (p : ℕ) [Fact p.Prime]
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : TopologicallyFinitelyGenerated G)
    (a b : ℕ)
    (h : FiniteDimensional (ZMod p)
          (continuousCohomologyZModPLifted p G 2) ∧
        Module.finrank (ZMod p)
            (continuousCohomologyZModPLifted p G 2) ≤
          topologicalGeneratorRank G + a + b) :
    FiniteDimensional (ZMod p) (continuousCohomologyZModP p G 2) ∧
      Module.finrank (ZMod p) (continuousCohomologyZModP p G 2) ≤
        finiteTopologicalGeneratorRank G + a + b := by
  refine ⟨(continuousCohomologyZModP_finiteDimensional_iff_lifted
    p G 2).2 h.1, ?_⟩
  rw [← continuousCohomologyZModPLiftedSmall_finrank_eq p G 2,
    finiteTopologicalGeneratorRank_eq_topologicalGeneratorRank G hG]
  exact h.2

/-- Maximal-group specialization of the LeanEval rank/coefficient adapter. -/
theorem maxEverywhereUnramified_smallH2_and_finiteGeneratorRank_bound_of_lifted
    (F : Type) [Field F] [NumberField F]
    (p : ℕ) [Fact p.Prime] (hpOdd : Odd p)
    (a b : ℕ)
    (h : FiniteDimensional (ZMod p)
          (continuousCohomologyZModPLifted p
            (MaxEverywhereUnramifiedProPGaloisGroup F p) 2) ∧
        Module.finrank (ZMod p)
            (continuousCohomologyZModPLifted p
              (MaxEverywhereUnramifiedProPGaloisGroup F p) 2) ≤
          topologicalGeneratorRank
              (MaxEverywhereUnramifiedProPGaloisGroup F p) + a + b) :
    FiniteDimensional (ZMod p)
        (continuousCohomologyZModP p
          (MaxEverywhereUnramifiedProPGaloisGroup F p) 2) ∧
      Module.finrank (ZMod p)
          (continuousCohomologyZModP p
            (MaxEverywhereUnramifiedProPGaloisGroup F p) 2) ≤
        finiteTopologicalGeneratorRank
            (MaxEverywhereUnramifiedProPGaloisGroup F p) + a + b :=
  smallH2_and_finiteGeneratorRank_bound_of_lifted p
    (MaxEverywhereUnramifiedProPGaloisGroup F p)
    (maxEverywhereUnramifiedProPGaloisGroup_topologicallyFinitelyGenerated
      F p hpOdd) a b h

end ClassFieldTower.Martinet.Shafarevich
