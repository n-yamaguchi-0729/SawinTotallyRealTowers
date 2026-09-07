import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Topology.Algebra.Group.Quotient
import ProCGroups.FiniteGeneration.Basic
import ProCGroups.ProP.FrattiniPowers
import ProCGroups.ProP.FrattiniQuotient
import ProCGroups.ProP.GeneratorRank

set_option autoImplicit false

/-!
# Minimal epimorphisms of finitely generated pro-p groups

Equal generator ranks make the induced epimorphism of finite Frattini quotients
injective. The original kernel therefore lies in the source Frattini subgroup.
-/

open scoped IsMulCommutative

namespace ClassFieldTower.ProP

open ProCGroups.FiniteGeneration

universe u v

-- Fix the module data at the generic field boundary before specializing to a quotient.
private theorem natCard_module
    (K : Type*) (V : Type*) [DivisionRing K] [AddCommGroup V]
    [moduleInst : Module K V] [finiteModuleInst : Module.Finite K V] :
    Nat.card V = Nat.card K ^ Module.finrank K V :=
  Module.natCard_eq_pow_finrank

/-- The Frattini quotient has cardinality p raised to the minimal generator number. -/
theorem natCard_powerCommutatorQuotient
    (p : ℕ) [Fact p.Prime]
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : ProCGroups.ProC.HasPGroupOpenNormalBasis p G)
    (hfg : TopologicallyFinitelyGenerated G) :
    Nat.card (powerCommutatorQuotient p G) = p ^ topologicalGeneratorRank G := by
  let : (closedPowerCommutator p G).Normal := closedPowerCommutator_normal p G
  let : IsClosed (closedPowerCommutator p G : Set G) := isClosed_closedPowerCommutator p G
  let : IsMulCommutative (powerCommutatorQuotient p G) :=
    powerCommutatorQuotient_isMulCommutative p G
  let qModule : Module (ZMod p) (Additive (powerCommutatorQuotient p G)) :=
    AddCommGroup.zmodModule (fun x => by
      change (Additive.toMul x) ^ p = 1
      exact powerCommutatorQuotient_pow_eq_one p G (Additive.toMul x))
  let : Finite (powerCommutatorQuotient p G) :=
    powerCommutatorQuotient_finite_of_topologicallyFinitelyGenerated hfg
  let qFiniteModule : Module.Finite (ZMod p) (Additive (powerCommutatorQuotient p G)) :=
    Module.Finite.of_finite
  have hCardRaw : Nat.card (Additive (powerCommutatorQuotient p G)) =
      Nat.card (ZMod p) ^ Module.finrank (ZMod p) (Additive (powerCommutatorQuotient p G)) :=
    natCard_module (ZMod p) (Additive (powerCommutatorQuotient p G))
      (moduleInst := qModule) (finiteModuleInst := qFiniteModule)
  have hCard : Nat.card (Additive (powerCommutatorQuotient p G)) =
      p ^ Module.finrank (ZMod p) (Additive (powerCommutatorQuotient p G)) :=
    hCardRaw.trans (congrArg (fun n : ℕ => n ^ Module.finrank (ZMod p)
      (Additive (powerCommutatorQuotient p G))) (Nat.card_zmod p))
  exact hCard.trans (congrArg (fun n : ℕ => p ^ n)
    (topologicalGeneratorRank_eq_powerCommutatorQuotient_finrank hG hfg).symm)

/-- A continuous epimorphism between equally generated pro-p groups has Frattini kernel. -/
theorem ker_le_closedPowerCommutator_of_generatorRank_eq
    (p : ℕ) [Fact p.Prime]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (hG : ProCGroups.ProC.HasPGroupOpenNormalBasis p G)
    (hH : ProCGroups.ProC.HasPGroupOpenNormalBasis p H)
    (hfg : TopologicallyFinitelyGenerated G) (hhfg : TopologicallyFinitelyGenerated H)
    (f : G →ₜ* H) (hf : Function.Surjective f)
    (hrank : topologicalGeneratorRank G = topologicalGeneratorRank H) :
    f.toMonoidHom.ker ≤ closedPowerCommutator p G := by
  let : (closedPowerCommutator p G).Normal := closedPowerCommutator_normal p G
  let : (closedPowerCommutator p H).Normal := closedPowerCommutator_normal p H
  let : Finite (powerCommutatorQuotient p G) :=
    powerCommutatorQuotient_finite_of_topologicallyFinitelyGenerated hfg
  let : Finite (powerCommutatorQuotient p H) :=
    powerCommutatorQuotient_finite_of_topologicallyFinitelyGenerated hhfg
  let q : powerCommutatorQuotient p G →* powerCommutatorQuotient p H :=
    QuotientGroup.map _ _ f.toMonoidHom
      (Subgroup.map_le_iff_le_comap.mp (closedPowerCommutator_map_le p G f))
  have hqsurj : Function.Surjective q := by
    intro y
    obtain ⟨h, rfl⟩ := powerCommutatorQuotientMk_surjective p H y
    obtain ⟨g, rfl⟩ := hf h
    exact ⟨powerCommutatorQuotientMk p G g, rfl⟩
  have hcard : Nat.card (powerCommutatorQuotient p G) =
      Nat.card (powerCommutatorQuotient p H) := by
    rw [natCard_powerCommutatorQuotient p G hG hfg,
      natCard_powerCommutatorQuotient p H hH hhfg, hrank]
  have hqinj : Function.Injective q :=
    ((Nat.bijective_iff_surjective_and_card q).mpr ⟨hqsurj, hcard⟩).injective
  intro g hg
  apply (QuotientGroup.eq_one_iff g).mp
  apply hqinj
  change powerCommutatorQuotientMk p H (f g) = q 1
  rw [show f g = 1 from hg, map_one, map_one]

end ClassFieldTower.ProP
