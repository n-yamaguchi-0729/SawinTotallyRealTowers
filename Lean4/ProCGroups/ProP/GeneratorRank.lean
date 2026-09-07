import ProCGroups.ProP.BurnsideBasis
import ProCGroups.ProP.ElementaryAbelianRank

set_option autoImplicit false
/-!
# Generator rank of a finitely generated pro-p group

This file packages the natural-valued topological generator rank and proves
that, for a topologically finitely generated pro-`p` group, it equals the
`ZMod p` dimension of the power--commutator quotient.

The quotient structures are canonical but deliberately section-local.  This
keeps them out of global instance search while avoiding repeated `letI`
blocks in theorem statements and proofs.
-/

open Set
open scoped IsMulCommutative

namespace ClassFieldTower.ProP

universe u

open ProCGroups.Generation
open ProCGroups.FiniteGeneration

/-- The natural-valued topological generator rank.  Its intended API is for groups whose
cardinal-valued topological rank is finite. -/
noncomputable def topologicalGeneratorRank
    (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G] : ℕ :=
  Cardinal.toNat (topologicalRank G)

section PowerCommutatorRank

variable {p : ℕ} {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [Fact (Nat.Prime p)]

local instance : (closedPowerCommutator p G).Normal :=
  closedPowerCommutator_normal p G

local instance : IsClosed (closedPowerCommutator p G : Set G) :=
  isClosed_closedPowerCommutator p G

local instance : IsMulCommutative (powerCommutatorQuotient p G) :=
  powerCommutatorQuotient_isMulCommutative p G

local instance : Module (ZMod p) (Additive (powerCommutatorQuotient p G)) :=
  AddCommGroup.zmodModule (fun x => by
    change (Additive.toMul x) ^ p = 1
    exact powerCommutatorQuotient_pow_eq_one p G (Additive.toMul x))

/-- The canonical `ZMod p` dimension of the power--commutator quotient. -/
noncomputable def powerCommutatorQuotientRank : ℕ :=
  Module.finrank (ZMod p) (Additive (powerCommutatorQuotient p G))

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- A topologically finitely generated power--commutator quotient is finite. -/
theorem powerCommutatorQuotient_finite_of_topologicallyFinitelyGenerated
    (hfg : TopologicallyFinitelyGenerated G) :
    Finite (powerCommutatorQuotient p G) := by
  classical
  rcases hfg with ⟨s, hs⟩
  let Y : Set (powerCommutatorQuotient p G) :=
    (powerCommutatorQuotientMk p G) '' (s : Set G)
  have hYfinite : Y.Finite := s.finite_toSet.image _
  let V : Submodule (ZMod p) (Additive (powerCommutatorQuotient p G)) :=
    Submodule.span (ZMod p) (Additive.ofMul '' Y)
  have hVfinite : V.carrier.Finite := by
    simpa [V] using (hYfinite.image Additive.ofMul).submoduleSpan (ZMod p)
  let K : Subgroup (powerCommutatorQuotient p G) :=
    AddSubgroup.toSubgroup' V.toAddSubgroup
  have hKfinite : (K : Set (powerCommutatorQuotient p G)).Finite := by
    change (Additive.ofMul ⁻¹' V.carrier).Finite
    apply hVfinite.preimage
    intro a _ b _ hab
    exact hab
  have hYK : Y ⊆ (K : Set (powerCommutatorQuotient p G)) := by
    intro y hy
    change V.carrier (Additive.ofMul y)
    exact Submodule.subset_span (R := ZMod p) (s := Additive.ofMul '' Y)
      ⟨y, hy, rfl⟩
  have hclosure_le : Subgroup.closure Y ≤ K :=
    (Subgroup.closure_le K).2 hYK
  have hYgen : TopologicallyGenerates (G := powerCommutatorQuotient p G) Y := by
    exact topologicallyGenerates_quotient_image (closedPowerCommutator p G) hs
  have htop_le : (⊤ : Subgroup (powerCommutatorQuotient p G)) ≤ K := by
    rw [← hYgen]
    exact Subgroup.topologicalClosure_minimal _ hclosure_le hKfinite.isClosed
  have hKtop : K = ⊤ := top_unique htop_le
  have huniv : (Set.univ : Set (powerCommutatorQuotient p G)).Finite := by
    simpa [hKtop] using hKfinite
  exact Set.finite_univ_iff.mp huniv

/-- Bounded generation of a finitely generated pro-`p` group is equivalent to the dimension
bound on its power--commutator quotient. -/
theorem topologicallyGeneratedByAtMost_iff_powerCommutatorQuotientRank_le
    (hpG : ProCGroups.ProC.HasPGroupOpenNormalBasis p G)
    (hfg : TopologicallyFinitelyGenerated G) {d : ℕ} :
    TopologicallyGeneratedByAtMost d G ↔ powerCommutatorQuotientRank (p := p) (G := G) ≤ d := by
  let _ : Finite (powerCommutatorQuotient p G) :=
    powerCommutatorQuotient_finite_of_topologicallyFinitelyGenerated hfg
  change TopologicallyGeneratedByAtMost d G ↔
    Module.finrank (ZMod p) (Additive (powerCommutatorQuotient p G)) ≤ d
  constructor
  · intro hd
    have hQ : TopologicallyGeneratedByAtMost d (powerCommutatorQuotient p G) :=
      TopologicallyGeneratedByAtMost.of_surjective
        (powerCommutatorQuotientMk p G)
        (powerCommutatorQuotientMk_surjective p G) hd
    exact finrank_le_of_topologicallyGeneratedByAtMost_zmod hQ
  · intro hdim
    have hbasis :
        TopologicallyGeneratedByAtMost
          (Module.finrank (ZMod p) (Additive (powerCommutatorQuotient p G)))
          (powerCommutatorQuotient p G) :=
      topologicallyGeneratedByAtMost_finrank_zmod
    have hQ : TopologicallyGeneratedByAtMost d (powerCommutatorQuotient p G) :=
      hbasis.mono hdim
    classical
    rcases hQ with ⟨s, hs_card, hs_gen⟩
    let liftQ : powerCommutatorQuotient p G → G :=
      Function.surjInv (powerCommutatorQuotientMk_surjective p G)
    let t : Finset G := s.image liftQ
    refine ⟨t, Finset.card_image_le.trans hs_card, ?_⟩
    apply (topologicallyGenerates_iff_powerCommutatorQuotient_image hpG).2
    have himage :
        (powerCommutatorQuotientMk p G) '' (t : Set G) =
          (s : Set (powerCommutatorQuotient p G)) := by
      ext y
      simp [t, liftQ, Function.surjInv_eq]
    rw [himage]
    exact hs_gen

/-- For a finitely generated pro-`p` group, generator rank is the canonical dimension of the
power--commutator quotient. -/
theorem topologicalGeneratorRank_eq_powerCommutatorQuotientRank
    (hpG : ProCGroups.ProC.HasPGroupOpenNormalBasis p G)
    (hfg : TopologicallyFinitelyGenerated G) :
    topologicalGeneratorRank G = powerCommutatorQuotientRank (p := p) (G := G) := by
  let d := powerCommutatorQuotientRank (p := p) (G := G)
  have hAtD : TopologicallyGeneratedByAtMost d G :=
    (topologicallyGeneratedByAtMost_iff_powerCommutatorQuotientRank_le hpG hfg).2 le_rfl
  have hrank_le : topologicalRank G ≤ (d : Cardinal) :=
    topologicalRank_le_of_topologicallyGeneratedByAtMost hAtD
  have hrank_lt : topologicalRank G < Cardinal.aleph0 :=
    hrank_le.trans_lt Cardinal.natCast_lt_aleph0
  have hcast : (topologicalGeneratorRank G : Cardinal) = topologicalRank G :=
    Cardinal.cast_toNat_of_lt_aleph0 hrank_lt
  apply le_antisymm
  · have hcard : (topologicalGeneratorRank G : Cardinal) ≤ (d : Cardinal) := by
      rw [hcast]
      exact hrank_le
    exact_mod_cast hcard
  · have hrank_eq_nat : topologicalRank G = (topologicalGeneratorRank G : Cardinal) :=
      hcast.symm
    have hAtRank : TopologicallyGeneratedByAtMost (topologicalGeneratorRank G) G :=
      topologicallyGeneratedByAtMost_of_topologicalRank_eq_nat hrank_eq_nat
    exact (topologicallyGeneratedByAtMost_iff_powerCommutatorQuotientRank_le hpG hfg).1 hAtRank

/-- The generator-rank formula written directly as a `ZMod p` finrank equality. -/
theorem topologicalGeneratorRank_eq_powerCommutatorQuotient_finrank
    (hpG : ProCGroups.ProC.HasPGroupOpenNormalBasis p G)
    (hfg : TopologicallyFinitelyGenerated G) :
    topologicalGeneratorRank G =
      Module.finrank (ZMod p) (Additive (powerCommutatorQuotient p G)) := by
  exact topologicalGeneratorRank_eq_powerCommutatorQuotientRank hpG hfg

end PowerCommutatorRank

end ClassFieldTower.ProP
