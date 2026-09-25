/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import GaloisCohomology.ProP.H2FiniteStageFamily
import Mathlib.LinearAlgebra.Dimension.Finite

set_option autoImplicit false
/-!
# Bounding degree two from finite-stage inflation ranges

If every finite-stage inflation range embeds in one fixed finite-dimensional target, then finite
families of ambient classes descending to a common stage force the whole ambient degree-two
cohomology to have the same dimension bound.  The stage embeddings need not be compatible.
-/

open scoped Topology

namespace ClassFieldTower.Cohomology

open ProCGroups ProCGroups.ProC

noncomputable section

universe u v

variable {p : ℕ} [Fact p.Prime]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
variable {W : Type v} [AddCommGroup W] [Module (ZMod p) W]

/-- A uniform finite-dimensional target for the finite-stage inflation ranges bounds the ambient
lifted degree-two cohomology.  No compatibility between the stagewise embeddings is required. -/
theorem finiteDimensional_and_finrank_degree_two_le_of_inflationRange_embeddings
    [FiniteDimensional (ZMod p) W]
    (hG : HasOpenNormalBasisInClass (FiniteGroupClass.pGroup p) G)
    (hEmbed : ∀ U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G,
      ∃ f : degreeTwoInflationRange (p := p) U →ₗ[ZMod p] W,
        Function.Injective f) :
    FiniteDimensional (ZMod p) (continuousCohomologyZModPLifted p G 2) ∧
      Module.finrank (ZMod p) (continuousCohomologyZModPLifted p G 2) ≤
        Module.finrank (ZMod p) W := by
  let V := continuousCohomologyZModPLifted p G 2
  have hrank : Module.rank (ZMod p) V ≤
      (Module.finrank (ZMod p) W : Cardinal) := by
    apply rank_le
    intro s hs
    obtain ⟨U, xU, hxU⟩ :=
      exists_openNormalSubgroupInClass_inflation_eq_degree_two_family hG
        (fun i : s ↦ (i : V))
    obtain ⟨fU, hfU⟩ := hEmbed U
    let y : s → degreeTwoInflationRange (p := p) U := fun i ↦
      ⟨i, xU i, hxU i⟩
    have hy : LinearIndependent (ZMod p) y := by
      apply LinearIndependent.of_comp (Submodule.subtype _)
      simpa [y, Function.comp_def] using hs
    have hfy : LinearIndependent (ZMod p) (fU ∘ y) :=
      hy.map' fU (LinearMap.ker_eq_bot.mpr hfU)
    simpa using hfy.fintype_card_le_finrank
  have hrank_lt : Module.rank (ZMod p) V < Cardinal.aleph0 :=
    hrank.trans_lt Cardinal.natCast_lt_aleph0
  let b := Module.Free.chooseBasis (ZMod p) V
  let : Fintype (Module.Free.ChooseBasisIndex (ZMod p) V) :=
    b.fintypeIndexOfRankLtAleph0 hrank_lt
  have hFinite : FiniteDimensional (ZMod p) V :=
    b.finiteDimensional_of_finite
  refine ⟨hFinite, ?_⟩
  let : FiniteDimensional (ZMod p) V := hFinite
  exact FiniteDimensional.finrank_le_iff_rank_le.mpr hrank

end

end ClassFieldTower.Cohomology
