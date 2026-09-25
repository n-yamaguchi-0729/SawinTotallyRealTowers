/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import GaloisCohomology.ProP.H2FiniteStage
import Mathlib.LinearAlgebra.Dimension.Free

set_option autoImplicit false
/-!
# Common finite-stage realization of degree-two classes

Finite families of lifted degree-two classes of a pro-`p` group inflate from one common finite
`p`-group quotient.  In particular, the ranges of finite-stage inflation cover the ambient
degree-two cohomology.
-/

open scoped Topology

namespace ClassFieldTower.Cohomology

open CategoryTheory
open ProCGroups ProCGroups.ProC

noncomputable section

universe u v

variable {p : ℕ} [Fact p.Prime]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

private theorem finiteDimensional_zmod_of_finite
    {V : Type v} [AddCommGroup V] [Module (ZMod p) V]
    (hV : Finite V) : FiniteDimensional (ZMod p) V := by
  let : Finite V := hV
  let b := Module.Free.chooseBasis (ZMod p) V
  let : Finite (Module.Free.ChooseBasisIndex (ZMod p) V) :=
    Finite.of_injective b b.injective
  exact b.finiteDimensional_of_finite

private theorem finite_resolutionX_trivial
    (Q : Type u) [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    (hQ : Finite Q) (n : ℕ) :
    Finite (TopRep.resolutionX (trivialZModPLifted p Q) n) := by
  let : Finite Q := hQ
  induction n with
  | zero =>
      change Finite (ULift.{u} (ZMod p))
      infer_instance
  | succ n ih =>
      let : Finite (TopRep.resolutionX (trivialZModPLifted p Q) n) := ih
      change Finite C(Q, TopRep.resolutionX (trivialZModPLifted p Q) n)
      exact Finite.of_injective
        (fun f : C(Q, TopRep.resolutionX (trivialZModPLifted p Q) n) ↦
          (f : Q → TopRep.resolutionX (trivialZModPLifted p Q) n))
        ContinuousMap.coe_injective

/-- Lifted mod-`p` degree-two continuous cohomology of a finite group is finite-dimensional.

This is proved from finiteness of the homogeneous cochain space, not assumed as a separate
finite-stage input. -/
theorem finiteDimensional_degree_two_of_finite
    {Q : Type u} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    (hQ : Finite Q) :
    FiniteDimensional (ZMod p) (continuousCohomologyZModPLifted p Q 2) := by
  let : Finite Q := hQ
  have hCochains : Finite ((trivialZModPCochainsLifted p Q).X 2) := by
    let : Finite (TopRep.resolutionX (trivialZModPLifted p Q) 3) :=
      finite_resolutionX_trivial Q hQ 3
    change Finite ((TopRep.resolutionX (trivialZModPLifted p Q) 3).ρ.invariants)
    infer_instance
  let : FiniteDimensional (ZMod p) ((trivialZModPCochainsLifted p Q).X 2) :=
    finiteDimensional_zmod_of_finite hCochains
  let : FiniteDimensional (ZMod p) (trivialZModPCocyclesLifted p Q 2) :=
    FiniteDimensional.of_injective
      ((trivialZModPCochainsLifted p Q).iCycles 2).hom.toLinearMap
      (topModule_mono_injective_lifted
        ((trivialZModPCochainsLifted p Q).iCycles 2))
  exact FiniteDimensional.of_surjective
    (ContinuousCohomology.π (trivialZModPLifted p Q) 2).hom.toLinearMap
    (ProP.PresentationH2Aux.homologyπ_surjective
      (trivialZModPLifted p Q) 2)

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- Inflating after transition to a finer quotient agrees with inflation from the original
quotient. -/
private theorem inflation_transition_eq
    {U V : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G}
    (hVU : (V.1 : Subgroup G) ≤ (U.1 : Subgroup G))
    (xU : continuousCohomologyZModPLifted p
      (G ⧸ (U.1 : Subgroup G)) 2) :
    continuousCohomologyZModPMapLifted p
        (OpenNormalSubgroupInClass.quotientProj V) 2
        (continuousCohomologyZModPMapLifted p
          (OpenNormalSubgroupInClass.transition hVU) 2 xU) =
      continuousCohomologyZModPMapLifted p
        (OpenNormalSubgroupInClass.quotientProj U) 2 xU := by
  change
    (continuousCohomologyZModPMapLifted p
          (OpenNormalSubgroupInClass.transition hVU) 2 ≫
        continuousCohomologyZModPMapLifted p
          (OpenNormalSubgroupInClass.quotientProj V) 2) xU = _
  rw [← continuousCohomologyZModPMapLifted_comp,
    OpenNormalSubgroupInClass.transition_comp_quotientProj]

/-- A finite set of lifted degree-two classes inflates from one common finite `p`-group
quotient. -/
private theorem exists_common_inflation_finset
    {ι : Type v}
    (hG : HasOpenNormalBasisInClass (FiniteGroupClass.pGroup p) G)
    (x : ι → continuousCohomologyZModPLifted p G 2)
    (s : Finset ι) :
    ∃ U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G,
      ∀ i, i ∈ s →
        ∃ xU : continuousCohomologyZModPLifted p
            (G ⧸ (U.1 : Subgroup G)) 2,
          continuousCohomologyZModPMapLifted p
            (OpenNormalSubgroupInClass.quotientProj U) 2 xU = x i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨OpenNormalSubgroupInClass.top, by simp⟩
  | @insert a s ha ih =>
      obtain ⟨U, hU⟩ := ih
      obtain ⟨V, xV, hxV⟩ :=
        exists_openNormalSubgroupInClass_inflation_eq_degree_two hG (x a)
      let W := OpenNormalSubgroupInClass.inf
        (FiniteGroupClass.pGroup_formation p) U V
      have hWU : (W.1 : Subgroup G) ≤ (U.1 : Subgroup G) := by
        exact inf_le_left
      have hWV : (W.1 : Subgroup G) ≤ (V.1 : Subgroup G) := by
        exact inf_le_right
      refine ⟨W, ?_⟩
      intro i hi
      rw [Finset.mem_insert] at hi
      rcases hi with rfl | hi
      · refine ⟨continuousCohomologyZModPMapLifted p
          (OpenNormalSubgroupInClass.transition hWV) 2 xV, ?_⟩
        exact (inflation_transition_eq hWV xV).trans hxV
      · obtain ⟨xiU, hxiU⟩ := hU i hi
        refine ⟨continuousCohomologyZModPMapLifted p
          (OpenNormalSubgroupInClass.transition hWU) 2 xiU, ?_⟩
        exact (inflation_transition_eq hWU xiU).trans hxiU

/-- Every finite family of lifted degree-two classes of a pro-`p` group inflates from one common
finite `p`-group quotient. -/
theorem exists_openNormalSubgroupInClass_inflation_eq_degree_two_family
    {ι : Type v} [Fintype ι]
    (hG : HasOpenNormalBasisInClass (FiniteGroupClass.pGroup p) G)
    (x : ι → continuousCohomologyZModPLifted p G 2) :
    ∃ U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G,
      ∃ xU : ι → continuousCohomologyZModPLifted p
          (G ⧸ (U.1 : Subgroup G)) 2,
        ∀ i,
          continuousCohomologyZModPMapLifted p
            (OpenNormalSubgroupInClass.quotientProj U) 2 (xU i) = x i := by
  classical
  obtain ⟨U, hU⟩ := exists_common_inflation_finset hG x Finset.univ
  choose xU hxU using fun i ↦ hU i (Finset.mem_univ i)
  exact ⟨U, xU, hxU⟩

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- The subspace of ambient degree-two classes inflated from a fixed finite quotient. -/
noncomputable abbrev degreeTwoInflationRange
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G) :
    Submodule (ZMod p) (continuousCohomologyZModPLifted p G 2) :=
  LinearMap.range
    (continuousCohomologyZModPMapLifted p
      (OpenNormalSubgroupInClass.quotientProj U) 2).hom.toLinearMap

/-- Finite-stage inflation ranges cover all lifted degree-two classes. -/
theorem iSup_degreeTwoInflationRange_eq_top
    (hG : HasOpenNormalBasisInClass (FiniteGroupClass.pGroup p) G) :
    (⨆ U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G,
      degreeTwoInflationRange (p := p) U) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨U, xU, hxU⟩ :=
    exists_openNormalSubgroupInClass_inflation_eq_degree_two hG x
  apply (le_iSup
    (fun V : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G ↦
      degreeTwoInflationRange (p := p) V) U)
  exact ⟨xU, hxU⟩

end

end ClassFieldTower.Cohomology
