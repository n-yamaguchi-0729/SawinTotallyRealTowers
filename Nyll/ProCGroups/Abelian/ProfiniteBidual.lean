/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.Abelian.FiniteBidual
import Nyll.ProCGroups.ProC.OpenNormalSubgroups.Basic
import Nyll.ProCGroups.ProC.OpenNormalSubgroups.BasisAtOne
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Pontryagin biduality for profinite abelian groups

Every circle-valued character factors through a finite quotient, because the
circle has no subgroup contained in a sufficiently small arc. Finite duality
therefore solves any finite set of evaluation equations. Compactness solves
all of them simultaneously. Finite quotients also prove injectivity, giving
the actual topological bidual isomorphism, including finite torsion.
-/

noncomputable section

open ProCGroups.ProC

namespace ProCGroups.Duality

universe u

variable {G : Type u} [CommGroup G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]

/-- A continuous circle-valued character on a profinite group kills an open normal subgroup. -/
theorem exists_openNormal_le_character_ker (χ : PontryaginDual G) :
    ∃ U : OpenNormalSubgroup G, (U : Subgroup G) ≤ χ.toMonoidHom.ker := by
  have hopen : IsOpen (χ ⁻¹' Circle.centeredArc (Real.pi / 2)) :=
    (Circle.isOpen_centeredArc _).preimage χ.continuous
  have hone : (1 : G) ∈ χ ⁻¹' Circle.centeredArc (Real.pi / 2) := by
    change χ 1 ∈ Circle.centeredArc (Real.pi / 2)
    rw [map_one, Circle.mem_centeredArc (div_le_self Real.pi_nonneg (by norm_num))]
    simpa only [Circle.coe_one, Complex.arg_one, abs_zero] using
      (half_pos Real.pi_pos)
  obtain ⟨U, hU⟩ := exists_openNormalSubgroup_sub_open_nhds_of_one hopen hone
  refine ⟨U, fun g hg => ?_⟩
  apply Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two
  intro n _hn
  rw [← map_pow]
  exact hU ((U : Subgroup G).pow_mem hg n)

/-- A finite family of continuous characters factors through a common finite quotient. -/
theorem exists_openNormal_le_character_kers (s : Finset (PontryaginDual G)) :
    ∃ U : OpenNormalSubgroup G, ∀ χ ∈ s, (U : Subgroup G) ≤ χ.toMonoidHom.ker := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨⊤, fun _ h => False.elim (Finset.notMem_empty _ h)⟩
  | @insert χ s _hχ ih =>
    obtain ⟨U, hU⟩ := exists_openNormal_le_character_ker χ
    obtain ⟨V, hV⟩ := ih
    refine ⟨U ⊓ V, fun ψ hψ => ?_⟩
    rcases Finset.mem_insert.mp hψ with rfl | hψ
    · exact fun g hg => hU hg.1
    · exact fun g hg => hV ψ hψ hg.2

/-- Each finite family of bidual evaluation equations has a solution in the original group. -/
theorem exists_finite_evaluation (η : PontryaginDual (PontryaginDual G))
    (s : Finset (PontryaginDual G)) : ∃ g : G, ∀ χ ∈ s, χ g = η χ := by
  obtain ⟨U, hU⟩ := exists_openNormal_le_character_kers s
  let Q := G ⧸ (U : Subgroup G)
  let q : G →ₜ* Q := OpenNormalSubgroup.quotientProj U
  let ηQ : PontryaginDual (PontryaginDual Q) := η.comp (PontryaginDual.map q)
  obtain ⟨a, ha⟩ := (finite_bidualEvaluation_bijective Q).surjective ηQ
  obtain ⟨g, rfl⟩ := OpenNormalSubgroup.quotientProj_surjective U a
  refine ⟨g, fun χ hχ => ?_⟩
  let χQ : PontryaginDual Q := QuotientGroup.liftₜ (U : Subgroup G) χ (hU χ hχ)
  have he : PontryaginDual.map q χQ = χ := ContinuousMonoidHom.ext fun _ => rfl
  exact (congrArg (fun ν : PontryaginDual (PontryaginDual Q) => ν χQ) ha).trans
    (congrArg η he)

/-- Compactness turns finite evaluation solvability into surjectivity onto the actual bidual. -/
theorem profinite_bidualEvaluation_surjective :
    Function.Surjective (bidualEvaluation G) := by
  intro η
  let F : PontryaginDual G → Set G := fun χ => {g | χ g = η χ}
  have hclosed : ∀ χ, IsClosed (F χ) := fun χ =>
    isClosed_eq χ.continuous continuous_const
  have hfinite : ∀ s : Finset (PontryaginDual G), (⋂ χ ∈ s, F χ).Nonempty := by
    intro s
    obtain ⟨g, hg⟩ := exists_finite_evaluation η s
    exact ⟨g, Set.mem_iInter.mpr fun χ => Set.mem_iInter.mpr (hg χ)⟩
  obtain ⟨g, hg⟩ := CompactSpace.iInter_nonempty hclosed hfinite
  exact ⟨g, PontryaginDual.ext fun χ => Set.mem_iInter.mp hg χ⟩

/-- Finite quotient characters separate distinct elements of a profinite abelian group. -/
theorem profinite_bidualEvaluation_injective :
    Function.Injective (bidualEvaluation G) := by
  intro x y h
  by_contra hxy
  have hdiff : x / y ≠ 1 := fun he => hxy (div_eq_one.mp he)
  let W : Set G := ({x / y} : Set G)ᶜ
  have hopen : IsOpen W := isClosed_singleton.isOpen_compl
  have hone : (1 : G) ∈ W := Ne.symm hdiff
  obtain ⟨U, hU⟩ := exists_openNormalSubgroup_sub_open_nhds_of_one hopen hone
  let Q := G ⧸ (U : Subgroup G)
  let q : G →ₜ* Q := OpenNormalSubgroup.quotientProj U
  have hq : q x = q y := by
    apply finite_characters_separate Q
    intro χ
    exact congrArg (fun η : PontryaginDual (PontryaginDual G) =>
      η (PontryaginDual.map q χ)) h
  have hmem : x / y ∈ (U : Subgroup G) :=
    OpenNormalSubgroup.quotientProj_eq_quotientProj_iff.mp hq
  exact hU hmem rfl

/-- A profinite abelian group is canonically isomorphic, with its actual topology,
to its Pontryagin double dual. This retains all torsion. -/
def profiniteBidualEquiv : G ≃ₜ* PontryaginDual (PontryaginDual G) := by
  let e : G ≃* PontryaginDual (PontryaginDual G) :=
    MulEquiv.ofBijective (bidualEvaluation G).toMonoidHom
      ⟨profinite_bidualEvaluation_injective, profinite_bidualEvaluation_surjective⟩
  exact
    { toMulEquiv := e
      continuous_toFun := (bidualEvaluation G).continuous
      continuous_invFun := (Continuous.homeoOfEquivCompactToT2 (f := e.toEquiv)
        (bidualEvaluation G).continuous).continuous_invFun }

/-- The bidual isomorphism is the canonical evaluation pairing. -/
theorem profiniteBidualEquiv_apply (g : G) (χ : PontryaginDual G) :
    profiniteBidualEquiv g χ = χ g := rfl

end ProCGroups.Duality
