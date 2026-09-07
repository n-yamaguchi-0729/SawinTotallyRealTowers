import ProCGroups.GolodShafarevich.FiniteDimensions
import ProCGroups.GolodShafarevich.NumericalCriterion
import ProCGroups.GolodShafarevich.TruncatedInequality
import ProCGroups.ProP.Presentation.RelationCardinal
import ProCGroups.ProP.Presentation.RelatorDepth

set_option autoImplicit false
/-!
# Finite Golod--Shafarevich bound

The truncated Fox inequality and its numerical criterion imply the classical
strict bound `d² < 4r` for a finite nontrivial pro-`p` group.  The result is
first stated for a concrete minimal presentation and then for the canonical
minimal relation rank.  Its contrapositive is the reusable infinitude
criterion.
-/

open scoped Topology

namespace ClassFieldTower.ProP

open ProCGroups
open ProCGroups.Generation

noncomputable section

universe u

namespace FiniteProPPresentation

variable {p d r : ℕ} [Fact p.Prime]
variable {sourceData :
  FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u}
    (FiniteGroupClass.pGroup p)}
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- A minimal presentation of a nontrivial target has a positive displayed
generator count. -/
theorem displayedGeneratorCard_pos
    [Nontrivial G]
    (P : FiniteProPPresentation p d r sourceData G)
    (hP : P.IsMinimal) :
    0 < d := by
  apply Nat.pos_of_ne_zero
  intro hd
  apply topologicalRank_ne_zero (G := G)
  rw [P.target_topologicalRank_eq_nat hP, hd]
  norm_num

/-- The strict Golod--Shafarevich bound for one concrete finite minimal
presentation. -/
theorem finite_sq_generatorCard_lt_four_mul_relationCard
    [Finite G] [Nontrivial G]
    (P : FiniteProPPresentation p d r sourceData G)
    (hP : P.IsMinimal) :
    d ^ 2 < 4 * r := by
  let ν : Fin r → ℕ := fun _ ↦ 2
  let A : ℕ → ℕ :=
    truncatedAugmentationDimension (p := p) (G := G)
  have hdepth : ∀ i, 2 ≤ ν i := fun _ ↦ le_rfl
  have hrelDepth : ∀ i, P.RelatorZassenhausDepthAtLeast (ν i) i := by
    intro i
    exact P.relatorZassenhausDepthAtLeast_two hP i
  have hineq : ∀ N,
      1 + d * backshift A N 1 ≤
        A N + ∑ i : Fin r, backshift A N (ν i) := by
    intro N
    simpa [A, ν, backshift, truncatedAugmentationDimensionStar] using
      finitePresentation_truncatedCoefficientInequality P ν hrelDepth N
  exact square_generator_lt_four_relations_of_truncated ν A
    (truncatedAugmentationDimension_monotone (p := p) (G := G))
    (truncatedAugmentationDimension_bounded (p := p) (G := G))
    hineq hdepth (P.displayedGeneratorCard_pos hP)

end FiniteProPPresentation

variable {p : ℕ} [Fact p.Prime]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- A finite nontrivial pro-`p` group with a finite minimal presentation
satisfies the strict generator/relation-rank bound. -/
theorem finite_sq_generatorRank_lt_four_mul_relationRank
    [Finite G] [Nontrivial G]
    (hG : HasFiniteMinimalPresentation p G) :
    topologicalGeneratorRank G ^ 2 < 4 * minimalRelationRank p G hG := by
  obtain ⟨sourceData, d, P, hP⟩ :=
    exists_presentation_relationCard_eq_minimal hG
  simpa only [P.target_topologicalGeneratorRank_eq hP] using
    P.finite_sq_generatorCard_lt_four_mul_relationCard hP

/-- If the generator square reaches four times the minimal relation rank,
the pro-`p` group is infinite. -/
theorem infinite_of_four_mul_relationRank_le_generatorRank_sq
    [Nontrivial G]
    (hG : HasFiniteMinimalPresentation p G)
    (hineq : 4 * minimalRelationRank p G hG ≤
      topologicalGeneratorRank G ^ 2) :
    Infinite G := by
  by_contra hfinite
  let : Finite G := Finite.of_not_infinite hfinite
  have hstrict := finite_sq_generatorRank_lt_four_mul_relationRank hG
  omega

end


end ClassFieldTower.ProP
