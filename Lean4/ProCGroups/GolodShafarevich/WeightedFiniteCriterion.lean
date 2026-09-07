import ProCGroups.GolodShafarevich.FiniteDimensions
import ProCGroups.GolodShafarevich.NumericalCriterion
import ProCGroups.GolodShafarevich.TruncatedInequality
import ProCGroups.ProP.Presentation.RelatorDepth

set_option autoImplicit false

/-!
# Weighted finite-presentation Golod--Shafarevich criterion

Arbitrary displayed relator depth bounds are already supported by the
truncated Fox inequality. No minimality or finite-presentation assertion
about a later countable quotient is required here.
-/

namespace ClassFieldTower.ProP

open ProCGroups

noncomputable section

universe u

namespace FiniteProPPresentation

variable {p d r : ℕ} [Fact p.Prime]
variable {sourceData :
  FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u}
    (FiniteGroupClass.pGroup p)}
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- Every finite target satisfies strict positivity of the polynomial of
any displayed finite presentation with the given lower relator depths. -/
theorem finite_gsPolynomial_pos
    [Finite G] (P : FiniteProPPresentation p d r sourceData G)
    (ν : Fin r → ℕ)
    (hν : ∀ i, P.RelatorZassenhausDepthAtLeast (ν i) i)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    0 < 1 - d * t + ∑ i : Fin r, t ^ ν i := by
  let A : ℕ → ℕ := truncatedAugmentationDimension (p := p) (G := G)
  have hineq : ∀ N,
      1 + d * backshift A N 1 ≤
        A N + ∑ i : Fin r, backshift A N (ν i) := by
    intro N
    simpa [A, backshift, truncatedAugmentationDimensionStar] using
      finitePresentation_truncatedCoefficientInequality P ν hν N
  have hA0 : 0 < A 0 := by
    simp [A]
  exact gsPolynomial_pos_of_truncated ν A
    (truncatedAugmentationDimension_bounded (p := p) (G := G))
    hA0 hineq ht0 ht1

/-- A nonpositive weighted polynomial forces the target of an actual
finite presentation to be infinite. -/
theorem infinite_of_gsPolynomial_nonpos
    (P : FiniteProPPresentation p d r sourceData G)
    (ν : Fin r → ℕ)
    (hν : ∀ i, P.RelatorZassenhausDepthAtLeast (ν i) i)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hpoly : 1 - (d : ℝ) * t + ∑ i : Fin r, t ^ ν i ≤ 0) :
    Infinite G := by
  by_contra hfinite
  let : Finite G := Finite.of_not_infinite hfinite
  exact (not_lt_of_ge hpoly) (P.finite_gsPolynomial_pos ν hν ht0 ht1)

end FiniteProPPresentation

end

end ClassFieldTower.ProP
