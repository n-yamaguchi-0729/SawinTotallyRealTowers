import ProCGroups.GolodShafarevich.GradedPieces
import ProCGroups.GolodShafarevich.TruncatedFoxSequence
import Mathlib.Algebra.Exact.Sequence
import Mathlib.Algebra.Field.ZMod

set_option autoImplicit false
/-!
# Truncated Golod--Shafarevich dimension inequality

The numerical core is rank--nullity for a right-exact sequence of finite
dimensional vector spaces.  It is stated separately from the filtered Fox
maps so the Nat arithmetic and the linear-algebra argument remain reusable.
-/

namespace ClassFieldTower.ProP

open CompletedGroupAlgebra
open ProCGroups

noncomputable section

universe u v₀ v₁ v₂ v₃

/-- Dimension inequality attached to a right-exact sequence of finite
dimensional vector spaces. -/
theorem finrank_add_le_of_linear_rightExact
    {k : Type u} [DivisionRing k]
    {R : Type v₀} {X : Type v₁} {Y : Type v₂} {Z : Type v₃}
    [AddCommGroup R] [Module k R] [FiniteDimensional k R]
    [AddCommGroup X] [Module k X] [FiniteDimensional k X]
    [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
    [AddCommGroup Z] [Module k Z] [FiniteDimensional k Z]
    (f : R →ₗ[k] X) (g : X →ₗ[k] Y) (h : Y →ₗ[k] Z)
    (hfg : Function.Exact f g) (hgh : Function.Exact g h)
    (hh : Function.Surjective h) :
    Module.finrank k X + Module.finrank k Z ≤
      Module.finrank k Y + Module.finrank k R := by
  have hf_le : Module.finrank k (LinearMap.ker g) ≤ Module.finrank k R := by
    rw [hfg.linearMap_ker_eq]
    exact f.finrank_range_le
  have hg_rank := g.finrank_range_add_finrank_ker
  have hh_rank := h.finrank_range_add_finrank_ker
  have hh_range : LinearMap.range h = ⊤ := LinearMap.range_eq_top.mpr hh
  rw [hh_range, finrank_top, hgh.linearMap_ker_eq] at hh_rank
  omega

variable {p : ℕ} [Fact p.Prime]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- Rank--nullity on shifted augmentation truncations, before inserting the
concrete filtered Fox maps. -/
theorem shiftedTruncation_coefficient_inequality_of_rightExact
    [Finite G] {d r N : ℕ} (ν : Fin r → ℕ)
    (f : (∀ i : Fin r,
        ShiftedAugmentationTruncation (p := p) (G := G) N (ν i)) →ₗ[ZMod p]
      (Fin d → ShiftedAugmentationTruncation (p := p) (G := G) N 1))
    (g : (Fin d → ShiftedAugmentationTruncation (p := p) (G := G) N 1) →ₗ[ZMod p]
      ShiftedAugmentationTruncation (p := p) (G := G) N 0)
    (h : ShiftedAugmentationTruncation (p := p) (G := G) N 0 →ₗ[ZMod p]
      ZMod p)
    (hfg : Function.Exact f g) (hgh : Function.Exact g h)
    (hh : Function.Surjective h) :
    1 + d * shiftedTruncatedAugmentationDimension (p := p) (G := G) N 1 ≤
      truncatedAugmentationDimension (p := p) (G := G) N +
        ∑ i, shiftedTruncatedAugmentationDimension (p := p) (G := G) N (ν i) := by
  let : Finite (ModPCompletedGroupAlgebra p G) :=
    finite_modPCompletedGroupAlgebra
  have hdim := finrank_add_le_of_linear_rightExact
    (k := ZMod p)
    (R := ∀ i : Fin r,
      ShiftedAugmentationTruncation (p := p) (G := G) N (ν i))
    (X := Fin d → ShiftedAugmentationTruncation (p := p) (G := G) N 1)
    (Y := ShiftedAugmentationTruncation (p := p) (G := G) N 0)
    (Z := ZMod p) f g h hfg hgh hh
  rw [Module.finrank_self, Module.finrank_pi_fintype,
    Module.finrank_pi_fintype] at hdim
  simp only [Fintype.card_fin, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Nat.add_comm] at hdim
  change 1 + d * shiftedTruncatedAugmentationDimension (p := p) (G := G) N 1 ≤
    truncatedAugmentationDimension (p := p) (G := G) N +
      ∑ i, shiftedTruncatedAugmentationDimension (p := p) (G := G) N (ν i) at hdim
  exact hdim

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- Nat-safe form of the truncated coefficient inequality. -/
theorem natSafe_truncatedAugmentationCoefficientInequality_of_rightExact
    [Finite G] {d r N : ℕ} (ν : Fin r → ℕ)
    (f : (∀ i : Fin r,
        ShiftedAugmentationTruncation (p := p) (G := G) N (ν i)) →ₗ[ZMod p]
      (Fin d → ShiftedAugmentationTruncation (p := p) (G := G) N 1))
    (g : (Fin d → ShiftedAugmentationTruncation (p := p) (G := G) N 1) →ₗ[ZMod p]
      ShiftedAugmentationTruncation (p := p) (G := G) N 0)
    (h : ShiftedAugmentationTruncation (p := p) (G := G) N 0 →ₗ[ZMod p]
      ZMod p)
    (hfg : Function.Exact f g) (hgh : Function.Exact g h)
    (hh : Function.Surjective h) :
    1 + d * truncatedAugmentationDimensionStar (p := p) (G := G) N 1 ≤
      truncatedAugmentationDimension (p := p) (G := G) N +
        ∑ i, truncatedAugmentationDimensionStar (p := p) (G := G) N (ν i) := by
  simpa only [shiftedTruncatedAugmentationDimension_eq_star] using
    shiftedTruncation_coefficient_inequality_of_rightExact
      (p := p) (G := G) ν f g h hfg hgh hh

variable {d r : ℕ}
variable {sourceData :
  FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u}
    (FiniteGroupClass.pGroup p)}

/-- The Nat-safe truncated Golod--Shafarevich coefficient inequality attached
to an actual finite pro-`p` presentation.  All exactness inputs are supplied
by the filtered Fox--Crowell sequence. -/
theorem finitePresentation_truncatedCoefficientInequality
    [Finite G]
    (P : FiniteProPPresentation p d r sourceData G)
    (ν : Fin r → ℕ)
    (hν : ∀ j, P.RelatorZassenhausDepthAtLeast (ν j) j)
    (N : ℕ) :
    1 + d * truncatedAugmentationDimensionStar (p := p) (G := G) N 1 ≤
      truncatedAugmentationDimension (p := p) (G := G) N +
        ∑ i, truncatedAugmentationDimensionStar
          (p := p) (G := G) N (ν i) := by
  rcases presentationModP_truncatedFoxSequence_rightExact P ν hν N with
    ⟨hrel, htail, hsurj⟩
  exact natSafe_truncatedAugmentationCoefficientInequality_of_rightExact
    (p := p) (G := G) ν
    (presentationModPTruncatedRelationMap P ν hν N)
    (presentationModPTruncatedFoxBoundary P N)
    (presentationModPTruncatedAugmentation (p := p) (G := G) N)
    hrel htail hsurj

end

end ClassFieldTower.ProP
