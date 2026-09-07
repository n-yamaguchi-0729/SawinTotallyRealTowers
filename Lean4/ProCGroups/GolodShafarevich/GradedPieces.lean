import ProCGroups.ProP.Zassenhaus.AugmentationFiltration

set_option autoImplicit false
/-!
# Truncated augmentation dimensions

This file packages the finite-dimensional quotients of a mod-`p` completed
group algebra used by the truncated Golod--Shafarevich inequality.  The
shifted definition uses truncated subtraction, so shifts beyond the cutoff
give the zero quotient without side conditions in downstream statements.
-/

namespace ClassFieldTower.ProP

open CompletedGroupAlgebra
open ProCGroups

noncomputable section

universe u

variable {p : ℕ} [Fact p.Prime]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- For a finite profinite group, its mod-`p` completed group algebra is a
finite type.  This is kept as a theorem so no noncanonical global instance is
installed. -/
theorem finite_modPCompletedGroupAlgebra [Finite G] :
    Finite (ModPCompletedGroupAlgebra p G) := by
  let _ : Finite
      (CompletedGroupAlgebraIndexInClass G (FiniteGroupClass.pGroup p)) :=
    inferInstance
  let stageFinite
      (U : CompletedGroupAlgebraIndexInClass G (FiniteGroupClass.pGroup p)) :
      Finite ((completedGroupAlgebraSystemInClass
        (FiniteGroupClass.pGroup p) (ZMod p) G).X U) := by
    change Finite (CompletedGroupAlgebraStageInClass
      (FiniteGroupClass.pGroup p) (ZMod p) G U)
    exact finite_completedGroupAlgebraStageInClass
      (R := ZMod p) (G := G) (FiniteGroupClass.pGroup p) U
  let _ := stageFinite
  let _ : Finite
      ((U : CompletedGroupAlgebraIndexInClass G (FiniteGroupClass.pGroup p)) →
        (completedGroupAlgebraSystemInClass
          (FiniteGroupClass.pGroup p) (ZMod p) G).X U) := Pi.finite
  exact Finite.of_injective Subtype.val Subtype.val_injective

/-- The subspace killed at cutoff `N` after a filtration shift `shift`. -/
def shiftedClosedAugmentationSubmodule (N shift : ℕ) :
    Submodule (ZMod p) (ModPCompletedGroupAlgebra p G) :=
  (closedAugmentationPower p G (N + 1 - shift)).restrictScalars (ZMod p)

/-- The completed group algebra truncated at `N`, with filtration shift
`shift`. -/
abbrev ShiftedAugmentationTruncation (N shift : ℕ) :=
  ModPCompletedGroupAlgebra p G ⧸
    shiftedClosedAugmentationSubmodule (p := p) (G := G) N shift

/-- Dimension of the unshifted truncation `Λ / I^(N+1)`. -/
def truncatedAugmentationDimension (N : ℕ) : ℕ :=
  Module.finrank (ZMod p)
    (ShiftedAugmentationTruncation (p := p) (G := G) N 0)

/-- Dimension of the truncation after an arbitrary filtration shift. -/
def shiftedTruncatedAugmentationDimension (N shift : ℕ) : ℕ :=
  Module.finrank (ZMod p)
    (ShiftedAugmentationTruncation (p := p) (G := G) N shift)

/-- Nat-safe shifted dimension: `A (N-shift)` inside the cutoff and zero
outside it. -/
def truncatedAugmentationDimensionStar (N shift : ℕ) : ℕ :=
  if shift ≤ N then
    truncatedAugmentationDimension (p := p) (G := G) (N - shift)
  else 0

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
@[simp] theorem closedAugmentationPower_zero_eq_top :
    closedAugmentationPower p G 0 = ⊤ := by
  rw [closedAugmentationPower, Submodule.pow_zero, Ideal.one_eq_top]
  apply le_antisymm le_top
  exact subset_closure

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- The quotient definition of a shifted dimension agrees with its Nat-safe
piecewise form. -/
theorem shiftedTruncatedAugmentationDimension_eq_star (N shift : ℕ) :
    shiftedTruncatedAugmentationDimension (p := p) (G := G) N shift =
      truncatedAugmentationDimensionStar (p := p) (G := G) N shift := by
  by_cases hs : shift ≤ N
  · rw [truncatedAugmentationDimensionStar, if_pos hs]
    have hsub :
        shiftedClosedAugmentationSubmodule (p := p) (G := G) N shift =
          shiftedClosedAugmentationSubmodule (p := p) (G := G) (N - shift) 0 := by
      unfold shiftedClosedAugmentationSubmodule
      exact congrArg
        (fun n ↦ (closedAugmentationPower p G n).restrictScalars (ZMod p))
        (by omega)
    unfold shiftedTruncatedAugmentationDimension truncatedAugmentationDimension
    exact (Submodule.quotEquivOfEq _ _ hsub).finrank_eq
  · rw [truncatedAugmentationDimensionStar, if_neg hs]
    have hexp : N + 1 - shift = 0 := by omega
    have hsub :
        shiftedClosedAugmentationSubmodule (p := p) (G := G) N shift = ⊤ := by
      unfold shiftedClosedAugmentationSubmodule
      calc
        (closedAugmentationPower p G (N + 1 - shift)).restrictScalars (ZMod p) =
            (closedAugmentationPower p G 0).restrictScalars (ZMod p) :=
          congrArg
            (fun n ↦ (closedAugmentationPower p G n).restrictScalars (ZMod p))
            hexp
        _ = ⊤ := by
          rw [closedAugmentationPower_zero_eq_top]
          ext x
          simp
    unfold shiftedTruncatedAugmentationDimension
    calc
      Module.finrank (ZMod p)
          (ShiftedAugmentationTruncation (p := p) (G := G) N shift) =
          Module.finrank (ZMod p)
            (ModPCompletedGroupAlgebra p G ⧸
              (⊤ : Submodule (ZMod p) (ModPCompletedGroupAlgebra p G))) :=
        (Submodule.quotEquivOfEq _ _ hsub).finrank_eq
      _ = 0 := Module.finrank_zero_of_subsingleton

end

end ClassFieldTower.ProP
