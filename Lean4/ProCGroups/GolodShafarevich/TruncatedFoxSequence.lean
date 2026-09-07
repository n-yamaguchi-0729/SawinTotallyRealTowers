import ProCGroups.GolodShafarevich.TruncatedFoxMaps

set_option autoImplicit false
/-!
# Right exactness of the truncated mod-p Fox sequence

Strict lifting for the filtered Fox complex and the augmentation-ideal
description of the boundary range give a concrete right-exact sequence on
shifted finite truncations.
-/

namespace ClassFieldTower.ProP

open CompletedGroupAlgebra
open FoxDifferential
open ProCGroups

noncomputable section

universe u

variable {p d r : ℕ} [Fact p.Prime]
variable {sourceData :
  FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u}
    (FiniteGroupClass.pGroup p)}
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- Strict filtered lifting makes the induced relation--boundary pair exact. -/
theorem presentationModPTruncatedRelationBoundary_exact
    (P : FiniteProPPresentation p d r sourceData G)
    (ν : Fin r → ℕ)
    (hν : ∀ j, P.RelatorZassenhausDepthAtLeast (ν j) j)
    (N : ℕ) :
    Function.Exact (presentationModPTruncatedRelationMap P ν hν N)
      (presentationModPTruncatedFoxBoundary P N) := by
  intro x
  constructor
  · intro hx
    obtain ⟨v, rfl⟩ :=
      presentationModPTruncatedFoxCoordinates_mk_surjective (p := p) (G := G) (d := d) N x
    rw [presentationModPTruncatedFoxBoundary_mk] at hx
    have hboundaryShift :
        presentationModPFoxBoundary P
            (presentationModPFoxCoordinateFinEquiv
              (p := p) (d := d) (G := G) v) ∈
          shiftedClosedAugmentationSubmodule (p := p) (G := G) N 0 :=
      (Submodule.Quotient.mk_eq_zero
        (shiftedClosedAugmentationSubmodule
          (p := p) (G := G) N 0)).mp hx
    have hboundary :
        presentationModPFoxBoundary P
            (presentationModPFoxCoordinateFinEquiv
              (p := p) (d := d) (G := G) v) ∈
          closedAugmentationPower p G (N + 1) := by
      simpa [shiftedClosedAugmentationSubmodule] using hboundaryShift
    rcases presentationModPRelationMatrix_lift_mod_coordinateFiltration
        P N
        (presentationModPFoxCoordinateFinEquiv
          (p := p) (d := d) (G := G) v)
        hboundary with ⟨a, ha⟩
    refine ⟨fun j ↦ Submodule.Quotient.mk (a j), ?_⟩
    rw [presentationModPTruncatedRelationMap_mk]
    funext i
    apply (Submodule.Quotient.eq _).mpr
    have hi := ha (ULift.up i)
    change v i - (presentationModPRelationMatrix P a) (ULift.up i) ∈
      closedAugmentationPower p G N at hi
    have hneg := (closedAugmentationPower p G N).neg_mem hi
    simpa [shiftedClosedAugmentationSubmodule] using hneg
  · rintro ⟨y, rfl⟩
    have hcomp := LinearMap.congr_fun
      (presentationModPTruncatedFoxBoundary_comp_relationMap P ν hν N) y
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using hcomp

/-- Tail equality identifies the induced boundary kernel with its range. -/
theorem presentationModPTruncatedBoundaryAugmentation_exact
    (P : FiniteProPPresentation p d r sourceData G) (N : ℕ) :
    Function.Exact (presentationModPTruncatedFoxBoundary P N)
      (presentationModPTruncatedAugmentation (p := p) (G := G) N) := by
  intro x
  constructor
  · intro hx
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective
      (shiftedClosedAugmentationSubmodule
        (p := p) (G := G) N 0) x
    rw [presentationModPTruncatedAugmentation_mk] at hx
    have haIdeal : a ∈ modPAugmentationIdeal p G := hx
    have haRange : a ∈ LinearMap.range (presentationModPFoxBoundary P) := by
      rw [presentationModPFoxBoundary_range_eq_augmentationIdeal P]
      exact haIdeal
    rcases haRange with ⟨v, hv⟩
    let w : Fin d → ModPCompletedGroupAlgebra p G :=
      (presentationModPFoxCoordinateFinEquiv
        (p := p) (d := d) (G := G)).symm v
    refine ⟨fun i ↦ Submodule.Quotient.mk (w i), ?_⟩
    rw [presentationModPTruncatedFoxBoundary_mk]
    change Submodule.Quotient.mk
        (presentationModPFoxBoundary P
          (presentationModPFoxCoordinateFinEquiv
            (p := p) (d := d) (G := G) w)) =
      Submodule.Quotient.mk a
    rw [show presentationModPFoxCoordinateFinEquiv
        (p := p) (d := d) (G := G) w = v by
      exact (presentationModPFoxCoordinateFinEquiv
        (p := p) (d := d) (G := G)).apply_symm_apply v]
    rw [hv]
  · rintro ⟨y, rfl⟩
    have hcomp := LinearMap.congr_fun
      (presentationModPTruncatedAugmentation_comp_foxBoundary P N) y
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using hcomp

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- The induced augmentation is surjective. -/
theorem presentationModPTruncatedAugmentation_surjective (N : ℕ) :
    Function.Surjective
      (presentationModPTruncatedAugmentation (p := p) (G := G) N) := by
  intro c
  refine ⟨Submodule.Quotient.mk
    (algebraMap (ZMod p) (ModPCompletedGroupAlgebra p G) c), ?_⟩
  rw [presentationModPTruncatedAugmentation_mk]
  exact completedGroupAlgebraCanonicalAugmentationInClass_algebraMap
    (R := ZMod p) (G := G) (FiniteGroupClass.pGroup p) c

/-- Concrete right-exact data for the truncated mod-`p` Fox sequence. -/
theorem presentationModP_truncatedFoxSequence_rightExact
    (P : FiniteProPPresentation p d r sourceData G)
    (ν : Fin r → ℕ)
    (hν : ∀ j, P.RelatorZassenhausDepthAtLeast (ν j) j)
    (N : ℕ) :
    Function.Exact (presentationModPTruncatedRelationMap P ν hν N)
        (presentationModPTruncatedFoxBoundary P N) ∧
      Function.Exact (presentationModPTruncatedFoxBoundary P N)
        (presentationModPTruncatedAugmentation (p := p) (G := G) N) ∧
      Function.Surjective
        (presentationModPTruncatedAugmentation (p := p) (G := G) N) := by
  exact ⟨presentationModPTruncatedRelationBoundary_exact P ν hν N,
    presentationModPTruncatedBoundaryAugmentation_exact P N,
    presentationModPTruncatedAugmentation_surjective
      (p := p) (G := G) N⟩

end

end ClassFieldTower.ProP
