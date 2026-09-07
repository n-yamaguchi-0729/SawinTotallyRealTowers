import ProCGroups.ProP.Fox.ModPBoundary
import ProCGroups.ProP.Fox.ClosedSpan
import ProCGroups.ProP.Fox.CoefficientReductionCompatibility

set_option autoImplicit false
/-!
# Mod-p images of the displayed Fox-row span

Coordinatewise coefficient reduction sends the integral completed Fox rows
to their mod-`p` counterparts.  The integral closed-span theorem and the
closed range of the finite mod-`p` relation matrix then show that every
kernel Fox row belongs to that matrix range.
-/

open scoped Topology

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

/-- Coordinatewise continuous reduction from integral completed Fox
coordinates to mod-`p` completed Fox coordinates. -/
def presentationFoxCoordinatesModPReduction :
    ContinuousAddMonoidHom
      (PresentationFoxCoordinates (p := p) (d := d) (G := G))
      (PresentationModPFoxCoordinates (p := p) (d := d) (G := G)) where
  toFun v i := modPCoefficientReduction p G (v i)
  map_zero' := by
    funext i
    exact map_zero (modPCoefficientReduction p G)
  map_add' v w := by
    funext i
    exact map_add (modPCoefficientReduction p G) (v i) (w i)
  continuous_toFun := by
    apply continuous_pi
    intro i
    exact (continuous_modPCoefficientReduction p G).comp (continuous_apply i)

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- Coordinatewise evaluation of mod-`p` reduction. -/
@[simp]
theorem presentationFoxCoordinatesModPReduction_apply
    (v : PresentationFoxCoordinates (p := p) (d := d) (G := G))
    (i : ULift.{u} (Fin d)) :
    presentationFoxCoordinatesModPReduction (p := p) (G := G) v i =
      modPCoefficientReduction p G (v i) :=
  rfl

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- Coordinatewise reduction is semilinear for coefficient reduction. -/
theorem presentationFoxCoordinatesModPReduction_smul
    (a : PresentationFoxCoefficientRing (p := p) (G := G))
    (v : PresentationFoxCoordinates (p := p) (d := d) (G := G)) :
    presentationFoxCoordinatesModPReduction (p := p) (G := G) (a • v) =
      modPCoefficientReduction p G a •
        presentationFoxCoordinatesModPReduction (p := p) (G := G) v := by
  ext i
  simp only [presentationFoxCoordinatesModPReduction_apply, Pi.smul_apply,
    smul_eq_mul, map_mul]

/-- Reduction of the integral presentation derivative is the mod-`p`
presentation derivative. -/
@[simp]
theorem presentationFoxCoordinatesModPReduction_derivative
    (P : FiniteProPPresentation p d r sourceData G)
    (f : sourceData.carrier) :
    presentationFoxCoordinatesModPReduction (p := p) (G := G)
        (presentationFoxDerivative P f) =
      presentationModPFoxDerivative P f := by
  ext i
  rfl

/-- Reduction sends every integral displayed row to its mod-`p` displayed
row. -/
@[simp]
theorem presentationFoxCoordinatesModPReduction_displayedRelatorFoxRow
    (P : FiniteProPPresentation p d r sourceData G)
    (i : Fin r) :
    presentationFoxCoordinatesModPReduction (p := p) (G := G)
        (displayedRelatorFoxRow P i) =
      displayedRelatorModPFoxRow P i := by
  rfl

/-- Reduction of an integral kernel row is the mod-`p` derivative of its
underlying kernel element. -/
@[simp]
theorem presentationFoxCoordinatesModPReduction_kernelFoxRow
    (P : FiniteProPPresentation p d r sourceData G)
    (n : P.quotient.toMonoidHom.ker) :
    presentationFoxCoordinatesModPReduction (p := p) (G := G)
        (kernelFoxRow P n) =
      presentationModPFoxDerivative P n.1 := by
  rfl

/-- Each displayed mod-`p` row belongs to the finite relation-matrix range. -/
theorem displayedRelatorModPFoxRow_mem_relationMatrix_range
    (P : FiniteProPPresentation p d r sourceData G)
    (i : Fin r) :
    displayedRelatorModPFoxRow P i ∈
      LinearMap.range (presentationModPRelationMatrix P) := by
  rw [presentationModPRelationMatrix_range_eq_span]
  exact Submodule.subset_span ⟨i, rfl⟩

/-- Coordinatewise reduction sends the algebraic integral displayed-row
span into the mod-`p` relation-matrix range. -/
theorem presentationFoxCoordinatesModPReduction_mem_relationMatrix_range_of_mem_span
    (P : FiniteProPPresentation p d r sourceData G)
    (v : PresentationFoxCoordinates (p := p) (d := d) (G := G))
    (hv : v ∈ Submodule.span
      (PresentationFoxCoefficientRing (p := p) (G := G))
      (Set.range (displayedRelatorFoxRow P))) :
    presentationFoxCoordinatesModPReduction (p := p) (G := G) v ∈
      LinearMap.range (presentationModPRelationMatrix P) := by
  refine Submodule.span_induction
    (p := fun z _ ↦
      presentationFoxCoordinatesModPReduction (p := p) (G := G) z ∈
        LinearMap.range (presentationModPRelationMatrix P))
    ?_ ?_ ?_ ?_ hv
  · rintro z ⟨i, rfl⟩
    rw [presentationFoxCoordinatesModPReduction_displayedRelatorFoxRow]
    exact displayedRelatorModPFoxRow_mem_relationMatrix_range P i
  · rw [map_zero]
    exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  · intro a x _ hx
    rw [presentationFoxCoordinatesModPReduction_smul]
    exact Submodule.smul_mem _ (modPCoefficientReduction p G a) hx

/-- Every presentation-kernel Fox row modulo `p` belongs to the range of the
finite displayed relation matrix. -/
theorem presentationModPFoxDerivative_mem_relationMatrix_range
    (P : FiniteProPPresentation p d r sourceData G)
    (n : P.quotient.toMonoidHom.ker) :
    presentationModPFoxDerivative P n.1 ∈
      LinearMap.range (presentationModPRelationMatrix P) := by
  have hn := kernelFoxRow_mem_displayedRelatorFoxRowClosedSpan P n
  change kernelFoxRow P n ∈ closure
    ((Submodule.span
      (PresentationFoxCoefficientRing (p := p) (G := G))
      (Set.range (displayedRelatorFoxRow P)) :
        Submodule
          (PresentationFoxCoefficientRing (p := p) (G := G))
          (PresentationFoxCoordinates (p := p) (d := d) (G := G))) :
      Set (PresentationFoxCoordinates (p := p) (d := d) (G := G))) at hn
  have himage := map_mem_closure
    (f := presentationFoxCoordinatesModPReduction (p := p) (G := G))
    (s := ((Submodule.span
      (PresentationFoxCoefficientRing (p := p) (G := G))
      (Set.range (displayedRelatorFoxRow P)) :
        Submodule
          (PresentationFoxCoefficientRing (p := p) (G := G))
          (PresentationFoxCoordinates (p := p) (d := d) (G := G))) :
      Set (PresentationFoxCoordinates (p := p) (d := d) (G := G))))
    (t := Set.range (presentationModPRelationMatrix P))
    (presentationFoxCoordinatesModPReduction (p := p) (G := G)).continuous
    hn (by
      intro v hv
      exact
        presentationFoxCoordinatesModPReduction_mem_relationMatrix_range_of_mem_span
          P v hv)
  rw [(isClosed_range_presentationModPRelationMatrix P).closure_eq] at himage
  rw [presentationFoxCoordinatesModPReduction_kernelFoxRow] at himage
  rcases himage with ⟨a, ha⟩
  exact ⟨a, ha⟩

end

end ClassFieldTower.ProP
