import ProCGroups.ProP.Fox.Rows

set_option autoImplicit false
/-!
# Closed generation of completed kernel Fox rows

Continuity and crossed-product identities turn the inverse image of the
displayed-row span into a closed normal subgroup.  Since the displayed
relators closed-normally generate the kernel, every kernel row lies in their
closed coefficient span.
-/

open scoped Topology

namespace ClassFieldTower.ProP

open ProCGroups
open FoxDifferential

noncomputable section

universe u

variable {p d r : ℕ} [Fact p.Prime]
variable {sourceData :
  FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u}
    (FiniteGroupClass.pGroup p)}
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- Kernel elements whose completed Fox rows lie in the displayed closed
span. -/
def kernelRowsInDisplayedClosedSpan
    (P : FiniteProPPresentation p d r sourceData G) :
    Subgroup sourceData.carrier where
  carrier := {x |
    x ∈ P.quotient.toMonoidHom.ker ∧
      presentationFoxDerivative P x ∈ displayedRelatorFoxRowClosedSpan P}
  one_mem' := by
    constructor
    · simp
    · rw [ScalarCrossedHom.map_one]
      exact (displayedRelatorFoxRowClosedSpan P).zero_mem
  mul_mem' := by
    intro x y hx hy
    constructor
    · exact P.quotient.toMonoidHom.ker.mul_mem hx.1 hy.1
    · rw [ScalarCrossedHom.map_mul]
      exact (displayedRelatorFoxRowClosedSpan P).add_mem hx.2
        ((displayedRelatorFoxRowClosedSpan P).smul_mem _ hy.2)
  inv_mem' := by
    intro x hx
    constructor
    · exact P.quotient.toMonoidHom.ker.inv_mem hx.1
    · rw [ScalarCrossedHom.map_inv]
      exact (displayedRelatorFoxRowClosedSpan P).neg_mem
        ((displayedRelatorFoxRowClosedSpan P).smul_mem _ hx.2)

/-- The row-controlled kernel subgroup is normal in the free source. -/
theorem kernelRowsInDisplayedClosedSpan_normal
    (P : FiniteProPPresentation p d r sourceData G) :
    (kernelRowsInDisplayedClosedSpan P).Normal where
  conj_mem n hn g := by
    rcases hn with ⟨hnker, hnrow⟩
    constructor
    · change P.quotient (g * n * g⁻¹) = 1
      change P.quotient n = 1 at hnker
      simp [hnker]
    · rw [ScalarCrossedHom.map_conj]
      change P.quotient n = 1 at hnker
      have hcoeff :
          zcCompletedGroupAlgebraScalar
              (FiniteGroupClass.pGroup p) P.quotient.toMonoidHom
              (g * n * g⁻¹) = 1 := by
        simp [hnker]
      rw [hcoeff, one_smul]
      simpa only [add_sub_cancel_left] using
        (displayedRelatorFoxRowClosedSpan P).smul_mem
          (zcCompletedGroupAlgebraScalar
            (FiniteGroupClass.pGroup p) P.quotient.toMonoidHom g)
          hnrow

/-- The row-controlled kernel subgroup is topologically closed. -/
theorem isClosed_kernelRowsInDisplayedClosedSpan
    (P : FiniteProPPresentation p d r sourceData G) :
    IsClosed ((kernelRowsInDisplayedClosedSpan P : Subgroup sourceData.carrier) :
      Set sourceData.carrier) := by
  have hspan : IsClosed
      ((displayedRelatorFoxRowClosedSpan P :
        Submodule
          (PresentationFoxCoefficientRing (p := p) (G := G))
          (PresentationFoxCoordinates (p := p) (d := d) (G := G))) :
        Set (PresentationFoxCoordinates (p := p) (d := d) (G := G))) := by
    simpa only [displayedRelatorFoxRowClosedSpan] using
      (Submodule.isClosed_topologicalClosure
        (Submodule.span
          (PresentationFoxCoefficientRing (p := p) (G := G))
          (Set.range (displayedRelatorFoxRow P))))
  have hset :
      ((kernelRowsInDisplayedClosedSpan P : Subgroup sourceData.carrier) :
          Set sourceData.carrier) =
        (P.quotient.toMonoidHom.ker : Set sourceData.carrier) ∩
          (presentationFoxDerivative P) ⁻¹'
            (displayedRelatorFoxRowClosedSpan P :
              Set (PresentationFoxCoordinates (p := p) (d := d) (G := G))) := by
    ext x
    rfl
  rw [hset]
  exact
    (ProCGroups.ContinuousMonoidHom.isClosed_ker P.quotient).inter
      (hspan.preimage (continuous_presentationFoxDerivative P))

/-- Every displayed relator belongs to the row-controlled kernel subgroup. -/
theorem displayedRelators_subset_kernelRowsInDisplayedClosedSpan
    (P : FiniteProPPresentation p d r sourceData G) :
    Set.range P.relator ⊆ kernelRowsInDisplayedClosedSpan P := by
  rintro _ ⟨i, rfl⟩
  constructor
  · exact P.relator_mem_kernel i
  · apply Submodule.le_topologicalClosure
    exact Submodule.subset_span ⟨i, rfl⟩

/-- Every completed kernel row belongs to the closed coefficient span of the
displayed finite row family. -/
theorem kernelFoxRow_mem_displayedRelatorFoxRowClosedSpan
    (P : FiniteProPPresentation p d r sourceData G)
    (x : P.quotient.toMonoidHom.ker) :
    kernelFoxRow P x ∈ displayedRelatorFoxRowClosedSpan P := by
  let _ : (kernelRowsInDisplayedClosedSpan P).Normal :=
    kernelRowsInDisplayedClosedSpan_normal P
  have hle :
      ProCGroups.Presentations.closedNormalClosure (Set.range P.relator) ≤
        kernelRowsInDisplayedClosedSpan P :=
    ProCGroups.Presentations.closedNormalClosure_le_closed_normal
      (isClosed_kernelRowsInDisplayedClosedSpan P)
      (displayedRelators_subset_kernelRowsInDisplayedClosedSpan P)
  have hx : x.1 ∈
      ProCGroups.Presentations.closedNormalClosure (Set.range P.relator) := by
    rw [← P.kernel_eq_closedNormalClosure]
    exact x.2
  exact (hle hx).2

end

end ClassFieldTower.ProP
