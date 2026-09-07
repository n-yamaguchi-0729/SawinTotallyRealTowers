import ProCGroups.FoxDifferential.Completed.FiniteStage.BoundaryCycles

set_option autoImplicit false

/-!
# Fox differential: completed — finite stage — relation module

The principal declarations in this module are:

- `foxAlgebraicStageRelationGroup`
  The finite-stage relation group \(\ker(F/[N,N]N^n \to F/N)\). Its elements are exactly
  finite-stage kernel relations.
- `foxAlgebraicStageRelationBoundaryAddMonoidHom`
  The finite-stage relation boundary, written additively: \(N/[N,N]N^n \to
  ((\mathbb{Z}/n\mathbb{Z})[F/N])^X\).
- `foxAlgebraicStageRelationGroup_target_eq_one`
  Every finite-stage relation group element maps to \(1\) in the target normal quotient.
- `foxAlgebraicStageQuotientCoefficient_relation_eq_one`
  Every finite-stage relation group element has quotient coefficient equal to \(1\).
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u

variable {X : Type u} [DecidableEq X]
variable (N : Subgroup (FreeGroup X)) [N.Normal] (n : ℕ)

/--
The finite-stage relation group \(\ker(F/[N,N]N^n \to F/N)\). Its elements are exactly
finite-stage kernel relations.
-/
abbrev foxAlgebraicStageRelationGroup : Type u :=
  (foxCommutatorPowerQuotientMapToNormalQuotient
    (F := FreeGroup X) N n).ker

omit [DecidableEq X] in
/-- Every finite-stage relation group element maps to \(1\) in the target normal quotient. -/
@[simp]
theorem foxAlgebraicStageRelationGroup_target_eq_one
    (q : foxAlgebraicStageRelationGroup (X := X) N n) :
    foxCommutatorPowerQuotientMapToNormalQuotient
      (F := FreeGroup X) N n q.1 = 1 :=
  q.2

omit [DecidableEq X] in
/-- Every finite-stage relation group element has quotient coefficient equal to \(1\). -/
@[simp]
theorem foxAlgebraicStageQuotientCoefficient_relation_eq_one
    (q : foxAlgebraicStageRelationGroup (X := X) N n) :
    foxAlgebraicStageQuotientCoefficient (X := X) N n q.1 = 1 :=
  foxAlgebraicStageQuotientCoefficient_eq_one_of_kernel (X := X) N n q.2

/--
The finite-stage relation boundary, written additively: \(N/[N,N]N^n \to
((\mathbb{Z}/n\mathbb{Z})[F/N])^X\).
-/
def foxAlgebraicStageRelationBoundaryAddMonoidHom :
    Additive (foxAlgebraicStageRelationGroup (X := X) N n) →+
      foxAlgebraicStageCoordinateVector (X := X) N n where
  toFun q := foxAlgebraicStageQuotientDerivativeVector (X := X) N n
    (Additive.toMul q).1
  map_zero' := by
    change foxAlgebraicStageQuotientDerivativeVector (X := X) N n 1 = 0
    exact ScalarCrossedHom.map_one
      (foxAlgebraicStageQuotientDerivativeVector (X := X) N n)
  map_add' := by
    intro q r
    change foxAlgebraicStageQuotientDerivativeVector (X := X) N n
        ((Additive.toMul q).1 * (Additive.toMul r).1) =
      foxAlgebraicStageQuotientDerivativeVector (X := X) N n (Additive.toMul q).1 +
        foxAlgebraicStageQuotientDerivativeVector (X := X) N n (Additive.toMul r).1
    rw [ScalarCrossedHom.map_mul
      (foxAlgebraicStageQuotientDerivativeVector (X := X) N n),
      foxAlgebraicStageQuotientCoefficient_relation_eq_one]
    simp only [one_smul]

/--
The relation-boundary add monoid homomorphism is evaluated on a finite-stage relation by the
defining boundary formula.
-/
@[simp]
theorem foxAlgebraicStageRelationBoundaryAddMonoidHom_of
    (q : foxAlgebraicStageRelationGroup (X := X) N n) :
    foxAlgebraicStageRelationBoundaryAddMonoidHom (X := X) N n (Additive.ofMul q) =
      foxAlgebraicStageQuotientDerivativeVector (X := X) N n q.1 :=
  rfl

/-- The relation-boundary image, as an additive subgroup of the finite coordinate module. -/
def foxAlgebraicStageRelationBoundaryRange :
    AddSubgroup (foxAlgebraicStageCoordinateVector (X := X) N n) :=
  foxAlgebraicStageSourceKernelDerivativeAddSubgroup (X := X) N n

/--
The relation-boundary range has the finite-stage source-kernel derivative set as its underlying
set.
-/
@[simp]
theorem foxAlgebraicStageRelationBoundaryRange_coe :
    ((foxAlgebraicStageRelationBoundaryRange (X := X) N n :
        AddSubgroup (foxAlgebraicStageCoordinateVector (X := X) N n)) :
          Set (foxAlgebraicStageCoordinateVector (X := X) N n)) =
      foxAlgebraicStageSourceKernelDerivativeSet (X := X) N n :=
  rfl

/--
Membership in the finite-stage relation-boundary range is equivalent to the displayed coordinate
condition.
-/
theorem mem_foxAlgebraicStageRelationBoundaryRange_iff
    {N : Subgroup (FreeGroup X)} [N.Normal] {n : ℕ}
    {v : foxAlgebraicStageCoordinateVector (X := X) N n} :
    v ∈ foxAlgebraicStageRelationBoundaryRange (X := X) N n ↔
      ∃ q : Additive (foxAlgebraicStageRelationGroup (X := X) N n),
        foxAlgebraicStageRelationBoundaryAddMonoidHom (X := X) N n q = v := by
  constructor
  · intro hv
    rcases hv with ⟨q, hq, hv⟩
    let qrel : foxAlgebraicStageRelationGroup (X := X) N n := ⟨q, hq⟩
    refine ⟨Additive.ofMul qrel, ?_⟩
    simpa [qrel] using hv
  · rintro ⟨q, hq⟩
    let qrel : foxAlgebraicStageRelationGroup (X := X) N n := Additive.toMul q
    refine ⟨qrel.1, qrel.2, ?_⟩
    change
      foxAlgebraicStageQuotientDerivativeVector (X := X) N n
          (Additive.toMul q).1 = v at hq
    exact hq

/-- The finite-stage relation boundary lands in finite Fox boundary cycles. -/
theorem foxAlgebraicStageFoxBoundary_relationBoundary_eq_zero
    [Fintype X] (q : Additive (foxAlgebraicStageRelationGroup (X := X) N n)) :
    foxAlgebraicStageFoxBoundary (X := X) N n
      (foxAlgebraicStageRelationBoundaryAddMonoidHom (X := X) N n q) = 0 := by
  change
    foxAlgebraicStageFoxBoundary (X := X) N n
      (foxAlgebraicStageQuotientDerivativeVector (X := X) N n (Additive.toMul q).1) = 0
  rw [foxAlgebraicStageFoxBoundary_quotientDerivativeVector]
  rw [foxAlgebraicStageQuotientCoefficient_eq_one_of_kernel
    (X := X) N n (Additive.toMul q).2]
  simp only [sub_self]

/-- The relation-boundary range is contained in \(\ker \partial\). -/
theorem foxAlgebraicStageRelationBoundary_range_le_boundaryCycleSubmodule
    [Fintype X] :
    foxAlgebraicStageRelationBoundaryRange (X := X) N n ≤
      (foxAlgebraicStageBoundaryCycleSubmodule (X := X) N n).toAddSubgroup := by
  intro v hv
  rw [mem_foxAlgebraicStageRelationBoundaryRange_iff
    (X := X) (N := N) (n := n)] at hv
  rcases hv with ⟨q, rfl⟩
  exact foxAlgebraicStageFoxBoundary_relationBoundary_eq_zero (X := X) N n q

/-- Finite-stage exactness at the coordinate module. -/
def foxAlgebraicStageRelationBoundaryExact [Fintype X] : Prop :=
  Function.Exact
    (foxAlgebraicStageRelationBoundaryAddMonoidHom (X := X) N n)
    (foxAlgebraicStageFoxBoundary (X := X) N n)

/--
Finite-stage exactness is equivalent to the coverage statement formulated at the level of
finite-stage boundary cycles.
-/
theorem foxAlgebraicStageRelationBoundaryExact_iff_boundaryCyclesCoveredBySourceKernel
    {N : Subgroup (FreeGroup X)} [N.Normal] {n : ℕ} [Fintype X] :
    foxAlgebraicStageRelationBoundaryExact (X := X) N n ↔
      foxAlgebraicStageBoundaryCyclesCoveredBySourceKernel (X := X) N n := by
  constructor
  · intro hexact v hv
    have hvzero : foxAlgebraicStageFoxBoundary (X := X) N n v = 0 := hv
    rcases (hexact v).1 hvzero with ⟨q, hq⟩
    change v ∈ foxAlgebraicStageRelationBoundaryRange (X := X) N n
    rw [mem_foxAlgebraicStageRelationBoundaryRange_iff
      (X := X) (N := N) (n := n)]
    exact ⟨q, hq⟩
  · intro hcovered v
    constructor
    · intro hvzero
      have hvcycle : v ∈ foxAlgebraicStageBoundaryCycleSubmodule (X := X) N n := hvzero
      have hvsource : v ∈ foxAlgebraicStageSourceKernelDerivativeSet (X := X) N n :=
        hcovered hvcycle
      have hvsourceRange : v ∈ foxAlgebraicStageRelationBoundaryRange (X := X) N n := by
        change v ∈ foxAlgebraicStageSourceKernelDerivativeSet (X := X) N n
        exact hvsource
      rw [mem_foxAlgebraicStageRelationBoundaryRange_iff
        (X := X) (N := N) (n := n)] at hvsourceRange
      exact hvsourceRange
    · rintro ⟨q, hq⟩
      rw [← hq]
      exact foxAlgebraicStageFoxBoundary_relationBoundary_eq_zero (X := X) N n q

/--
Coverage of finite boundary cycles gives finite-stage exactness in the usual function-level
form.
-/
theorem foxAlgebraicStageRelationBoundaryExact_of_boundaryCyclesCoveredBySourceKernel
    [Fintype X]
    (hcovered : foxAlgebraicStageBoundaryCyclesCoveredBySourceKernel (X := X) N n) :
    foxAlgebraicStageRelationBoundaryExact (X := X) N n :=
  (foxAlgebraicStageRelationBoundaryExact_iff_boundaryCyclesCoveredBySourceKernel
    (X := X) (N := N) (n := n)).2 hcovered

/-- Function-level finite-stage exactness gives the set-level coverage used by the density step. -/
theorem foxAlgebraicStageBoundaryCyclesCoveredBySourceKernel_of_relationBoundaryExact
    [Fintype X]
    (hexact : foxAlgebraicStageRelationBoundaryExact (X := X) N n) :
    foxAlgebraicStageBoundaryCyclesCoveredBySourceKernel (X := X) N n :=
  (foxAlgebraicStageRelationBoundaryExact_iff_boundaryCyclesCoveredBySourceKernel
    (X := X) (N := N) (n := n)).1 hexact

end

end FoxDifferential
