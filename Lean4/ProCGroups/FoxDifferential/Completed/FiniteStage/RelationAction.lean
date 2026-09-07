import ProCGroups.FoxDifferential.Completed.FiniteStage.RelationModule

set_option autoImplicit false

/-!
# Fox differential: completed — finite stage — relation action

The principal declarations in this module are:

- `foxAlgebraicStageRelationConjBySource`
  Conjugating a finite-stage relation by an arbitrary source-quotient element gives another
  finite-stage relation.
- `foxAlgebraicStageTargetQuotientLiftToSource`
  A chosen source-quotient lift of an element of \(F/N\).
- `foxAlgebraicStageRelationConjBySource_val`
  Conjugating a finite-stage relation by a source element has the stated finite-stage value.
- `foxAlgebraicStageRelationBoundary_conjBySource`
  Relation-boundary equivariance for conjugation by a source-quotient element.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u

variable {X : Type u} [DecidableEq X]
variable (N : Subgroup (FreeGroup X)) [N.Normal] (n : ℕ)

/--
Conjugating a finite-stage relation by an arbitrary source-quotient element gives another
finite-stage relation.
-/
def foxAlgebraicStageRelationConjBySource
    (s : FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
    (q : foxAlgebraicStageRelationGroup (X := X) N n) :
    foxAlgebraicStageRelationGroup (X := X) N n :=
  ⟨s * q.1 * s⁻¹, by
    change foxCommutatorPowerQuotientMapToNormalQuotient
      (F := FreeGroup X) N n (s * q.1 * s⁻¹) = 1
    rw [map_mul, map_mul, map_inv, q.2]
    simp only [mul_one, mul_inv_cancel]⟩

omit [DecidableEq X] in
/-- Conjugating a finite-stage relation by a source element has the stated finite-stage value. -/
@[simp]
theorem foxAlgebraicStageRelationConjBySource_val
    (s : FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
    (q : foxAlgebraicStageRelationGroup (X := X) N n) :
    (foxAlgebraicStageRelationConjBySource (X := X) N n s q).1 = s * q.1 * s⁻¹ :=
  rfl

/-- Relation-boundary equivariance for conjugation by a source-quotient element. -/
theorem foxAlgebraicStageRelationBoundary_conjBySource
    (s : FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
    (q : foxAlgebraicStageRelationGroup (X := X) N n) :
    foxAlgebraicStageRelationBoundaryAddMonoidHom (X := X) N n
        (Additive.ofMul (foxAlgebraicStageRelationConjBySource (X := X) N n s q)) =
      foxAlgebraicStageQuotientCoefficient (X := X) N n s •
        foxAlgebraicStageRelationBoundaryAddMonoidHom (X := X) N n (Additive.ofMul q) := by
  rw [foxAlgebraicStageRelationBoundaryAddMonoidHom_of,
    foxAlgebraicStageRelationBoundaryAddMonoidHom_of,
    foxAlgebraicStageRelationConjBySource_val]
  have hconj :=
    ScalarCrossedHom.map_conj
      (foxAlgebraicStageQuotientDerivativeVector (X := X) N n)
      s q.1
  have hcoeff :
      foxAlgebraicStageQuotientCoefficient (X := X) N n (s * q.1 * s⁻¹) = 1 := by
    have htarget :
        foxCommutatorPowerQuotientMapToNormalQuotient
            (F := FreeGroup X) N n (s * q.1 * s⁻¹) = 1 := by
      rw [map_mul, map_mul, map_inv, q.2]
      simp only [mul_one, mul_inv_cancel]
    rw [foxAlgebraicStageQuotientCoefficient_apply, htarget]
    rfl
  calc
    foxAlgebraicStageQuotientDerivativeVector (X := X) N n (s * q.1 * s⁻¹) =
        foxAlgebraicStageQuotientDerivativeVector (X := X) N n s +
          foxAlgebraicStageQuotientCoefficient (X := X) N n s •
            foxAlgebraicStageQuotientDerivativeVector (X := X) N n q.1 -
          foxAlgebraicStageQuotientCoefficient (X := X) N n (s * q.1 * s⁻¹) •
            foxAlgebraicStageQuotientDerivativeVector (X := X) N n s := hconj
    _ = foxAlgebraicStageQuotientCoefficient (X := X) N n s •
          foxAlgebraicStageQuotientDerivativeVector (X := X) N n q.1 := by
          rw [hcoeff, one_smul]
          abel

/-- A chosen source-quotient lift of an element of \(F/N\). -/
def foxAlgebraicStageTargetQuotientLiftToSource
    (h : foxAlgebraicStageTargetQuotient (X := X) N) :
    FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n :=
  Classical.choose
    (foxCommutatorPowerQuotientMapToNormalQuotient_surjective
      (F := FreeGroup X) N n h)

omit [DecidableEq X] in
/-- The chosen lift to the source quotient satisfies its finite-stage target specification. -/
@[simp]
theorem foxAlgebraicStageTargetQuotientLiftToSource_spec
    (h : foxAlgebraicStageTargetQuotient (X := X) N) :
    foxCommutatorPowerQuotientMapToNormalQuotient (F := FreeGroup X) N n
      (foxAlgebraicStageTargetQuotientLiftToSource (X := X) N n h) = h :=
  Classical.choose_spec
    (foxCommutatorPowerQuotientMapToNormalQuotient_surjective
      (F := FreeGroup X) N n h)

omit [DecidableEq X] in
/-- The coefficient of a chosen source lift is the corresponding group-ring basis element. -/
@[simp]
theorem foxAlgebraicStageQuotientCoefficient_targetLift
    (h : foxAlgebraicStageTargetQuotient (X := X) N) :
    foxAlgebraicStageQuotientCoefficient (X := X) N n
        (foxAlgebraicStageTargetQuotientLiftToSource (X := X) N n h) =
      MonoidAlgebra.of (ModNCompletedCoeff n)
        (foxAlgebraicStageTargetQuotient (X := X) N) h := by
  rw [foxAlgebraicStageQuotientCoefficient_apply,
    foxAlgebraicStageTargetQuotientLiftToSource_spec]

/-- The relation boundary is equivariant on basis elements over \(\mathbb{Z}/n\mathbb{Z}[F/N]\). -/
theorem foxAlgebraicStageRelationBoundary_of_basis_smul
    (h : foxAlgebraicStageTargetQuotient (X := X) N)
    (q : foxAlgebraicStageRelationGroup (X := X) N n) :
    foxAlgebraicStageRelationBoundaryAddMonoidHom (X := X) N n
        (Additive.ofMul
          (foxAlgebraicStageRelationConjBySource (X := X) N n
            (foxAlgebraicStageTargetQuotientLiftToSource (X := X) N n h) q)) =
      (MonoidAlgebra.of (ModNCompletedCoeff n)
        (foxAlgebraicStageTargetQuotient (X := X) N) h) •
        foxAlgebraicStageRelationBoundaryAddMonoidHom (X := X) N n (Additive.ofMul q) := by
  rw [foxAlgebraicStageRelationBoundary_conjBySource,
    foxAlgebraicStageQuotientCoefficient_targetLift]

/-- The relation-boundary image is stable under multiplication by target group basis elements. -/
theorem foxAlgebraicStageRelationBoundaryRange_basis_smul_mem
    (h : foxAlgebraicStageTargetQuotient (X := X) N)
    {v : foxAlgebraicStageCoordinateVector (X := X) N n}
    (hv : v ∈ foxAlgebraicStageRelationBoundaryRange (X := X) N n) :
    (MonoidAlgebra.of (ModNCompletedCoeff n)
        (foxAlgebraicStageTargetQuotient (X := X) N) h) • v ∈
      foxAlgebraicStageRelationBoundaryRange (X := X) N n := by
  rw [mem_foxAlgebraicStageRelationBoundaryRange_iff
    (X := X) (N := N) (n := n)] at hv
  rcases hv with ⟨q, hq⟩
  let qmul : foxAlgebraicStageRelationGroup (X := X) N n := Additive.toMul q
  rw [mem_foxAlgebraicStageRelationBoundaryRange_iff
    (X := X) (N := N) (n := n)]
  refine ⟨Additive.ofMul
    (foxAlgebraicStageRelationConjBySource (X := X) N n
      (foxAlgebraicStageTargetQuotientLiftToSource (X := X) N n h) qmul), ?_⟩
  calc
    foxAlgebraicStageRelationBoundaryAddMonoidHom (X := X) N n
        (Additive.ofMul
          (foxAlgebraicStageRelationConjBySource (X := X) N n
            (foxAlgebraicStageTargetQuotientLiftToSource (X := X) N n h) qmul)) =
        (MonoidAlgebra.of (ModNCompletedCoeff n)
          (foxAlgebraicStageTargetQuotient (X := X) N) h) •
          foxAlgebraicStageRelationBoundaryAddMonoidHom (X := X) N n
            (Additive.ofMul qmul) := by
          exact foxAlgebraicStageRelationBoundary_of_basis_smul (X := X) N n h qmul
    _ = (MonoidAlgebra.of (ModNCompletedCoeff n)
          (foxAlgebraicStageTargetQuotient (X := X) N) h) • v := by
          have hqmul :
              foxAlgebraicStageRelationBoundaryAddMonoidHom (X := X) N n
                (Additive.ofMul qmul) = v := by
            simpa [qmul] using hq
          rw [hqmul]

end

end FoxDifferential
