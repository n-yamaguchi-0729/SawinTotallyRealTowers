import ProCGroups.FoxDifferential.Common.FoxBoundary
import ProCGroups.FoxDifferential.Completed.FiniteStage.Stage.Derivative.Rules
import Mathlib.Tactic.NoncommRing

set_option autoImplicit false

/-!
# Fox differential: finite stage — stage — derivative — boundary

The principal declarations in this module are:

- `foxAlgebraicStageFoxBoundary`
  The finite-stage Fox boundary/Euler map \(v \mapsto \sum_i v_i * ([x_i] - 1)\) on coordinate
  vectors.
- `foxAlgebraicStageFoxBoundary_apply`
  The finite-stage Fox boundary is evaluated on the canonical generators and then extended linearly
  to the finite-stage coordinate module.
- `foxAlgebraicStageFoxBoundary_single`
  The finite-stage Fox boundary sends a coordinate basis vector to its augmentation generator.
- `foxAlgebraicStageDerivative_fundamental_formula`
  Finite-stage Fox fundamental formula for a free-group word.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u

variable {X : Type u} [DecidableEq X]
variable (N : Subgroup (FreeGroup X)) [N.Normal] (n : ℕ)

/--
The finite-stage Fox boundary/Euler map \(v \mapsto \sum_i v_i * ([x_i] - 1)\) on coordinate
vectors.
-/
def foxAlgebraicStageFoxBoundary [Fintype X] :
    foxAlgebraicStageCoordinateVector (X := X) N n →ₗ[
      foxAlgebraicStageTargetGroupAlgebra (X := X) N n]
      foxAlgebraicStageTargetGroupAlgebra (X := X) N n where
  toFun v :=
    ∑ i : X,
      v i *
        (MonoidAlgebra.of (ModNCompletedCoeff n)
          (foxAlgebraicStageTargetQuotient (X := X) N)
          (QuotientGroup.mk' N (FreeGroup.of i)) - 1)
  map_add' := by
    intro v w
    simp only [Pi.add_apply, QuotientGroup.mk'_apply, MonoidAlgebra.of_apply, add_mul,
        Finset.sum_add_distrib]
  map_smul' := by
    intro r v
    simp only [Pi.smul_apply, smul_eq_mul, QuotientGroup.mk'_apply, MonoidAlgebra.of_apply,
        mul_assoc,
  RingHom.id_apply, Finset.mul_sum]

omit [DecidableEq X] in
/--
The finite-stage Fox boundary is evaluated on the canonical generators and then extended
linearly to the finite-stage coordinate module.
-/
theorem foxAlgebraicStageFoxBoundary_apply [Fintype X]
    (v : foxAlgebraicStageCoordinateVector (X := X) N n) :
    foxAlgebraicStageFoxBoundary (X := X) N n v =
      ∑ i : X,
        v i *
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (foxAlgebraicStageTargetQuotient (X := X) N)
            (QuotientGroup.mk' N (FreeGroup.of i)) - 1) :=
  rfl

/-- The finite-stage Fox boundary sends a coordinate basis vector to its augmentation generator. -/
@[simp]
theorem foxAlgebraicStageFoxBoundary_single [Fintype X] (i : X) :
    foxAlgebraicStageFoxBoundary (X := X) N n
        (Pi.single i (1 : foxAlgebraicStageTargetGroupAlgebra (X := X) N n)) =
      MonoidAlgebra.of (ModNCompletedCoeff n)
        (foxAlgebraicStageTargetQuotient (X := X) N)
        (QuotientGroup.mk' N (FreeGroup.of i)) - 1 := by
  rw [foxAlgebraicStageFoxBoundary_apply]
  rw [Finset.sum_eq_single i]
  · simp only [Pi.single_eq_same, QuotientGroup.mk'_apply, MonoidAlgebra.of_apply, one_mul]
  · intro j _ hji
    simp only [Pi.single_eq_of_ne hji, QuotientGroup.mk'_apply, MonoidAlgebra.of_apply, zero_mul]
  · simp only [Finset.mem_univ, not_true_eq_false, Pi.single_eq_same, QuotientGroup.mk'_apply,
  MonoidAlgebra.of_apply, one_mul, IsEmpty.forall_iff]

/-- Finite-stage Fox fundamental formula for a free-group word. -/
theorem foxAlgebraicStageDerivative_fundamental_formula
    [Fintype X] (w : FreeGroup X) :
    MonoidAlgebra.of (ModNCompletedCoeff n)
        (foxAlgebraicStageTargetQuotient (X := X) N) (QuotientGroup.mk' N w) - 1 =
      ∑ i : X,
        foxAlgebraicStageDerivative (X := X) N n i w *
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (foxAlgebraicStageTargetQuotient (X := X) N)
            (QuotientGroup.mk' N (FreeGroup.of i)) - 1) := by
  induction w using FreeGroup.induction_on with
  | C1 =>
      simp only [QuotientGroup.mk'_apply, MonoidAlgebra.of_apply, MonoidAlgebra.one_def,
  sub_self, foxAlgebraicStageDerivative, foxAlgebraicStageDerivativeVector, map_one,
      FoxAlgebraicStageSemidirect.one_left,
  Pi.zero_apply, zero_mul, Finset.sum_const_zero]
  | of x =>
      simp only [QuotientGroup.mk'_apply, MonoidAlgebra.of_apply, MonoidAlgebra.one_def,
          foxAlgebraicStageDerivative,
  foxAlgebraicStageDerivativeVector_of, Pi.single_apply, ite_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ,
  ↓reduceIte]
      have hone :
          (MonoidAlgebra.single
            (1 : foxAlgebraicStageTargetQuotient (X := X) N)
            (1 : ModNCompletedCoeff n) :
              foxAlgebraicStageTargetGroupAlgebra (X := X) N n) = 1 := by
        simp only [MonoidAlgebra.one_def]
      rw [hone, one_mul]
  | inv_of x hx =>
      simp only [QuotientGroup.mk'_apply, MonoidAlgebra.of_apply, MonoidAlgebra.one_def,
  foxAlgebraicStageDerivative, foxAlgebraicStageDerivativeVector, foxAlgebraicStageLift,
      map_inv, FreeGroup.lift_apply_of,
  FoxAlgebraicStageSemidirect.inv_left, Pi.neg_apply, Pi.smul_apply, Pi.single_apply,
      smul_eq_mul, mul_ite,
  MonoidAlgebra.single_mul_single, mul_one, mul_zero, neg_mul, ite_mul, zero_mul,
      Finset.sum_neg_distrib,
  Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      change
        MonoidAlgebra.single ((QuotientGroup.mk' N (FreeGroup.of x))⁻¹)
            (1 : ModNCompletedCoeff n) -
            MonoidAlgebra.single (1 : foxAlgebraicStageTargetQuotient (X := X) N)
              (1 : ModNCompletedCoeff n) =
          - (MonoidAlgebra.single ((QuotientGroup.mk' N (FreeGroup.of x))⁻¹)
              (1 : ModNCompletedCoeff n) *
              (MonoidAlgebra.single (QuotientGroup.mk' N (FreeGroup.of x))
                  (1 : ModNCompletedCoeff n) -
                MonoidAlgebra.single (1 : foxAlgebraicStageTargetQuotient (X := X) N)
                  (1 : ModNCompletedCoeff n)))
      have hone :
          (MonoidAlgebra.single
            (1 : foxAlgebraicStageTargetQuotient (X := X) N)
            (1 : ModNCompletedCoeff n) :
              foxAlgebraicStageTargetGroupAlgebra (X := X) N n) = 1 := by
        simp only [MonoidAlgebra.one_def]
      have hmul :
          (MonoidAlgebra.single ((QuotientGroup.mk' N (FreeGroup.of x))⁻¹)
              (1 : ModNCompletedCoeff n) *
            MonoidAlgebra.single (QuotientGroup.mk' N (FreeGroup.of x))
              (1 : ModNCompletedCoeff n) :
              foxAlgebraicStageTargetGroupAlgebra (X := X) N n) = 1 := by
        simp only [QuotientGroup.mk'_apply, MonoidAlgebra.single_mul_single, inv_mul_cancel,
            mul_one,
  MonoidAlgebra.one_def]
      rw [hone, mul_sub, hmul, mul_one]
      noncomm_ring
  | mul u v hu hv =>
      let gu : foxAlgebraicStageTargetGroupAlgebra (X := X) N n :=
        MonoidAlgebra.of (ModNCompletedCoeff n)
          (foxAlgebraicStageTargetQuotient (X := X) N) (QuotientGroup.mk' N u)
      let gv : foxAlgebraicStageTargetGroupAlgebra (X := X) N n :=
        MonoidAlgebra.of (ModNCompletedCoeff n)
          (foxAlgebraicStageTargetQuotient (X := X) N) (QuotientGroup.mk' N v)
      have hmul :
          MonoidAlgebra.of (ModNCompletedCoeff n)
              (foxAlgebraicStageTargetQuotient (X := X) N) (QuotientGroup.mk' N (u * v)) =
            gu * gv := by
        simp only [QuotientGroup.mk'_apply, QuotientGroup.mk_mul, MonoidAlgebra.of_apply,
  MonoidAlgebra.single_mul_single, mul_one, gu, gv]
      calc
        MonoidAlgebra.of (ModNCompletedCoeff n)
              (foxAlgebraicStageTargetQuotient (X := X) N) (QuotientGroup.mk' N (u * v)) - 1
            = (gu - 1) + gu * (gv - 1) := by
                rw [hmul]
                noncomm_ring
        _ =
            (∑ i : X,
              foxAlgebraicStageDerivative (X := X) N n i u *
                (MonoidAlgebra.of (ModNCompletedCoeff n)
                  (foxAlgebraicStageTargetQuotient (X := X) N)
                  (QuotientGroup.mk' N (FreeGroup.of i)) - 1)) +
              gu * (∑ i : X,
                foxAlgebraicStageDerivative (X := X) N n i v *
                  (MonoidAlgebra.of (ModNCompletedCoeff n)
                    (foxAlgebraicStageTargetQuotient (X := X) N)
                    (QuotientGroup.mk' N (FreeGroup.of i)) - 1)) := by
                rw [hu, hv]
        _ =
            ∑ i : X,
              (foxAlgebraicStageDerivative (X := X) N n i u +
                gu * foxAlgebraicStageDerivative (X := X) N n i v) *
                (MonoidAlgebra.of (ModNCompletedCoeff n)
                  (foxAlgebraicStageTargetQuotient (X := X) N)
                  (QuotientGroup.mk' N (FreeGroup.of i)) - 1) := by
                rw [Finset.mul_sum, ← Finset.sum_add_distrib]
                apply Finset.sum_congr rfl
                intro i hi
                noncomm_ring
        _ =
              ∑ i : X,
                foxAlgebraicStageDerivative (X := X) N n i (u * v) *
                (MonoidAlgebra.of (ModNCompletedCoeff n)
                  (foxAlgebraicStageTargetQuotient (X := X) N)
                  (QuotientGroup.mk' N (FreeGroup.of i)) - 1) := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [foxAlgebraicStageDerivative_mul]

/-- Boundary-map form of the finite-stage Fox fundamental formula. -/
theorem foxAlgebraicStageFoxBoundary_derivativeVector [Fintype X] (w : FreeGroup X) :
    foxAlgebraicStageFoxBoundary (X := X) N n
        (foxAlgebraicStageDerivativeVector (X := X) N n w) =
      foxAlgebraicStageCoefficient (X := X) N n w - 1 := by
  rw [foxAlgebraicStageFoxBoundary_apply, foxAlgebraicStageCoefficient_apply]
  simpa [foxAlgebraicStageDerivative] using
    (foxAlgebraicStageDerivative_fundamental_formula (X := X) N n w).symm

/--
Any scalar crossed homomorphism with the standard generator values satisfies the finite-stage
Fox boundary formula.
-/
theorem foxAlgebraicStageFoxBoundary_of_crossedHom
    [Fintype X]
    (delta : ScalarCrossedHom
      (foxAlgebraicStageCoefficient (X := X) N n)
      (foxAlgebraicStageCoordinateVector (X := X) N n))
    (hbasis :
      ∀ x : X, delta (FreeGroup.of x) =
        Pi.single x (1 : foxAlgebraicStageTargetGroupAlgebra (X := X) N n))
    (w : FreeGroup X) :
    foxAlgebraicStageFoxBoundary (X := X) N n (delta w) =
      foxAlgebraicStageCoefficient (X := X) N n w - 1 := by
  have hdelta_eq :
      delta = foxAlgebraicStageDerivativeVectorCrossedHom (X := X) N n :=
    foxAlgebraicStageDerivativeVector_unique (X := X) N n delta hbasis
  rw [hdelta_eq]
  exact foxAlgebraicStageFoxBoundary_derivativeVector (X := X) N n w

/--
The Fox--Euler sum for any scalar crossed homomorphism with the standard generator values is
\([w]-1\).
-/
theorem foxAlgebraicStageDerivative_fundamental_formula_of_crossedHom
    [Fintype X]
    (delta : ScalarCrossedHom
      (foxAlgebraicStageCoefficient (X := X) N n)
      (foxAlgebraicStageCoordinateVector (X := X) N n))
    (hbasis :
      ∀ x : X, delta (FreeGroup.of x) =
        Pi.single x (1 : foxAlgebraicStageTargetGroupAlgebra (X := X) N n))
    (w : FreeGroup X) :
    foxAlgebraicStageCoefficient (X := X) N n w - 1 =
      ∑ i : X,
        delta w i *
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (foxAlgebraicStageTargetQuotient (X := X) N)
            (QuotientGroup.mk' N (FreeGroup.of i)) - 1) := by
  simpa [foxAlgebraicStageFoxBoundary_apply] using
    (foxAlgebraicStageFoxBoundary_of_crossedHom
      (X := X) N n delta hbasis w).symm


end

end FoxDifferential
