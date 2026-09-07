import ProCGroups.FoxDifferential.Common.FoxBoundary
import ProCGroups.FoxDifferential.Completed.ProCIntegerCoefficients.FreeGroup.Derivative

set_option autoImplicit false

/-!
# Fox differential: completed — \(\mathbb{Z}_C\) coefficients — free group — coordinates

The principal declarations in this module are:

- `zcFreeGroupFoxBoundary`
  The completed Fox boundary/Euler map \(v \mapsto \sum_i v_i * ([\psi(x_i)]-1)\).
- `zcDifferentialToFreeFoxCoordinates`
  The linear map from the completed universal module to completed Fox-coordinate vectors.
- `zcFreeGroupFoxBoundary_apply`
  The boundary map is evaluated on the canonical generators and then extended linearly to the
  completed coordinate module.
- `zcFreeGroupFoxBoundary_eq_foxBoundaryMap`
  The completed Fox boundary is the generic finite Fox boundary map specialized to \(x \mapsto
  [\psi(x)] - 1\).
-/

namespace FoxDifferential

noncomputable section

open scoped BigOperators

universe u v


variable (C : ProCGroups.FiniteGroupClass.{v})
variable {X : Type u} [DecidableEq X]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

section FiniteBasis

variable [Fintype X]

/-- The completed Fox boundary/Euler map \(v \mapsto \sum_i v_i * ([\psi(x_i)]-1)\). -/
def zcFreeGroupFoxBoundary (ψ : FreeGroup X →* H) :
    ZCFreeFoxCoordinates C (X := X) (H := H) →ₗ[ZCCompletedGroupAlgebra C H]
      ZCCompletedGroupAlgebra C H where
  toFun v := ∑ i : X, v i * (zcGroupLike C H (ψ (FreeGroup.of i)) - 1)
  map_add' := by
    intro v w
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro r v
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, RingHom.id_apply, Finset.mul_sum]

omit [DecidableEq X] in
/--
The boundary map is evaluated on the canonical generators and then extended linearly to the
completed coordinate module.
-/
theorem zcFreeGroupFoxBoundary_apply
    (ψ : FreeGroup X →* H) (v : ZCFreeFoxCoordinates C (X := X) (H := H)) :
    zcFreeGroupFoxBoundary C ψ v =
      ∑ i : X, v i * (zcGroupLike C H (ψ (FreeGroup.of i)) - 1) :=
  rfl

omit [DecidableEq X] in
/--
The completed Fox boundary is the generic finite Fox boundary map specialized to \(x \mapsto
[\psi(x)] - 1\).
-/
theorem zcFreeGroupFoxBoundary_eq_foxBoundaryMap
    (ψ : FreeGroup X →* H) :
    zcFreeGroupFoxBoundary C ψ =
      foxBoundaryMap
        (fun i : X =>
          coefficientFoxBoundary (zcCompletedGroupAlgebraScalar C ψ) (FreeGroup.of i)) := by
  ext v
  rfl

/--
The completed Fox boundary sends a coordinate basis vector to the corresponding completed
augmentation generator.
-/
@[simp]
theorem zcFreeGroupFoxBoundary_single (ψ : FreeGroup X →* H) (i : X) :
    zcFreeGroupFoxBoundary C ψ
        (Pi.single i (1 : ZCCompletedGroupAlgebra C H)) =
      zcCompletedGroupAlgebraBoundary C ψ (FreeGroup.of i) := by
  rw [zcFreeGroupFoxBoundary_apply]
  rw [Finset.sum_eq_single i]
  · simp only [Pi.single_eq_same, one_mul]
    rfl
  · intro j _ hji
    simp only [Pi.single_eq_of_ne hji, zero_mul]
  · simp only [Finset.mem_univ, not_true_eq_false, Pi.single_eq_same, one_mul, IsEmpty.forall_iff]

/-- The linear map from the completed universal module to completed Fox-coordinate vectors. -/
def zcDifferentialToFreeFoxCoordinates (ψ : FreeGroup X →* H) :
    ZCCompletedDifferentialModule C ψ →ₗ[ZCCompletedGroupAlgebra C H]
      ZCFreeFoxCoordinates C (X := X) (H := H) :=
  zcFreeGroupFoxDerivativeVectorLinearMap C ψ

omit [Fintype X] in
/--
The completed coordinate map sends a universal differential to the completed Fox derivative
vector.
-/
@[simp]
theorem zcDifferentialToFreeFoxCoordinates_universal
    (ψ : FreeGroup X →* H) (w : FreeGroup X) :
    zcDifferentialToFreeFoxCoordinates C ψ
        (zcUniversalDifferential C ψ w) =
      zcFreeGroupFoxDerivativeVector C ψ w := by
  exact zcFreeGroupFoxDerivativeVectorLinearMap_universal C ψ w

/--
The linear map from completed Fox-coordinate vectors to the completed universal module, sending
the coordinate basis at \(x\) to \(d_{\psi}(x)\).
-/
def zcFreeFoxCoordinatesLinearMap (ψ : FreeGroup X →* H) :
    ZCFreeFoxCoordinates C (X := X) (H := H) →ₗ[ZCCompletedGroupAlgebra C H]
      ZCCompletedDifferentialModule C ψ where
  toFun v := ∑ x : X, v x • zcUniversalDifferential C ψ (FreeGroup.of x)
  map_add' := by
    intro v w
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro r v
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, Finset.smul_sum, smul_smul]

/--
The coordinate-to-differential map sends a coordinate basis vector to the corresponding
universal completed differential.
-/
@[simp]
theorem zcFreeFoxCoordinatesLinearMap_single (ψ : FreeGroup X →* H) (x : X) :
    zcFreeFoxCoordinatesLinearMap C ψ
        (Pi.single x (1 : ZCCompletedGroupAlgebra C H)) =
      zcUniversalDifferential C ψ (FreeGroup.of x) := by
  change (∑ y : X,
      ((Pi.single x (1 : ZCCompletedGroupAlgebra C H) :
        ZCFreeFoxCoordinates C (X := X) (H := H)) y) •
        zcUniversalDifferential C ψ (FreeGroup.of y)) =
    zcUniversalDifferential C ψ (FreeGroup.of x)
  rw [Finset.sum_eq_single x]
  · simp only [Pi.single_eq_same, one_smul]
  · intro y _ hy
    simp only [Pi.single_eq_of_ne hy, zero_smul]
  · simp only [Finset.mem_univ, not_true_eq_false, Pi.single_eq_same, one_smul, IsEmpty.forall_iff]

/--
The coordinate-to-differential map recovers the universal completed differential from the
completed derivative vector.
-/
theorem zcFreeFoxCoordinatesLinearMap_derivativeVector
    (ψ : FreeGroup X →* H) (w : FreeGroup X) :
    zcFreeFoxCoordinatesLinearMap C ψ
        (zcFreeGroupFoxDerivativeVector C ψ w) =
      zcUniversalDifferential C ψ w := by
  let beta : ScalarCrossedHom (zcCompletedGroupAlgebraScalar C ψ)
      (ZCCompletedDifferentialModule C ψ) :=
    (zcFreeGroupFoxDerivativeVector C ψ).mapLinear
      (zcFreeFoxCoordinatesLinearMap C ψ)
  have hbasis :
      ∀ x : X, beta (FreeGroup.of x) =
        zcUniversalDifferential C ψ (FreeGroup.of x) := by
    intro x
    change zcFreeFoxCoordinatesLinearMap C ψ
        (zcFreeGroupFoxDerivativeVector C ψ (FreeGroup.of x)) =
      zcUniversalDifferential C ψ (FreeGroup.of x)
    rw [zcFreeGroupFoxDerivativeVector_of, zcFreeFoxCoordinatesLinearMap_single]
  have hbeta_eq :
      beta =
        freeCrossedHomWithCoeff
          (A := ZCCompletedDifferentialModule C ψ)
          (zcCompletedGroupAlgebraScalar C ψ)
          (fun x => zcUniversalDifferential C ψ (FreeGroup.of x)) := by
    exact freeCrossedHomWithCoeff_unique
      (A := ZCCompletedDifferentialModule C ψ)
      (zcCompletedGroupAlgebraScalar C ψ)
      (fun x => zcUniversalDifferential C ψ (FreeGroup.of x))
      beta hbasis
  have huniv_eq :
      zcUniversalDifferential C ψ =
        freeCrossedHomWithCoeff
          (A := ZCCompletedDifferentialModule C ψ)
          (zcCompletedGroupAlgebraScalar C ψ)
          (fun x => zcUniversalDifferential C ψ (FreeGroup.of x)) := by
    exact freeCrossedHomWithCoeff_unique
      (A := ZCCompletedDifferentialModule C ψ)
      (zcCompletedGroupAlgebraScalar C ψ)
      (fun x => zcUniversalDifferential C ψ (FreeGroup.of x))
      (zcUniversalDifferential C ψ) (by intro x; rfl)
  exact congrArg
    (fun d : ScalarCrossedHom (zcCompletedGroupAlgebraScalar C ψ)
      (ZCCompletedDifferentialModule C ψ) => d w)
    (hbeta_eq.trans huniv_eq.symm)

/-- The coordinate map is a left inverse to the coordinate-to-differential map. -/
theorem zcDifferentialToFreeFoxCoordinates_comp_zcFreeFoxCoordinatesLinearMap
    (ψ : FreeGroup X →* H) :
    (zcDifferentialToFreeFoxCoordinates C ψ).comp
        (zcFreeFoxCoordinatesLinearMap C ψ) =
      LinearMap.id := by
  apply LinearMap.ext
  intro v
  rw [LinearMap.comp_apply]
  change zcDifferentialToFreeFoxCoordinates C ψ
      (∑ y : X, v y • zcUniversalDifferential C ψ (FreeGroup.of y)) = v
  rw [map_sum]
  simp only [map_smul, zcDifferentialToFreeFoxCoordinates_universal]
  funext x
  change ((∑ y : X,
      v y • zcFreeGroupFoxDerivativeVector C ψ (FreeGroup.of y)) :
      ZCFreeFoxCoordinates C (X := X) (H := H)) x = v x
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single x]
  · simp only [zcFreeGroupFoxDerivativeVector_of, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul,
      mul_one]
  · intro y _ hy
    have hxy : x ≠ y := fun h => hy h.symm
    simp only [zcFreeGroupFoxDerivativeVector_of, Pi.smul_apply, Pi.single_eq_of_ne hxy,
        smul_eq_mul, mul_zero]
  · simp only [Finset.mem_univ, not_true_eq_false, zcFreeGroupFoxDerivativeVector_of, Pi.smul_apply,
  Pi.single_eq_same, smul_eq_mul, mul_one, IsEmpty.forall_iff]

/-- The coordinate-to-differential map is a left inverse to the completed coordinate map. -/
theorem zcFreeFoxCoordinatesLinearMap_comp_zcDifferentialToFreeFoxCoordinates
    (ψ : FreeGroup X →* H) :
    (zcFreeFoxCoordinatesLinearMap C ψ).comp
        (zcDifferentialToFreeFoxCoordinates C ψ) =
      LinearMap.id := by
  apply crossedDifferentialModuleHom_ext
    (A := ZCCompletedDifferentialModule C ψ)
    (zcCompletedGroupAlgebraScalar C ψ)
  intro w
  change zcFreeFoxCoordinatesLinearMap C ψ
      (zcDifferentialToFreeFoxCoordinates C ψ
        (zcUniversalDifferential C ψ w)) =
    zcUniversalDifferential C ψ w
  rw [zcDifferentialToFreeFoxCoordinates_universal,
    zcFreeFoxCoordinatesLinearMap_derivativeVector]

/--
The linear equivalence between completed Fox coordinates and the completed universal
differential module of a finite-rank free group.
-/
def zcFreeFoxCoordinatesLinearEquivDifferential
    (ψ : FreeGroup X →* H) :
    ZCFreeFoxCoordinates C (X := X) (H := H) ≃ₗ[ZCCompletedGroupAlgebra C H]
      ZCCompletedDifferentialModule C ψ := by
  refine LinearEquiv.ofLinearMap
    (zcFreeFoxCoordinatesLinearMap C ψ)
    (zcDifferentialToFreeFoxCoordinates C ψ)
    ?_ ?_
  · exact zcFreeFoxCoordinatesLinearMap_comp_zcDifferentialToFreeFoxCoordinates C ψ
  · exact zcDifferentialToFreeFoxCoordinates_comp_zcFreeFoxCoordinatesLinearMap C ψ


end FiniteBasis


end

end FoxDifferential
