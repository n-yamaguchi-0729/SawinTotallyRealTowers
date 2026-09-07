import ProCGroups.FoxDifferential.Completed.Residue.FreeGroup.Universal

set_option autoImplicit false

/-!
# Fox differential: completed — residue — free group — coordinates

The principal declarations in this module are:

- `residueDifferentialToFreeFoxCoordinates`
  The linear map from the residue universal module to residue Fox-coordinate vectors.
- `residueFreeFoxCoordinatesLinearMap`
  The linear map from residue Fox-coordinate vectors to the residue universal module, sending the
  coordinate basis at \(x\) to \(d_{\psi}(x)\).
- `residueDifferentialToFreeFoxCoordinates_universal`
  The residue coordinate map sends a universal differential to the residue Fox derivative vector.
- `residueFreeFoxCoordinatesLinearMap_single`
  The coordinate-to-differential map sends a coordinate basis vector to the corresponding universal
  residue differential.
-/

namespace FoxDifferential

noncomputable section

open scoped BigOperators

universe u v


variable {X : Type u} {H : Type v} [Group H] [DecidableEq X]

section FiniteBasis

variable [Fintype X]

/-- The linear map from the residue universal module to residue Fox-coordinate vectors. -/
def residueDifferentialToFreeFoxCoordinates (n : ℕ) (ψ : FreeGroup X →* H) :
    ResidueDifferentialModule n ψ →ₗ[ResidueGroupRing n H]
      ResidueFreeFoxCoordinates n H X :=
  residueFreeGroupFoxDerivativeVectorLinearMap n ψ

omit [Fintype X] in
/--
The residue coordinate map sends a universal differential to the residue Fox derivative vector.
-/
@[simp]
theorem residueDifferentialToFreeFoxCoordinates_universal
    (n : ℕ) (ψ : FreeGroup X →* H) (w : FreeGroup X) :
    residueDifferentialToFreeFoxCoordinates n ψ
        (residueUniversalDifferential n ψ w) =
      residueFreeGroupFoxDerivativeVector n ψ w := by
  exact residueFreeGroupFoxDerivativeVectorLinearMap_universal n ψ w

/--
The linear map from residue Fox-coordinate vectors to the residue universal module, sending the
coordinate basis at \(x\) to \(d_{\psi}(x)\).
-/
def residueFreeFoxCoordinatesLinearMap (n : ℕ) (ψ : FreeGroup X →* H) :
    ResidueFreeFoxCoordinates n H X →ₗ[ResidueGroupRing n H]
      ResidueDifferentialModule n ψ where
  toFun v := ∑ x : X, v x • residueUniversalDifferential n ψ (FreeGroup.of x)
  map_add' := by
    intro v w
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro r v
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, smul_smul]

/--
The coordinate-to-differential map sends a coordinate basis vector to the corresponding
universal residue differential.
-/
@[simp]
theorem residueFreeFoxCoordinatesLinearMap_single
    (n : ℕ) (ψ : FreeGroup X →* H) (x : X) :
    residueFreeFoxCoordinatesLinearMap n ψ
        (Pi.single x (1 : ResidueGroupRing n H)) =
      residueUniversalDifferential n ψ (FreeGroup.of x) := by
  change (∑ y : X,
      ((Pi.single x (1 : ResidueGroupRing n H) : ResidueFreeFoxCoordinates n H X) y) •
        residueUniversalDifferential n ψ (FreeGroup.of y)) =
    residueUniversalDifferential n ψ (FreeGroup.of x)
  rw [Finset.sum_eq_single x]
  · simp only [Pi.single_eq_same, one_smul]
  · intro y _ hy
    simp only [Pi.single_eq_of_ne hy, zero_smul]
  · simp only [Finset.mem_univ, not_true_eq_false, Pi.single_eq_same, one_smul, IsEmpty.forall_iff]

/--
The coordinate-to-differential map recovers the universal residue differential from the residue
derivative vector.
-/
theorem residueFreeFoxCoordinatesLinearMap_derivativeVector
    (n : ℕ) (ψ : FreeGroup X →* H) (w : FreeGroup X) :
    residueFreeFoxCoordinatesLinearMap n ψ
        (residueFreeGroupFoxDerivativeVector n ψ w) =
      residueUniversalDifferential n ψ w := by
  let beta : ScalarCrossedHom (residueGroupRingScalar n ψ)
      (ResidueDifferentialModule n ψ) :=
    (residueFreeGroupFoxDerivativeVector n ψ).mapLinear
      (residueFreeFoxCoordinatesLinearMap n ψ)
  have hbasis :
      ∀ x : X, beta (FreeGroup.of x) =
        residueUniversalDifferential n ψ (FreeGroup.of x) := by
    intro x
    change residueFreeFoxCoordinatesLinearMap n ψ
        (residueFreeGroupFoxDerivativeVector n ψ (FreeGroup.of x)) =
      residueUniversalDifferential n ψ (FreeGroup.of x)
    rw [residueFreeGroupFoxDerivativeVector_of, residueFreeFoxCoordinatesLinearMap_single]
  have hbeta_eq :
      beta =
        freeCrossedHomWithCoeff
          (A := ResidueDifferentialModule n ψ)
          (residueGroupRingScalar n ψ)
          (fun x => residueUniversalDifferential n ψ (FreeGroup.of x)) := by
    exact freeCrossedHomWithCoeff_unique
      (A := ResidueDifferentialModule n ψ)
      (residueGroupRingScalar n ψ)
      (fun x => residueUniversalDifferential n ψ (FreeGroup.of x)) beta hbasis
  have huniv_eq :
      residueUniversalDifferential n ψ =
        freeCrossedHomWithCoeff
          (A := ResidueDifferentialModule n ψ)
          (residueGroupRingScalar n ψ)
          (fun x => residueUniversalDifferential n ψ (FreeGroup.of x)) := by
    exact freeCrossedHomWithCoeff_unique
      (A := ResidueDifferentialModule n ψ)
      (residueGroupRingScalar n ψ)
      (fun x => residueUniversalDifferential n ψ (FreeGroup.of x))
      (residueUniversalDifferential n ψ) (by intro x; rfl)
  exact congrArg
    (fun d : ScalarCrossedHom (residueGroupRingScalar n ψ)
      (ResidueDifferentialModule n ψ) => d w)
    (hbeta_eq.trans huniv_eq.symm)

/-- The coordinate map is a left inverse to the coordinate-to-differential map. -/
theorem residueDifferentialToFreeFoxCoordinates_comp_residueFreeFoxCoordinatesLinearMap
    (n : ℕ) (ψ : FreeGroup X →* H) :
    (residueDifferentialToFreeFoxCoordinates n ψ).comp
        (residueFreeFoxCoordinatesLinearMap n ψ) =
      LinearMap.id := by
  apply LinearMap.ext
  intro v
  rw [LinearMap.comp_apply]
  change residueDifferentialToFreeFoxCoordinates n ψ
      (∑ y : X, v y • residueUniversalDifferential n ψ (FreeGroup.of y)) = v
  rw [map_sum]
  simp only [map_smul, residueDifferentialToFreeFoxCoordinates_universal]
  funext x
  change ((∑ y : X,
      v y • residueFreeGroupFoxDerivativeVector n ψ (FreeGroup.of y)) :
      ResidueFreeFoxCoordinates n H X) x = v x
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single x]
  · simp only [residueFreeGroupFoxDerivativeVector_of, Pi.smul_apply, Pi.single_eq_same,
      smul_eq_mul, mul_one]
  · intro y _ hy
    have hxy : x ≠ y := fun h => hy h.symm
    simp only [residueFreeGroupFoxDerivativeVector_of, Pi.smul_apply, Pi.single_eq_of_ne hxy,
        smul_eq_mul,
  mul_zero]
  · simp only [Finset.mem_univ, not_true_eq_false, residueFreeGroupFoxDerivativeVector_of,
      Pi.smul_apply,
  Pi.single_eq_same, smul_eq_mul, mul_one, IsEmpty.forall_iff]

/-- The coordinate-to-differential map is a left inverse to the residue coordinate map. -/
theorem residueFreeFoxCoordinatesLinearMap_comp_residueDifferentialToFreeFoxCoordinates
    (n : ℕ) (ψ : FreeGroup X →* H) :
    (residueFreeFoxCoordinatesLinearMap n ψ).comp
        (residueDifferentialToFreeFoxCoordinates n ψ) =
      LinearMap.id := by
  apply residueDifferentialModuleHom_ext n ψ
  intro w
  simp only [LinearMap.comp_apply, residueDifferentialToFreeFoxCoordinates_universal,
  residueFreeFoxCoordinatesLinearMap_derivativeVector, LinearMap.id_coe, id_eq]

/--
The linear equivalence between residue Fox coordinates and the residue universal differential
module of a finite-rank free group.
-/
def residueFreeFoxCoordinatesLinearEquivDifferential
    (n : ℕ) (ψ : FreeGroup X →* H) :
    ResidueFreeFoxCoordinates n H X ≃ₗ[ResidueGroupRing n H]
      ResidueDifferentialModule n ψ := by
  refine LinearEquiv.ofLinearMap
    (residueFreeFoxCoordinatesLinearMap n ψ)
    (residueDifferentialToFreeFoxCoordinates n ψ)
    ?_ ?_
  · exact residueFreeFoxCoordinatesLinearMap_comp_residueDifferentialToFreeFoxCoordinates
      n ψ
  · exact residueDifferentialToFreeFoxCoordinates_comp_residueFreeFoxCoordinatesLinearMap
      n ψ

end FiniteBasis


end

end FoxDifferential
