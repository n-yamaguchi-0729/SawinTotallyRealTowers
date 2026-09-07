import ProCGroups.FoxDifferential.Completed.FreeProC.StageProjection

set_option autoImplicit false

/-!
# Fox differential: completed — free pro-\(C\) — coordinate stage projection

The principal declarations in this module are:

- `zcFreeFoxCoordinatesStageMap`
  Coordinatewise finite-stage projection on completed Fox vectors, induced by a coefficient ring map
  \(\mathbb{Z}_C\llbracket H\rrbracket \to (\mathbb{Z}/n\mathbb{Z})[F/N]\).
- `freeProCZCCompletedFoxSemidirectStageMapOfCoeff`
  The semidirect finite-stage projection induced by a coefficient projection and a target quotient
  map.
- `zcFreeFoxCoordinatesStageMap_apply`
  The finite-stage map on completed Fox-coordinate vectors is computed coordinatewise by the
  underlying coefficient-stage map.
- `zcFreeFoxCoordinatesStageMap_single`
  The finite-stage coordinate map for completed free Fox coordinates has the stated value on a
  single generator.
-/

namespace FoxDifferential

noncomputable section

open scoped BigOperators
open ProCGroups.ProC

universe u

section CoordinateStageMap

variable {C : ProCGroups.FiniteGroupClass}
variable {X H : Type u}
variable [DecidableEq X]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable (N : Subgroup (FreeGroup X)) [N.Normal]
variable (n : ℕ) [Fact (0 < n)]

/--
Coordinatewise finite-stage projection on completed Fox vectors, induced by a coefficient ring
map \(\mathbb{Z}_C\llbracket H\rrbracket \to (\mathbb{Z}/n\mathbb{Z})[F/N]\).
-/
def zcFreeFoxCoordinatesStageMap
    (stageCoeff :
      ZCCompletedGroupAlgebra C H →+*
        foxAlgebraicStageTargetGroupAlgebra (X := X) N n) :
    ZCFreeFoxCoordinates C (X := X) (H := H) →+
      foxAlgebraicStageCoordinateVector (X := X) N n where
  toFun v := fun i : X => stageCoeff (v i)
  map_zero' := by
    funext i
    exact map_zero stageCoeff
  map_add' v w := by
    funext i
    exact map_add stageCoeff (v i) (w i)

omit [DecidableEq X] [Fact (0 < n)] in
/--
The finite-stage map on completed Fox-coordinate vectors is computed coordinatewise by the
underlying coefficient-stage map.
-/
@[simp]
theorem zcFreeFoxCoordinatesStageMap_apply
    (stageCoeff :
      ZCCompletedGroupAlgebra C H →+*
        foxAlgebraicStageTargetGroupAlgebra (X := X) N n)
    (v : ZCFreeFoxCoordinates C (X := X) (H := H))
    (i : X) :
    zcFreeFoxCoordinatesStageMap (C := C) (X := X) (H := H) N n stageCoeff v i =
      stageCoeff (v i) :=
  rfl

omit [Fact (0 < n)] in
/--
The finite-stage coordinate map for completed free Fox coordinates has the stated value on a
single generator.
-/
@[simp]
theorem zcFreeFoxCoordinatesStageMap_single
    (stageCoeff :
      ZCCompletedGroupAlgebra C H →+*
        foxAlgebraicStageTargetGroupAlgebra (X := X) N n)
    (i : X) :
    zcFreeFoxCoordinatesStageMap (C := C) (X := X) (H := H) N n stageCoeff
        (Pi.single i (1 : ZCCompletedGroupAlgebra C H)) =
      Pi.single i (1 : foxAlgebraicStageTargetGroupAlgebra (X := X) N n) := by
  funext j
  by_cases hji : j = i
  · subst hji
    simp only [zcFreeFoxCoordinatesStageMap_apply, Pi.single_eq_same, map_one]
  · simp only [zcFreeFoxCoordinatesStageMap_apply, Pi.single_eq_of_ne hji, map_zero]

omit [DecidableEq X] [Fact (0 < n)] in
/--
If the coefficient projection sends completed group-like elements to finite quotient basis
terms, then the coordinate projection respects the scalar action used in the Fox semidirect
product.
-/
theorem zcFreeFoxCoordinatesStageMap_smul_groupLike
    (stageCoeff :
      ZCCompletedGroupAlgebra C H →+*
        foxAlgebraicStageTargetGroupAlgebra (X := X) N n)
    (stageRight : H →* foxAlgebraicStageTargetQuotient (X := X) N)
    (hgroupLike : ∀ h : H,
      stageCoeff (zcGroupLike C H h) =
        MonoidAlgebra.of (ModNCompletedCoeff n)
          (foxAlgebraicStageTargetQuotient (X := X) N) (stageRight h))
    (h : H)
    (v : ZCFreeFoxCoordinates C (X := X) (H := H)) :
    zcFreeFoxCoordinatesStageMap (C := C) (X := X) (H := H) N n stageCoeff
        (zcGroupLike C H h • v) =
      (MonoidAlgebra.of (ModNCompletedCoeff n)
        (foxAlgebraicStageTargetQuotient (X := X) N) (stageRight h)) •
        zcFreeFoxCoordinatesStageMap
          (C := C) (X := X) (H := H) N n stageCoeff v := by
  funext i
  change stageCoeff (zcGroupLike C H h * v i) =
    (MonoidAlgebra.of (ModNCompletedCoeff n)
      (foxAlgebraicStageTargetQuotient (X := X) N) (stageRight h)) * stageCoeff (v i)
  rw [map_mul, hgroupLike]

omit [DecidableEq X] [TopologicalSpace H] [IsTopologicalGroup H] in
/--
Generator-level target compatibility implies word-level compatibility of the right finite
quotient map with the free-group quotient map.
-/
theorem finiteStageRight_comp_lift_eq_quotientMk
    (φ : X → H)
    (stageRight : H →* foxAlgebraicStageTargetQuotient (X := X) N)
    (hright_generators : ∀ i : X,
      stageRight (φ i) = QuotientGroup.mk' N (FreeGroup.of i))
    (w : FreeGroup X) :
    stageRight (FreeGroup.lift φ w) = QuotientGroup.mk' N w := by
  induction w using FreeGroup.induction_on with
  | C1 =>
      simp only [map_one]
  | of x =>
      simpa using hright_generators x
  | inv_of x hx =>
      simpa using congrArg Inv.inv hx
  | mul u v hu hv =>
      simp only [map_mul, hu, QuotientGroup.mk'_apply, hv]

omit [DecidableEq X] [Fact (0 < n)] in
/--
Boundary compatibility from a coefficient projection whose group-like values agree with the
finite quotient generators.
-/
theorem foxAlgebraicStageFoxBoundary_zcFreeFoxCoordinatesStageMap
    [Fintype X]
    (φ : X → H)
    (stageCoeff :
      ZCCompletedGroupAlgebra C H →+*
        foxAlgebraicStageTargetGroupAlgebra (X := X) N n)
    (hgroupLike_generators : ∀ i : X,
      stageCoeff (zcGroupLike C H (φ i)) =
        MonoidAlgebra.of (ModNCompletedCoeff n)
          (foxAlgebraicStageTargetQuotient (X := X) N)
          (QuotientGroup.mk' N (FreeGroup.of i)))
    (v : ZCFreeFoxCoordinates C (X := X) (H := H)) :
    foxAlgebraicStageFoxBoundary (X := X) N n
        (zcFreeFoxCoordinatesStageMap (C := C) (X := X) (H := H) N n stageCoeff v) =
      stageCoeff
        (zcFreeGroupFoxBoundary C (FreeGroup.lift φ) v) := by
  rw [foxAlgebraicStageFoxBoundary_apply,
    zcFreeGroupFoxBoundary_apply]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change stageCoeff (v i) *
      (MonoidAlgebra.of (ModNCompletedCoeff n)
          (foxAlgebraicStageTargetQuotient (X := X) N)
          (QuotientGroup.mk' N (FreeGroup.of i)) - 1) =
    stageCoeff (v i *
      (zcGroupLike C H ((FreeGroup.lift φ) (FreeGroup.of i)) - 1))
  rw [map_mul, map_sub]
  simp only [QuotientGroup.mk'_apply, MonoidAlgebra.of_apply, FreeGroup.lift_apply_of,
      hgroupLike_generators,
  map_one]

omit [DecidableEq X] [Fact (0 < n)] in
/-- Boundary compatibility in the right-quotient form used by the semidirect stage maps. -/
theorem foxAlgebraicStageFoxBoundary_zcFreeFoxCoordinatesStageMap_of_groupLike
    [Fintype X]
    (φ : X → H)
    (stageCoeff :
      ZCCompletedGroupAlgebra C H →+*
        foxAlgebraicStageTargetGroupAlgebra (X := X) N n)
    (stageRight : H →* foxAlgebraicStageTargetQuotient (X := X) N)
    (hgroupLike : ∀ h : H,
      stageCoeff (zcGroupLike C H h) =
        MonoidAlgebra.of (ModNCompletedCoeff n)
          (foxAlgebraicStageTargetQuotient (X := X) N) (stageRight h))
    (hright_generators : ∀ i : X,
      stageRight (φ i) = QuotientGroup.mk' N (FreeGroup.of i))
    (v : ZCFreeFoxCoordinates C (X := X) (H := H)) :
    foxAlgebraicStageFoxBoundary (X := X) N n
        (zcFreeFoxCoordinatesStageMap (C := C) (X := X) (H := H) N n stageCoeff v) =
      stageCoeff
        (zcFreeGroupFoxBoundary C (FreeGroup.lift φ) v) := by
  exact foxAlgebraicStageFoxBoundary_zcFreeFoxCoordinatesStageMap
    (C := C) (X := X) (H := H) N n φ stageCoeff
    (fun i => by rw [hgroupLike (φ i), hright_generators i]) v

omit [Fact (0 < n)] in
/--
The coordinate projection sends the completed free Fox derivative vector to the finite-stage Fox
derivative vector.
-/
theorem zcFreeFoxCoordinatesStageMap_derivativeVector
    (φ : X → H)
    (stageCoeff :
      ZCCompletedGroupAlgebra C H →+*
        foxAlgebraicStageTargetGroupAlgebra (X := X) N n)
    (stageRight : H →* foxAlgebraicStageTargetQuotient (X := X) N)
    (hgroupLike : ∀ h : H,
      stageCoeff (zcGroupLike C H h) =
        MonoidAlgebra.of (ModNCompletedCoeff n)
          (foxAlgebraicStageTargetQuotient (X := X) N) (stageRight h))
    (hright_word : ∀ w : FreeGroup X,
      stageRight (FreeGroup.lift φ w) = QuotientGroup.mk' N w)
    (w : FreeGroup X) :
    zcFreeFoxCoordinatesStageMap (C := C) (X := X) (H := H) N n stageCoeff
        (zcFreeGroupFoxDerivativeVector C (FreeGroup.lift φ) w) =
      foxAlgebraicStageDerivativeVector (X := X) N n w := by
  let delta : ScalarCrossedHom
      (foxAlgebraicStageCoefficient (X := X) N n)
      (foxAlgebraicStageCoordinateVector (X := X) N n) :=
    { toFun := fun w =>
        zcFreeFoxCoordinatesStageMap
          (C := C) (X := X) (H := H) N n stageCoeff
          (zcFreeGroupFoxDerivativeVector C (FreeGroup.lift φ) w)
      map_mul' := by
        intro u v
        rw [scalarCrossedAction_apply]
        change
          zcFreeFoxCoordinatesStageMap (C := C) (X := X) (H := H) N n stageCoeff
              (zcFreeGroupFoxDerivativeVector C
                (FreeGroup.lift φ) (u * v)) =
            zcFreeFoxCoordinatesStageMap (C := C) (X := X) (H := H) N n stageCoeff
              (zcFreeGroupFoxDerivativeVector C
                (FreeGroup.lift φ) u) +
              foxAlgebraicStageCoefficient (X := X) N n u •
                zcFreeFoxCoordinatesStageMap (C := C) (X := X) (H := H) N n stageCoeff
                  (zcFreeGroupFoxDerivativeVector C
                    (FreeGroup.lift φ) v)
        rw [ScalarCrossedHom.map_mul, zcCompletedGroupAlgebraScalar_apply]
        rw [map_add]
        rw [zcFreeFoxCoordinatesStageMap_smul_groupLike
          (C := C) (X := X) (H := H) N n stageCoeff stageRight hgroupLike]
        rw [hright_word u]
        rfl }
  have hbasis : ∀ x : X, delta (FreeGroup.of x) =
      Pi.single x (1 : foxAlgebraicStageTargetGroupAlgebra (X := X) N n) := by
    intro x
    change zcFreeFoxCoordinatesStageMap
        (C := C) (X := X) (H := H) N n stageCoeff
        (zcFreeGroupFoxDerivativeVector C
          (FreeGroup.lift φ) (FreeGroup.of x)) =
      Pi.single x (1 : foxAlgebraicStageTargetGroupAlgebra (X := X) N n)
    rw [zcFreeGroupFoxDerivativeVector_of]
    exact zcFreeFoxCoordinatesStageMap_single
      (C := C) (X := X) (H := H) N n stageCoeff x
  have hdelta_eq := foxAlgebraicStageDerivativeVector_unique (X := X) N n delta hbasis
  change
    delta w =
      foxAlgebraicStageDerivativeVectorCrossedHom (X := X) N n w
  exact congrArg (fun d => d w) hdelta_eq

omit [Fact (0 < n)] in
/-- Generator-level right compatibility is enough for the derivative-vector projection formula. -/
theorem zcFreeFoxCoordinatesStageMap_derivativeVector_of_generators
    (φ : X → H)
    (stageCoeff :
      ZCCompletedGroupAlgebra C H →+*
        foxAlgebraicStageTargetGroupAlgebra (X := X) N n)
    (stageRight : H →* foxAlgebraicStageTargetQuotient (X := X) N)
    (hgroupLike : ∀ h : H,
      stageCoeff (zcGroupLike C H h) =
        MonoidAlgebra.of (ModNCompletedCoeff n)
          (foxAlgebraicStageTargetQuotient (X := X) N) (stageRight h))
    (hright_generators : ∀ i : X,
      stageRight (φ i) = QuotientGroup.mk' N (FreeGroup.of i))
    (w : FreeGroup X) :
    zcFreeFoxCoordinatesStageMap (C := C) (X := X) (H := H) N n stageCoeff
        (zcFreeGroupFoxDerivativeVector C (FreeGroup.lift φ) w) =
      foxAlgebraicStageDerivativeVector (X := X) N n w := by
  exact zcFreeFoxCoordinatesStageMap_derivativeVector
    (C := C) (X := X) (H := H) N n φ stageCoeff stageRight hgroupLike
    (finiteStageRight_comp_lift_eq_quotientMk
      (X := X) (H := H) N φ stageRight hright_generators) w

/--
The semidirect finite-stage projection induced by a coefficient projection and a target quotient
map.
-/
def freeProCZCCompletedFoxSemidirectStageMapOfCoeff
    (stageCoeff :
      ZCCompletedGroupAlgebra C H →+*
        foxAlgebraicStageTargetGroupAlgebra (X := X) N n)
    (stageRight : H →* foxAlgebraicStageTargetQuotient (X := X) N)
    (hgroupLike : ∀ h : H,
      stageCoeff (zcGroupLike C H h) =
        MonoidAlgebra.of (ModNCompletedCoeff n)
          (foxAlgebraicStageTargetQuotient (X := X) N) (stageRight h)) :
    ZCCompletedFoxSemidirect C X H →*
      FoxAlgebraicStageSemidirect (X := X) N n :=
  freeProCZCCompletedFoxSemidirectStageMap
    (C := C) (X := X) (H := H) N n
    (zcFreeFoxCoordinatesStageMap (C := C) (X := X) (H := H) N n stageCoeff)
    stageRight
    (zcFreeFoxCoordinatesStageMap_smul_groupLike
      (C := C) (X := X) (H := H) N n stageCoeff stageRight hgroupLike)

omit [DecidableEq X] [Fact (0 < n)] in
/--
The left component of the semidirect finite-stage projection is obtained by applying the
coefficient homomorphism stagewise while leaving the quotient support fixed.
-/
@[simp]
theorem freeProCZCCompletedFoxSemidirectStageMapOfCoeff_left
    (stageCoeff :
      ZCCompletedGroupAlgebra C H →+*
        foxAlgebraicStageTargetGroupAlgebra (X := X) N n)
    (stageRight : H →* foxAlgebraicStageTargetQuotient (X := X) N)
    (hgroupLike : ∀ h : H,
      stageCoeff (zcGroupLike C H h) =
        MonoidAlgebra.of (ModNCompletedCoeff n)
          (foxAlgebraicStageTargetQuotient (X := X) N) (stageRight h))
    (y : ZCCompletedFoxSemidirect C X H) :
    (freeProCZCCompletedFoxSemidirectStageMapOfCoeff
      (C := C) (X := X) (H := H) N n stageCoeff stageRight hgroupLike y).left =
      zcFreeFoxCoordinatesStageMap (C := C) (X := X) (H := H) N n stageCoeff y.left :=
  rfl

omit [DecidableEq X] [Fact (0 < n)] in
/--
The right component of the semidirect finite-stage projection is the chosen target quotient map,
independent of the coefficient projection.
-/
@[simp]
theorem freeProCZCCompletedFoxSemidirectStageMapOfCoeff_right
    (stageCoeff :
      ZCCompletedGroupAlgebra C H →+*
        foxAlgebraicStageTargetGroupAlgebra (X := X) N n)
    (stageRight : H →* foxAlgebraicStageTargetQuotient (X := X) N)
    (hgroupLike : ∀ h : H,
      stageCoeff (zcGroupLike C H h) =
        MonoidAlgebra.of (ModNCompletedCoeff n)
          (foxAlgebraicStageTargetQuotient (X := X) N) (stageRight h))
    (y : ZCCompletedFoxSemidirect C X H) :
    (freeProCZCCompletedFoxSemidirectStageMapOfCoeff
      (C := C) (X := X) (H := H) N n stageCoeff stageRight hgroupLike y).right =
      stageRight y.right :=
  rfl

omit [DecidableEq X] [Fact (0 < n)] in
/-- Boundary-cycle preservation for the semidirect map built from a coefficient projection. -/
theorem freeProCZCCompletedFoxSemidirectStageMapOfCoeff_mem_finiteBoundaryCycleSet
    [Fintype X]
    (φ : X → H)
    (stageCoeff :
      ZCCompletedGroupAlgebra C H →+*
        foxAlgebraicStageTargetGroupAlgebra (X := X) N n)
    (stageRight : H →* foxAlgebraicStageTargetQuotient (X := X) N)
    (hgroupLike : ∀ h : H,
      stageCoeff (zcGroupLike C H h) =
        MonoidAlgebra.of (ModNCompletedCoeff n)
          (foxAlgebraicStageTargetQuotient (X := X) N) (stageRight h))
    (hright_generators : ∀ i : X,
      stageRight (φ i) = QuotientGroup.mk' N (FreeGroup.of i))
    {y : ZCCompletedFoxSemidirect C X H}
    (hy : y ∈ freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ) :
    freeProCZCCompletedFoxSemidirectStageMapOfCoeff
        (C := C) (X := X) (H := H) N n stageCoeff stageRight hgroupLike y ∈
      foxAlgebraicStageSemidirectBoundaryCycleSet (X := X) N n := by
  exact
    freeProCZCCompletedFoxSemidirectStageMap_mem_finiteBoundaryCycleSet
      (C := C) (X := X) (H := H) N n φ
      (zcFreeFoxCoordinatesStageMap (C := C) (X := X) (H := H) N n stageCoeff)
      stageRight
      (zcFreeFoxCoordinatesStageMap_smul_groupLike
        (C := C) (X := X) (H := H) N n stageCoeff stageRight hgroupLike)
      stageCoeff.toAddMonoidHom
      (foxAlgebraicStageFoxBoundary_zcFreeFoxCoordinatesStageMap_of_groupLike
        (C := C) (X := X) (H := H) N n φ stageCoeff stageRight hgroupLike
        hright_generators)
      hy

omit [Fact (0 < n)] in
/-- Kernel-word preservation for the semidirect map built from a coefficient projection. -/
theorem freeProCZCCompletedFoxSemidirectStageMapOfCoeff_kernelWordPoint
    (φ : X → H)
    (stageCoeff :
      ZCCompletedGroupAlgebra C H →+*
        foxAlgebraicStageTargetGroupAlgebra (X := X) N n)
    (stageRight : H →* foxAlgebraicStageTargetQuotient (X := X) N)
    (hgroupLike : ∀ h : H,
      stageCoeff (zcGroupLike C H h) =
        MonoidAlgebra.of (ModNCompletedCoeff n)
          (foxAlgebraicStageTargetQuotient (X := X) N) (stageRight h))
    (hright_generators : ∀ i : X,
      stageRight (φ i) = QuotientGroup.mk' N (FreeGroup.of i))
    (w : FreeGroup X) :
    freeProCZCCompletedFoxSemidirectStageMapOfCoeff
        (C := C) (X := X) (H := H) N n stageCoeff stageRight hgroupLike
        (freeProCZCCompletedFoxSemidirectKernelWordPoint (C := C) φ w) =
      foxAlgebraicStageSemidirectKernelWordPoint (X := X) N n w := by
  exact
    freeProCZCCompletedFoxSemidirectStageMap_kernelWordPoint
      (C := C) (X := X) (H := H) N n φ
      (zcFreeFoxCoordinatesStageMap (C := C) (X := X) (H := H) N n stageCoeff)
      stageRight
      (zcFreeFoxCoordinatesStageMap_smul_groupLike
        (C := C) (X := X) (H := H) N n stageCoeff stageRight hgroupLike)
      (zcFreeFoxCoordinatesStageMap_derivativeVector_of_generators
        (C := C) (X := X) (H := H) N n φ stageCoeff stageRight hgroupLike
        hright_generators)
      w

end CoordinateStageMap

end

end FoxDifferential
