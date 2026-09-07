import ProCGroups.FoxDifferential.Completed.FiniteStage.BoundaryCycles

set_option autoImplicit false

/-!
# Fox differential: completed — finite stage — boundary cycle hom

The principal declarations in this module are:

- `foxAlgebraicStageSourceKernel`
  The kernel of the finite source-to-target quotient \(F/[N,N]N^n \to F/N\).
- `foxAlgebraicStageSourceKernelDerivativeAddHom`
  The descended finite-stage Fox derivative, restricted to the source quotient kernel, is an
  additive homomorphism.
- `foxAlgebraicStageSourceKernelDerivativeAddHom_of`
  The finite-stage boundary or derivative construction defines the corresponding additive
  homomorphism.
- `foxAlgebraicStageSourceKernelDerivativeAddHom_range_eq`
  The range of the additive source-kernel derivative map is exactly the source-kernel derivative
  additive subgroup already used in the finite-stage density target.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u

variable {X : Type u} [DecidableEq X]
variable (N : Subgroup (FreeGroup X)) [N.Normal] (n : ℕ)

/-- The kernel of the finite source-to-target quotient \(F/[N,N]N^n \to F/N\). -/
abbrev foxAlgebraicStageSourceKernel : Type u :=
  (foxCommutatorPowerQuotientMapToNormalQuotient
    (F := FreeGroup X) N n).ker

/--
The descended finite-stage Fox derivative, restricted to the source quotient kernel, is an
additive homomorphism.
-/
def foxAlgebraicStageSourceKernelDerivativeAddHom :
    Additive (foxAlgebraicStageSourceKernel (X := X) N n) →+
      foxAlgebraicStageCoordinateVector (X := X) N n where
  toFun q :=
    foxAlgebraicStageQuotientDerivativeVector (X := X) N n (Additive.toMul q).1
  map_zero' := by
    change foxAlgebraicStageQuotientDerivativeVector (X := X) N n
      (1 : FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) = 0
    exact ScalarCrossedHom.map_one
      (foxAlgebraicStageQuotientDerivativeVector (X := X) N n)
  map_add' := by
    intro q r
    change foxAlgebraicStageQuotientDerivativeVector (X := X) N n
        ((Additive.toMul q).1 * (Additive.toMul r).1) =
      foxAlgebraicStageQuotientDerivativeVector (X := X) N n (Additive.toMul q).1 +
        foxAlgebraicStageQuotientDerivativeVector (X := X) N n (Additive.toMul r).1
    rw [ScalarCrossedHom.map_mul
      (foxAlgebraicStageQuotientDerivativeVector (X := X) N n)]
    have hqcoeff :
        foxAlgebraicStageQuotientCoefficient (X := X) N n (Additive.toMul q).1 = 1 :=
      foxAlgebraicStageQuotientCoefficient_eq_one_of_kernel (X := X) N n
        (Additive.toMul q).2
    rw [hqcoeff]
    simp only [one_smul]

/--
The finite-stage boundary or derivative construction defines the corresponding additive
homomorphism.
-/
@[simp]
theorem foxAlgebraicStageSourceKernelDerivativeAddHom_of
    (q : foxAlgebraicStageSourceKernel (X := X) N n) :
    foxAlgebraicStageSourceKernelDerivativeAddHom (X := X) N n (Additive.ofMul q) =
      foxAlgebraicStageQuotientDerivativeVector (X := X) N n q.1 :=
  rfl

/--
The range of the additive source-kernel derivative map is exactly the source-kernel derivative
additive subgroup already used in the finite-stage density target.
-/
theorem foxAlgebraicStageSourceKernelDerivativeAddHom_range_eq :
    AddMonoidHom.range (foxAlgebraicStageSourceKernelDerivativeAddHom (X := X) N n) =
      foxAlgebraicStageSourceKernelDerivativeAddSubgroup (X := X) N n := by
  ext v
  constructor
  · intro hv
    rcases hv with ⟨q, rfl⟩
    refine ⟨(Additive.toMul q).1, (Additive.toMul q).2, rfl⟩
  · intro hv
    rcases hv with ⟨q, hq, rfl⟩
    exact ⟨Additive.ofMul
      (⟨q, hq⟩ : foxAlgebraicStageSourceKernel (X := X) N n), rfl⟩

/-- The source-kernel derivative map, with codomain restricted to finite Fox boundary cycles. -/
def foxAlgebraicStageSourceKernelDerivativeToBoundaryCycles [Fintype X] :
    Additive (foxAlgebraicStageSourceKernel (X := X) N n) →+
      foxAlgebraicStageBoundaryCycleSubmodule (X := X) N n where
  toFun q :=
    ⟨foxAlgebraicStageQuotientDerivativeVector (X := X) N n (Additive.toMul q).1,
      foxAlgebraicStageSourceKernelDerivativeSet_subset_boundaryCycleSubmodule (X := X) N n
        ⟨(Additive.toMul q).1, (Additive.toMul q).2, rfl⟩⟩
  map_zero' := by
    apply Subtype.ext
    change foxAlgebraicStageQuotientDerivativeVector (X := X) N n
      (1 : FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) = 0
    exact ScalarCrossedHom.map_one
      (foxAlgebraicStageQuotientDerivativeVector (X := X) N n)
  map_add' := by
    intro q r
    apply Subtype.ext
    change foxAlgebraicStageQuotientDerivativeVector (X := X) N n
        ((Additive.toMul q).1 * (Additive.toMul r).1) =
      foxAlgebraicStageQuotientDerivativeVector (X := X) N n (Additive.toMul q).1 +
        foxAlgebraicStageQuotientDerivativeVector (X := X) N n (Additive.toMul r).1
    rw [ScalarCrossedHom.map_mul
      (foxAlgebraicStageQuotientDerivativeVector (X := X) N n)]
    have hqcoeff :
        foxAlgebraicStageQuotientCoefficient (X := X) N n (Additive.toMul q).1 = 1 :=
      foxAlgebraicStageQuotientCoefficient_eq_one_of_kernel (X := X) N n
        (Additive.toMul q).2
    rw [hqcoeff]
    simp only [one_smul]

/--
The map from the finite source kernel to boundary cycles has coordinates given by the
finite-stage quotient derivative vector.
-/
@[simp]
theorem foxAlgebraicStageSourceKernelDerivativeToBoundaryCycles_val
    [Fintype X] (q : foxAlgebraicStageSourceKernel (X := X) N n) :
    (foxAlgebraicStageSourceKernelDerivativeToBoundaryCycles (X := X) N n
      (Additive.ofMul q) : foxAlgebraicStageCoordinateVector (X := X) N n) =
      foxAlgebraicStageQuotientDerivativeVector (X := X) N n q.1 :=
  rfl

/--
The finite-stage coverage statement is precisely surjectivity of the source-kernel derivative
map onto the boundary-cycle subgroup.
-/
theorem foxAlgebraicStageBoundaryCyclesCovered_iff_surj_derivativeToBoundaryCycles
    {N : Subgroup (FreeGroup X)} [N.Normal] {n : ℕ} [Fintype X] :
    foxAlgebraicStageBoundaryCyclesCoveredBySourceKernel (X := X) N n ↔
      Function.Surjective
        (foxAlgebraicStageSourceKernelDerivativeToBoundaryCycles (X := X) N n) := by
  constructor
  · intro hcover y
    rcases hcover y.2 with ⟨q, hq, hqy⟩
    refine ⟨Additive.ofMul
      (⟨q, hq⟩ : foxAlgebraicStageSourceKernel (X := X) N n), ?_⟩
    apply Subtype.ext
    simpa using hqy
  · intro hsurj v hv
    rcases hsurj ⟨v, hv⟩ with ⟨q, hq⟩
    refine ⟨(Additive.toMul q).1, (Additive.toMul q).2, ?_⟩
    exact congrArg Subtype.val hq

/--
If the restricted source-kernel derivative map is surjective, then the source-kernel image is
all of the finite boundary-cycle subgroup.
-/
theorem foxAlgebraicStageSourceKernelDerivativeSet_eq_boundaryCycleSubmodule_of_surjective
    [Fintype X]
    (hsurj : Function.Surjective
      (foxAlgebraicStageSourceKernelDerivativeToBoundaryCycles (X := X) N n)) :
    foxAlgebraicStageSourceKernelDerivativeSet (X := X) N n =
      (foxAlgebraicStageBoundaryCycleSubmodule (X := X) N n :
        Set (foxAlgebraicStageCoordinateVector (X := X) N n)) := by
  exact
    (foxAlgebraicStageSourceKernelDerivativeSet_eq_boundaryCycleSubmodule_iff
      (X := X) (N := N) (n := n)).2
      ((foxAlgebraicStageBoundaryCyclesCovered_iff_surj_derivativeToBoundaryCycles
        (X := X) (N := N) (n := n)).2 hsurj)

end

end FoxDifferential
