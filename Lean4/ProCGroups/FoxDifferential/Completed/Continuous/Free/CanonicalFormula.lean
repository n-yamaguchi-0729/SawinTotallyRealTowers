import ProCGroups.FoxDifferential.Completed.Continuous.Free.SourceFormula

set_option autoImplicit false

/-!
# Fox differential: completed — continuous — free — canonical formula

The principal declarations in this module are:

- `freeProCZCCompletedFoxDerivativeVector_boundary`
  Boundary-map form of the source-shaped completed Fox formula for the canonical free pro-\(C\)
  semidirect lift.
- `freeProCZCCompletedFoxDerivative_fundamental_formula`
  Source-shaped completed Fox fundamental formula for the canonical free pro-\(C\) semidirect lift.
- `freeProCZCCompletedFoxDerivative_euler_formula`
  Explicit \([\rho g] - 1\) form of the source-shaped completed Fox-Euler formula for the canonical
  free pro-\(C\) semidirect lift.
-/

namespace FoxDifferential

noncomputable section

open scoped BigOperators

universe u


variable {C : ProCGroups.FiniteGroupClass.{u}}
variable (X H : Type u) [DecidableEq X]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]


variable {F : Type u}
variable [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
variable [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
variable [TopologicalSpace X]

variable [DiscreteTopology X]

section CanonicalSourceFormula

variable [Fintype X]
variable [CompactSpace (ZCCompletedFoxSemidirect C X H)]
variable [T2Space (ZCCompletedFoxSemidirect C X H)]
variable [TotallyDisconnectedSpace (ZCCompletedFoxSemidirect C X H)]
variable [CompactSpace (ZCCompletedFoxSemidirect C PUnit.{u + 1} H)]
variable [T2Space (ZCCompletedFoxSemidirect C PUnit.{u + 1} H)]
variable [TotallyDisconnectedSpace (ZCCompletedFoxSemidirect C PUnit.{u + 1} H)]

/--
Boundary-map form of the source-shaped completed Fox formula for the canonical free pro-\(C\)
semidirect lift.
-/
theorem freeProCZCCompletedFoxDerivativeVector_boundary
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup (C := C) ι)
    (htarget :
    ProCGroups.ProC.HasOpenNormalBasisInClass C (ZCCompletedFoxSemidirect C X H))
    (htargetUnit :
    ProCGroups.ProC.HasOpenNormalBasisInClass C (ZCCompletedFoxSemidirect C PUnit H))
    (φ : X → H) (g : F) :
    freeProCZCCompletedFoxBoundary C φ
        (freeProCZCCompletedFoxDerivativeVector
          (C := C) hι htarget φ
          (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C := C) X H φ) g) =
      zcCompletedGroupAlgebraBoundary C
        (freeProCZCCompletedFoxRightHom
          (C := C) hι htarget φ
          (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C := C) X H φ)) g := by
  let hφ : Continuous (freeProCZCCompletedFoxSemidirectGenerator (C := C) φ) :=
    continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C := C) X H φ
  simpa [freeProCZCCompletedFoxBoundary] using
    freeProCZCCompletedFoxBoundary_of_continuousCrossedDifferential
      (C := C) X H hι htargetUnit
      (freeProCZCCompletedFoxRightHom
        (C := C) hι htarget φ hφ)
      (freeProCZCCompletedFoxDerivativeVector
        (C := C) hι htarget φ hφ)
      (continuous_freeProCZCCompletedFoxDerivativeVector
        (C := C) X H hι htarget φ hφ)
      (continuous_freeProCZCCompletedFoxRightHom
        (C := C) X H hι htarget φ hφ)
      (freeProCZCCompletedFoxDerivativeVector_generator
        (C := C) hι htarget φ hφ)
      g

/--
Source-shaped completed Fox fundamental formula for the canonical free pro-\(C\) semidirect
lift.
-/
theorem freeProCZCCompletedFoxDerivative_fundamental_formula
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup (C := C) ι)
    (htarget :
    ProCGroups.ProC.HasOpenNormalBasisInClass C (ZCCompletedFoxSemidirect C X H))
    (htargetUnit :
    ProCGroups.ProC.HasOpenNormalBasisInClass C (ZCCompletedFoxSemidirect C PUnit H))
    (φ : X → H) (g : F) :
    zcCompletedGroupAlgebraBoundary C
        (freeProCZCCompletedFoxRightHom
          (C := C) hι htarget φ
          (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C := C) X H φ)) g =
      ∑ x : X,
        freeProCZCCompletedFoxDerivativeVector
            (C := C) hι htarget φ
            (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C := C) X H φ) g x *
          (zcGroupLike C H (φ x) - 1) := by
  simpa [freeProCZCCompletedFoxBoundary_apply] using
    (freeProCZCCompletedFoxDerivativeVector_boundary
      (C := C) X H hι htarget htargetUnit φ g).symm

/--
Explicit \([\rho g] - 1\) form of the source-shaped completed Fox-Euler formula for the
canonical free pro-\(C\) semidirect lift.
-/
theorem freeProCZCCompletedFoxDerivative_euler_formula
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup (C := C) ι)
    (htarget :
    ProCGroups.ProC.HasOpenNormalBasisInClass C (ZCCompletedFoxSemidirect C X H))
    (htargetUnit :
    ProCGroups.ProC.HasOpenNormalBasisInClass C (ZCCompletedFoxSemidirect C PUnit H))
    (φ : X → H) (g : F) :
    zcGroupLike C H
        (freeProCZCCompletedFoxRightHom
          (C := C) hι htarget φ
          (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C := C) X H φ) g) - 1 =
      ∑ x : X,
        freeProCZCCompletedFoxDerivativeVector
            (C := C) hι htarget φ
            (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C := C) X H φ) g x *
          (zcGroupLike C H (φ x) - 1) := by
  convert
    freeProCZCCompletedFoxDerivative_fundamental_formula
      (C := C) X H hι htarget htargetUnit φ g
      using 1
  rfl

end CanonicalSourceFormula



end

end FoxDifferential
