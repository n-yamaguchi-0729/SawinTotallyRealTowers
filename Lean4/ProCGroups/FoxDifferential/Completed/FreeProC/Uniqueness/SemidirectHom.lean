import ProCGroups.FoxDifferential.Completed.FreeProC.SemidirectLift

set_option autoImplicit false

/-!
# Fox differential: completed — free pro-\(C\) — uniqueness — semidirect hom

The principal declarations in this module are:

- `freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential`
  A completed crossed differential and its coefficient homomorphism combine into a semidirect
  homomorphism.
- `freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential_left`
  The semidirect homomorphism attached to a crossed differential has \(\delta\) as its left
  component.
- `freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential_right`
  The semidirect homomorphism attached to a crossed differential has \(\psi\)s its right component.
- `continuous_freeProCZCCompletedFoxSemidirectGenerator_of_crossedDifferential`
  If a crossed-differential semidirect homomorphism is continuous and has the standard generator
  coordinates, then the corresponding semidirect generator map is continuous.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.FreeProC

universe u


variable {C : ProCGroups.FiniteGroupClass.{u}}
variable {X F H : Type u}
variable [TopologicalSpace X]
variable [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
variable [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
variable [DecidableEq X]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable [TopologicalSpace (ZCCompletedFoxSemidirect C X H)]
variable [IsTopologicalGroup (ZCCompletedFoxSemidirect C X H)]

/--
A completed crossed differential and its coefficient homomorphism combine into a semidirect
homomorphism.
-/
def freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential
    (ψ : F →* H)
    (delta : ScalarCrossedHom (zcCompletedGroupAlgebraScalar C ψ)
      (ZCFreeFoxCoordinates C (X := X) (H := H))) :
    F →* ZCCompletedFoxSemidirect C X H where
  toFun g := { left := delta g, right := ψ g }
  map_one' := by
    apply ZCCompletedFoxSemidirect.ext
    · exact delta.map_one
    · simp only [map_one, ZCCompletedFoxSemidirect.one_right]
  map_mul' g h := by
    apply ZCCompletedFoxSemidirect.ext
    · exact delta.map_mul g h
    · simp only [map_mul, ZCCompletedFoxSemidirect.mul_right]

omit [TopologicalSpace X] [TopologicalSpace F] [IsTopologicalGroup F] [DecidableEq X]
  [TopologicalSpace (ZCCompletedFoxSemidirect C X H)]
  [IsTopologicalGroup (ZCCompletedFoxSemidirect C X H)] in
/--
The semidirect homomorphism attached to a crossed differential has \(\delta\) as its left
component.
-/
@[simp]
theorem freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential_left
    (ψ : F →* H)
    (delta : ScalarCrossedHom (zcCompletedGroupAlgebraScalar C ψ)
      (ZCFreeFoxCoordinates C (X := X) (H := H)))
    (g : F) :
    (freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential
      (X := X) ψ delta g).left = delta g :=
  rfl

omit [TopologicalSpace X] [TopologicalSpace F] [IsTopologicalGroup F] [DecidableEq X]
  [TopologicalSpace (ZCCompletedFoxSemidirect C X H)]
  [IsTopologicalGroup (ZCCompletedFoxSemidirect C X H)] in
/--
The semidirect homomorphism attached to a crossed differential has \(\psi\)s its right
component.
-/
@[simp]
theorem freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential_right
    (ψ : F →* H)
    (delta : ScalarCrossedHom (zcCompletedGroupAlgebraScalar C ψ)
      (ZCFreeFoxCoordinates C (X := X) (H := H)))
    (g : F) :
    (freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential
      (X := X) ψ delta g).right = ψ g :=
  rfl

omit [IsTopologicalGroup (ZCCompletedFoxSemidirect C X H)] in
/--
If a crossed-differential semidirect homomorphism is continuous and has the standard generator
coordinates, then the corresponding semidirect generator map is continuous.
-/
theorem continuous_freeProCZCCompletedFoxSemidirectGenerator_of_crossedDifferential
    {ι : X → F} (hι : IsFreeProCGroup (C := C) ι)
    (ψ : F →* H)
    (delta : ScalarCrossedHom (zcCompletedGroupAlgebraScalar C ψ)
      (ZCFreeFoxCoordinates C (X := X) (H := H)))
    (hcontinuous :
      Continuous (freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential
        (X := X) ψ delta))
    (hbasis :
      ∀ x : X, delta (ι x) = Pi.single x (1 : ZCCompletedGroupAlgebra C H)) :
    Continuous (freeProCZCCompletedFoxSemidirectGenerator (C := C) (fun x : X => ψ (ι x))) := by
  have hgenerator :
      (fun x : X =>
        freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential
          (X := X) ψ delta (ι x)) =
        freeProCZCCompletedFoxSemidirectGenerator (C := C) (fun x : X => ψ (ι x)) := by
    funext x
    apply ZCCompletedFoxSemidirect.ext
    · exact hbasis x
    · rfl
  rw [← hgenerator]
  exact hcontinuous.comp hι.continuous_ι


end

end FoxDifferential
