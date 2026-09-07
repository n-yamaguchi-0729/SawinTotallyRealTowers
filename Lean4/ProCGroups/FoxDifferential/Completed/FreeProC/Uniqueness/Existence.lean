import ProCGroups.FoxDifferential.Completed.FreeProC.Uniqueness.Lift
import ProCGroups.FoxDifferential.Completed.FreeProC.Uniqueness.Morphism

set_option autoImplicit false

/-!
# Fox differential: completed — free pro-\(C\) — uniqueness — existence

The principal declarations in this module are:

- `existsUnique_freeProCZCCompletedFoxSemidirectLift`
  Existence and uniqueness of the continuous completed Fox semidirect lift from a free pro-\(C\)
  source.
- `existsUnique_freeProCZCCompletedFoxSemidirectLift_components`
  Componentwise existence and uniqueness of the continuous completed Fox semidirect lift from a free
  pro-\(C\) source.
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

section ProfiniteTarget

variable [CompactSpace (ZCCompletedFoxSemidirect C X H)]
variable [T2Space (ZCCompletedFoxSemidirect C X H)]
variable [TotallyDisconnectedSpace (ZCCompletedFoxSemidirect C X H)]

/--
Existence and uniqueness of the continuous completed Fox semidirect lift from a free pro-\(C\)
source.
-/
theorem existsUnique_freeProCZCCompletedFoxSemidirectLift
    {ι : X → F} (hι : IsFreeProCGroup (C := C) ι)
    (htarget : ProCGroups.ProC.HasOpenNormalBasisInClass C (ZCCompletedFoxSemidirect C X H))
    (φ : X → H)
    (hφ : Continuous (freeProCZCCompletedFoxSemidirectGenerator (C := C) φ)) :
    ∃! f : F →* ZCCompletedFoxSemidirect C X H,
      Continuous f ∧
        ∀ x : X, f (ι x) = freeProCZCCompletedFoxSemidirectGenerator (C := C) φ x :=
  hι.existsUnique_lift htarget (freeProCZCCompletedFoxSemidirectGenerator (C := C) φ) hφ

/--
Componentwise existence and uniqueness of the continuous completed Fox semidirect lift from a
free pro-\(C\) source.
-/
theorem existsUnique_freeProCZCCompletedFoxSemidirectLift_components
    {ι : X → F} (hι : IsFreeProCGroup (C := C) ι)
    (htarget : ProCGroups.ProC.HasOpenNormalBasisInClass C (ZCCompletedFoxSemidirect C X H))
    (φ : X → H)
    (hφ : Continuous (freeProCZCCompletedFoxSemidirectGenerator (C := C) φ)) :
    ∃! f : F →* ZCCompletedFoxSemidirect C X H,
      Continuous f ∧
        (∀ x : X, (f (ι x)).left =
          Pi.single x (1 : ZCCompletedGroupAlgebra C H)) ∧
        ∀ x : X, (f (ι x)).right = φ x := by
  refine ⟨freeProCZCCompletedFoxSemidirectLift
        (C := C) hι htarget φ hφ, ?_, ?_⟩
  · exact ⟨
      continuous_freeProCZCCompletedFoxSemidirectLift
        (C := C) hι htarget φ hφ,
      freeProCZCCompletedFoxSemidirectLift_left_generator
        (C := C) hι htarget φ hφ,
      freeProCZCCompletedFoxSemidirectLift_right_generator
        (C := C) hι htarget φ hφ⟩
  · intro f hf
    exact freeProCZCCompletedFoxSemidirectLift_unique_of_components
      (C := C) hι htarget φ hφ f hf.1 hf.2.1 hf.2.2

end ProfiniteTarget

end

end FoxDifferential
