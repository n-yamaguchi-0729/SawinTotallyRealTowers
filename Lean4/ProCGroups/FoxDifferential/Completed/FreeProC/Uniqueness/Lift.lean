import ProCGroups.FoxDifferential.Completed.FreeProC.Uniqueness.SemidirectHom

set_option autoImplicit false

/-!
# Fox differential: completed — free pro-\(C\) — uniqueness — lift

The principal declarations in this module are:

- `freeProCZCCompletedFoxSemidirectLift_unique`
  Continuous completed Fox semidirect lifts from a free pro-\(C\) source are unique once their
  generator values are prescribed.
- `freeProCZCCompletedFoxSemidirectLift_unique_of_components`
  Componentwise uniqueness for continuous completed Fox semidirect lifts from a free pro-\(C\)
  source.
- `freeProCZCCompletedFoxSemidirectLiftHom_unique`
  Continuous completed Fox semidirect homomorphisms from a free pro-\(C\) source are unique once
  their generator values are prescribed.
- `freeProCZCCompletedFoxSemidirectLiftHom_unique_of_components`
  Componentwise uniqueness for continuous completed Fox semidirect homomorphisms from a free
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
Continuous completed Fox semidirect lifts from a free pro-\(C\) source are unique once their
generator values are prescribed.
-/
theorem freeProCZCCompletedFoxSemidirectLift_unique
    {ι : X → F} (hι : IsFreeProCGroup (C := C) ι)
    (htarget : ProCGroups.ProC.HasOpenNormalBasisInClass C (ZCCompletedFoxSemidirect C X H))
    (φ : X → H)
    (hφ : Continuous (freeProCZCCompletedFoxSemidirectGenerator (C := C) φ))
    (f : F →* ZCCompletedFoxSemidirect C X H)
    (hf : Continuous f)
    (hgenerator :
      ∀ x : X, f (ι x) = freeProCZCCompletedFoxSemidirectGenerator (C := C) φ x) :
    f = freeProCZCCompletedFoxSemidirectLift
        (C := C) hι htarget φ hφ :=
  hι.lift_unique htarget (freeProCZCCompletedFoxSemidirectGenerator (C := C) φ)
    hφ hf hgenerator

/--
Componentwise uniqueness for continuous completed Fox semidirect lifts from a free pro-\(C\)
source.
-/
theorem freeProCZCCompletedFoxSemidirectLift_unique_of_components
    {ι : X → F} (hι : IsFreeProCGroup (C := C) ι)
    (htarget : ProCGroups.ProC.HasOpenNormalBasisInClass C (ZCCompletedFoxSemidirect C X H))
    (φ : X → H)
    (hφ : Continuous (freeProCZCCompletedFoxSemidirectGenerator (C := C) φ))
    (f : F →* ZCCompletedFoxSemidirect C X H)
    (hf : Continuous f)
    (hleft :
      ∀ x : X, (f (ι x)).left =
        Pi.single x (1 : ZCCompletedGroupAlgebra C H))
    (hright : ∀ x : X, (f (ι x)).right = φ x) :
    f = freeProCZCCompletedFoxSemidirectLift
        (C := C) hι htarget φ hφ := by
  apply freeProCZCCompletedFoxSemidirectLift_unique
    (C := C) hι htarget φ hφ f hf
  intro x
  apply ZCCompletedFoxSemidirect.ext
  · exact hleft x
  · exact hright x

/--
Continuous completed Fox semidirect homomorphisms from a free pro-\(C\) source are unique once
their generator values are prescribed.
-/
theorem freeProCZCCompletedFoxSemidirectLiftHom_unique
    {ι : X → F} (hι : IsFreeProCGroup (C := C) ι)
    (htarget : ProCGroups.ProC.HasOpenNormalBasisInClass C (ZCCompletedFoxSemidirect C X H))
    (φ : X → H)
    (hφ : Continuous (freeProCZCCompletedFoxSemidirectGenerator (C := C) φ))
    (f : F →ₜ* ZCCompletedFoxSemidirect C X H)
    (hgenerator :
      ∀ x : X, f (ι x) = freeProCZCCompletedFoxSemidirectGenerator (C := C) φ x) :
    f = freeProCZCCompletedFoxSemidirectLiftHom
        (C := C) hι htarget φ hφ :=
  hι.liftHom_unique htarget (freeProCZCCompletedFoxSemidirectGenerator (C := C) φ)
    hφ hgenerator

/--
Componentwise uniqueness for continuous completed Fox semidirect homomorphisms from a free
pro-\(C\) source.
-/
theorem freeProCZCCompletedFoxSemidirectLiftHom_unique_of_components
    {ι : X → F} (hι : IsFreeProCGroup (C := C) ι)
    (htarget : ProCGroups.ProC.HasOpenNormalBasisInClass C (ZCCompletedFoxSemidirect C X H))
    (φ : X → H)
    (hφ : Continuous (freeProCZCCompletedFoxSemidirectGenerator (C := C) φ))
    (f : F →ₜ* ZCCompletedFoxSemidirect C X H)
    (hleft :
      ∀ x : X, (f (ι x)).left =
        Pi.single x (1 : ZCCompletedGroupAlgebra C H))
    (hright : ∀ x : X, (f (ι x)).right = φ x) :
    f = freeProCZCCompletedFoxSemidirectLiftHom
        (C := C) hι htarget φ hφ := by
  apply freeProCZCCompletedFoxSemidirectLiftHom_unique
    (C := C) hι htarget φ hφ f
  intro x
  apply ZCCompletedFoxSemidirect.ext
  · exact hleft x
  · exact hright x

/--
Existence and uniqueness of the continuous completed Fox semidirect homomorphism from a free
pro-\(C\) source.
-/
theorem existsUnique_freeProCZCCompletedFoxSemidirectLiftHom
    {ι : X → F} (hι : IsFreeProCGroup (C := C) ι)
    (htarget : ProCGroups.ProC.HasOpenNormalBasisInClass C (ZCCompletedFoxSemidirect C X H))
    (φ : X → H)
    (hφ : Continuous (freeProCZCCompletedFoxSemidirectGenerator (C := C) φ)) :
    ∃! f : F →ₜ* ZCCompletedFoxSemidirect C X H,
      ∀ x : X, f (ι x) = freeProCZCCompletedFoxSemidirectGenerator (C := C) φ x := by
  refine ⟨freeProCZCCompletedFoxSemidirectLiftHom
        (C := C) hι htarget φ hφ, ?_, ?_⟩
  · exact freeProCZCCompletedFoxSemidirectLiftHom_generator
      (C := C) hι htarget φ hφ
  · intro f hf
    exact freeProCZCCompletedFoxSemidirectLiftHom_unique
      (C := C) hι htarget φ hφ f hf

/--
Componentwise existence and uniqueness of the continuous completed Fox semidirect homomorphism
from a free pro-\(C\) source.
-/
theorem existsUnique_freeProCZCCompletedFoxSemidirectLiftHom_components
    {ι : X → F} (hι : IsFreeProCGroup (C := C) ι)
    (htarget : ProCGroups.ProC.HasOpenNormalBasisInClass C (ZCCompletedFoxSemidirect C X H))
    (φ : X → H)
    (hφ : Continuous (freeProCZCCompletedFoxSemidirectGenerator (C := C) φ)) :
    ∃! f : F →ₜ* ZCCompletedFoxSemidirect C X H,
      (∀ x : X, (f (ι x)).left =
        Pi.single x (1 : ZCCompletedGroupAlgebra C H)) ∧
      ∀ x : X, (f (ι x)).right = φ x := by
  refine ⟨freeProCZCCompletedFoxSemidirectLiftHom
        (C := C) hι htarget φ hφ, ?_, ?_⟩
  · exact ⟨
      freeProCZCCompletedFoxSemidirectLiftHom_left_generator
        (C := C) hι htarget φ hφ,
      freeProCZCCompletedFoxSemidirectLiftHom_right_generator
        (C := C) hι htarget φ hφ⟩
  · intro f hf
    exact freeProCZCCompletedFoxSemidirectLiftHom_unique_of_components
      (C := C) hι htarget φ hφ f hf.1 hf.2

end ProfiniteTarget

end

end FoxDifferential
