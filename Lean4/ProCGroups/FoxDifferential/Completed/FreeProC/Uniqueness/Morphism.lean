import ProCGroups.FoxDifferential.Completed.FreeProC.SemidirectLift

set_option autoImplicit false

/-!
# Fox differential: completed — free pro-\(C\) — uniqueness — morphism

The principal declarations in this module are:

- `freeProCZCCompletedFoxSemidirectLiftMorphism_unique`
  Categorical completed Fox semidirect morphisms from a free pro-\(C\) source are unique once their
  generator values are prescribed.
- `freeProCZCCompletedFoxSemidirectLiftMorphism_unique_of_components`
  Componentwise uniqueness for categorical completed Fox semidirect morphisms from a free pro-\(C\)
  source.
- `existsUnique_freeProCZCCompletedFoxSemidirectLiftMorphism`
  Existence and uniqueness of the categorical completed Fox semidirect morphism from a free
  pro-\(C\) source.
- `existsUnique_freeProCZCCompletedFoxSemidirectLiftMorphism_components`
  Componentwise existence and uniqueness of the categorical completed Fox semidirect morphism from a
  free pro-\(C\) source.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.FreeProC

universe u

variable {C : ProCGroups.FiniteGroupClass.{u}}
variable {X F H : Type u}
variable [TopologicalSpace X]
variable [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
variable [DecidableEq X]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable [TopologicalSpace (ZCCompletedFoxSemidirect C X H)]
variable [IsTopologicalGroup (ZCCompletedFoxSemidirect C X H)]
variable [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
variable [CompactSpace (ZCCompletedFoxSemidirect C X H)]
variable [T2Space (ZCCompletedFoxSemidirect C X H)]
variable [TotallyDisconnectedSpace
  (ZCCompletedFoxSemidirect C X H)]

/--
Categorical completed Fox semidirect morphisms from a free pro-\(C\) source are unique once
their generator values are prescribed.
-/
theorem freeProCZCCompletedFoxSemidirectLiftMorphism_unique
    (hFC : ProCGroups.ProC.HasOpenNormalBasisInClass C (F))
    (hTargetC : ProCGroups.ProC.HasOpenNormalBasisInClass C
      (ZCCompletedFoxSemidirect C X H))
    {ι : X → F} (hι : IsFreeProCGroup (C := C) ι)
    (φ : X → H)
    (hφ : Continuous (freeProCZCCompletedFoxSemidirectGenerator (C := C) φ))
    (f :
      ProCGrp.of C (ProfiniteGrp.of F) hFC ⟶
        ProCGrp.of C
          (ProfiniteGrp.of
            (ZCCompletedFoxSemidirect C X H))
          hTargetC)
    (hgenerator :
      ∀ x : X, f (ι x) = freeProCZCCompletedFoxSemidirectGenerator (C := C) φ x) :
    f = freeProCZCCompletedFoxSemidirectLiftMorphism
      (C := C) hFC hTargetC hι φ hφ := by
  apply ProCGrp.hom_ext
  apply ContinuousMonoidHom.toMonoidHom_injective
  exact congrArg
    (fun h : F →ₜ* ZCCompletedFoxSemidirect C X H => h.toMonoidHom)
    (hι.liftHom_unique
      hTargetC
      (freeProCZCCompletedFoxSemidirectGenerator (C := C) φ) hφ
      (f := ProCGrp.continuousHom f) hgenerator)

/--
Componentwise uniqueness for categorical completed Fox semidirect morphisms from a free
pro-\(C\) source.
-/
theorem freeProCZCCompletedFoxSemidirectLiftMorphism_unique_of_components
    (hFC : ProCGroups.ProC.HasOpenNormalBasisInClass C (F))
    (hTargetC : ProCGroups.ProC.HasOpenNormalBasisInClass C
      (ZCCompletedFoxSemidirect C X H))
    {ι : X → F} (hι : IsFreeProCGroup (C := C) ι)
    (φ : X → H)
    (hφ : Continuous (freeProCZCCompletedFoxSemidirectGenerator (C := C) φ))
    (f :
      ProCGrp.of C (ProfiniteGrp.of F) hFC ⟶
        ProCGrp.of C
          (ProfiniteGrp.of
            (ZCCompletedFoxSemidirect C X H))
          hTargetC)
    (hleft :
      ∀ x : X, (f (ι x)).left =
        Pi.single x (1 : ZCCompletedGroupAlgebra C H))
    (hright : ∀ x : X, (f (ι x)).right = φ x) :
    f = freeProCZCCompletedFoxSemidirectLiftMorphism
      (C := C) hFC hTargetC hι φ hφ := by
  apply freeProCZCCompletedFoxSemidirectLiftMorphism_unique
    (C := C) hFC hTargetC hι φ hφ f
  intro x
  apply ZCCompletedFoxSemidirect.ext
  · exact hleft x
  · exact hright x

/--
Existence and uniqueness of the categorical completed Fox semidirect morphism from a free
pro-\(C\) source.
-/
theorem existsUnique_freeProCZCCompletedFoxSemidirectLiftMorphism
    (hFC : ProCGroups.ProC.HasOpenNormalBasisInClass C (F))
    (hTargetC : ProCGroups.ProC.HasOpenNormalBasisInClass C
      (ZCCompletedFoxSemidirect C X H))
    {ι : X → F} (hι : IsFreeProCGroup (C := C) ι)
    (φ : X → H)
    (hφ : Continuous (freeProCZCCompletedFoxSemidirectGenerator (C := C) φ)) :
    ∃! f :
      ProCGrp.of C (ProfiniteGrp.of F) hFC ⟶
        ProCGrp.of C
          (ProfiniteGrp.of
            (ZCCompletedFoxSemidirect C X H))
          hTargetC,
      ∀ x : X, f (ι x) = freeProCZCCompletedFoxSemidirectGenerator (C := C) φ x := by
  refine ⟨freeProCZCCompletedFoxSemidirectLiftMorphism
      (C := C) hFC hTargetC hι φ hφ, ?_, ?_⟩
  · exact freeProCZCCompletedFoxSemidirectLiftMorphism_generator
      (C := C) hFC hTargetC hι φ hφ
  · intro f hf
    exact freeProCZCCompletedFoxSemidirectLiftMorphism_unique
      (C := C) hFC hTargetC hι φ hφ f hf

/--
Componentwise existence and uniqueness of the categorical completed Fox semidirect morphism from
a free pro-\(C\) source.
-/
theorem existsUnique_freeProCZCCompletedFoxSemidirectLiftMorphism_components
    (hFC : ProCGroups.ProC.HasOpenNormalBasisInClass C (F))
    (hTargetC : ProCGroups.ProC.HasOpenNormalBasisInClass C
      (ZCCompletedFoxSemidirect C X H))
    {ι : X → F} (hι : IsFreeProCGroup (C := C) ι)
    (φ : X → H)
    (hφ : Continuous (freeProCZCCompletedFoxSemidirectGenerator (C := C) φ)) :
    ∃! f :
      ProCGrp.of C (ProfiniteGrp.of F) hFC ⟶
        ProCGrp.of C
          (ProfiniteGrp.of
            (ZCCompletedFoxSemidirect C X H))
          hTargetC,
      (∀ x : X, (f (ι x)).left =
        Pi.single x (1 : ZCCompletedGroupAlgebra C H)) ∧
      ∀ x : X, (f (ι x)).right = φ x := by
  refine ⟨freeProCZCCompletedFoxSemidirectLiftMorphism
      (C := C) hFC hTargetC hι φ hφ, ?_, ?_⟩
  · exact
      ⟨freeProCZCCompletedFoxSemidirectLiftMorphism_left_generator
          (C := C) hFC hTargetC hι φ hφ,
        freeProCZCCompletedFoxSemidirectLiftMorphism_right_generator
          (C := C) hFC hTargetC hι φ hφ⟩
  · intro f hf
    exact freeProCZCCompletedFoxSemidirectLiftMorphism_unique_of_components
      (C := C) hFC hTargetC hι φ hφ f hf.1 hf.2

end

end FoxDifferential
