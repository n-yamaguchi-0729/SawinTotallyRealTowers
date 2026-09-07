import ProCGroups.FoxDifferential.Completed.Continuous.Free.CanonicalFormula
import ProCGroups.FoxDifferential.Completed.FreeProC.Uniqueness.Existence

set_option autoImplicit false

/-!
# Fox differential: completed — continuous — free — discrete generators

The principal declarations in this module are:

- `existsUnique_freeProCZCCompletedFoxSemidirectLiftHom_of_discreteGenerators`
  Continuous completed Fox semidirect homomorphisms from a free pro-\(C\) source are unique for
  discrete generators, without a separate generator-continuity hypothesis.
- `existsUnique_freeProCZCFoxSemiLiftHom_components_of_discreteGenerators`
  Componentwise continuous completed Fox semidirect homomorphisms from a free pro-\(C\) source are
  unique for discrete generators, without a separate generator-continuity hypothesis.
- `existsUnique_freeProCZCCompletedFoxSemidirectLift_of_discreteGenerators`
  Continuous completed Fox semidirect lifts from a free pro-\(C\) source are unique for discrete
  generators, without a separate generator-continuity hypothesis.
- `existsUnique_freeProCZCFoxSemiLift_components_of_discreteGenerators`
  Componentwise continuous completed Fox semidirect lifts from a free pro-\(C\) source are unique
  for discrete generators, without a separate generator-continuity hypothesis.
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

section ProfiniteTarget

variable [CompactSpace (ZCCompletedFoxSemidirect C X H)]
variable [T2Space (ZCCompletedFoxSemidirect C X H)]
variable [TotallyDisconnectedSpace (ZCCompletedFoxSemidirect C X H)]

/--
Continuous completed Fox semidirect homomorphisms from a free pro-\(C\) source are unique for
discrete generators, without a separate generator-continuity hypothesis.
-/
theorem existsUnique_freeProCZCCompletedFoxSemidirectLiftHom_of_discreteGenerators
    {ι : X → F} (hι : ProCGroups.FreeProC.IsFreeProCGroup (C := C) ι)
    (htarget : ProCGroups.ProC.HasOpenNormalBasisInClass C (ZCCompletedFoxSemidirect C X H))
    (φ : X → H) :
    ∃! f : F →ₜ* ZCCompletedFoxSemidirect C X H,
      ∀ x : X, f (ι x) = freeProCZCCompletedFoxSemidirectGenerator (C := C) φ x :=
  existsUnique_freeProCZCCompletedFoxSemidirectLiftHom
    (C := C) hι htarget φ
    (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C := C) X H φ)

/--
Componentwise continuous completed Fox semidirect homomorphisms from a free pro-\(C\) source are
unique for discrete generators, without a separate generator-continuity hypothesis.
-/
theorem existsUnique_freeProCZCFoxSemiLiftHom_components_of_discreteGenerators
    {ι : X → F} (hι : ProCGroups.FreeProC.IsFreeProCGroup (C := C) ι)
    (htarget : ProCGroups.ProC.HasOpenNormalBasisInClass C (ZCCompletedFoxSemidirect C X H))
    (φ : X → H) :
    ∃! f : F →ₜ* ZCCompletedFoxSemidirect C X H,
      (∀ x : X, (f (ι x)).left =
        Pi.single x (1 : ZCCompletedGroupAlgebra C H)) ∧
      ∀ x : X, (f (ι x)).right = φ x :=
  existsUnique_freeProCZCCompletedFoxSemidirectLiftHom_components
    (C := C) hι htarget φ
    (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C := C) X H φ)

/--
Continuous completed Fox semidirect lifts from a free pro-\(C\) source are unique for discrete
generators, without a separate generator-continuity hypothesis.
-/
theorem existsUnique_freeProCZCCompletedFoxSemidirectLift_of_discreteGenerators
    {ι : X → F} (hι : ProCGroups.FreeProC.IsFreeProCGroup (C := C) ι)
    (htarget : ProCGroups.ProC.HasOpenNormalBasisInClass C (ZCCompletedFoxSemidirect C X H))
    (φ : X → H) :
    ∃! f : F →* ZCCompletedFoxSemidirect C X H,
      Continuous f ∧
        ∀ x : X, f (ι x) =
          freeProCZCCompletedFoxSemidirectGenerator (C := C) φ x :=
  existsUnique_freeProCZCCompletedFoxSemidirectLift
    (C := C) hι htarget φ
    (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C := C) X H φ)

/--
Componentwise continuous completed Fox semidirect lifts from a free pro-\(C\) source are unique
for discrete generators, without a separate generator-continuity hypothesis.
-/
theorem existsUnique_freeProCZCFoxSemiLift_components_of_discreteGenerators
    {ι : X → F} (hι : ProCGroups.FreeProC.IsFreeProCGroup (C := C) ι)
    (htarget : ProCGroups.ProC.HasOpenNormalBasisInClass C (ZCCompletedFoxSemidirect C X H))
    (φ : X → H) :
    ∃! f : F →* ZCCompletedFoxSemidirect C X H,
      Continuous f ∧
        (∀ x : X, (f (ι x)).left =
          Pi.single x (1 : ZCCompletedGroupAlgebra C H)) ∧
        ∀ x : X, (f (ι x)).right = φ x :=
  existsUnique_freeProCZCCompletedFoxSemidirectLift_components
    (C := C) hι htarget φ
    (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C := C) X H φ)

end ProfiniteTarget


end

end FoxDifferential
