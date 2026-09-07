import ProCGroups.FoxDifferential.Completed.FreeProC.Uniqueness.Derivative
import ProCGroups.FoxDifferential.Completed.Continuous.Topology

set_option autoImplicit false

/-!
# Fox differential: completed — continuous — free — continuity

The principal declarations in this module are:

- `continuous_freeProCZCCompletedFoxSemidirectGenerator`
  The completed Fox semidirect generator map is continuous when both component maps are continuous.
- `continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete`
  The completed Fox semidirect generator map is continuous for a discrete generating space.
- `continuous_freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential`
  A crossed-differential graph into the completed Fox semidirect target is continuous when both its
  component maps are continuous.
- `continuous_freeProCZCCompletedFoxRightHom`
  The target-group component of the free pro-\(C\) completed Fox semidirect lift is continuous.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open scoped BigOperators

universe u


variable {C : ProCGroups.FiniteGroupClass.{u}}
variable (X H : Type u) [DecidableEq X]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/--
The completed Fox semidirect generator map is continuous when both component maps are
continuous.
-/
theorem continuous_freeProCZCCompletedFoxSemidirectGenerator
    [TopologicalSpace X]
    (φ : X → H)
    (hleft : Continuous (fun x : X =>
      Pi.single x (1 : ZCCompletedGroupAlgebra C H)))
    (hφ : Continuous φ) :
    Continuous (freeProCZCCompletedFoxSemidirectGenerator (C := C) φ) := by
  rw [continuous_induced_rng]
  exact hleft.prodMk hφ

/-- The completed Fox semidirect generator map is continuous for a discrete generating space. -/
theorem continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete
    [TopologicalSpace X] [DiscreteTopology X] (φ : X → H) :
    Continuous (freeProCZCCompletedFoxSemidirectGenerator (C := C) φ) :=
  continuous_of_discreteTopology

variable {F : Type u}
variable [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
variable [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]

omit
  [DecidableEq X] [IsTopologicalGroup F]
  [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F] in
/--
A crossed-differential graph into the completed Fox semidirect target is continuous when both
its component maps are continuous.
-/
theorem continuous_freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential
    (ψ : F →* H)
    (delta : ScalarCrossedHom (zcCompletedGroupAlgebraScalar C ψ)
      (ZCFreeFoxCoordinates C (X := X) (H := H)))
    (hdelta_continuous : Continuous delta) (hψ_continuous : Continuous ψ) :
    Continuous (freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential
      (C := C) (X := X) (F := F) (H := H) ψ delta) := by
  rw [continuous_induced_rng]
  exact hdelta_continuous.prodMk hψ_continuous

variable [TopologicalSpace X]

section ProfiniteTarget

variable [CompactSpace (ZCCompletedFoxSemidirect C X H)]
variable [T2Space (ZCCompletedFoxSemidirect C X H)]
variable [TotallyDisconnectedSpace (ZCCompletedFoxSemidirect C X H)]

/-- The target-group component of the free pro-\(C\) completed Fox semidirect lift is continuous. -/
theorem continuous_freeProCZCCompletedFoxRightHom
    {ι : X → F} (hι : ProCGroups.FreeProC.IsFreeProCGroup (C := C) ι)
    (htarget : ProCGroups.ProC.HasOpenNormalBasisInClass C (ZCCompletedFoxSemidirect C X H))
    (φ : X → H)
    (hφ : Continuous (freeProCZCCompletedFoxSemidirectGenerator (C := C) φ)) :
    Continuous (freeProCZCCompletedFoxRightHom
      (C := C) hι htarget φ hφ) := by
  change Continuous (fun g : F =>
    (freeProCZCCompletedFoxSemidirectLift
      (C := C) hι htarget φ hφ g).right)
  exact (continuous_zcCompletedFoxSemidirect_right C X H).comp
    (continuous_freeProCZCCompletedFoxSemidirectLift
      (C := C) hι htarget φ hφ)

omit
  [TopologicalSpace X] in
/-- The right component of the converging-set completed Fox semidirect lift is continuous. -/
theorem continuous_freeProCZCCompletedFoxRightHomOfConvergingSet
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsEpimorphicallyFreeProCGroupOnConvergingSet
      (C := C) X F ι)
    (htarget : ProCGroups.ProC.HasOpenNormalBasisInClass C (ZCCompletedFoxSemidirect C X H))
    (φ : X → H)
    (hφconv :
      ProCGroups.FreeProC.FamilyConvergesToOneAlongOpenSubgroups
        (G := ZCCompletedFoxSemidirect C X H)
        (freeProCZCCompletedFoxSemidirectGenerator (C := C) φ))
    (hφgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := ZCCompletedFoxSemidirect C X H)
        (Set.range (freeProCZCCompletedFoxSemidirectGenerator (C := C) φ))) :
    Continuous (freeProCZCCompletedFoxRightHomOfConvergingSet
      (C := C) hι htarget φ hφconv hφgen) := by
  change Continuous (fun g : F =>
    (freeProCZCCompletedFoxSemidirectLiftOfConvergingSet
      (C := C) hι htarget φ hφconv hφgen g).right)
  exact (continuous_zcCompletedFoxSemidirect_right C X H).comp
    (continuous_freeProCZCCompletedFoxSemidirectLiftOfConvergingSet
      (C := C) hι htarget φ hφconv hφgen)

section ProfiniteCodomain

variable [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]

omit
  [TopologicalSpace X] in
/--
The right component of the converging-set semidirect Fox lift is exactly the universal
free-pro-\(C\) lift of its generator values.
-/
theorem freeProCZCCompletedFoxRightHomOfConvergingSet_eq_lift
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsEpimorphicallyFreeProCGroupOnConvergingSet
      (C := C) X F ι)
    (hH : ProCGroups.ProC.HasOpenNormalBasisInClass C (H))
    (htarget : ProCGroups.ProC.HasOpenNormalBasisInClass C (ZCCompletedFoxSemidirect C X H))
    (φ : X → H)
    (hφconv :
      ProCGroups.FreeProC.FamilyConvergesToOneAlongOpenSubgroups
        (G := ZCCompletedFoxSemidirect C X H)
        (freeProCZCCompletedFoxSemidirectGenerator (C := C) φ))
    (hφgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := ZCCompletedFoxSemidirect C X H)
        (Set.range (freeProCZCCompletedFoxSemidirectGenerator (C := C) φ)))
    (hφHconv : ProCGroups.FreeProC.FamilyConvergesToOneAlongOpenSubgroups (G := H) φ)
    (hφHgen : ProCGroups.Generation.TopologicallyGenerates (G := H) (Set.range φ)) :
    freeProCZCCompletedFoxRightHomOfConvergingSet
        (C := C) hι htarget φ hφconv hφgen =
      hι.lift hH φ hφHconv hφHgen := by
  apply hι.lift_unique hH φ hφHconv hφHgen
  · exact continuous_freeProCZCCompletedFoxRightHomOfConvergingSet
      (C := C) X H hι htarget φ hφconv hφgen
  · intro x
    simp only [freeProCZCCompletedFoxRightHomOfConvergingSet_generator]

end ProfiniteCodomain

omit
  [TopologicalSpace X] in
/--
The closed-generated completed Fox semidirect lift is continuous as a map to the full semidirect
target.
-/
theorem continuous_freeProCZCCompletedFoxSemidirectLiftViaClosedGenerated
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsEpimorphicallyFreeProCGroupOnConvergingSet
      (C := C) X F ι)
    (φ : X → H)
    (htarget :
      ProCGroups.ProC.HasOpenNormalBasisInClass C
        (freeProCZCCompletedFoxSemidirectClosedGeneratedTarget (C := C) φ : Subgroup
            (ZCCompletedFoxSemidirect C X H)))
    (hφconv :
      ProCGroups.FreeProC.FamilyConvergesToOneAlongOpenSubgroups
        (G :=
          (freeProCZCCompletedFoxSemidirectClosedGeneratedTarget (C := C) φ : Subgroup
              (ZCCompletedFoxSemidirect C X H)))
        (freeProCZCCompletedFoxSemidirectClosedGeneratedGenerator (C := C) φ)) :
    Continuous (freeProCZCCompletedFoxSemidirectLiftViaClosedGenerated
      (C := C) hι φ htarget hφconv) := by
  change Continuous (fun g : F =>
    (freeProCZCCompletedFoxSemidirectLiftToClosedGenerated
      (C := C) hι φ htarget hφconv g :
        ZCCompletedFoxSemidirect C X H))
  exact continuous_subtype_val.comp
    (freeProCZCCompletedFoxSemidirectLiftHomToClosedGenerated
      (C := C) hι φ htarget hφconv).continuous_toFun

omit
  [TopologicalSpace X] in
/-- The right component of the closed-generated completed Fox semidirect lift is continuous. -/
theorem continuous_freeProCZCCompletedFoxRightHomViaClosedGenerated
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsEpimorphicallyFreeProCGroupOnConvergingSet
      (C := C) X F ι)
    (φ : X → H)
    (htarget :
      ProCGroups.ProC.HasOpenNormalBasisInClass C
        (freeProCZCCompletedFoxSemidirectClosedGeneratedTarget (C := C) φ : Subgroup
            (ZCCompletedFoxSemidirect C X H)))
    (hφconv :
      ProCGroups.FreeProC.FamilyConvergesToOneAlongOpenSubgroups
        (G :=
          (freeProCZCCompletedFoxSemidirectClosedGeneratedTarget (C := C) φ : Subgroup
              (ZCCompletedFoxSemidirect C X H)))
        (freeProCZCCompletedFoxSemidirectClosedGeneratedGenerator (C := C) φ)) :
    Continuous (freeProCZCCompletedFoxRightHomViaClosedGenerated
      (C := C) hι φ htarget hφconv) := by
  change Continuous (fun g : F =>
    (freeProCZCCompletedFoxSemidirectLiftViaClosedGenerated
      (C := C) hι φ htarget hφconv g).right)
  exact (continuous_zcCompletedFoxSemidirect_right C X H).comp
    (continuous_freeProCZCCompletedFoxSemidirectLiftViaClosedGenerated
      (C := C) X H hι φ htarget hφconv)

section ProfiniteCodomain

variable [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]

omit
  [TopologicalSpace X] in
/--
The right component of the closed-generated semidirect Fox lift is the universal free-pro-\(C\)
lift of its generator values.
-/
theorem freeProCZCCompletedFoxRightHomViaClosedGenerated_eq_lift
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsEpimorphicallyFreeProCGroupOnConvergingSet
      (C := C) X F ι)
    (hH : ProCGroups.ProC.HasOpenNormalBasisInClass C (H))
    (φ : X → H)
    (htarget :
      ProCGroups.ProC.HasOpenNormalBasisInClass C
        (freeProCZCCompletedFoxSemidirectClosedGeneratedTarget (C := C) φ : Subgroup
            (ZCCompletedFoxSemidirect C X H)))
    (hφconv :
      ProCGroups.FreeProC.FamilyConvergesToOneAlongOpenSubgroups
        (G :=
          (freeProCZCCompletedFoxSemidirectClosedGeneratedTarget (C := C) φ : Subgroup
              (ZCCompletedFoxSemidirect C X H)))
        (freeProCZCCompletedFoxSemidirectClosedGeneratedGenerator (C := C) φ))
    (hφHconv : ProCGroups.FreeProC.FamilyConvergesToOneAlongOpenSubgroups (G := H) φ)
    (hφHgen : ProCGroups.Generation.TopologicallyGenerates (G := H) (Set.range φ)) :
    freeProCZCCompletedFoxRightHomViaClosedGenerated
        (C := C) hι φ htarget hφconv =
      hι.lift hH φ hφHconv hφHgen := by
  apply hι.lift_unique hH φ hφHconv hφHgen
  · exact continuous_freeProCZCCompletedFoxRightHomViaClosedGenerated
      (C := C) X H hι φ htarget hφconv
  · intro x
    simp only [freeProCZCCompletedFoxRightHomViaClosedGenerated_generator]

omit
  [TopologicalSpace X] in
/--
The right component of the closed-generated semidirect Fox lift is the intended continuous
homomorphism with the same generator values.
-/
theorem freeProCZCCompletedFoxRightHomViaClosedGenerated_eq_continuousHom
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsEpimorphicallyFreeProCGroupOnConvergingSet
      (C := C) X F ι)
    (hH : ProCGroups.ProC.HasOpenNormalBasisInClass C (H))
    (φ : X → H)
    (htarget :
      ProCGroups.ProC.HasOpenNormalBasisInClass C
        (freeProCZCCompletedFoxSemidirectClosedGeneratedTarget (C := C) φ : Subgroup
            (ZCCompletedFoxSemidirect C X H)))
    (hφconv :
      ProCGroups.FreeProC.FamilyConvergesToOneAlongOpenSubgroups
        (G :=
          (freeProCZCCompletedFoxSemidirectClosedGeneratedTarget (C := C) φ : Subgroup
              (ZCCompletedFoxSemidirect C X H)))
        (freeProCZCCompletedFoxSemidirectClosedGeneratedGenerator (C := C) φ))
    (hφHconv : ProCGroups.FreeProC.FamilyConvergesToOneAlongOpenSubgroups (G := H) φ)
    (hφHgen : ProCGroups.Generation.TopologicallyGenerates (G := H) (Set.range φ))
    (ψ : F →ₜ* H)
    (hψ_gen : ∀ x : X, ψ (ι x) = φ x) :
    freeProCZCCompletedFoxRightHomViaClosedGenerated
        (C := C) hι φ htarget hφconv =
      ψ.toMonoidHom := by
  have hright_lift :
      freeProCZCCompletedFoxRightHomViaClosedGenerated
          (C := C) hι φ htarget hφconv =
        hι.lift hH φ hφHconv hφHgen :=
    freeProCZCCompletedFoxRightHomViaClosedGenerated_eq_lift
      (C := C) X H hι hH φ htarget hφconv hφHconv hφHgen
  have hψ_lift :
      ψ.toMonoidHom = hι.lift hH φ hφHconv hφHgen := by
    apply hι.lift_unique hH φ hφHconv hφHgen
    · exact ψ.continuous_toFun
    · exact hψ_gen
  exact hright_lift.trans hψ_lift.symm

end ProfiniteCodomain

omit
  [TopologicalSpace X] in
/-- The derivative-vector component of the closed-generated semidirect lift is continuous. -/
theorem continuous_freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsEpimorphicallyFreeProCGroupOnConvergingSet
      (C := C) X F ι)
    (φ : X → H)
    (htarget :
      ProCGroups.ProC.HasOpenNormalBasisInClass C
        (freeProCZCCompletedFoxSemidirectClosedGeneratedTarget (C := C) φ : Subgroup
            (ZCCompletedFoxSemidirect C X H)))
    (hφconv :
      ProCGroups.FreeProC.FamilyConvergesToOneAlongOpenSubgroups
        (G :=
          (freeProCZCCompletedFoxSemidirectClosedGeneratedTarget (C := C) φ : Subgroup
              (ZCCompletedFoxSemidirect C X H)))
        (freeProCZCCompletedFoxSemidirectClosedGeneratedGenerator (C := C) φ)) :
    Continuous (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
      (C := C) hι φ htarget hφconv) := by
  change Continuous (fun g : F =>
    (freeProCZCCompletedFoxSemidirectLiftViaClosedGenerated
      (C := C) hι φ htarget hφconv g).left)
  exact (continuous_zcCompletedFoxSemidirect_left C X H).comp
    (continuous_freeProCZCCompletedFoxSemidirectLiftViaClosedGenerated
      (C := C) X H hι φ htarget hφconv)

/--
The completed Fox derivative-vector component of the free pro-\(C\) semidirect lift is
continuous.
-/
theorem continuous_freeProCZCCompletedFoxDerivativeVector
    {ι : X → F} (hι : ProCGroups.FreeProC.IsFreeProCGroup (C := C) ι)
    (htarget : ProCGroups.ProC.HasOpenNormalBasisInClass C (ZCCompletedFoxSemidirect C X H))
    (φ : X → H)
    (hφ : Continuous (freeProCZCCompletedFoxSemidirectGenerator (C := C) φ)) :
    Continuous (freeProCZCCompletedFoxDerivativeVector
      (C := C) hι htarget φ hφ) := by
  change Continuous (fun g : F =>
    (freeProCZCCompletedFoxSemidirectLift
      (C := C) hι htarget φ hφ g).left)
  exact (continuous_zcCompletedFoxSemidirect_left C X H).comp
    (continuous_freeProCZCCompletedFoxSemidirectLift
      (C := C) hι htarget φ hφ)

omit
  [TopologicalSpace X] in
/--
The derivative-vector component of the converging-set completed Fox semidirect lift is
continuous.
-/
theorem continuous_freeProCZCCompletedFoxDerivativeVectorOfConvergingSet
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsEpimorphicallyFreeProCGroupOnConvergingSet
      (C := C) X F ι)
    (htarget : ProCGroups.ProC.HasOpenNormalBasisInClass C (ZCCompletedFoxSemidirect C X H))
    (φ : X → H)
    (hφconv :
      ProCGroups.FreeProC.FamilyConvergesToOneAlongOpenSubgroups
        (G := ZCCompletedFoxSemidirect C X H)
        (freeProCZCCompletedFoxSemidirectGenerator (C := C) φ))
    (hφgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := ZCCompletedFoxSemidirect C X H)
        (Set.range (freeProCZCCompletedFoxSemidirectGenerator (C := C) φ))) :
    Continuous (freeProCZCCompletedFoxDerivativeVectorOfConvergingSet
      (C := C) hι htarget φ hφconv hφgen) := by
  change Continuous (fun g : F =>
    (freeProCZCCompletedFoxSemidirectLiftOfConvergingSet
      (C := C) hι htarget φ hφconv hφgen g).left)
  exact (continuous_zcCompletedFoxSemidirect_left C X H).comp
    (continuous_freeProCZCCompletedFoxSemidirectLiftOfConvergingSet
      (C := C) hι htarget φ hφconv hφgen)

end ProfiniteTarget

/--
The semidirect generator map attached to a continuous crossed differential is continuous once
the component maps are continuous.
-/
theorem continuous_freeProCZCFoxSemiGenerator_of_continuousCrossedDiff
    {ι : X → F} (hι : ProCGroups.FreeProC.IsFreeProCGroup (C := C) ι)
    (ψ : F →* H)
    (delta : ScalarCrossedHom (zcCompletedGroupAlgebraScalar C ψ)
      (ZCFreeFoxCoordinates C (X := X) (H := H)))
    (hdelta_continuous : Continuous delta) (hψ_continuous : Continuous ψ)
    (hbasis :
      ∀ x : X, delta (ι x) =
        Pi.single x (1 : ZCCompletedGroupAlgebra C H)) :
    Continuous (freeProCZCCompletedFoxSemidirectGenerator (C := C) (fun x : X => ψ (ι x))) :=
  continuous_freeProCZCCompletedFoxSemidirectGenerator_of_crossedDifferential
    (C := C) hι ψ delta
    (continuous_freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential
      (C := C) (X := X) (F := F) (H := H)
      ψ delta hdelta_continuous hψ_continuous)
    hbasis

section ProfiniteTarget

variable [CompactSpace (ZCCompletedFoxSemidirect C X H)]
variable [T2Space (ZCCompletedFoxSemidirect C X H)]
variable [TotallyDisconnectedSpace (ZCCompletedFoxSemidirect C X H)]

/--
Continuous completed crossed differentials with continuous coefficient homomorphism are uniquely
identified with the canonical free pro-\(C\) completed Fox derivative vector.
-/
theorem freeProCZCCompletedFoxDerivativeVector_unique_of_continuousCrossedDiff_components
    {ι : X → F} (hι : ProCGroups.FreeProC.IsFreeProCGroup (C := C) ι)
    (htarget : ProCGroups.ProC.HasOpenNormalBasisInClass C (ZCCompletedFoxSemidirect C X H))
    (ψ : F →* H)
    (delta : ScalarCrossedHom (zcCompletedGroupAlgebraScalar C ψ)
      (ZCFreeFoxCoordinates C (X := X) (H := H)))
    (hdelta_continuous : Continuous delta) (hψ_continuous : Continuous ψ)
    (hbasis :
      ∀ x : X, delta (ι x) =
        Pi.single x (1 : ZCCompletedGroupAlgebra C H)) :
    (fun g : F => delta g) =
      fun g : F =>
        freeProCZCCompletedFoxDerivativeVector
          (C := C) hι htarget (fun x : X => ψ (ι x))
          (continuous_freeProCZCFoxSemiGenerator_of_continuousCrossedDiff
            (C := C) X H hι ψ delta hdelta_continuous hψ_continuous hbasis) g :=
  freeProCZCCompletedFoxDerivativeVector_unique_of_continuousCrossedDifferential
    (C := C) hι htarget ψ delta
    (continuous_freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential
      (C := C) (X := X) (F := F) (H := H)
      ψ delta hdelta_continuous hψ_continuous)
    hbasis

end ProfiniteTarget

end

end FoxDifferential
