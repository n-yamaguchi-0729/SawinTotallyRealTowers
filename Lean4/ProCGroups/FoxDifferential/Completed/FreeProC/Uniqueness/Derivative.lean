import ProCGroups.FoxDifferential.Completed.FreeProC.Uniqueness.SemidirectHom

set_option autoImplicit false

/-!
# Fox differential: completed — free pro-\(C\) — uniqueness — derivative

The principal declarations in this module are:

- `freeProCZCCompletedFoxDerivativeVector_unique_of_semidirect`
  Any continuous semidirect lift with the prescribed generator components has the canonical free
  pro-\(C\) completed Fox derivative vector as its left component.
- `freeProCZCCompletedFoxDerivativeVector_unique_of_continuousCrossedDifferential`
  Continuous completed crossed differentials on a free pro-\(C\) source are uniquely determined by
  their standard generator values, provided their semidirect graph is continuous.
- `freeProCZCCompletedCrossedDifferential_ext`
  Extensionality for continuous completed crossed differentials on a free pro-\(C\) source. The
  continuity hypotheses are put on the associated semidirect homomorphisms, which is the form used
  by the completed Fox construction before the target topology is fully structural.
- `freeProCZCCompletedFoxRightHom_eq_of_continuousCrossedDifferential`
  The coefficient homomorphism of a continuous completed crossed differential agrees with the right
  component of the canonical free pro-\(C\) semidirect lift.
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
Any continuous semidirect lift with the prescribed generator components has the canonical free
pro-\(C\) completed Fox derivative vector as its left component.
-/
theorem freeProCZCCompletedFoxDerivativeVector_unique_of_semidirect
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
    (fun g : F => (f g).left) =
      freeProCZCCompletedFoxDerivativeVector
        (C := C) hι htarget φ hφ := by
  have hgenerator :
      ∀ x : X, f (ι x) = freeProCZCCompletedFoxSemidirectGenerator (C := C) φ x := by
    intro x
    apply ZCCompletedFoxSemidirect.ext
    · exact hleft x
    · exact hright x
  have hf_eq := hι.lift_unique htarget
    (freeProCZCCompletedFoxSemidirectGenerator (C := C) φ) hφ hf hgenerator
  funext g
  rw [hf_eq]
  rfl

/--
Continuous completed crossed differentials on a free pro-\(C\) source are uniquely determined by
their standard generator values, provided their semidirect graph is continuous.
-/
theorem freeProCZCCompletedFoxDerivativeVector_unique_of_continuousCrossedDifferential
    {ι : X → F} (hι : IsFreeProCGroup (C := C) ι)
    (htarget : ProCGroups.ProC.HasOpenNormalBasisInClass C (ZCCompletedFoxSemidirect C X H))
    (ψ : F →* H)
    (delta : ScalarCrossedHom (zcCompletedGroupAlgebraScalar C ψ)
      (ZCFreeFoxCoordinates C (X := X) (H := H)))
    (hcontinuous :
      Continuous (freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential
        (X := X) ψ delta))
    (hbasis :
      ∀ x : X, delta (ι x) = Pi.single x (1 : ZCCompletedGroupAlgebra C H)) :
    (fun g : F => delta g) =
      fun g : F =>
        freeProCZCCompletedFoxDerivativeVector
          (C := C) hι htarget (fun x : X => ψ (ι x))
          (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_crossedDifferential
            (C := C) hι ψ delta hcontinuous hbasis) g := by
  have hleft :
      ∀ x : X,
        (freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential
          (X := X) ψ delta (ι x)).left =
          Pi.single x (1 : ZCCompletedGroupAlgebra C H) := by
    intro x
    exact hbasis x
  have hright :
      ∀ x : X,
        (freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential
          (X := X) ψ delta (ι x)).right = ψ (ι x) := by
    intro x
    rfl
  have hunique := freeProCZCCompletedFoxDerivativeVector_unique_of_semidirect
    (C := C) hι htarget (fun x : X => ψ (ι x))
    (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_crossedDifferential
      (C := C) hι ψ delta hcontinuous hbasis)
    (freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential
      (X := X) ψ delta)
    hcontinuous hleft hright
  simpa using hunique

omit [DecidableEq X] in
/--
Extensionality for continuous completed crossed differentials on a free pro-\(C\) source. The
continuity hypotheses are put on the associated semidirect homomorphisms, which is the form used
by the completed Fox construction before the target topology is fully structural.
-/
theorem freeProCZCCompletedCrossedDifferential_ext
    {ι : X → F} (hι : IsFreeProCGroup (C := C) ι)
    (htarget : ProCGroups.ProC.HasOpenNormalBasisInClass C (ZCCompletedFoxSemidirect C X H))
    (ψ : F →* H)
    (delta epsilon :
      ScalarCrossedHom (zcCompletedGroupAlgebraScalar C ψ)
        (ZCFreeFoxCoordinates C (X := X) (H := H)))
    (hdelta_continuous :
      Continuous (freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential
        (X := X) ψ delta))
    (hepsilon_continuous :
      Continuous (freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential
        (X := X) ψ epsilon))
    (hbasis : ∀ x : X, delta (ι x) = epsilon (ι x)) :
    delta = epsilon := by
  let f : F →* ZCCompletedFoxSemidirect C X H :=
    freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential
      (X := X) ψ delta
  let g : F →* ZCCompletedFoxSemidirect C X H :=
    freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential
      (X := X) ψ epsilon
  have hfg : ∀ x : X, f (ι x) = g (ι x) := by
    intro x
    apply ZCCompletedFoxSemidirect.ext
    · exact hbasis x
    · rfl
  have hsemidirect : f = g := hι.hom_ext htarget hdelta_continuous hepsilon_continuous hfg
  apply CrossedHom.ext
  intro a
  exact congrArg
    (fun q : F →* ZCCompletedFoxSemidirect C X H => (q a).left)
    hsemidirect

/--
The coefficient homomorphism of a continuous completed crossed differential agrees with the
right component of the canonical free pro-\(C\) semidirect lift.
-/
theorem freeProCZCCompletedFoxRightHom_eq_of_continuousCrossedDifferential
    {ι : X → F} (hι : IsFreeProCGroup (C := C) ι)
    (htarget : ProCGroups.ProC.HasOpenNormalBasisInClass C (ZCCompletedFoxSemidirect C X H))
    (ψ : F →* H)
    (delta : ScalarCrossedHom (zcCompletedGroupAlgebraScalar C ψ)
      (ZCFreeFoxCoordinates C (X := X) (H := H)))
    (hcontinuous :
      Continuous (freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential
        (X := X) ψ delta))
    (hbasis :
      ∀ x : X, delta (ι x) = Pi.single x (1 : ZCCompletedGroupAlgebra C H)) :
    ψ =
      freeProCZCCompletedFoxRightHom
        (C := C) hι htarget (fun x : X => ψ (ι x))
        (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_crossedDifferential
          (C := C) hι ψ delta hcontinuous hbasis) := by
  apply MonoidHom.ext
  intro g
  have hgenerator :
      ∀ x : X,
        freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential
            (X := X) ψ delta (ι x) =
          freeProCZCCompletedFoxSemidirectGenerator (C := C) (fun x : X => ψ (ι x)) x := by
    intro x
    apply ZCCompletedFoxSemidirect.ext
    · exact hbasis x
    · rfl
  have hsemidirect := hι.lift_unique htarget
    (freeProCZCCompletedFoxSemidirectGenerator (C := C) (fun x : X => ψ (ι x)))
    (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_crossedDifferential
      (C := C) hι ψ delta hcontinuous hbasis)
    (f := freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential
      (X := X) ψ delta)
    hcontinuous hgenerator
  change ψ g =
    ((hι.lift htarget
      (freeProCZCCompletedFoxSemidirectGenerator (C := C) (fun x : X => ψ (ι x)))
      (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_crossedDifferential
        (C := C) hι ψ delta hcontinuous hbasis)) g).right
  exact congrArg
    (fun f : F →* ZCCompletedFoxSemidirect C X H => (f g).right) hsemidirect

end ProfiniteTarget

end

end FoxDifferential
