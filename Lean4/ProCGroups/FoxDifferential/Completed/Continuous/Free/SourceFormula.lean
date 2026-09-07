import ProCGroups.FoxDifferential.Completed.Continuous.Free.Continuity

set_option autoImplicit false

/-!
# Fox differential: completed — continuous — free — source formula

The principal declarations in this module are:

- `freeProCZCCompletedFoxBoundary_of_continuousCrossedDifferential`
  Source-shaped completed Fox boundary formula for continuous crossed differentials out of a free
  pro-\(C\) source.
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

section SourceFormula

variable [Fintype X]
variable [CompactSpace (ZCCompletedFoxSemidirect C PUnit.{u + 1} H)]
variable [T2Space (ZCCompletedFoxSemidirect C PUnit.{u + 1} H)]
variable [TotallyDisconnectedSpace (ZCCompletedFoxSemidirect C PUnit.{u + 1} H)]

/--
Source-shaped completed Fox boundary formula for continuous crossed differentials out of a free
pro-\(C\) source.
-/
theorem freeProCZCCompletedFoxBoundary_of_continuousCrossedDifferential
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup (C := C) ι)
    (htargetUnit :
      ProCGroups.ProC.HasOpenNormalBasisInClass C (ZCCompletedFoxSemidirect C PUnit H))
    (ψ : F →* H)
    (delta : ScalarCrossedHom (zcCompletedGroupAlgebraScalar C ψ)
      (ZCFreeFoxCoordinates C (X := X) (H := H)))
    (hdelta_continuous : Continuous delta) (hψ_continuous : Continuous ψ)
    (hbasis :
      ∀ x : X, delta (ι x) =
        Pi.single x (1 : ZCCompletedGroupAlgebra C H))
    (g : F) :
    freeProCZCCompletedFoxBoundary C (fun x : X => ψ (ι x))
        (delta g) =
      zcCompletedGroupAlgebraBoundary C ψ g := by
  let toPUnitCoordinates :
      ZCCompletedGroupAlgebra C H →ₗ[ZCCompletedGroupAlgebra C H]
        ZCFreeFoxCoordinates C (X := PUnit) (H := H) :=
    { toFun := fun a _ => a
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let beta :
      ScalarCrossedHom (zcCompletedGroupAlgebraScalar C ψ)
        (ZCCompletedGroupAlgebra C H) :=
    delta.mapLinear
      (freeProCZCCompletedFoxBoundary C (fun x : X => ψ (ι x)))
  let betaVec :
      ScalarCrossedHom (zcCompletedGroupAlgebraScalar C ψ)
        (ZCFreeFoxCoordinates C (X := PUnit) (H := H)) :=
    beta.mapLinear toPUnitCoordinates
  let boundaryVec :
      ScalarCrossedHom (zcCompletedGroupAlgebraScalar C ψ)
        (ZCFreeFoxCoordinates C (X := PUnit) (H := H)) :=
    (coefficientFoxBoundaryCrossedHom
      (zcCompletedGroupAlgebraScalar C ψ)).mapLinear toPUnitCoordinates
  have hbeta_continuous : Continuous beta := by
    exact (continuous_freeProCZCCompletedFoxBoundary C
      (fun x : X => ψ (ι x))).comp hdelta_continuous
  have hbetaVec_continuous : Continuous betaVec := by
    exact continuous_pi fun _ => hbeta_continuous
  have hboundary_continuous :
      Continuous (zcCompletedGroupAlgebraBoundary C ψ) :=
    continuous_zcCompletedGroupAlgebraBoundary
      (C := C) (G := H) ψ hψ_continuous
  have hboundaryVec_continuous : Continuous boundaryVec := by
    exact continuous_pi fun _ => hboundary_continuous
  let f : F →* ZCCompletedFoxSemidirect C PUnit H :=
    freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential
      (C := C) (X := PUnit) (F := F) (H := H) ψ betaVec
  let h : F →* ZCCompletedFoxSemidirect C PUnit H :=
    freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential
      (C := C) (X := PUnit) (F := F) (H := H) ψ boundaryVec
  have hf_continuous : Continuous f :=
    continuous_freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential
      (C := C) (X := PUnit) (F := F) (H := H)
      ψ betaVec hbetaVec_continuous hψ_continuous
  have hh_continuous : Continuous h :=
    continuous_freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential
      (C := C) (X := PUnit) (F := F) (H := H) ψ boundaryVec
      hboundaryVec_continuous hψ_continuous
  have hgen : ∀ x : X, f (ι x) = h (ι x) := by
    intro x
    apply ZCCompletedFoxSemidirect.ext
    · funext u
      simp only [freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential_left,
        ScalarCrossedHom.mapLinear_apply, hbasis x,
        freeProCZCCompletedFoxBoundary_single,
        coefficientFoxBoundaryCrossedHom_apply,
        zcCompletedGroupAlgebraScalar_apply, f, betaVec, beta, h, boundaryVec,
        toPUnitCoordinates]
    · rfl
  have hfh : f = h := hι.hom_ext htargetUnit hf_continuous hh_continuous hgen
  have hleft := congrArg
    (fun q : F →* ZCCompletedFoxSemidirect C PUnit H =>
      (q g).left PUnit.unit) hfh
  convert hleft using 1
  all_goals
    simp [f, h, betaVec, boundaryVec, beta, toPUnitCoordinates,
      zcCompletedGroupAlgebraBoundary]
  all_goals rfl

end SourceFormula



end

end FoxDifferential
