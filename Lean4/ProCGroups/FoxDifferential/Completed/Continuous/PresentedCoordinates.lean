import ProCGroups.FoxDifferential.Common.FiniteFamilyLinearMap
import ProCGroups.FoxDifferential.Completed.Continuous.Universal.NaturalTopology

set_option autoImplicit false

/-!
# Fox differential: completed — continuous — presented coordinates

The principal declarations in this module are:

- `presentedCompletedDifferentialFamilyMapProCInteger`
  The \(\mathbb{Z}_C\llbracket H\rrbracket\)-linear family map sending the standard coordinate
  vector \(e_i\) to d(family i).
- `presentedSeparatedDifferentialFamilyMapProCInteger`
  The finite-family map into the separated completed differential module.
- `presentedCompletedDifferentialFamilyMapProCInteger_single`
  The finite-family map sends the \(i\)-th standard coordinate vector to \(d(\mathrm{family}\ i)\).
- `presentedSeparatedDifferentialFamilyMapProCInteger_single`
  The separated finite-family map sends the \(i\)-th standard coordinate vector to the separated
  differential of \(\mathrm{family}\ i\).
-/

namespace CrowellExactSequence

noncomputable section

open scoped BigOperators
open FoxDifferential

universe u v w

variable {G H : Type u}
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]


variable (C : ProCGroups.FiniteGroupClass.{u})

/--
The \(\mathbb{Z}_C\llbracket H\rrbracket\)-linear family map sending the standard coordinate
vector \(e_i\) to d(family i).
-/
def presentedCompletedDifferentialFamilyMapProCInteger
    (psi : ContinuousMonoidHom G H)
    {X : Type v} [Fintype X] (family : X -> G) :
    (X -> ZCCompletedGroupAlgebra C H) →ₗ[ZCCompletedGroupAlgebra C H]
      ZCCompletedDifferentialModule C psi.toMonoidHom :=
  finiteFamilyLinearMap
    (R := ZCCompletedGroupAlgebra C H)
    (fun i : X => zcUniversalDifferential C psi.toMonoidHom (family i))

omit [IsTopologicalGroup G] in
/--
The finite-family map sends the \(i\)-th standard coordinate vector to \(d(\mathrm{family}\
i)\).
-/
@[simp]
theorem presentedCompletedDifferentialFamilyMapProCInteger_single
    (psi : ContinuousMonoidHom G H)
    {X : Type v} [Fintype X] [DecidableEq X] (family : X -> G) (i : X) :
    presentedCompletedDifferentialFamilyMapProCInteger
        (G := G) (H := H) C psi family (Pi.single i 1) =
      zcUniversalDifferential C psi.toMonoidHom (family i) := by
  exact
    finiteFamilyLinearMap_single
      (R := ZCCompletedGroupAlgebra C H)
      (fun i : X => zcUniversalDifferential C psi.toMonoidHom (family i)) i

/-- The finite-family map into the separated completed differential module. -/
def presentedSeparatedDifferentialFamilyMapProCInteger
    (psi : ContinuousMonoidHom G H)
    {X : Type v} [Fintype X] (family : X -> G) :
    ZCFreeFoxCoordinates C (X := X) (H := H) →ₗ[ZCCompletedGroupAlgebra C H]
      ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom :=
  finiteFamilyLinearMap
    (R := ZCCompletedGroupAlgebra C H)
    (fun i : X => zcSeparatedUniversalDifferential C psi.toMonoidHom (family i))

omit [IsTopologicalGroup G] in
/--
The separated finite-family map sends the \(i\)-th standard coordinate vector to the separated
differential of \(\mathrm{family}\ i\).
-/
@[simp]
theorem presentedSeparatedDifferentialFamilyMapProCInteger_single
    (psi : ContinuousMonoidHom G H)
    {X : Type v} [Fintype X] [DecidableEq X] (family : X -> G) (i : X) :
    presentedSeparatedDifferentialFamilyMapProCInteger
        (G := G) (H := H) C psi family (Pi.single i 1) =
      zcSeparatedUniversalDifferential C psi.toMonoidHom (family i) := by
  exact
    finiteFamilyLinearMap_single
      (R := ZCCompletedGroupAlgebra C H)
      (fun i : X => zcSeparatedUniversalDifferential C psi.toMonoidHom (family i)) i

omit [IsTopologicalGroup G] in
/--
Projecting the separated finite-family map to a finite stage agrees with projecting the
algebraic finite-family map to the same finite stage.
-/
theorem zcSepDiffModuleStageProj_comp_presentedSepFamilyMap
    (psi : ContinuousMonoidHom G H)
    {X : Type v} [Fintype X] [DecidableEq X] (family : X -> G)
    (i : ZCCompletedDifferentialModuleIndex C psi.toMonoidHom) :
    (zcSeparatedCompletedDifferentialModuleStageProjectionAdd C psi.toMonoidHom i).comp
        (presentedSeparatedDifferentialFamilyMapProCInteger
          (G := G) (H := H) C psi family) =
      (zcCompletedDifferentialModuleStageProjection C psi.toMonoidHom i).comp
        (presentedCompletedDifferentialFamilyMapProCInteger
          (G := G) (H := H) C psi family) := by
  apply linearMap_ext_pi_single
  intro x
  rw [LinearMap.comp_apply, LinearMap.comp_apply,
    presentedSeparatedDifferentialFamilyMapProCInteger_single,
    presentedCompletedDifferentialFamilyMapProCInteger_single,
    zcSeparatedCompletedDifferentialModuleStageProjectionAdd_universal,
    zcCompletedDifferentialModuleStageProjection_universal]

omit [IsTopologicalGroup G] in
/--
The finite-family map into \(A_{\psi}(C)\) is continuous for the finite-stage completed
topology on \(A_{\psi}(C)\).
-/
theorem continuous_presentedCompletedDifferentialFamilyMapProCInteger_naturalTopology
    (psi : ContinuousMonoidHom G H)
    {X : Type v} [Fintype X] (family : X -> G) :
    @Continuous
      (ZCFreeFoxCoordinates C (X := X) (H := H))
      (ZCCompletedDifferentialModule C psi.toMonoidHom)
      inferInstance
      (zcCompletedDifferentialModuleNaturalTopology C psi.toMonoidHom)
      (presentedCompletedDifferentialFamilyMapProCInteger
        (G := G) (H := H) C psi family) := by
  classical
  rw [continuous_induced_rng]
  change Continuous
    (fun x : ZCFreeFoxCoordinates C (X := X) (H := H) =>
      fun i : ZCCompletedDifferentialModuleIndex C psi.toMonoidHom =>
        zcCompletedDifferentialModuleStageProjectionAdd C psi.toMonoidHom i
          (presentedCompletedDifferentialFamilyMapProCInteger
            (G := G) (H := H) C psi family x))
  refine continuous_pi fun i => ?_
  let : TopologicalSpace (zcCompletedDifferentialModuleStageRing C psi.toMonoidHom i) :=
    inferInstance
  let : DiscreteTopology (zcCompletedDifferentialModuleStageRing C psi.toMonoidHom i) :=
    inferInstance
  have hstageAction :
      Continuous (fun p : zcCompletedDifferentialModuleStageRing C psi.toMonoidHom i ×
          ZCCompletedDifferentialModuleStage C psi.toMonoidHom i => p.1 • p.2) :=
    continuous_of_discreteTopology
  have hsum :
      Continuous
        (fun x : ZCFreeFoxCoordinates C (X := X) (H := H) =>
          ∑ k, x k •
            zcCompletedDifferentialModuleStageDifferential C psi.toMonoidHom i (family k)) := by
    refine continuous_finsetSum _ fun k _ => ?_
    have hcoeff :
        Continuous (fun x : ZCFreeFoxCoordinates C (X := X) (H := H) =>
          zcCompletedGroupAlgebraProjectionRingHom C H i.target (x k)) :=
      (continuous_zcCompletedGroupAlgebraProjectionRingHom (C := C) (G := H) i.target).comp
        (continuous_apply k)
    have hconst :
        Continuous (fun _ : ZCFreeFoxCoordinates C (X := X) (H := H) =>
          zcCompletedDifferentialModuleStageDifferential C psi.toMonoidHom i (family k)) :=
      continuous_const
    have hterm := hstageAction.comp (hcoeff.prodMk hconst)
    change Continuous
      (fun x : ZCFreeFoxCoordinates C (X := X) (H := H) =>
        x k • zcCompletedDifferentialModuleStageDifferential
          C psi.toMonoidHom i (family k)) at hterm
    exact hterm
  have hfun :
      (fun a : ZCFreeFoxCoordinates C (X := X) (H := H) =>
        zcCompletedDifferentialModuleStageProjectionAdd C psi.toMonoidHom i
          (presentedCompletedDifferentialFamilyMapProCInteger
            (G := G) (H := H) C psi family a)) =
        (fun x : ZCFreeFoxCoordinates C (X := X) (H := H) =>
          ∑ k, x k •
            zcCompletedDifferentialModuleStageDifferential
              C psi.toMonoidHom i (family k)) := by
    funext a
    simp only [zcCompletedDifferentialModuleStageProjectionAdd_apply,
      presentedCompletedDifferentialFamilyMapProCInteger,
      finiteFamilyLinearMap_apply,
      map_sum, map_smul, zcCompletedDifferentialModuleStageProjection_universal]
  rw [hfun]
  exact hsum

/-- The basis property for a finite family in the Fox completed differential module. -/
def IsPresentedCompletedDifferentialFamilyBasisProCInteger
    (psi : ContinuousMonoidHom G H)
    {X : Type v} [Fintype X] (family : X -> G) : Prop :=
  Function.Bijective
    (presentedCompletedDifferentialFamilyMapProCInteger
      (G := G) (H := H) C psi family)

omit [IsTopologicalGroup G] in
/-- The completed differential basis property is invariant under reindexing a finite family. -/
theorem isPresentedCompletedDifferentialFamilyBasisProCInteger_reindex
    (psi : ContinuousMonoidHom G H)
    {X : Type v} [Fintype X]
    {Y : Type w} [Fintype Y]
    (e : X ≃ Y) (family : Y -> G)
    (hbasis_A :
      IsPresentedCompletedDifferentialFamilyBasisProCInteger
        (G := G) (H := H) C psi family) :
    IsPresentedCompletedDifferentialFamilyBasisProCInteger
      (G := G) (H := H) C psi (fun x : X => family (e x)) := by
  classical
  dsimp [IsPresentedCompletedDifferentialFamilyBasisProCInteger]
  have hmap :
      presentedCompletedDifferentialFamilyMapProCInteger
          (G := G) (H := H) C psi (fun x : X => family (e x)) =
        (presentedCompletedDifferentialFamilyMapProCInteger
          (G := G) (H := H) C psi family).comp
          (piReindexLinearEquiv
            (R := ZCCompletedGroupAlgebra C H) e).toLinearMap := by
    simpa [presentedCompletedDifferentialFamilyMapProCInteger] using
      (finiteFamilyLinearMap_reindex
        (R := ZCCompletedGroupAlgebra C H)
        (M := ZCCompletedDifferentialModule C psi.toMonoidHom)
        e (fun y : Y => zcUniversalDifferential C psi.toMonoidHom (family y)))
  rw [hmap]
  exact hbasis_A.comp
    (piReindexLinearEquiv
      (R := ZCCompletedGroupAlgebra C H) e).bijective

/-- Coordinates associated to a basis family in \(A_{\psi}(C)\). -/
def presentedCompletedDifferentialFamilyCoordinatesProCInteger
    (psi : ContinuousMonoidHom G H)
    {X : Type v} [Fintype X] (family : X -> G)
    (hbasis_A :
      IsPresentedCompletedDifferentialFamilyBasisProCInteger
        (G := G) (H := H) C psi family) :
    ZCCompletedDifferentialModule C psi.toMonoidHom ≃ₗ[ZCCompletedGroupAlgebra C H]
      (X -> ZCCompletedGroupAlgebra C H) :=
  (LinearEquiv.ofBijective
    (presentedCompletedDifferentialFamilyMapProCInteger
      (G := G) (H := H) C psi family)
    hbasis_A).symm

omit [IsTopologicalGroup G] in
/-- The inverse coordinate equivalence has underlying linear map equal to the finite-family map. -/
theorem presentedCompletedDifferentialFamilyCoordinatesProCInteger_symm_toLinearMap
    (psi : ContinuousMonoidHom G H)
    {X : Type v} [Fintype X] (family : X -> G)
    (hbasis_A :
      IsPresentedCompletedDifferentialFamilyBasisProCInteger
        (G := G) (H := H) C psi family) :
    (presentedCompletedDifferentialFamilyCoordinatesProCInteger
      (G := G) (H := H) C psi family hbasis_A).symm.toLinearMap =
      presentedCompletedDifferentialFamilyMapProCInteger
        (G := G) (H := H) C psi family :=
  rfl

omit [IsTopologicalGroup G] in
/--
The coordinate equivalence sends \(d(\mathrm{family}\ i)\) to the \(i\)-th standard coordinate
vector.
-/
@[simp 900]
theorem presentedCompletedDifferentialFamilyCoordinatesProCInteger_d_family
    (psi : ContinuousMonoidHom G H)
    {X : Type v} [Fintype X] [DecidableEq X] (family : X -> G)
    (hbasis_A :
      IsPresentedCompletedDifferentialFamilyBasisProCInteger
        (G := G) (H := H) C psi family) (i : X) :
    presentedCompletedDifferentialFamilyCoordinatesProCInteger
        (G := G) (H := H) C psi family hbasis_A
        (zcUniversalDifferential C psi.toMonoidHom (family i)) =
      Pi.single i (1 : ZCCompletedGroupAlgebra C H) := by
  let coords :=
    presentedCompletedDifferentialFamilyCoordinatesProCInteger
      (G := G) (H := H) C psi family hbasis_A
  have hsingle :
      coords.symm (Pi.single i (1 : ZCCompletedGroupAlgebra C H)) =
        zcUniversalDifferential C psi.toMonoidHom (family i) := by
    change
      presentedCompletedDifferentialFamilyMapProCInteger
          (G := G) (H := H) C psi family (Pi.single i 1) =
        zcUniversalDifferential C psi.toMonoidHom (family i)
    exact presentedCompletedDifferentialFamilyMapProCInteger_single
      (G := G) (H := H) C psi family i
  calc
    coords (zcUniversalDifferential C psi.toMonoidHom (family i)) =
        coords (coords.symm (Pi.single i (1 : ZCCompletedGroupAlgebra C H))) := by
          rw [hsingle]
    _ = Pi.single i (1 : ZCCompletedGroupAlgebra C H) := by
          exact coords.apply_symm_apply (Pi.single i (1 : ZCCompletedGroupAlgebra C H))

end

end CrowellExactSequence
