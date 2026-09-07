import ProCGroups.FoxDifferential.Completed.Continuous.ClosedGeneratedCoordinates.Basic

set_option autoImplicit false

/-!
# Fox differential: completed — continuous — closed generated coordinates — equiv

The principal declarations in this module are:

- `separatedClosedGeneratedDerivativeCoordinateLinearEquivProCInteger`
  Coordinate equivalence for the separated completed differential module, obtained from the
  closed-generated Fox coordinates without assuming algebraic relation-submodule closedness.
- `closedGeneratedDerivativeCoordinateLinearEquivProCInteger_of_fundamental_formula`
  The closed-generated fundamental formula yields a coordinate equivalence for \(A_{\psi}(C)\); the
  displayed family map is bijective with inverse given by the closed-generated Fox coordinate map.
- `separatedClosedGeneratedDerivativeCoordinateLinearEquivProCInteger_toLinearMap`
  The linear map underlying the separated closed-generated derivative-coordinate equivalence is the
  pro-\(C\) integer derivative-coordinate map.
- `separatedClosedGeneratedDerivativeCoordinateLinearEquivProCInteger_universal`
  The separated finite family map is a left inverse to the separated closed-generated coordinate
  lift.
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

section ClosedGeneratedCoordinates

variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
variable [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
variable (C : ProCGroups.FiniteGroupClass.{u})
variable (psi : ContinuousMonoidHom G H)
variable {X : Type u} [Fintype X] [DecidableEq X]
variable (family : X → G)
variable
  (hfree :
    ProCGroups.FreeProC.IsEpimorphicallyFreeProCGroupOnConvergingSet
      (C := C) X G family)
variable
  (htarget :
    ProCGroups.ProC.HasOpenNormalBasisInClass C
      (freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
        (C := C) (fun i : X => psi (family i)) : Subgroup
          (ZCCompletedFoxSemidirect C X H)))
variable
  (hφconv :
    ProCGroups.FreeProC.FamilyConvergesToOneAlongOpenSubgroups
      (G :=
        (freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
          (C := C) (fun i : X => psi (family i)) : Subgroup
            (ZCCompletedFoxSemidirect C X H)))
      (freeProCZCCompletedFoxSemidirectClosedGeneratedGenerator
        (C := C) (fun i : X => psi (family i))))


/--
Coordinate equivalence for the separated completed differential module, obtained from the
closed-generated Fox coordinates without assuming algebraic relation-submodule closedness.
-/
def separatedClosedGeneratedDerivativeCoordinateLinearEquivProCInteger
    [T1Space (ZCFreeFoxCoordinates C (X := X) (H := H))]
    [Nonempty
      (ZCCompletedDifferentialModuleIndex C psi.toMonoidHom)]
    (hdir : Directed (· ≤ ·)
      (id : ZCCompletedDifferentialModuleIndex C psi.toMonoidHom →
        ZCCompletedDifferentialModuleIndex C psi.toMonoidHom))
    (hGbasis : ProCGroups.ProC.HasOpenNormalBasisInClass C (G))
    (hH : ProCGroups.ProC.HasOpenNormalBasisInClass C (H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOneAlongOpenSubgroups
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i)))) :
    ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom
      ≃ₗ[ZCCompletedGroupAlgebra C H]
        ZCFreeFoxCoordinates C (X := X) (H := H) :=
  LinearEquiv.ofLinearMap
    (separatedClosedGeneratedDerivativeCoordinatesLinearMapProCInteger
      (G := G) (H := H) C psi family hfree htarget hφconv
      hdir hGbasis hH hφHconv hφHgen)
    (presentedSeparatedDifferentialFamilyMapProCInteger
      (G := G) (H := H) C psi family)
    (separatedClosedGeneratedDerivativeCoordinatesLinearMapProCInteger_comp_familyMap
      (G := G) (H := H) C psi family hfree htarget hφconv
      hdir hGbasis hH hφHconv hφHgen)
    (presentedSepDifferentialFamilyMapZC_comp_sepClosedGenDerivativeCoordinatesLinearMapZC
      (G := G) (H := H) C psi family hfree htarget hφconv
      hdir hGbasis hH hφHconv hφHgen)

/--
The linear map underlying the separated closed-generated derivative-coordinate equivalence is
the pro-\(C\) integer derivative-coordinate map.
-/
theorem separatedClosedGeneratedDerivativeCoordinateLinearEquivProCInteger_toLinearMap
    [T1Space (ZCFreeFoxCoordinates C (X := X) (H := H))]
    [Nonempty
      (ZCCompletedDifferentialModuleIndex C psi.toMonoidHom)]
    (hdir : Directed (· ≤ ·)
      (id : ZCCompletedDifferentialModuleIndex C psi.toMonoidHom →
        ZCCompletedDifferentialModuleIndex C psi.toMonoidHom))
    (hGbasis : ProCGroups.ProC.HasOpenNormalBasisInClass C (G))
    (hH : ProCGroups.ProC.HasOpenNormalBasisInClass C (H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOneAlongOpenSubgroups
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i)))) :
    (separatedClosedGeneratedDerivativeCoordinateLinearEquivProCInteger
      (G := G) (H := H) C psi family hfree htarget hφconv
      hdir hGbasis hH hφHconv hφHgen).toLinearMap =
    separatedClosedGeneratedDerivativeCoordinatesLinearMapProCInteger
      (G := G) (H := H) C psi family hfree htarget hφconv
      hdir hGbasis hH hφHconv hφHgen :=
  rfl

/--
The separated finite family map is a left inverse to the separated closed-generated coordinate
lift.
-/
@[simp 900]
theorem separatedClosedGeneratedDerivativeCoordinateLinearEquivProCInteger_universal
    [T1Space (ZCFreeFoxCoordinates C (X := X) (H := H))]
    [Nonempty
      (ZCCompletedDifferentialModuleIndex C psi.toMonoidHom)]
    (hdir : Directed (· ≤ ·)
      (id : ZCCompletedDifferentialModuleIndex C psi.toMonoidHom →
        ZCCompletedDifferentialModuleIndex C psi.toMonoidHom))
    (hGbasis : ProCGroups.ProC.HasOpenNormalBasisInClass C (G))
    (hH : ProCGroups.ProC.HasOpenNormalBasisInClass C (H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOneAlongOpenSubgroups
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i))))
    (g : G) :
    separatedClosedGeneratedDerivativeCoordinateLinearEquivProCInteger
        (G := G) (H := H) C psi family hfree htarget hφconv
        hdir hGbasis hH hφHconv hφHgen
        (zcSeparatedUniversalDifferential
          C psi.toMonoidHom g) =
      freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
        (C := C) hfree (fun i : X => psi (family i)) htarget hφconv g := by
  change
    (separatedClosedGeneratedDerivativeCoordinateLinearEquivProCInteger
        (G := G) (H := H) C psi family hfree htarget hφconv
        hdir hGbasis hH hφHconv hφHgen).toLinearMap
      (zcSeparatedUniversalDifferential
        C psi.toMonoidHom g) =
      freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
        (C := C) hfree (fun i : X => psi (family i)) htarget hφconv g
  rw [separatedClosedGeneratedDerivativeCoordinateLinearEquivProCInteger_toLinearMap]
  exact
    separatedClosedGeneratedDerivativeCoordinatesLinearMapProCInteger_universal
      (G := G) (H := H) C psi family hfree htarget hφconv
      hdir hGbasis hH hφHconv hφHgen g

/--
Every finite-stage projection of \(A_{\psi}(C)\) factors through the closed-generated
coordinate lift, without assuming finite-stage separation or closedness of the relation
submodule.
-/
theorem zcDiffModuleStageProj_eq_familyMap_comp_closedGenCoord
    (hH : ProCGroups.ProC.HasOpenNormalBasisInClass C (H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOneAlongOpenSubgroups
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i))))
    (i : ZCCompletedDifferentialModuleIndex
        C psi.toMonoidHom) :
    zcCompletedDifferentialModuleStageProjection
        C psi.toMonoidHom i =
      ((zcCompletedDifferentialModuleStageProjection
            C psi.toMonoidHom i).comp
        (presentedCompletedDifferentialFamilyMapProCInteger
          (G := G) (H := H) C psi family)).comp
        (closedGeneratedDerivativeCoordinatesLinearMapProCInteger
          (G := G) (H := H) C psi family hfree htarget hφconv
          hH hφHconv hφHgen) := by
  apply crossedDifferentialModuleHom_ext
    (A := ZCCompletedDifferentialModuleStage C psi.toMonoidHom i)
    (zcCompletedGroupAlgebraScalar C psi.toMonoidHom)
  intro g
  change
    zcCompletedDifferentialModuleStageProjection C psi.toMonoidHom i
        (zcUniversalDifferential C psi.toMonoidHom g) =
      zcCompletedDifferentialModuleStageProjection C psi.toMonoidHom i
        (presentedCompletedDifferentialFamilyMapProCInteger
          (G := G) (H := H) C psi family
          (closedGeneratedDerivativeCoordinatesLinearMapProCInteger
            (G := G) (H := H) C psi family hfree htarget hφconv
            hH hφHconv hφHgen
            (zcUniversalDifferential C psi.toMonoidHom g)))
  rw [closedGeneratedDerivativeCoordinatesLinearMapProCInteger_universal
    (G := G) (H := H) C psi family hfree htarget hφconv hH hφHconv hφHgen g]
  exact
    (closedGenerated_fundamental_formula_stageProj
      (G := G) (H := H) C psi family hfree htarget hφconv
      hH hφHconv hφHgen i g).symm

omit [Fintype X] in
/--
Equality of closed-generated coordinates implies equality after every finite stage projection.
-/
theorem zcCompletedDifferentialModuleStageProjection_eq_of_closedGeneratedCoordinate_eq
    [Finite X]
    (hH : ProCGroups.ProC.HasOpenNormalBasisInClass C (H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOneAlongOpenSubgroups
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i))))
    {a b : ZCCompletedDifferentialModule
        C psi.toMonoidHom}
    (hab :
      closedGeneratedDerivativeCoordinatesLinearMapProCInteger
          (G := G) (H := H) C psi family hfree htarget hφconv
          hH hφHconv hφHgen a =
        closedGeneratedDerivativeCoordinatesLinearMapProCInteger
          (G := G) (H := H) C psi family hfree htarget hφconv
          hH hφHconv hφHgen b)
    (i : ZCCompletedDifferentialModuleIndex
        C psi.toMonoidHom) :
    zcCompletedDifferentialModuleStageProjection
        C psi.toMonoidHom i a =
      zcCompletedDifferentialModuleStageProjection
        C psi.toMonoidHom i b := by
  let : Fintype X := Fintype.ofFinite X
  let P :=
    zcCompletedDifferentialModuleStageProjection
      C psi.toMonoidHom i
  let M :=
    presentedCompletedDifferentialFamilyMapProCInteger
      (G := G) (H := H) C psi family
  let L :=
    closedGeneratedDerivativeCoordinatesLinearMapProCInteger
      (G := G) (H := H) C psi family hfree htarget hφconv
      hH hφHconv hφHgen
  have hfactor :=
    zcDiffModuleStageProj_eq_familyMap_comp_closedGenCoord
      (G := G) (H := H) C psi family hfree htarget hφconv
      hH hφHconv hφHgen i
  have hfactor' : P = (P.comp M).comp L := by
    simpa [P, M, L] using hfactor
  calc
    zcCompletedDifferentialModuleStageProjection
        C psi.toMonoidHom i a = ((P.comp M).comp L) a := by
          simpa [P, M, L] using congrArg (fun f => f a) hfactor'
    _ = ((P.comp M).comp L) b := by
          exact congrArg (fun x => (P.comp M) x) (by simpa [L] using hab)
    _ =
        zcCompletedDifferentialModuleStageProjection
          C psi.toMonoidHom i b := by
          simpa [P, M, L] using (congrArg (fun f => f b) hfactor').symm

omit [Fintype X] in
/--
If finite stage projections already separate points, then the closed-generated coordinate lift
is injective.
-/
theorem closedGenDerivativeCoordinatesLinearMapZC_inj_of_stageProjsSeparate
    [Finite X]
    (hH : ProCGroups.ProC.HasOpenNormalBasisInClass C (H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOneAlongOpenSubgroups
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i))))
    (hsep :
      zcCompletedDifferentialModuleStageProjectionsSeparate
        C psi.toMonoidHom) :
    Function.Injective
      (closedGeneratedDerivativeCoordinatesLinearMapProCInteger
        (G := G) (H := H) C psi family hfree htarget hφconv
        hH hφHconv hφHgen) := by
  let : Fintype X := Fintype.ofFinite X
  intro a b hab
  apply hsep
  funext i
  change
    zcCompletedDifferentialModuleStageProjection C psi.toMonoidHom i a =
      zcCompletedDifferentialModuleStageProjection C psi.toMonoidHom i b
  exact
    zcCompletedDifferentialModuleStageProjection_eq_of_closedGeneratedCoordinate_eq
      (G := G) (H := H) C psi family hfree htarget hφconv
      hH hφHconv hφHgen hab i

/--
The completed fundamental formula for the closed-generated Fox coordinates is equivalent to
injectivity of the closed-generated coordinate lift \(A_{\psi}(C) \to \mathbb{Z}_C\llbracket
H\rrbracket^{X}\). The forward direction says that the family map and the coordinate lift are
inverse linear maps. The reverse direction is the non-circular reduction used in the
Morishita-aligned route: since the coordinate lift is already a left inverse to the family map,
injectivity forces the formula \(\sum_i D_i(g) d x_i = d g\) in the algebraic Crowell module.
-/
theorem closedGenerated_fundamental_formula_iff_closedGeneratedCoordinate_injective
    {C : ProCGroups.FiniteGroupClass.{u}}
    {psi : ContinuousMonoidHom G H}
    {family : X → G}
    {hfree htarget hφconv}
    (hH : ProCGroups.ProC.HasOpenNormalBasisInClass C (H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOneAlongOpenSubgroups
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i)))) :
    (∀ g : G,
      presentedCompletedDifferentialFamilyMapProCInteger
          (G := G) (H := H) C psi family
          (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
            (C := C) hfree (fun i : X => psi (family i)) htarget hφconv g) =
        zcUniversalDifferential C psi.toMonoidHom g) ↔
      Function.Injective
        (closedGeneratedDerivativeCoordinatesLinearMapProCInteger
          (G := G) (H := H) (C := C) (psi := psi) (family := family)
          (hfree := hfree) (htarget := htarget) (hφconv := hφconv)
          hH hφHconv hφHgen) := by
  let M :=
    presentedCompletedDifferentialFamilyMapProCInteger
      (G := G) (H := H) C psi family
  let L :=
    closedGeneratedDerivativeCoordinatesLinearMapProCInteger
      (G := G) (H := H) C psi family hfree htarget hφconv
      hH hφHconv hφHgen
  have hLM : L.comp M = LinearMap.id := by
    simpa [L, M] using
      closedGeneratedDerivativeCoordinatesLinearMapProCInteger_comp_familyMap
        (G := G) (H := H) C psi family hfree htarget hφconv
        hH hφHconv hφHgen
  constructor
  · intro hfundamental
    have hML : M.comp L = LinearMap.id := by
      apply crossedDifferentialModuleHom_ext
        (A := ZCCompletedDifferentialModule C psi.toMonoidHom)
        (zcCompletedGroupAlgebraScalar C psi.toMonoidHom)
      intro g
      calc
        (M.comp L)
            (zcUniversalDifferential C psi.toMonoidHom g) =
            M
              (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
                (C := C) hfree (fun i : X => psi (family i)) htarget hφconv g) := by
              change
                M (L (zcUniversalDifferential C psi.toMonoidHom g)) =
                  M
                    (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
                      (C := C) hfree (fun i : X => psi (family i)) htarget hφconv g)
              rw [closedGeneratedDerivativeCoordinatesLinearMapProCInteger_universal
                (G := G) (H := H) C psi family hfree htarget hφconv
                hH hφHconv hφHgen g]
        _ = zcUniversalDifferential C psi.toMonoidHom g :=
            hfundamental g
        _ = LinearMap.id
            (zcUniversalDifferential C psi.toMonoidHom g) := rfl
    intro a b hab
    calc
      a = (M.comp L) a := by rw [hML]; rfl
      _ = M (L a) := rfl
      _ = M (L b) := by rw [hab]
      _ = (M.comp L) b := rfl
      _ = b := by rw [hML]; rfl
  · intro hLinj g
    apply hLinj
    calc
      L
          (presentedCompletedDifferentialFamilyMapProCInteger
            (G := G) (H := H) C psi family
            (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
              (C := C) hfree (fun i : X => psi (family i)) htarget hφconv g)) =
          (L.comp M)
            (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
              (C := C) hfree (fun i : X => psi (family i)) htarget hφconv g) := rfl
      _ = freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
            (C := C) hfree (fun i : X => psi (family i)) htarget hφconv g := by
            rw [hLM]
            rfl
      _ = L (zcUniversalDifferential C psi.toMonoidHom g) := by
            rw [closedGeneratedDerivativeCoordinatesLinearMapProCInteger_universal
              (G := G) (H := H) C psi family hfree htarget hφconv
              hH hφHconv hφHgen g]

omit [Fintype X] in
/--
A direct non-circular closedness criterion through the closed-generated coordinate lift. For a
pro-\(C\) source the coordinate lift is continuous for the finite-stage natural topology. Thus
injectivity of this lift gives closedness of the defining crossed-differential relation
submodule by the general Hausdorff target reflection criterion.
-/
theorem zcDiffModuleRelSubmoduleClosed_of_closedGenCoord_hasOpenNormalBasisInClass_of_inj
    (hGbasis : ProCGroups.ProC.HasOpenNormalBasisInClass C (G))
    (hH : ProCGroups.ProC.HasOpenNormalBasisInClass C (H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOneAlongOpenSubgroups
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i))))
    (hcoord_inj :
      Function.Injective
        (closedGeneratedDerivativeCoordinatesLinearMapProCInteger
          (G := G) (H := H) C psi family hfree htarget hφconv
          hH hφHconv hφHgen)) :
    zcCompletedDifferentialModuleRelationSubmoduleClosed
      C psi.toMonoidHom := by
  exact
    zcDiffModuleRelSubmoduleClosed_of_inj_continuous_naturalTopology
      C psi.toMonoidHom
      (closedGeneratedDerivativeCoordinatesLinearMapProCInteger
        (G := G) (H := H) C psi family hfree htarget hφconv
        hH hφHconv hφHgen)
      hcoord_inj
      (continuous_closedGenDerivativeCoordinatesLinearMapZC_naturalTopology_of_openNormalBasis
        (G := G) (H := H) C psi family hfree htarget hφconv
        hGbasis hH hφHconv hφHgen)

/--
Closed-generated module-valued fundamental formula from topological uniqueness of continuous
crossed differentials. The extra continuity hypotheses are the precise topological input not
supplied by the algebraic definition of the \(\mathbb{Z}_C\)-completed differential module:
they say that the displayed closed-generated expansion and the universal differential are
continuous into a Hausdorff topology on \(A_{\psi}(C)\).
-/
theorem closedGenerated_fundamental_formula_of_continuous
    [TopologicalSpace (ZCCompletedDifferentialModule
      C psi.toMonoidHom)]
    [T2Space (ZCCompletedDifferentialModule
      C psi.toMonoidHom)]
    (hH : ProCGroups.ProC.HasOpenNormalBasisInClass C (H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOneAlongOpenSubgroups
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i))))
    (hmodule_continuous :
      Continuous
        (fun g : G =>
          presentedCompletedDifferentialFamilyMapProCInteger
              (G := G) (H := H) C psi family
              (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
                (C := C) hfree (fun i : X => psi (family i)) htarget hφconv g)))
    (huniv_continuous :
      Continuous
        (fun g : G =>
          zcUniversalDifferential C psi.toMonoidHom g)) :
    ∀ g : G,
      presentedCompletedDifferentialFamilyMapProCInteger
          (G := G) (H := H) C psi family
          (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
            (C := C) hfree (fun i : X => psi (family i)) htarget hφconv g) =
        zcUniversalDifferential C psi.toMonoidHom g := by
  let M :=
    presentedCompletedDifferentialFamilyMapProCInteger
      (G := G) (H := H) C psi family
  let φ : X → H := fun i => psi (family i)
  have hright :
      freeProCZCCompletedFoxRightHomViaClosedGenerated
          (C := C) hfree φ htarget hφconv =
        psi.toMonoidHom := by
    exact
      freeProCZCCompletedFoxRightHomViaClosedGenerated_eq_continuousHom
        (C := C) X H hfree hH φ htarget hφconv hφHconv hφHgen psi
        (by intro i; rfl)
  let Dclosed : ScalarCrossedHom
      (zcCompletedGroupAlgebraScalar C psi.toMonoidHom)
      (ZCFreeFoxCoordinates C (X := X) (H := H)) :=
    { toFun := fun g =>
        freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
          (C := C) hfree φ htarget hφconv g
      map_mul' := by
        intro a b
        rw [← hright]
        exact
          ScalarCrossedHom.map_mul
            (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
              (C := C) hfree φ htarget hφconv) a b }
  let Dmodule : ScalarCrossedHom
      (zcCompletedGroupAlgebraScalar C psi.toMonoidHom)
      (ZCCompletedDifferentialModule C psi.toMonoidHom) :=
    Dclosed.mapLinear M
  have hEq :
      Dmodule =
        zcUniversalDifferential C psi.toMonoidHom := by
    refine
      CrossedHom.eq_of_continuous_of_topologicallyGenerates
        Dmodule (zcUniversalDifferential C psi.toMonoidHom)
        ?_ ?_ hfree.generates_range ?_
    · change Continuous (fun g : G => M (Dclosed g))
      exact hmodule_continuous
    · simpa using huniv_continuous
    · rintro _ ⟨i, rfl⟩
      calc
        Dmodule (family i) =
            M (Pi.single i
              (1 : ZCCompletedGroupAlgebra C H)) := by
              change
                M
                    (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
                      (C := C) hfree φ htarget hφconv (family i)) =
                  M (Pi.single i (1 : ZCCompletedGroupAlgebra C H))
              rw [freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated_generator]
        _ = zcUniversalDifferential C psi.toMonoidHom
              (family i) := by
              simpa [M] using
                presentedCompletedDifferentialFamilyMapProCInteger_single
                  (G := G) (H := H) C psi family i
  intro g
  exact congrArg
    (fun d : ScalarCrossedHom
      (zcCompletedGroupAlgebraScalar C psi.toMonoidHom)
      (ZCCompletedDifferentialModule C psi.toMonoidHom) => d g)
    hEq

/--
Natural-topology form of the closed-generated fundamental formula, assuming the finite-stage
projections separate points of \(A_{\psi}(C)\).
-/
theorem closedGenerated_fundamental_formula_naturalTopology_of_separating
    (hsep :
      zcCompletedDifferentialModuleStageProjectionsSeparate
        C psi.toMonoidHom)
    (hH : ProCGroups.ProC.HasOpenNormalBasisInClass C (H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOneAlongOpenSubgroups
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i)))) :
    ∀ g : G,
      presentedCompletedDifferentialFamilyMapProCInteger
          (G := G) (H := H) C psi family
          (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
            (C := C) hfree (fun i : X => psi (family i)) htarget hφconv g) =
        zcUniversalDifferential C psi.toMonoidHom g := by
  let : TopologicalSpace
      (ZCCompletedDifferentialModule C psi.toMonoidHom) :=
    zcCompletedDifferentialModuleNaturalTopology C psi.toMonoidHom
  let : T2Space
      (ZCCompletedDifferentialModule C psi.toMonoidHom) :=
    t2Space_zcCompletedDifferentialModuleNaturalTopology_of_separating
      C psi.toMonoidHom hsep
  exact
    closedGenerated_fundamental_formula_of_continuous
      (G := G) (H := H) C psi family hfree htarget hφconv
      hH hφHconv hφHgen
      (by
        simpa using
          continuous_closedGenerated_module_expansion_naturalTopology
            (G := G) (H := H) C psi family hfree htarget hφconv)
      (by
        simpa using
          continuous_zcUniversalDifferential_naturalTopology
            C psi.toMonoidHom)

omit [Fintype X] in
/--
For a pro-\(C\) source, closedness of the algebraic crossed-differential relation submodule is
equivalent to injectivity of the closed-generated coordinate lift. This is the precise
non-circular frontier left by the Morishita-aligned route. The implication from closedness to
injectivity goes through finite-stage separation and the completed fundamental formula. The
converse uses only continuity of the coordinate lift for the finite-stage natural topology and
the Hausdorff target reflection criterion.
-/
theorem zcDiffModuleRelSubmoduleClosed_iff_closedGenCoord_inj_of_hasOpenNormalBasisInClass
    {C : ProCGroups.FiniteGroupClass.{u}}
    {psi : ContinuousMonoidHom G H}
    (family : X → G) (hfree htarget hφconv) [Finite X]
    [Nonempty
      (ZCCompletedDifferentialModuleIndex C psi.toMonoidHom)]
    (hdir : Directed (· ≤ ·)
      (id : ZCCompletedDifferentialModuleIndex C psi.toMonoidHom →
        ZCCompletedDifferentialModuleIndex C psi.toMonoidHom))
    (hGbasis : ProCGroups.ProC.HasOpenNormalBasisInClass C (G))
    (hH : ProCGroups.ProC.HasOpenNormalBasisInClass C (H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOneAlongOpenSubgroups
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i)))) :
    zcCompletedDifferentialModuleRelationSubmoduleClosed
        C psi.toMonoidHom ↔
      Function.Injective
        (closedGeneratedDerivativeCoordinatesLinearMapProCInteger
          (G := G) (H := H) (C := C) (psi := psi) (family := family)
          (hfree := hfree) (htarget := htarget) (hφconv := hφconv)
          hH hφHconv hφHgen) := by
  let : Fintype X := Fintype.ofFinite X
  constructor
  · intro hclosed
    have hsep :
        zcCompletedDifferentialModuleStageProjectionsSeparate
          C psi.toMonoidHom :=
      (zcDiffModuleRelSubmoduleClosed_iff_stageProjsSeparate
        (C := C) (ψ := psi.toMonoidHom) hdir).1 hclosed
    exact
      closedGenDerivativeCoordinatesLinearMapZC_inj_of_stageProjsSeparate
        (G := G) (H := H) C psi family hfree htarget hφconv
        hH hφHconv hφHgen hsep
  · intro hcoord_inj
    exact
      zcDiffModuleRelSubmoduleClosed_of_closedGenCoord_hasOpenNormalBasisInClass_of_inj
        (G := G) (H := H) C psi family hfree htarget hφconv
        hGbasis hH hφHconv hφHgen hcoord_inj

/--
Once the closed-generated Fox vector satisfies the universal fundamental formula in
\(A_{\psi}(C)\), the displayed family differentials form a finite coordinate basis of
\(A_{\psi}(C)\).
-/
theorem isPresentedCompletedDifferentialFamilyBasisZC_of_closedGen_fundFormula
    (hH : ProCGroups.ProC.HasOpenNormalBasisInClass C (H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOneAlongOpenSubgroups
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i))))
    (hfundamental :
      ∀ g : G,
        presentedCompletedDifferentialFamilyMapProCInteger
            (G := G) (H := H) C psi family
            (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
              (C := C) hfree (fun i : X => psi (family i)) htarget hφconv g) =
          zcUniversalDifferential C psi.toMonoidHom g) :
    IsPresentedCompletedDifferentialFamilyBasisProCInteger
      (G := G) (H := H) C psi family := by
  let M :=
    presentedCompletedDifferentialFamilyMapProCInteger
      (G := G) (H := H) C psi family
  let L :=
    closedGeneratedDerivativeCoordinatesLinearMapProCInteger
      (G := G) (H := H) C psi family hfree htarget hφconv hH hφHconv hφHgen
  have hLM : L.comp M = LinearMap.id := by
    exact
      closedGeneratedDerivativeCoordinatesLinearMapProCInteger_comp_familyMap
        (G := G) (H := H) C psi family hfree htarget hφconv hH hφHconv hφHgen
  have hML : M.comp L = LinearMap.id := by
    apply crossedDifferentialModuleHom_ext
      (A := ZCCompletedDifferentialModule C psi.toMonoidHom)
      (zcCompletedGroupAlgebraScalar C psi.toMonoidHom)
    intro g
    calc
      (M.comp L) (zcUniversalDifferential C psi.toMonoidHom g) =
          M
            (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
              (C := C) hfree (fun i : X => psi (family i)) htarget hφconv g) := by
          change
            M (L (zcUniversalDifferential C psi.toMonoidHom g)) =
              M
                (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
                  (C := C) hfree (fun i : X => psi (family i)) htarget hφconv g)
          rw [closedGeneratedDerivativeCoordinatesLinearMapProCInteger_universal
            (G := G) (H := H) C psi family hfree htarget hφconv hH hφHconv hφHgen g]
      _ = zcUniversalDifferential C psi.toMonoidHom g :=
          hfundamental g
      _ = LinearMap.id
          (zcUniversalDifferential C psi.toMonoidHom g) := rfl
  constructor
  · intro x y hxy
    have h := congrArg L hxy
    calc
      x = (L.comp M) x := by rw [hLM]; rfl
      _ = L (M x) := rfl
      _ = L (M y) := h
      _ = (L.comp M) y := rfl
      _ = y := by rw [hLM]; rfl
  · intro m
    refine ⟨L m, ?_⟩
    have h := congrArg (fun f => f m) hML
    change M (L m) = m at h
    exact h


end ClosedGeneratedCoordinates

omit [IsTopologicalGroup G] in
/-- A left inverse to a bijective family map is the coordinate inverse associated to the basis. -/
theorem presentedCompletedDifferentialFamilyCoordinatesProCInteger_eq_of_leftInverse
    (psi : ContinuousMonoidHom G H)
    {X : Type v} [Fintype X] (family : X -> G)
    (hbasis_A :
      IsPresentedCompletedDifferentialFamilyBasisProCInteger
        (G := G) (H := H) C psi family)
    (L :
      ZCCompletedDifferentialModule C psi.toMonoidHom →ₗ[ZCCompletedGroupAlgebra C H]
        (X → ZCCompletedGroupAlgebra C H))
    (hL :
      L.comp
        (presentedCompletedDifferentialFamilyMapProCInteger
          (G := G) (H := H) C psi family) =
      LinearMap.id) :
    L =
      (presentedCompletedDifferentialFamilyCoordinatesProCInteger
        (G := G) (H := H) C psi family hbasis_A).toLinearMap := by
  let coords :=
    presentedCompletedDifferentialFamilyCoordinatesProCInteger
      (G := G) (H := H) C psi family hbasis_A
  let f :=
    presentedCompletedDifferentialFamilyMapProCInteger
      (G := G) (H := H) C psi family
  have hcoords : coords.toLinearMap.comp f = LinearMap.id := by
    apply LinearMap.ext
    intro x
    change coords (coords.symm x) = x
    exact coords.apply_symm_apply x
  apply LinearMap.ext
  intro m
  rcases hbasis_A.2 m with ⟨x, hx⟩
  rw [← hx]
  calc
    L (f x) = (L.comp f) x := rfl
    _ = x := by
      rw [hL]
      rfl
    _ = (coords.toLinearMap.comp f) x := by
      rw [hcoords]
      rfl
    _ = coords.toLinearMap (f x) := rfl

section ClosedGeneratedCoordinateEquiv

variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
variable [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
variable (C : ProCGroups.FiniteGroupClass.{u})
variable (psi : ContinuousMonoidHom G H)
variable {X : Type u} [Fintype X] [DecidableEq X]
variable (family : X → G)
variable
  (hfree :
    ProCGroups.FreeProC.IsEpimorphicallyFreeProCGroupOnConvergingSet
      (C := C) X G family)
variable
  (htarget :
    ProCGroups.ProC.HasOpenNormalBasisInClass C
      (freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
        (C := C) (fun i : X => psi (family i)) : Subgroup
          (ZCCompletedFoxSemidirect C X H)))
variable
  (hφconv :
    ProCGroups.FreeProC.FamilyConvergesToOneAlongOpenSubgroups
      (G :=
        (freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
          (C := C) (fun i : X => psi (family i)) : Subgroup
            (ZCCompletedFoxSemidirect C X H)))
      (freeProCZCCompletedFoxSemidirectClosedGeneratedGenerator
        (C := C) (fun i : X => psi (family i))))


/--
The closed-generated fundamental formula yields a coordinate equivalence for \(A_{\psi}(C)\);
the displayed family map is bijective with inverse given by the closed-generated Fox coordinate
map.
-/
def closedGeneratedDerivativeCoordinateLinearEquivProCInteger_of_fundamental_formula
    (hH : ProCGroups.ProC.HasOpenNormalBasisInClass C (H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOneAlongOpenSubgroups
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i))))
    (hfundamental :
      ∀ g : G,
        presentedCompletedDifferentialFamilyMapProCInteger
            (G := G) (H := H) C psi family
            (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
              (C := C) hfree (fun i : X => psi (family i)) htarget hφconv g) =
          zcUniversalDifferential C psi.toMonoidHom g) :
    ZCCompletedDifferentialModule C psi.toMonoidHom
      ≃ₗ[ZCCompletedGroupAlgebra C H]
        ZCFreeFoxCoordinates C (X := X) (H := H) :=
  presentedCompletedDifferentialFamilyCoordinatesProCInteger
    (G := G) (H := H) C psi family
    (isPresentedCompletedDifferentialFamilyBasisZC_of_closedGen_fundFormula
      (G := G) (H := H) C psi family hfree htarget hφconv
      hH hφHconv hφHgen hfundamental)

/--
The coordinate equivalence from the fundamental formula has the closed-generated coordinate map
as its forward linear map.
-/
theorem closedGenDerivativeCoordinateLinearEquivZC_of_fundFormula_toLinearMap
    (hH : ProCGroups.ProC.HasOpenNormalBasisInClass C (H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOneAlongOpenSubgroups
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i))))
    (hfundamental :
      ∀ g : G,
        presentedCompletedDifferentialFamilyMapProCInteger
            (G := G) (H := H) C psi family
            (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
              (C := C) hfree (fun i : X => psi (family i)) htarget hφconv g) =
          zcUniversalDifferential C psi.toMonoidHom g) :
    (closedGeneratedDerivativeCoordinateLinearEquivProCInteger_of_fundamental_formula
      (G := G) (H := H) C psi family hfree htarget hφconv
      hH hφHconv hφHgen hfundamental).toLinearMap =
      closedGeneratedDerivativeCoordinatesLinearMapProCInteger
        (G := G) (H := H) C psi family hfree htarget hφconv
        hH hφHconv hφHgen := by
  let hbasis_A :=
    isPresentedCompletedDifferentialFamilyBasisZC_of_closedGen_fundFormula
      (G := G) (H := H) C psi family hfree htarget hφconv
      hH hφHconv hφHgen hfundamental
  let L :=
    closedGeneratedDerivativeCoordinatesLinearMapProCInteger
      (G := G) (H := H) C psi family hfree htarget hφconv
      hH hφHconv hφHgen
  have hleft :
      L.comp
        (presentedCompletedDifferentialFamilyMapProCInteger
          (G := G) (H := H) C psi family) =
      LinearMap.id :=
    closedGeneratedDerivativeCoordinatesLinearMapProCInteger_comp_familyMap
      (G := G) (H := H) C psi family hfree htarget hφconv
      hH hφHconv hφHgen
  have hL :
      L =
        (presentedCompletedDifferentialFamilyCoordinatesProCInteger
          (G := G) (H := H) C psi family hbasis_A).toLinearMap :=
    presentedCompletedDifferentialFamilyCoordinatesProCInteger_eq_of_leftInverse
      (G := G) (H := H) C psi family hbasis_A L hleft
  simpa [closedGeneratedDerivativeCoordinateLinearEquivProCInteger_of_fundamental_formula,
    hbasis_A, L] using hL.symm

/--
A completed coordinate equivalence and continuity of the coordinate map composed with the
algebraic quotient map imply closedness for the finite-stage pre-module topology.
-/
theorem zcDiffModuleRelSubmoduleClosed_of_closedGenCoordPrequotient_continuous_of_fundFormula
    [T1Space (ZCFreeFoxCoordinates C (X := X) (H := H))]
    (hH : ProCGroups.ProC.HasOpenNormalBasisInClass C (H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOneAlongOpenSubgroups
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i))))
    (hfundamental :
      ∀ g : G,
        presentedCompletedDifferentialFamilyMapProCInteger
            (G := G) (H := H) C psi family
            (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
              (C := C) hfree (fun i : X => psi (family i)) htarget hφconv g) =
          zcUniversalDifferential C psi.toMonoidHom g)
    (hprecoord_continuous :
      @Continuous
        (CrossedDifferentialPreModule
          (ZCCompletedGroupAlgebra C H) G)
        (ZCFreeFoxCoordinates C (X := X) (H := H))
        (zcCompletedDifferentialPreModuleNaturalTopology
          C psi.toMonoidHom)
        inferInstance
        (fun x =>
          (closedGeneratedDerivativeCoordinateLinearEquivProCInteger_of_fundamental_formula
            (G := G) (H := H) C psi family hfree htarget hφconv
            hH hφHconv hφHgen hfundamental).toLinearMap
            ((crossedDifferentialRelationSubmodule
              (zcCompletedGroupAlgebraScalar
                C psi.toMonoidHom)).mkQ x))) :
    zcCompletedDifferentialModuleRelationSubmoduleClosed
      C psi.toMonoidHom := by
  let e :=
    closedGeneratedDerivativeCoordinateLinearEquivProCInteger_of_fundamental_formula
      (G := G) (H := H) C psi family hfree htarget hφconv
      hH hφHconv hφHgen hfundamental
  exact
    zcDiffModuleRelSubmoduleClosed_of_inj_continuous_comp_mkQ
      C psi.toMonoidHom e.toLinearMap e.injective hprecoord_continuous

/--
The closed-generated coordinate equivalence and continuity of the coordinate map \(A_{\psi}(C)
\to \mathbb{Z}_C\llbracket H\rrbracket^{X}\) imply closedness for the quotient finite-stage
natural topology.
-/
theorem zcDiffRelSubmoduleClosed_of_closedGenCoord_fundFormula
    [T1Space (ZCFreeFoxCoordinates C (X := X) (H := H))]
    (hH : ProCGroups.ProC.HasOpenNormalBasisInClass C (H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOneAlongOpenSubgroups
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i))))
    (hfundamental :
      ∀ g : G,
        presentedCompletedDifferentialFamilyMapProCInteger
            (G := G) (H := H) C psi family
            (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
              (C := C) hfree (fun i : X => psi (family i)) htarget hφconv g) =
          zcUniversalDifferential C psi.toMonoidHom g)
    (hcoord_continuous :
      @Continuous
        (ZCCompletedDifferentialModule C psi.toMonoidHom)
        (ZCFreeFoxCoordinates C (X := X) (H := H))
        (zcCompletedDifferentialModuleNaturalTopology
          C psi.toMonoidHom)
        inferInstance
        (closedGeneratedDerivativeCoordinateLinearEquivProCInteger_of_fundamental_formula
          (G := G) (H := H) C psi family hfree htarget hφconv
          hH hφHconv hφHgen hfundamental).toLinearMap) :
    zcCompletedDifferentialModuleRelationSubmoduleClosed
      C psi.toMonoidHom := by
  let e :=
    closedGeneratedDerivativeCoordinateLinearEquivProCInteger_of_fundamental_formula
      (G := G) (H := H) C psi family hfree htarget hφconv
      hH hφHconv hφHgen hfundamental
  exact
    zcDiffModuleRelSubmoduleClosed_of_inj_continuous_naturalTopology
      C psi.toMonoidHom e.toLinearMap e.injective hcoord_continuous

/--
Closedness from the closed-generated fundamental formula and finite-stage coordinate
factorization. The factorization hypothesis is the concrete finite-stage compatibility needed
to make the closed-generated coordinate map continuous for the natural topology on the
algebraic \(A_{\psi}(C)\).
-/
theorem zcDiffModuleRelSubmoduleClosed_of_closedGenCoord_stage_factorization_of_fundFormula
    [T1Space (ZCFreeFoxCoordinates C (X := X) (H := H))]
    (hH : ProCGroups.ProC.HasOpenNormalBasisInClass C (H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOneAlongOpenSubgroups
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i))))
    (hfundamental :
      ∀ g : G,
        presentedCompletedDifferentialFamilyMapProCInteger
            (G := G) (H := H) C psi family
            (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
              (C := C) hfree (fun i : X => psi (family i)) htarget hφconv g) =
          zcUniversalDifferential C psi.toMonoidHom g) :
    (∀ (x : X) (j : ZCCompletedGroupAlgebraIndex C H),
        ∃ i : ZCCompletedDifferentialModuleIndex
            C psi.toMonoidHom,
          ∃ stageCoord :
            ZCCompletedDifferentialModuleStage
                C psi.toMonoidHom i →
              ZCCompletedGroupAlgebraStage C H j,
            ∀ a :
              ZCCompletedDifferentialModule C psi.toMonoidHom,
              zcCompletedGroupAlgebraProjection C H j
                  (closedGeneratedDerivativeCoordinatesLinearMapProCInteger
                    (G := G) (H := H) C psi family hfree htarget hφconv
                    hH hφHconv hφHgen a x) =
                stageCoord
                  (zcCompletedDifferentialModuleStageProjection
                    C psi.toMonoidHom i a)) →
    zcCompletedDifferentialModuleRelationSubmoduleClosed
      C psi.toMonoidHom := by
  intro hfactor
  refine
    zcDiffRelSubmoduleClosed_of_closedGenCoord_fundFormula
      (G := G) (H := H) C psi family hfree htarget hφconv
      hH hφHconv hφHgen hfundamental ?_
  have hcoord :=
    continuous_closedGenDerivCoordsZC_of_stageFactorization
      (G := G) (H := H) C psi family hfree htarget hφconv
      hH hφHconv hφHgen hfactor
  have hmap :=
    closedGenDerivativeCoordinateLinearEquivZC_of_fundFormula_toLinearMap
      (G := G) (H := H) C psi family hfree htarget hφconv
      hH hφHconv hφHgen hfundamental
  simpa [hmap] using hcoord

/--
Closedness from the completed fundamental formula once the source is a concrete pro-\(C\)
group. The finite-stage factorization is supplied internally by the open-normal pro-\(C\) basis
of the source, so the only remaining mathematical input is the non-circular module-valued
fundamental formula.
-/
theorem zcDiffModuleRelSubmoduleClosed_of_closedGenCoord_hasOpenNormalBasisInClass_of_fundFormula
    [T1Space (ZCFreeFoxCoordinates C (X := X) (H := H))]
    (hGbasis : ProCGroups.ProC.HasOpenNormalBasisInClass C (G))
    (hH : ProCGroups.ProC.HasOpenNormalBasisInClass C (H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOneAlongOpenSubgroups
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i))))
    (hfundamental :
      ∀ g : G,
        presentedCompletedDifferentialFamilyMapProCInteger
            (G := G) (H := H) C psi family
            (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
              (C := C) hfree (fun i : X => psi (family i)) htarget hφconv g) =
          zcUniversalDifferential C psi.toMonoidHom g) :
    zcCompletedDifferentialModuleRelationSubmoduleClosed
      C psi.toMonoidHom :=
  zcDiffModuleRelSubmoduleClosed_of_closedGenCoord_stage_factorization_of_fundFormula
    (G := G) (H := H) C psi family hfree htarget hφconv
    hH hφHconv hφHgen hfundamental
    (fun x j =>
      closedGenDerivativeCoordinatesLinearMapZC_stage_factorization_of_hasOpenNormalBasisInClass
        (G := G) (H := H) C psi family hfree htarget hφconv hGbasis
        hH hφHconv hφHgen x j)

/--
The closed-generated coordinate equivalence sends the universal differential of \(g\) to the
completed Fox-derivative coordinate vector of \(g\).
-/
@[simp 900]
theorem closedGenDerivativeCoordinateLinearEquivZC_of_fundFormula_universal
    (hH : ProCGroups.ProC.HasOpenNormalBasisInClass C (H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOneAlongOpenSubgroups
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i))))
    (hfundamental :
      ∀ g : G,
        presentedCompletedDifferentialFamilyMapProCInteger
            (G := G) (H := H) C psi family
            (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
              (C := C) hfree (fun i : X => psi (family i)) htarget hφconv g) =
          zcUniversalDifferential C psi.toMonoidHom g)
    (g : G) :
    closedGeneratedDerivativeCoordinateLinearEquivProCInteger_of_fundamental_formula
        (G := G) (H := H) C psi family hfree htarget hφconv
        hH hφHconv hφHgen hfundamental
        (zcUniversalDifferential C psi.toMonoidHom g) =
      freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
        (C := C) hfree (fun i : X => psi (family i)) htarget hφconv g := by
  have hmap :=
    congrArg
      (fun L :
          ZCCompletedDifferentialModule C psi.toMonoidHom
            →ₗ[ZCCompletedGroupAlgebra C H]
              ZCFreeFoxCoordinates C (X := X) (H := H) =>
        L (zcUniversalDifferential C psi.toMonoidHom g))
      (closedGenDerivativeCoordinateLinearEquivZC_of_fundFormula_toLinearMap
        (G := G) (H := H) C psi family hfree htarget hφconv
        hH hφHconv hφHgen hfundamental)
  calc
    closedGeneratedDerivativeCoordinateLinearEquivProCInteger_of_fundamental_formula
        (G := G) (H := H) C psi family hfree htarget hφconv
        hH hφHconv hφHgen hfundamental
        (zcUniversalDifferential C psi.toMonoidHom g)
        =
      closedGeneratedDerivativeCoordinatesLinearMapProCInteger
        (G := G) (H := H) C psi family hfree htarget hφconv
        hH hφHconv hφHgen
        (zcUniversalDifferential C psi.toMonoidHom g) := hmap
    _ =
      freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
        (C := C) hfree (fun i : X => psi (family i)) htarget hφconv g := by
        exact closedGeneratedDerivativeCoordinatesLinearMapProCInteger_universal
          (G := G) (H := H) C psi family hfree htarget hφconv
          hH hφHconv hφHgen g

end ClosedGeneratedCoordinateEquiv

end

end CrowellExactSequence
