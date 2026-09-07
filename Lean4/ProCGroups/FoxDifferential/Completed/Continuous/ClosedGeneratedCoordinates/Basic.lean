import ProCGroups.FoxDifferential.Completed.Continuous.PresentedCoordinates
import ProCGroups.FoxDifferential.Completed.Continuous.TopologicalGeneration

set_option autoImplicit false

/-!
# Fox differential: completed — continuous — closed generated coordinates — basic

The principal declarations in this module are:

- `closedGeneratedDerivativeCoordinatesLinearMapProCIntegerOfRightHom`
  The closed-generated Fox vector, read as a crossed differential with the intended scalar \(\psi\),
  gives a linear map from \(A_{\psi}(C)\) to finite completed Fox coordinates.
- `closedGeneratedDerivativeCoordinatesLinearMapProCInteger`
  Closed-generated coordinates with the right component identified by the epimorphic
  generated-target lifting property.
- `continuous_closedGenerated_module_expansion_naturalTopology`
  The closed-generated expansion into \(A_{\psi}(C)\) is continuous for the finite-stage completed
  topology on \(A_{\psi}(C)\).
- `closedGeneratedDerivativeCoordinatesLinearMapProCIntegerOfRightHom_universal`
  Evaluation of the closed-generated coordinate lift on universal differentials.
-/

namespace CrowellExactSequence

noncomputable section

open scoped BigOperators
open FoxDifferential

universe u v w

variable {G H : Type u}
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

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
The closed-generated expansion into \(A_{\psi}(C)\) is continuous for the finite-stage
completed topology on \(A_{\psi}(C)\).
-/
theorem continuous_closedGenerated_module_expansion_naturalTopology :
    @Continuous G
      (ZCCompletedDifferentialModule C psi.toMonoidHom)
      inferInstance
      (zcCompletedDifferentialModuleNaturalTopology
        C psi.toMonoidHom)
      (fun g : G =>
        presentedCompletedDifferentialFamilyMapProCInteger
          (G := G) (H := H) C psi family
          (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
            (C := C) hfree (fun i : X => psi (family i)) htarget hφconv g)) := by
  let : TopologicalSpace
      (ZCCompletedDifferentialModule C psi.toMonoidHom) :=
    zcCompletedDifferentialModuleNaturalTopology C psi.toMonoidHom
  change Continuous
    (fun g : G =>
      presentedCompletedDifferentialFamilyMapProCInteger
        (G := G) (H := H) C psi family
        (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
          (C := C) hfree (fun i : X => psi (family i)) htarget hφconv g))
  exact
    (continuous_presentedCompletedDifferentialFamilyMapProCInteger_naturalTopology
      (G := G) (H := H) C psi family).comp
      (continuous_freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
        (C := C) X H hfree (fun i : X => psi (family i)) htarget hφconv)

/--
The closed-generated Fox vector, read as a crossed differential with the intended scalar
\(\psi\), gives a linear map from \(A_{\psi}(C)\) to finite completed Fox coordinates.
-/
def closedGeneratedDerivativeCoordinatesLinearMapProCIntegerOfRightHom
    (hright :
      freeProCZCCompletedFoxRightHomViaClosedGenerated
          (C := C) hfree (fun i : X => psi (family i)) htarget hφconv =
        psi.toMonoidHom) :
      ZCCompletedDifferentialModule C psi.toMonoidHom →ₗ[
      ZCCompletedGroupAlgebra C H]
      ZCFreeFoxCoordinates C (X := X) (H := H) :=
  crossedHomModuleLift
    (A := ZCFreeFoxCoordinates C (X := X) (H := H))
    (zcCompletedGroupAlgebraScalar C psi.toMonoidHom)
    { toFun := fun g =>
        freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
          (C := C) hfree (fun i : X => psi (family i)) htarget hφconv g
      map_mul' := by
        intro g h
        rw [← hright]
        exact
          ScalarCrossedHom.map_mul
            (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
              (C := C) hfree (fun i : X => psi (family i)) htarget hφconv)
            g h }

omit [Fintype X] in
/-- Evaluation of the closed-generated coordinate lift on universal differentials. -/
@[simp]
theorem closedGeneratedDerivativeCoordinatesLinearMapProCIntegerOfRightHom_universal
    (hright :
      freeProCZCCompletedFoxRightHomViaClosedGenerated
          (C := C) hfree (fun i : X => psi (family i)) htarget hφconv =
        psi.toMonoidHom)
    (g : G) :
    closedGeneratedDerivativeCoordinatesLinearMapProCIntegerOfRightHom
        (G := G) (H := H) C psi family hfree htarget hφconv hright
        (zcUniversalDifferential C psi.toMonoidHom g) =
      freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
        (C := C) hfree (fun i : X => psi (family i)) htarget hφconv g := by
  change
    crossedHomModuleLift
        (zcCompletedGroupAlgebraScalar C psi.toMonoidHom) _
        (universalCrossedDifferential
          (zcCompletedGroupAlgebraScalar C psi.toMonoidHom) g) =
      freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
        (C := C) hfree (fun i : X => psi (family i)) htarget hφconv g
  rw [crossedHomModuleLift_universal]
  rfl
/-- The closed-generated coordinate lift is a left inverse to the family map. -/
theorem closedGenDerivativeCoordinatesLinearMapZCOfRightHom_comp_familyMap
    (hright :
      freeProCZCCompletedFoxRightHomViaClosedGenerated
          (C := C) hfree (fun i : X => psi (family i)) htarget hφconv =
        psi.toMonoidHom) :
    (closedGeneratedDerivativeCoordinatesLinearMapProCIntegerOfRightHom
        (G := G) (H := H) C psi family hfree htarget hφconv hright).comp
      (presentedCompletedDifferentialFamilyMapProCInteger
        (G := G) (H := H) C psi family) =
    LinearMap.id := by
  let L :=
    closedGeneratedDerivativeCoordinatesLinearMapProCIntegerOfRightHom
      (G := G) (H := H) C psi family hfree htarget hφconv hright
  have hL_family :
      ∀ i : X,
        L (zcUniversalDifferential C psi.toMonoidHom (family i)) =
          Pi.single i (1 : ZCCompletedGroupAlgebra C H) := by
    intro i
    calc
      L (zcUniversalDifferential C psi.toMonoidHom (family i)) =
          freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
            (C := C) hfree (fun i : X => psi (family i)) htarget hφconv
            (family i) := by
            simpa [L] using
              closedGeneratedDerivativeCoordinatesLinearMapProCIntegerOfRightHom_universal
                (G := G) (H := H) C psi family hfree htarget hφconv hright
                (family i)
      _ = Pi.single i (1 : ZCCompletedGroupAlgebra C H) := by
          simp only [freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated_generator]
  simpa [L, presentedCompletedDifferentialFamilyMapProCInteger,
    finiteFamilyLinearMap] using
    (finiteFamilyLinearMap_leftInverse_of_mapsToSingle
      (R := ZCCompletedGroupAlgebra C H)
      (generators := fun i : X =>
        zcUniversalDifferential C psi.toMonoidHom (family i))
      L hL_family)

/-- Closed-generated coordinates with the right component identified by the epimorphic
generated-target lifting property. -/
def closedGeneratedDerivativeCoordinatesLinearMapProCInteger
    (hH : ProCGroups.ProC.HasOpenNormalBasisInClass C (H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOneAlongOpenSubgroups
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i)))) :
    ZCCompletedDifferentialModule C psi.toMonoidHom →ₗ[
      ZCCompletedGroupAlgebra C H]
      ZCFreeFoxCoordinates C (X := X) (H := H) :=
  closedGeneratedDerivativeCoordinatesLinearMapProCIntegerOfRightHom
    (G := G) (H := H) C psi family hfree htarget hφconv
    (freeProCZCCompletedFoxRightHomViaClosedGenerated_eq_continuousHom
      (C := C) X H hfree hH (fun i : X => psi (family i)) htarget hφconv
      hφHconv hφHgen psi (by intro i; rfl))

omit [Fintype X] in
/--
The closed-generated coordinate map sends the universal completed differential of `g` to the
closed-generated Fox derivative vector of `g`.
-/
@[simp]
theorem closedGeneratedDerivativeCoordinatesLinearMapProCInteger_universal
    (hH : ProCGroups.ProC.HasOpenNormalBasisInClass C (H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOneAlongOpenSubgroups
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i))))
    (g : G) :
    closedGeneratedDerivativeCoordinatesLinearMapProCInteger
        (G := G) (H := H) C psi family hfree htarget hφconv
        hH hφHconv hφHgen
        (zcUniversalDifferential C psi.toMonoidHom g) =
      freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
        (C := C) hfree (fun i : X => psi (family i)) htarget hφconv g := by
  unfold closedGeneratedDerivativeCoordinatesLinearMapProCInteger
  exact
    closedGeneratedDerivativeCoordinatesLinearMapProCIntegerOfRightHom_universal
      (G := G) (H := H) C psi family hfree htarget hφconv
      (freeProCZCCompletedFoxRightHomViaClosedGenerated_eq_continuousHom
        (C := C) X H hfree hH (fun i : X => psi (family i)) htarget hφconv
        hφHconv hφHgen psi (by intro i; rfl))
      g
omit [Fintype X] in
/--
The coordinate map \(A_{\psi}(C) \to \mathbb{Z}_C\llbracket H\rrbracket^{X}\) is continuous for
the natural finite-stage topology when every finite coefficient coordinate factors through a
finite source, target, and coefficient stage.
-/
theorem continuous_closedGenDerivCoordsZC_of_stageFactorization
    (hH : ProCGroups.ProC.HasOpenNormalBasisInClass C (H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOneAlongOpenSubgroups
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i))))
    (hfactor :
      ∀ (x : X) (j : ZCCompletedGroupAlgebraIndex C H),
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
                    C psi.toMonoidHom i a)) :
    @Continuous
      (ZCCompletedDifferentialModule C psi.toMonoidHom)
      (ZCFreeFoxCoordinates C (X := X) (H := H))
      (zcCompletedDifferentialModuleNaturalTopology
        C psi.toMonoidHom)
      inferInstance
      (closedGeneratedDerivativeCoordinatesLinearMapProCInteger
        (G := G) (H := H) C psi family hfree htarget hφconv
        hH hφHconv hφHgen) := by
  let : TopologicalSpace
      (ZCCompletedDifferentialModule C psi.toMonoidHom) :=
    zcCompletedDifferentialModuleNaturalTopology
      C psi.toMonoidHom
  let L :=
    closedGeneratedDerivativeCoordinatesLinearMapProCInteger
      (G := G) (H := H) C psi family hfree htarget hφconv
      hH hφHconv hφHgen
  change @Continuous
    (ZCCompletedDifferentialModule C psi.toMonoidHom)
    (X → ZCCompletedGroupAlgebra C H)
    (zcCompletedDifferentialModuleNaturalTopology
      C psi.toMonoidHom)
    inferInstance L
  refine continuous_pi fun x => ?_
  refine Continuous.subtype_mk (p := ZCCompletedGroupAlgebraCompatible
    C H) ?_ (fun a => (L a x).property)
  refine continuous_pi fun j => ?_
  rcases hfactor x j with ⟨i, stageCoord, hstageCoord⟩
  let : TopologicalSpace
      (ZCCompletedDifferentialModuleStage
        C psi.toMonoidHom i) := inferInstance
  let : DiscreteTopology
      (ZCCompletedDifferentialModuleStage
        C psi.toMonoidHom i) := inferInstance
  have hstage : Continuous stageCoord := continuous_of_discreteTopology
  have hproj :
      @Continuous
        (ZCCompletedDifferentialModule C psi.toMonoidHom)
        (ZCCompletedDifferentialModuleStage
          C psi.toMonoidHom i)
        (zcCompletedDifferentialModuleNaturalTopology
          C psi.toMonoidHom)
        inferInstance
        (zcCompletedDifferentialModuleStageProjection
          C psi.toMonoidHom i) :=
    continuous_zcCompletedDifferentialModuleStageProjection_naturalTopology
      C psi.toMonoidHom i
  have hcomp : Continuous
      (fun a :
        ZCCompletedDifferentialModule C psi.toMonoidHom =>
        stageCoord
          (zcCompletedDifferentialModuleStageProjection
            C psi.toMonoidHom i a)) :=
    hstage.comp hproj
  have hfun :
      (fun a :
        ZCCompletedDifferentialModule C psi.toMonoidHom =>
        zcCompletedGroupAlgebraProjection C H j (L a x)) =
      (fun a :
        ZCCompletedDifferentialModule C psi.toMonoidHom =>
        stageCoord
          (zcCompletedDifferentialModuleStageProjection
            C psi.toMonoidHom i a)) := by
    funext a
    simpa [L] using hstageCoord a
  change Continuous
    (fun a :
      ZCCompletedDifferentialModule C psi.toMonoidHom =>
      zcCompletedGroupAlgebraProjection C H j (L a x))
  rw [hfun]
  exact hcomp

omit [Fintype X] in
/--
Concrete finite-stage factorization of each closed-generated coordinate. For a fixed coordinate
x and finite coefficient/target stage j, the scalar-valued closed-generated Fox derivative is
locally unchanged at \(1\) after intersecting with the target kernel. The pro-\(C\) open-normal
basis supplies a source quotient in the same finite quotient class, and the
crossed-differential rule descends the coordinate to that quotient.
-/
theorem closedGenDerivativeCoordinatesLinearMapZC_stage_factorization_of_hasOpenNormalBasisInClass
    (hGbasis : ProCGroups.ProC.HasOpenNormalBasisInClass C (G))
    (hH : ProCGroups.ProC.HasOpenNormalBasisInClass C (H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOneAlongOpenSubgroups
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i))))
    (x : X) (j : ZCCompletedGroupAlgebraIndex C H) :
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
                C psi.toMonoidHom i a) := by
  let C := C
  let φ : X → H := fun i => psi (family i)
  let L :=
    closedGeneratedDerivativeCoordinatesLinearMapProCInteger
      (G := G) (H := H) C psi family hfree htarget hφconv
      hH hφHconv hφHgen
  let coordStage :
      ZCFreeFoxCoordinates C (X := X) (H := H) →ₗ[ZCCompletedGroupAlgebra C H]
        ZCCompletedGroupAlgebraStage C H j :=
    {
    toFun v := zcCompletedGroupAlgebraProjection C H j (v x)
    map_add' v w := by
      simp only [Pi.add_apply, zcCompletedGroupAlgebraProjection_add]
    map_smul' r v := by
      change zcCompletedGroupAlgebraProjection C H j (r * v x) =
        zcCompletedGroupAlgebraProjection C H j r *
          zcCompletedGroupAlgebraProjection C H j (v x)
      exact zcCompletedGroupAlgebraProjection_mul C H j r (v x)
    }
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
        intro g h
        rw [← hright]
        exact
          ScalarCrossedHom.map_mul
            (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
              (C := C) hfree φ htarget hφconv) g h }
  let D : ScalarCrossedHom
      (zcCompletedGroupAlgebraScalar C psi.toMonoidHom)
      (ZCCompletedGroupAlgebraStage C H j) :=
    Dclosed.mapLinear coordStage
  have hDcont : Continuous D := by
    have hvec :
        Continuous Dclosed := by
      change Continuous
        (fun g : G =>
          freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
            (C := C) hfree φ htarget hφconv g)
      exact
        (continuous_freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
          (C := C) X H hfree φ htarget hφconv)
    have hcoord : Continuous (fun g : G => Dclosed g x) :=
      (continuous_apply x).comp hvec
    have hproj :
        Continuous (fun a : ZCCompletedGroupAlgebra C H =>
          zcCompletedGroupAlgebraProjection C H j a) :=
      continuous_zcCompletedGroupAlgebraProjection C H j
    change Continuous
      (fun g : G =>
        zcCompletedGroupAlgebraProjection C H j (Dclosed g x))
    exact hproj.comp hcoord
  let Utarget : OpenNormalSubgroup H := (OrderDual.ofDual j.2).1
  let W : Set G :=
    {g : G | D g = 0 ∧ psi.toMonoidHom g ∈ (Utarget : Subgroup H)}
  have hDzero_open : IsOpen {g : G | D g = 0} := by
    change IsOpen (D ⁻¹' ({0} : Set (ZCCompletedGroupAlgebraStage C H j)))
    exact (isOpen_discrete _).preimage hDcont
  have htarget_open :
      IsOpen {g : G | psi.toMonoidHom g ∈ (Utarget : Subgroup H)} := by
    change IsOpen (psi ⁻¹' (((Utarget : Subgroup H) : Set H)))
    exact (ProCGroups.openNormalSubgroup_isOpen (G := H) Utarget).preimage
      psi.continuous_toFun
  have hWopen : IsOpen W := hDzero_open.inter htarget_open
  have h1W : (1 : G) ∈ W := by
    constructor
    · exact ScalarCrossedHom.map_one D
    · simp only [ContinuousMonoidHom.coe_toMonoidHom, map_one, one_mem, Utarget]
  rcases hGbasis.exists_openNormalSubgroupInClass_sub_open_nhds_of_one hWopen h1W with
    ⟨V, hVW⟩
  let i : ZCCompletedDifferentialModuleIndex C psi.toMonoidHom :=
    { source := V
      target := j
      compatible := by
        intro g hg
        exact (hVW hg).2 }
  have hD_eq_of_mem :
      ∀ a b : G, a⁻¹ * b ∈ (V.1 : Subgroup G) → D a = D b := by
    intro a b hab
    have hzero : D (a⁻¹ * b) = 0 := (hVW hab).1
    have hmul := ScalarCrossedHom.map_mul D a (a⁻¹ * b)
    have habmul : a * (a⁻¹ * b) = b := by simp only [mul_inv_cancel_left]
    symm
    calc
      D b = D (a * (a⁻¹ * b)) := by rw [habmul]
      _ = D a + zcCompletedGroupAlgebraScalar C psi.toMonoidHom a •
            D (a⁻¹ * b) := hmul
      _ = D a := by rw [hzero, smul_zero, add_zero]
  let Dstage : ScalarCrossedHom
      (zcCompletedDifferentialModuleStageScalar C psi.toMonoidHom i)
      (ZCCompletedGroupAlgebraStage C H j) :=
    { toFun := fun q => Quotient.liftOn' q D (by
        intro a b hab
        have habi : a⁻¹ * b ∈ (i.source.1 : Subgroup G) := by
          have hq : (a : G ⧸ (i.source.1 : Subgroup G)) = b := Quotient.sound' hab
          exact QuotientGroup.eq.1 hq
        exact hD_eq_of_mem a b (by simpa [i] using habi))
      map_mul' := by
        intro q r
        refine QuotientGroup.induction_on q ?_
        intro a
        refine QuotientGroup.induction_on r ?_
        intro b
        change D (a * b) =
          D a + zcCompletedDifferentialModuleStageScalar C psi.toMonoidHom i
            (QuotientGroup.mk' (i.source.1 : Subgroup G) a) • D b
        have hscalar :
            zcCompletedDifferentialModuleStageScalar C psi.toMonoidHom i
                (QuotientGroup.mk' (i.source.1 : Subgroup G) a) =
              zcCompletedGroupAlgebraProjectionRingHom C H j
                (zcCompletedGroupAlgebraScalar C psi.toMonoidHom a) := by
          dsimp [i, C, zcCompletedGroupAlgebraScalar]
          rfl
        have h := ScalarCrossedHom.map_mul D a b
        change D (a * b) =
          D a + zcCompletedGroupAlgebraProjectionRingHom C H j
            (zcCompletedGroupAlgebraScalar C psi.toMonoidHom a) • D b at h
        rw [hscalar]
        exact h }
  let stageCoordFinite :
      ZCCompletedDifferentialModuleStage C psi.toMonoidHom i →ₗ[
        zcCompletedDifferentialModuleStageRing C psi.toMonoidHom i]
        ZCCompletedGroupAlgebraStage C H j :=
    crossedHomModuleLift
      (A := ZCCompletedGroupAlgebraStage C H j)
      (zcCompletedDifferentialModuleStageScalar C psi.toMonoidHom i)
      Dstage
  let : Module (ZCCompletedGroupAlgebra C H)
      (ZCCompletedDifferentialModuleStage C psi.toMonoidHom i) :=
    Module.compHom _ (zcCompletedGroupAlgebraProjectionRingHom C H i.target)
  let stageCoordLinear :
      ZCCompletedDifferentialModuleStage C psi.toMonoidHom i →ₗ[
        ZCCompletedGroupAlgebra C H]
        ZCCompletedGroupAlgebraStage C H j :=
    {
    toFun := stageCoordFinite
    map_add' m n := by
      exact map_add stageCoordFinite m n
    map_smul' r m := by
      change stageCoordFinite
          ((zcCompletedGroupAlgebraProjectionRingHom C H i.target r) • m) =
        (zcCompletedGroupAlgebraProjectionRingHom C H i.target r) • stageCoordFinite m
      exact map_smul stageCoordFinite
        (zcCompletedGroupAlgebraProjectionRingHom C H i.target r) m
    }
  have hcomp :
      stageCoordLinear.comp
          (zcCompletedDifferentialModuleStageProjection C psi.toMonoidHom i) =
        coordStage.comp L := by
    apply crossedDifferentialModuleHom_ext
      (A := ZCCompletedGroupAlgebraStage C H j)
      (zcCompletedGroupAlgebraScalar C psi.toMonoidHom)
    intro g
    change stageCoordLinear
        (zcCompletedDifferentialModuleStageProjection C psi.toMonoidHom i
          (zcUniversalDifferential C psi.toMonoidHom g)) =
      coordStage (L (zcUniversalDifferential C psi.toMonoidHom g))
    calc
      stageCoordLinear
          (zcCompletedDifferentialModuleStageProjection C psi.toMonoidHom i
            (zcUniversalDifferential C psi.toMonoidHom g)) =
      stageCoordFinite
          (zcCompletedDifferentialModuleStageDifferential C psi.toMonoidHom i g) := by
            rw [zcCompletedDifferentialModuleStageProjection_universal]
            rfl
      _ = Dstage (zcCompletedDifferentialModuleStageSourceProj C psi.toMonoidHom i g) := by
        change
          crossedHomModuleLift
              (zcCompletedDifferentialModuleStageScalar C psi.toMonoidHom i)
              Dstage
              (universalCrossedDifferential
                (zcCompletedDifferentialModuleStageScalar C psi.toMonoidHom i)
                (zcCompletedDifferentialModuleStageSourceProj
                  C psi.toMonoidHom i g)) =
            Dstage
              (zcCompletedDifferentialModuleStageSourceProj C psi.toMonoidHom i g)
        rw [crossedHomModuleLift_universal]
      _ = D g := by
            rfl
      _ = coordStage (Dclosed g) := rfl
      _ = coordStage (L (zcUniversalDifferential C psi.toMonoidHom g)) := by
            change
              coordStage
                  (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
                    (C := C) hfree φ htarget hφconv g) =
                coordStage (L (zcUniversalDifferential C psi.toMonoidHom g))
            rw [closedGeneratedDerivativeCoordinatesLinearMapProCInteger_universal
              (G := G) (H := H) C psi family hfree htarget hφconv
              hH hφHconv hφHgen g]
  refine ⟨i, fun m => stageCoordLinear m, ?_⟩
  intro a
  have h := congrArg (fun f => f a) hcomp
  change coordStage (L a) =
    stageCoordLinear
      (zcCompletedDifferentialModuleStageProjection C psi.toMonoidHom i a)
  exact h.symm

omit [Fintype X] in
/--
The closed-generated coordinate lift is continuous for the natural finite-stage topology once
the source is a concrete pro-\(C\) group.
-/
theorem continuous_closedGenDerivativeCoordinatesLinearMapZC_naturalTopology_of_openNormalBasis
    (hGbasis : ProCGroups.ProC.HasOpenNormalBasisInClass C (G))
    (hH : ProCGroups.ProC.HasOpenNormalBasisInClass C (H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOneAlongOpenSubgroups
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i)))) :
    @Continuous
      (ZCCompletedDifferentialModule C psi.toMonoidHom)
      (ZCFreeFoxCoordinates C (X := X) (H := H))
      (zcCompletedDifferentialModuleNaturalTopology
        C psi.toMonoidHom)
      inferInstance
      (closedGeneratedDerivativeCoordinatesLinearMapProCInteger
        (G := G) (H := H) C psi family hfree htarget hφconv
        hH hφHconv hφHgen) :=
  continuous_closedGenDerivCoordsZC_of_stageFactorization
    (G := G) (H := H) C psi family hfree htarget hφconv hH hφHconv hφHgen
    (fun x j =>
      closedGenDerivativeCoordinatesLinearMapZC_stage_factorization_of_hasOpenNormalBasisInClass
        (G := G) (H := H) C psi family hfree htarget hφconv hGbasis
        hH hφHconv hφHgen x j)

omit [Fintype X] in
/--
The pre-quotient closed-generated coordinate lift is continuous for the finite-stage pre-module
topology once the source is a concrete pro-\(C\) group.
-/
theorem continuous_closedGenDerivativeCoordinatesPreliftZC_naturalTopology_of_openNormalBasis
    (hGbasis : ProCGroups.ProC.HasOpenNormalBasisInClass C (G))
    (hH : ProCGroups.ProC.HasOpenNormalBasisInClass C (H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOneAlongOpenSubgroups
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i)))) :
    @Continuous
      (CrossedDifferentialPreModule
        (ZCCompletedGroupAlgebra C H) G)
      (ZCFreeFoxCoordinates C (X := X) (H := H))
      (zcCompletedDifferentialPreModuleNaturalTopology
        C psi.toMonoidHom)
      inferInstance
      (crossedDifferentialModuleLiftLinear
        (R := ZCCompletedGroupAlgebra C H)
        (fun g : G =>
          freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
            (C := C) hfree (fun i : X => psi (family i)) htarget hφconv g)) := by
  let C := C
  let : TopologicalSpace
      (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G) :=
    zcCompletedDifferentialPreModuleNaturalTopology C psi.toMonoidHom
  let : TopologicalSpace (ZCCompletedDifferentialModule C psi.toMonoidHom) :=
    zcCompletedDifferentialModuleNaturalTopology C psi.toMonoidHom
  let Dclosed : G → ZCFreeFoxCoordinates C (X := X) (H := H) :=
    fun g =>
      freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
        (C := C) hfree (fun i : X => psi (family i)) htarget hφconv g
  let L :=
    closedGeneratedDerivativeCoordinatesLinearMapProCInteger
      (G := G) (H := H) C psi family hfree htarget hφconv hH hφHconv hφHgen
  let q :
      CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G →ₗ[
        ZCCompletedGroupAlgebra C H]
        ZCFreeFoxCoordinates C (X := X) (H := H) :=
    L.comp
      (crossedDifferentialRelationSubmodule
        (zcCompletedGroupAlgebraScalar C psi.toMonoidHom)).mkQ
  have hqcont :
      @Continuous
        (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)
        (ZCFreeFoxCoordinates C (X := X) (H := H))
        (zcCompletedDifferentialPreModuleNaturalTopology C psi.toMonoidHom)
        inferInstance q := by
    have hLcont :=
      continuous_closedGenDerivativeCoordinatesLinearMapZC_naturalTopology_of_openNormalBasis
        (G := G) (H := H) C psi family hfree htarget hφconv
        hGbasis hH hφHconv hφHgen
    have hmk :=
      continuous_zcCompletedDifferentialModule_mkQ_naturalTopology
        C psi.toMonoidHom
    exact hLcont.comp hmk
  have hq :
      q =
        crossedDifferentialModuleLiftLinear
          (R := ZCCompletedGroupAlgebra C H) Dclosed := by
    apply Finsupp.lhom_ext
    intro g r
    have hsingle :
        ((crossedDifferentialRelationSubmodule
          (zcCompletedGroupAlgebraScalar C psi.toMonoidHom)).mkQ
            (Finsupp.single g r) :
          ZCCompletedDifferentialModule C psi.toMonoidHom) =
          r • zcUniversalDifferential C psi.toMonoidHom g := by
      rw [← Finsupp.smul_single_one]
      rfl
    calc
      q (Finsupp.single g r) =
          L ((crossedDifferentialRelationSubmodule
            (zcCompletedGroupAlgebraScalar C psi.toMonoidHom)).mkQ
              (Finsupp.single g r)) := rfl
      _ = L (r • zcUniversalDifferential C psi.toMonoidHom g) := by
            rw [hsingle]
      _ = r • L (zcUniversalDifferential C psi.toMonoidHom g) := by
            rw [map_smul]
      _ = r • Dclosed g := by
            rw [closedGeneratedDerivativeCoordinatesLinearMapProCInteger_universal]
      _ =
          crossedDifferentialModuleLiftLinear
            (R := ZCCompletedGroupAlgebra C H) Dclosed (Finsupp.single g r) := by
            rw [crossedDifferentialModuleLiftLinear_single]
  rw [hq] at hqcont
  simpa [C, Dclosed] using hqcont

omit [Fintype X] in
/-- Closed-generated coordinates as a map out of the separated completed differential module. -/
def separatedClosedGeneratedDerivativeCoordinatesLinearMapProCInteger
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
    ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom →ₗ[
      ZCCompletedGroupAlgebra C H]
      ZCFreeFoxCoordinates C (X := X) (H := H) := by
  let C := C
  have hright :
      freeProCZCCompletedFoxRightHomViaClosedGenerated
          (C := C) hfree (fun i : X => psi (family i)) htarget hφconv =
        psi.toMonoidHom :=
    freeProCZCCompletedFoxRightHomViaClosedGenerated_eq_continuousHom
      (C := C) X H hfree hH (fun i : X => psi (family i)) htarget hφconv
      hφHconv hφHgen psi (by intro i; rfl)
  let Dclosed : ScalarCrossedHom
      (zcCompletedGroupAlgebraScalar C psi.toMonoidHom)
      (ZCFreeFoxCoordinates C (X := X) (H := H)) :=
    { toFun := fun g =>
        freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
          (C := C) hfree (fun i : X => psi (family i)) htarget hφconv g
      map_mul' := by
        intro g h
        rw [← hright]
        exact
          ScalarCrossedHom.map_mul
            (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
              (C := C) hfree (fun i : X => psi (family i)) htarget hφconv)
            g h }
  exact
    zcSeparatedCompletedDifferentialModuleLiftOfContinuousPrelift
      C psi.toMonoidHom hdir Dclosed
      (by
        change
          @Continuous
            (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)
            (ZCFreeFoxCoordinates C (X := X) (H := H))
            (zcCompletedDifferentialPreModuleNaturalTopology C psi.toMonoidHom)
            inferInstance
            (crossedDifferentialModuleLiftLinear
              (R := ZCCompletedGroupAlgebra C H)
              (fun g : G =>
                freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
                  (C := C) hfree (fun i : X => psi (family i)) htarget hφconv g))
        exact
          continuous_closedGenDerivativeCoordinatesPreliftZC_naturalTopology_of_openNormalBasis
            (G := G) (H := H) C psi family hfree htarget hφconv
            hGbasis hH hφHconv hφHgen)

omit [Fintype X] in
/--
The separated closed-generated derivative-coordinate linear map has the stated universal
property over the pro-\(C\) integers.
-/
@[simp 900]
theorem separatedClosedGeneratedDerivativeCoordinatesLinearMapProCInteger_universal
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
    separatedClosedGeneratedDerivativeCoordinatesLinearMapProCInteger
        (G := G) (H := H) C psi family hfree htarget hφconv
        hdir hGbasis hH hφHconv hφHgen
        (zcSeparatedUniversalDifferential
          C psi.toMonoidHom g) =
      freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
        (C := C) hfree (fun i : X => psi (family i)) htarget hφconv g := by
  unfold separatedClosedGeneratedDerivativeCoordinatesLinearMapProCInteger
  exact
    zcSeparatedCompletedDifferentialModuleLiftOfContinuousPrelift_universal
      C psi.toMonoidHom hdir _ _ g

/--
The separated closed-generated coordinate lift is a left inverse to the separated finite family
map.
-/
theorem separatedClosedGeneratedDerivativeCoordinatesLinearMapProCInteger_comp_familyMap
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
    (separatedClosedGeneratedDerivativeCoordinatesLinearMapProCInteger
        (G := G) (H := H) C psi family hfree htarget hφconv
        hdir hGbasis hH hφHconv hφHgen).comp
      (presentedSeparatedDifferentialFamilyMapProCInteger
        (G := G) (H := H) C psi family) =
    LinearMap.id := by
  let L :=
    separatedClosedGeneratedDerivativeCoordinatesLinearMapProCInteger
      (G := G) (H := H) C psi family hfree htarget hφconv
      hdir hGbasis hH hφHconv hφHgen
  have hL_family :
      ∀ i : X,
        L (zcSeparatedUniversalDifferential
            C psi.toMonoidHom (family i)) =
          Pi.single i (1 : ZCCompletedGroupAlgebra C H) := by
    intro i
    calc
      L (zcSeparatedUniversalDifferential
          C psi.toMonoidHom (family i)) =
          freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
            (C := C) hfree (fun i : X => psi (family i)) htarget hφconv
            (family i) := by
            simpa [L] using
              separatedClosedGeneratedDerivativeCoordinatesLinearMapProCInteger_universal
                (G := G) (H := H) C psi family hfree htarget hφconv
                hdir hGbasis hH hφHconv hφHgen (family i)
      _ = Pi.single i (1 : ZCCompletedGroupAlgebra C H) := by
          simp only [freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated_generator]
  simpa [L, presentedSeparatedDifferentialFamilyMapProCInteger,
    finiteFamilyLinearMap] using
    (finiteFamilyLinearMap_leftInverse_of_mapsToSingle
      (R := ZCCompletedGroupAlgebra C H)
      (generators := fun i : X =>
        zcSeparatedUniversalDifferential
          C psi.toMonoidHom (family i))
      L hL_family)

/--
Composing the closed-generated derivative-coordinate lift with the completed differential
family map is the identity.
-/
theorem closedGeneratedDerivativeCoordinatesLinearMapProCInteger_comp_familyMap
    (hH : ProCGroups.ProC.HasOpenNormalBasisInClass C (H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOneAlongOpenSubgroups
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i)))) :
    (closedGeneratedDerivativeCoordinatesLinearMapProCInteger
        (G := G) (H := H) C psi family hfree htarget hφconv
        hH hφHconv hφHgen).comp
      (presentedCompletedDifferentialFamilyMapProCInteger
        (G := G) (H := H) C psi family) =
    LinearMap.id := by
  unfold closedGeneratedDerivativeCoordinatesLinearMapProCInteger
  exact
    closedGenDerivativeCoordinatesLinearMapZCOfRightHom_comp_familyMap
      (G := G) (H := H) C psi family hfree htarget hφconv
    (freeProCZCCompletedFoxRightHomViaClosedGenerated_eq_continuousHom
      (C := C) X H hfree hH (fun i : X => psi (family i)) htarget hφconv
      hφHconv hφHgen psi (by intro i; rfl))

/-- The closed-generated fundamental formula after projection to any finite source, target, and
coefficient stage; no point-separation hypothesis for the stage projections of
\(A_{\psi}(C)\) is required. -/
theorem closedGenerated_fundamental_formula_stageProj
    (hH : ProCGroups.ProC.HasOpenNormalBasisInClass C (H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOneAlongOpenSubgroups
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i))))
    (i : ZCCompletedDifferentialModuleIndex
        C psi.toMonoidHom)
    (g : G) :
    zcCompletedDifferentialModuleStageProjection
        C psi.toMonoidHom i
        (presentedCompletedDifferentialFamilyMapProCInteger
          (G := G) (H := H) C psi family
          (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
            (C := C) hfree (fun i : X => psi (family i)) htarget hφconv g)) =
      zcCompletedDifferentialModuleStageProjection
        C psi.toMonoidHom i
        (zcUniversalDifferential C psi.toMonoidHom g) := by
  let C := C
  let φ : X → H := fun i => psi (family i)
  let M :=
    presentedCompletedDifferentialFamilyMapProCInteger
      (G := G) (H := H) C psi family
  let P := zcCompletedDifferentialModuleStageProjection C psi.toMonoidHom i
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
        intro g h
        rw [← hright]
        exact
          ScalarCrossedHom.map_mul
            (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
              (C := C) hfree φ htarget hφconv) g h }
  let Dstage : ScalarCrossedHom
      (zcCompletedGroupAlgebraScalar C psi.toMonoidHom)
      (ZCCompletedDifferentialModuleStage C psi.toMonoidHom i) :=
    Dclosed.mapLinear (P.comp M)
  have hstage_continuous : Continuous Dstage := by
    let : TopologicalSpace (ZCCompletedDifferentialModule C psi.toMonoidHom) :=
      zcCompletedDifferentialModuleNaturalTopology C psi.toMonoidHom
    have hmodule :
        @Continuous G
          (ZCCompletedDifferentialModule C psi.toMonoidHom)
          inferInstance
          (zcCompletedDifferentialModuleNaturalTopology C psi.toMonoidHom)
          (fun g : G => M (Dclosed g)) := by
      change Continuous
        (fun g : G =>
          presentedCompletedDifferentialFamilyMapProCInteger
            (G := G) (H := H) C psi family
            (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
              (C := C) hfree φ htarget hφconv g))
      exact
        (continuous_closedGenerated_module_expansion_naturalTopology
          (G := G) (H := H) C psi family hfree htarget hφconv)
    have hP :
        @Continuous
          (ZCCompletedDifferentialModule C psi.toMonoidHom)
          (ZCCompletedDifferentialModuleStage C psi.toMonoidHom i)
          (zcCompletedDifferentialModuleNaturalTopology C psi.toMonoidHom)
          inferInstance P := by
      simpa [C, P] using
        (continuous_zcCompletedDifferentialModuleStageProjection_naturalTopology
          C psi.toMonoidHom i)
    change Continuous (fun g : G => P (M (Dclosed g)))
    exact hP.comp hmodule
  have huniv_stage_continuous :
      Continuous (zcCompletedDifferentialModuleStageDifferential C psi.toMonoidHom i) := by
    let : TopologicalSpace (ZCCompletedDifferentialModule C psi.toMonoidHom) :=
      zcCompletedDifferentialModuleNaturalTopology C psi.toMonoidHom
    have huniv :
        @Continuous G
          (ZCCompletedDifferentialModule C psi.toMonoidHom)
          inferInstance
          (zcCompletedDifferentialModuleNaturalTopology C psi.toMonoidHom)
          (zcUniversalDifferential C psi.toMonoidHom) :=
      continuous_zcUniversalDifferential_naturalTopology C psi.toMonoidHom
    have hP :
        @Continuous
          (ZCCompletedDifferentialModule C psi.toMonoidHom)
          (ZCCompletedDifferentialModuleStage C psi.toMonoidHom i)
          (zcCompletedDifferentialModuleNaturalTopology C psi.toMonoidHom)
          inferInstance P := by
      simpa [C, P] using
        (continuous_zcCompletedDifferentialModuleStageProjection_naturalTopology
          C psi.toMonoidHom i)
    have hcomp : Continuous (fun g : G => P (zcUniversalDifferential C psi.toMonoidHom g)) :=
      hP.comp huniv
    have hfun :
        (fun g : G => P (zcUniversalDifferential C psi.toMonoidHom g)) =
          zcCompletedDifferentialModuleStageDifferential C psi.toMonoidHom i := by
      funext g
      change
        zcCompletedDifferentialModuleStageProjection C psi.toMonoidHom i
            (zcUniversalDifferential C psi.toMonoidHom g) =
          zcCompletedDifferentialModuleStageDifferential C psi.toMonoidHom i g
      exact zcCompletedDifferentialModuleStageProjection_universal
        C psi.toMonoidHom i g
    rw [← hfun]
    exact hcomp
  have hEq :
      Dstage =
        zcCompletedDifferentialModuleStageDifferential C psi.toMonoidHom i := by
    refine
      CrossedHom.eq_of_continuous_of_topologicallyGenerates
        Dstage
        (zcCompletedDifferentialModuleStageDifferential C psi.toMonoidHom i)
        hstage_continuous huniv_stage_continuous hfree.generates_range ?_
    rintro _ ⟨x, rfl⟩
    have hDclosed :
        Dclosed (family x) = Pi.single x (1 : ZCCompletedGroupAlgebra C H) := by
      change
        freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
            (C := C) hfree φ htarget hφconv (family x) =
          Pi.single x (1 : ZCCompletedGroupAlgebra C H)
      exact
        freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated_generator
          (C := C) hfree φ htarget hφconv x
    calc
      Dstage (family x) =
          P (M (Pi.single x (1 : ZCCompletedGroupAlgebra C H))) := by
            change P (M (Dclosed (family x))) =
              P (M (Pi.single x (1 : ZCCompletedGroupAlgebra C H)))
            rw [hDclosed]
      _ =
          P (zcUniversalDifferential C psi.toMonoidHom (family x)) := by
            simpa [M] using congrArg P
              (presentedCompletedDifferentialFamilyMapProCInteger_single
                (G := G) (H := H) C psi family x)
      _ =
          zcCompletedDifferentialModuleStageDifferential C psi.toMonoidHom i
            (family x) := by
            change
              zcCompletedDifferentialModuleStageProjection C psi.toMonoidHom i
                  (zcUniversalDifferential C psi.toMonoidHom (family x)) =
                zcCompletedDifferentialModuleStageDifferential
                  C psi.toMonoidHom i (family x)
            exact zcCompletedDifferentialModuleStageProjection_universal
              C psi.toMonoidHom i (family x)
  have hEqg :=
    congrArg
      (fun d : ScalarCrossedHom
        (zcCompletedGroupAlgebraScalar C psi.toMonoidHom)
        (ZCCompletedDifferentialModuleStage C psi.toMonoidHom i) => d g)
      hEq
  change Dstage g =
    P (zcUniversalDifferential C psi.toMonoidHom g)
  exact hEqg.trans
    (zcCompletedDifferentialModuleStageProjection_universal
      C psi.toMonoidHom i g).symm

/--
The separated finite family map is a left inverse to the separated closed-generated coordinate
lift.
-/
theorem presentedSepDifferentialFamilyMapZC_comp_sepClosedGenDerivativeCoordinatesLinearMapZC
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
    (presentedSeparatedDifferentialFamilyMapProCInteger
        (G := G) (H := H) C psi family).comp
      (separatedClosedGeneratedDerivativeCoordinatesLinearMapProCInteger
        (G := G) (H := H) C psi family hfree htarget hφconv
        hdir hGbasis hH hφHconv hφHgen) =
    LinearMap.id := by
  let C := C
  let Msep :=
    presentedSeparatedDifferentialFamilyMapProCInteger
      (G := G) (H := H) C psi family
  let M :=
    presentedCompletedDifferentialFamilyMapProCInteger
      (G := G) (H := H) C psi family
  let Lsep :=
    separatedClosedGeneratedDerivativeCoordinatesLinearMapProCInteger
      (G := G) (H := H) C psi family hfree htarget hφconv
      hdir hGbasis hH hφHconv hφHgen
  apply zcSeparatedCompletedDifferentialModuleHom_ext C psi.toMonoidHom
  intro g
  rw [LinearMap.comp_apply]
  change Msep (Lsep (zcSeparatedUniversalDifferential C psi.toMonoidHom g)) =
    zcSeparatedUniversalDifferential C psi.toMonoidHom g
  rw [separatedClosedGeneratedDerivativeCoordinatesLinearMapProCInteger_universal]
  have hzero :
      Msep
          (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
            (C := C) hfree (fun i : X => psi (family i)) htarget hφconv g) -
        zcSeparatedUniversalDifferential C psi.toMonoidHom g = 0 := by
    apply zcSeparatedCompletedDifferentialModuleStageProjectionsSeparate C psi.toMonoidHom
    intro i
    rw [map_sub, sub_eq_zero]
    calc
      zcSeparatedCompletedDifferentialModuleStageProjectionAdd C psi.toMonoidHom i
          (Msep
            (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
              (C := C) hfree (fun i : X => psi (family i)) htarget hφconv g)) =
          zcCompletedDifferentialModuleStageProjection C psi.toMonoidHom i
            (M
              (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
                (C := C) hfree (fun i : X => psi (family i)) htarget hφconv g)) := by
            have hstage :=
              zcSepDiffModuleStageProj_comp_presentedSepFamilyMap
                (G := G) (H := H) C psi family i
            have hstage_at :=
              congrArg
                (fun L : ZCFreeFoxCoordinates C (X := X) (H := H) →ₗ[
                    ZCCompletedGroupAlgebra C H]
                    ZCCompletedDifferentialModuleStage C psi.toMonoidHom i =>
                  L
                    (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
                      (C := C) hfree (fun i : X => psi (family i)) htarget hφconv g))
                hstage
            change
              zcSeparatedCompletedDifferentialModuleStageProjectionAdd
                  C psi.toMonoidHom i
                  (Msep
                    (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
                      (C := C) hfree (fun i : X => psi (family i)) htarget hφconv g)) =
                zcCompletedDifferentialModuleStageProjection
                  C psi.toMonoidHom i
                  (M
                    (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
                      (C := C) hfree (fun i : X => psi (family i)) htarget hφconv g))
              at hstage_at
            exact hstage_at
      _ =
          zcCompletedDifferentialModuleStageProjection C psi.toMonoidHom i
            (zcUniversalDifferential C psi.toMonoidHom g) := by
            exact
              closedGenerated_fundamental_formula_stageProj
                (G := G) (H := H) C psi family hfree htarget hφconv
                hH hφHconv hφHgen i g
      _ =
          zcSeparatedCompletedDifferentialModuleStageProjectionAdd C psi.toMonoidHom i
            (zcSeparatedUniversalDifferential C psi.toMonoidHom g) := by
            exact
              (zcCompletedDifferentialModuleStageProjection_universal
                C psi.toMonoidHom i g).trans
                (zcSeparatedCompletedDifferentialModuleStageProjectionAdd_universal
                  C psi.toMonoidHom i g).symm
  exact sub_eq_zero.mp hzero

end ClosedGeneratedCoordinates

end

end CrowellExactSequence
