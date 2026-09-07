import ProCGroups.FoxDifferential.Completed.Continuous.ClosedGeneratedCoordinates.Equiv

set_option autoImplicit false

/-!
# Fox differential: completed — continuous — closed generated coordinates — topology

The principal declarations in this module are:

- `closedGeneratedDerivativeCoordinateTopologyProCInteger_of_fundamental_formula`
  The coordinate topology on \(A_{\psi}(C)\) transported from the closed-generated coordinate
  equivalence.
- `continuous_closedGenDerivativeCoordinateLinearEquivZC_of_fundFormula`
  The closed-generated coordinate equivalence is continuous for the transported coordinate topology
  on \(A_{\psi}(C)\).
- `t2Space_closedGenDerivativeCoordinateTopologyZC_of_fundFormula`
  The coordinate topology transported to \(A_{\psi}(C)\) is Hausdorff.
- `continuous_closedGenDerivativeCoordinateLinearEquivZC_of_fundFormula_symm`
  The inverse of the closed-generated coordinate equivalence is continuous for the transported
  coordinate topology on \(A_{\psi}(C)\). Equivalently, the displayed family map
  \(\mathbb{Z}_C\llbracket H\rrbracket^{X} \to A_{\psi}(C)\) is continuous for this topology.
-/

namespace CrowellExactSequence

noncomputable section

open scoped BigOperators
open FoxDifferential

universe u v w

variable {G H : Type u}
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

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
The coordinate topology on \(A_{\psi}(C)\) transported from the closed-generated coordinate
equivalence.
-/
@[implicit_reducible]
def closedGeneratedDerivativeCoordinateTopologyProCInteger_of_fundamental_formula
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
    TopologicalSpace
      (ZCCompletedDifferentialModule C psi.toMonoidHom) :=
  TopologicalSpace.induced
    (closedGeneratedDerivativeCoordinateLinearEquivProCInteger_of_fundamental_formula
      (G := G) (H := H) C psi family hfree htarget hφconv
      hH hφHconv hφHgen hfundamental)
    inferInstance

/--
The closed-generated coordinate equivalence is continuous for the transported coordinate
topology on \(A_{\psi}(C)\).
-/
theorem continuous_closedGenDerivativeCoordinateLinearEquivZC_of_fundFormula
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
    @Continuous
      (ZCCompletedDifferentialModule C psi.toMonoidHom)
      (ZCFreeFoxCoordinates C (X := X) (H := H))
      (closedGeneratedDerivativeCoordinateTopologyProCInteger_of_fundamental_formula
        (G := G) (H := H) C psi family hfree htarget hφconv
        hH hφHconv hφHgen hfundamental)
      inferInstance
      (closedGeneratedDerivativeCoordinateLinearEquivProCInteger_of_fundamental_formula
        (G := G) (H := H) C psi family hfree htarget hφconv
        hH hφHconv hφHgen hfundamental) := by
  exact continuous_induced_dom

/-- The coordinate topology transported to \(A_{\psi}(C)\) is Hausdorff. -/
theorem t2Space_closedGenDerivativeCoordinateTopologyZC_of_fundFormula
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
    @T2Space
      (ZCCompletedDifferentialModule C psi.toMonoidHom)
      (closedGeneratedDerivativeCoordinateTopologyProCInteger_of_fundamental_formula
        (G := G) (H := H) C psi family hfree htarget hφconv
        hH hφHconv hφHgen hfundamental) := by
  let : TopologicalSpace
      (ZCCompletedDifferentialModule C psi.toMonoidHom) :=
    closedGeneratedDerivativeCoordinateTopologyProCInteger_of_fundamental_formula
      (G := G) (H := H) C psi family hfree htarget hφconv
      hH hφHconv hφHgen hfundamental
  let e :=
    closedGeneratedDerivativeCoordinateLinearEquivProCInteger_of_fundamental_formula
      (G := G) (H := H) C psi family hfree htarget hφconv
      hH hφHconv hφHgen hfundamental
  have hcont : Continuous (e :
      ZCCompletedDifferentialModule C psi.toMonoidHom →
        ZCFreeFoxCoordinates C (X := X) (H := H)) := by
    simpa [e] using
      (continuous_closedGenDerivativeCoordinateLinearEquivZC_of_fundFormula
        (G := G) (H := H) C psi family hfree htarget hφconv
        hH hφHconv hφHgen hfundamental)
  exact T2Space.of_injective_continuous e.injective hcont

/--
The inverse of the closed-generated coordinate equivalence is continuous for the transported
coordinate topology on \(A_{\psi}(C)\). Equivalently, the displayed family map
\(\mathbb{Z}_C\llbracket H\rrbracket^{X} \to A_{\psi}(C)\) is continuous for this topology.
-/
theorem continuous_closedGenDerivativeCoordinateLinearEquivZC_of_fundFormula_symm
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
    @Continuous
      (ZCFreeFoxCoordinates C (X := X) (H := H))
      (ZCCompletedDifferentialModule C psi.toMonoidHom)
      inferInstance
      (closedGeneratedDerivativeCoordinateTopologyProCInteger_of_fundamental_formula
        (G := G) (H := H) C psi family hfree htarget hφconv
        hH hφHconv hφHgen hfundamental)
        (closedGeneratedDerivativeCoordinateLinearEquivProCInteger_of_fundamental_formula
          (G := G) (H := H) C psi family hfree htarget hφconv
          hH hφHconv hφHgen hfundamental).symm := by
  let e :=
    closedGeneratedDerivativeCoordinateLinearEquivProCInteger_of_fundamental_formula
      (G := G) (H := H) C psi family hfree htarget hφconv
      hH hφHconv hφHgen hfundamental
  rw [continuous_induced_rng]
  change Continuous
    (fun x : ZCFreeFoxCoordinates C (X := X) (H := H) =>
      e (e.symm x))
  have hfun :
      (fun x : ZCFreeFoxCoordinates C (X := X) (H := H) =>
        e (e.symm x)) =
        (fun x : ZCFreeFoxCoordinates C (X := X) (H := H) => x) := by
    funext x
    exact e.apply_symm_apply x
  rw [hfun]
  exact continuous_id

/--
The displayed family map is continuous for the coordinate topology transported to
\(A_{\psi}(C)\).
-/
theorem continuous_presentedCompletedDifferentialFamilyMapZC_coordTopology_of_fundFormula
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
    @Continuous
      (ZCFreeFoxCoordinates C (X := X) (H := H))
      (ZCCompletedDifferentialModule C psi.toMonoidHom)
      inferInstance
      (closedGeneratedDerivativeCoordinateTopologyProCInteger_of_fundamental_formula
        (G := G) (H := H) C psi family hfree htarget hφconv
        hH hφHconv hφHgen hfundamental)
        (presentedCompletedDifferentialFamilyMapProCInteger
          (G := G) (H := H) C psi family) := by
  let e :=
    closedGeneratedDerivativeCoordinateLinearEquivProCInteger_of_fundamental_formula
      (G := G) (H := H) C psi family hfree htarget hφconv
      hH hφHconv hφHgen hfundamental
  change @Continuous
      (ZCFreeFoxCoordinates C (X := X) (H := H))
      (ZCCompletedDifferentialModule C psi.toMonoidHom)
      inferInstance
      (closedGeneratedDerivativeCoordinateTopologyProCInteger_of_fundamental_formula
        (G := G) (H := H) C psi family hfree htarget hφconv
        hH hφHconv hφHgen hfundamental)
      (presentedCompletedDifferentialFamilyMapProCInteger
        (G := G) (H := H) C psi family)
  have hsymm :
      e.symm.toLinearMap =
        presentedCompletedDifferentialFamilyMapProCInteger
          (G := G) (H := H) C psi family := by
    simpa [e, closedGeneratedDerivativeCoordinateLinearEquivProCInteger_of_fundamental_formula]
      using
        (presentedCompletedDifferentialFamilyCoordinatesProCInteger_symm_toLinearMap
          (G := G) (H := H) C psi family
          (isPresentedCompletedDifferentialFamilyBasisZC_of_closedGen_fundFormula
            (G := G) (H := H) C psi family hfree htarget hφconv
            hH hφHconv hφHgen hfundamental))
  rw [← hsymm]
  change @Continuous
    (ZCFreeFoxCoordinates C (X := X) (H := H))
    (ZCCompletedDifferentialModule C psi.toMonoidHom)
    inferInstance
    (closedGeneratedDerivativeCoordinateTopologyProCInteger_of_fundamental_formula
      (G := G) (H := H) C psi family hfree htarget hφconv
      hH hφHconv hφHgen hfundamental)
    ((closedGeneratedDerivativeCoordinateLinearEquivProCInteger_of_fundamental_formula
      (G := G) (H := H) C psi family hfree htarget hφconv
      hH hφHconv hφHgen hfundamental).symm :
        ZCFreeFoxCoordinates C (X := X) (H := H) →
          ZCCompletedDifferentialModule C psi.toMonoidHom)
  exact
    continuous_closedGenDerivativeCoordinateLinearEquivZC_of_fundFormula_symm
      (G := G) (H := H) C psi family hfree htarget hφconv
      hH hφHconv hφHgen hfundamental

/--
The universal differential \(g \mapsto d(g)\) is continuous for the coordinate topology
transported to \(A_{\psi}(C)\).
-/
theorem continuous_zcUniversalDifferential_coordinateTopology_of_fundamental_formula
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
    @Continuous G
      (ZCCompletedDifferentialModule C psi.toMonoidHom)
      inferInstance
      (closedGeneratedDerivativeCoordinateTopologyProCInteger_of_fundamental_formula
        (G := G) (H := H) C psi family hfree htarget hφconv
        hH hφHconv hφHgen hfundamental)
        (fun g : G => zcUniversalDifferential C psi.toMonoidHom g) := by
  let e :=
    closedGeneratedDerivativeCoordinateLinearEquivProCInteger_of_fundamental_formula
      (G := G) (H := H) C psi family hfree htarget hφconv
      hH hφHconv hφHgen hfundamental
  rw [continuous_induced_rng]
  change Continuous
    (fun g : G =>
      e (zcUniversalDifferential C psi.toMonoidHom g))
  have hfun :
      (fun g : G =>
        e (zcUniversalDifferential C psi.toMonoidHom g)) =
        (fun g : G =>
          freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
            (C := C) hfree (fun i : X => psi (family i)) htarget hφconv g) := by
    funext g
    exact
      closedGenDerivativeCoordinateLinearEquivZC_of_fundFormula_universal
        (G := G) (H := H) C psi family hfree htarget hφconv
        hH hφHconv hφHgen hfundamental g
  rw [hfun]
  exact
    continuous_freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
      (C := C) X H hfree (fun i : X => psi (family i)) htarget hφconv

/-- Addition is continuous for the transported coordinate topology on \(A_{\psi}(C)\). -/
theorem continuous_add_closedGenDerivativeCoordinateTopologyZC_of_fundFormula
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
    letI : TopologicalSpace
        (ZCCompletedDifferentialModule C psi.toMonoidHom) :=
      closedGeneratedDerivativeCoordinateTopologyProCInteger_of_fundamental_formula
        (G := G) (H := H) C psi family hfree htarget hφconv
        hH hφHconv hφHgen hfundamental
    Continuous (fun p :
      ZCCompletedDifferentialModule C psi.toMonoidHom ×
        ZCCompletedDifferentialModule C psi.toMonoidHom =>
      p.1 + p.2) := by
  let : TopologicalSpace
      (ZCCompletedDifferentialModule C psi.toMonoidHom) :=
    closedGeneratedDerivativeCoordinateTopologyProCInteger_of_fundamental_formula
      (G := G) (H := H) C psi family hfree htarget hφconv
      hH hφHconv hφHgen hfundamental
  let e :=
    closedGeneratedDerivativeCoordinateLinearEquivProCInteger_of_fundamental_formula
      (G := G) (H := H) C psi family hfree htarget hφconv
      hH hφHconv hφHgen hfundamental
  have he : Continuous (e :
      ZCCompletedDifferentialModule C psi.toMonoidHom →
        ZCFreeFoxCoordinates C (X := X) (H := H)) := by
    simpa [e] using
      (continuous_closedGenDerivativeCoordinateLinearEquivZC_of_fundFormula
        (G := G) (H := H) C psi family hfree htarget hφconv
        hH hφHconv hφHgen hfundamental)
  rw [continuous_induced_rng]
  change Continuous
    (fun p :
      ZCCompletedDifferentialModule C psi.toMonoidHom ×
        ZCCompletedDifferentialModule C psi.toMonoidHom =>
      e (p.1 + p.2))
  have hcont :=
    (he.comp continuous_fst).add (he.comp continuous_snd)
  change Continuous
    (fun p :
      ZCCompletedDifferentialModule C psi.toMonoidHom ×
        ZCCompletedDifferentialModule C psi.toMonoidHom =>
      e p.1 + e p.2) at hcont
  have hfun :
      (fun p :
        ZCCompletedDifferentialModule C psi.toMonoidHom ×
          ZCCompletedDifferentialModule C psi.toMonoidHom =>
        e (p.1 + p.2)) =
      (fun p :
        ZCCompletedDifferentialModule C psi.toMonoidHom ×
          ZCCompletedDifferentialModule C psi.toMonoidHom =>
        e p.1 + e p.2) := by
    funext p
    exact map_add e p.1 p.2
  rw [hfun]
  exact hcont

/-- Negation is continuous for the transported coordinate topology on \(A_{\psi}(C)\). -/
theorem continuous_neg_closedGenDerivativeCoordinateTopologyZC_of_fundFormula
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
    letI : TopologicalSpace
        (ZCCompletedDifferentialModule C psi.toMonoidHom) :=
      closedGeneratedDerivativeCoordinateTopologyProCInteger_of_fundamental_formula
        (G := G) (H := H) C psi family hfree htarget hφconv
        hH hφHconv hφHgen hfundamental
    Continuous
      (fun a : ZCCompletedDifferentialModule C psi.toMonoidHom => -a) := by
  let : TopologicalSpace
      (ZCCompletedDifferentialModule C psi.toMonoidHom) :=
    closedGeneratedDerivativeCoordinateTopologyProCInteger_of_fundamental_formula
      (G := G) (H := H) C psi family hfree htarget hφconv
      hH hφHconv hφHgen hfundamental
  let e :=
    closedGeneratedDerivativeCoordinateLinearEquivProCInteger_of_fundamental_formula
      (G := G) (H := H) C psi family hfree htarget hφconv
      hH hφHconv hφHgen hfundamental
  have he : Continuous (e :
      ZCCompletedDifferentialModule C psi.toMonoidHom →
        ZCFreeFoxCoordinates C (X := X) (H := H)) := by
    simpa [e] using
      (continuous_closedGenDerivativeCoordinateLinearEquivZC_of_fundFormula
        (G := G) (H := H) C psi family hfree htarget hφconv
        hH hφHconv hφHgen hfundamental)
  rw [continuous_induced_rng]
  change Continuous
    (fun a : ZCCompletedDifferentialModule C psi.toMonoidHom => e (-a))
  have hcont := he.neg
  change Continuous
    (fun a : ZCCompletedDifferentialModule C psi.toMonoidHom => -(e a)) at hcont
  have hfun :
      (fun a : ZCCompletedDifferentialModule C psi.toMonoidHom => e (-a)) =
        (fun a : ZCCompletedDifferentialModule C psi.toMonoidHom => -(e a)) := by
    funext a
    exact map_neg e a
  rw [hfun]
  exact hcont

/--
Scalar multiplication is continuous for the transported coordinate topology on \(A_{\psi}(C)\).
-/
theorem continuous_smul_closedGenDerivativeCoordinateTopologyZC_of_fundFormula
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
    letI : TopologicalSpace
        (ZCCompletedDifferentialModule C psi.toMonoidHom) :=
      closedGeneratedDerivativeCoordinateTopologyProCInteger_of_fundamental_formula
        (G := G) (H := H) C psi family hfree htarget hφconv
        hH hφHconv hφHgen hfundamental
    Continuous
      (fun p :
        ZCCompletedGroupAlgebra C H ×
          ZCCompletedDifferentialModule C psi.toMonoidHom =>
        p.1 • p.2) := by
  let : TopologicalSpace
      (ZCCompletedDifferentialModule C psi.toMonoidHom) :=
    closedGeneratedDerivativeCoordinateTopologyProCInteger_of_fundamental_formula
      (G := G) (H := H) C psi family hfree htarget hφconv
      hH hφHconv hφHgen hfundamental
  let e :=
    closedGeneratedDerivativeCoordinateLinearEquivProCInteger_of_fundamental_formula
      (G := G) (H := H) C psi family hfree htarget hφconv
      hH hφHconv hφHgen hfundamental
  have he : Continuous (e :
      ZCCompletedDifferentialModule C psi.toMonoidHom →
        ZCFreeFoxCoordinates C (X := X) (H := H)) := by
    simpa [e] using
      (continuous_closedGenDerivativeCoordinateLinearEquivZC_of_fundFormula
        (G := G) (H := H) C psi family hfree htarget hφconv
        hH hφHconv hφHgen hfundamental)
  rw [continuous_induced_rng]
  change Continuous
    (fun p :
      ZCCompletedGroupAlgebra C H ×
        ZCCompletedDifferentialModule C psi.toMonoidHom =>
      e (p.1 • p.2))
  have hfst :
      Continuous
        (fun p : ZCCompletedGroupAlgebra C H ×
            ZCCompletedDifferentialModule C psi.toMonoidHom => p.1) :=
    continuous_fst
  have hsnd :
      Continuous
        (fun p : ZCCompletedGroupAlgebra C H ×
            ZCCompletedDifferentialModule C psi.toMonoidHom => e p.2) :=
    he.comp continuous_snd
  have hcont :
      Continuous
        (fun p : ZCCompletedGroupAlgebra C H ×
            ZCCompletedDifferentialModule C psi.toMonoidHom =>
          p.1 • e p.2) :=
    hfst.smul hsnd
  have hfun :
      (fun p : ZCCompletedGroupAlgebra C H ×
          ZCCompletedDifferentialModule C psi.toMonoidHom =>
        e (p.1 • p.2)) =
      (fun p : ZCCompletedGroupAlgebra C H ×
          ZCCompletedDifferentialModule C psi.toMonoidHom =>
        p.1 • e p.2) := by
    funext p
    exact map_smul e p.1 p.2
  rw [hfun]
  exact hcont

end ClosedGeneratedCoordinateEquiv

end

end CrowellExactSequence
