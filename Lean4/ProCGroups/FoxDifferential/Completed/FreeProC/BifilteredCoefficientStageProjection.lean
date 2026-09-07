import ProCGroups.FoxDifferential.Completed.FreeProC.CoordinateStageProjection
import ProCGroups.FoxDifferential.Completed.FreeProC.BifilteredSystemStageProjection

set_option autoImplicit false

/-!
# Fox differential: completed — free pro-\(C\) — bifiltered coefficient stage projection

The principal declarations in this module are:

- `zcFreeFoxCoordinatesBifilteredStageMap`
  Coordinate maps attached to a compatible family of coefficient maps.
- `freeProCZCCompletedFoxSemidirectBifilteredStageMapOfCoeff`
  Completed-to-finite semidirect maps induced by coefficient maps.
- `zcFreeFoxCoordinatesBifilteredStageMap_apply`
  The bifiltered finite-stage map on completed Fox-coordinate vectors is computed coordinatewise by
  the underlying coefficient-stage map.
- `zcFreeFoxCoordinatesBifilteredStageMap_transition`
  Coefficient-map transition compatibility implies transition compatibility for coordinate vectors.
-/

namespace FoxDifferential

noncomputable section

open scoped Topology
open ProCGroups.ProC

universe u v

section BifilteredCoefficientMaps

variable {C : ProCGroups.FiniteGroupClass}
variable {X H : Type u}
variable [DecidableEq X]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable [TopologicalSpace (ZCCompletedFoxSemidirect C X H)]
variable [IsTopologicalGroup (ZCCompletedFoxSemidirect C X H)]
variable {J : Type v} [Preorder J]
variable (Nstage : J → Subgroup (FreeGroup X)) [∀ j, (Nstage j).Normal]
variable (nstage : J → ℕ) [∀ j, Fact (0 < nstage j)]
variable (hN : ∀ {i j : J}, i ≤ j → Nstage j ≤ Nstage i)
variable (hn : ∀ {i j : J}, i ≤ j → nstage i ∣ nstage j)

/-- Coordinate maps attached to a compatible family of coefficient maps. -/
def zcFreeFoxCoordinatesBifilteredStageMap
    (stageCoeff : ∀ j : J,
      ZCCompletedGroupAlgebra C H →+*
        foxAlgebraicStageTargetGroupAlgebra (X := X) (Nstage j) (nstage j))
    (j : J) :
    ZCFreeFoxCoordinates C (X := X) (H := H) →+
      foxAlgebraicStageCoordinateVector (X := X) (Nstage j) (nstage j) :=
  zcFreeFoxCoordinatesStageMap
    (C := C) (X := X) (H := H) (Nstage j) (nstage j) (stageCoeff j)

omit [DecidableEq X] [TopologicalSpace (ZCCompletedFoxSemidirect C X H)] [IsTopologicalGroup
    (ZCCompletedFoxSemidirect C X H)] [Preorder J] [∀ (j : J), Fact (0 < nstage j)] in
/--
The bifiltered finite-stage map on completed Fox-coordinate vectors is computed coordinatewise
by the underlying coefficient-stage map.
-/
@[simp]
theorem zcFreeFoxCoordinatesBifilteredStageMap_apply
    (stageCoeff : ∀ j : J,
      ZCCompletedGroupAlgebra C H →+*
        foxAlgebraicStageTargetGroupAlgebra (X := X) (Nstage j) (nstage j))
    (j : J)
    (v : ZCFreeFoxCoordinates C (X := X) (H := H))
    (x : X) :
    zcFreeFoxCoordinatesBifilteredStageMap
        (C := C) (X := X) (H := H) Nstage nstage stageCoeff j v x =
      stageCoeff j (v x) :=
  rfl

omit [DecidableEq X] [TopologicalSpace (ZCCompletedFoxSemidirect C X H)] [IsTopologicalGroup
    (ZCCompletedFoxSemidirect C X H)] [∀ (j : J), Fact (0 < nstage j)] in
/--
Coefficient-map transition compatibility implies transition compatibility for coordinate
vectors.
-/
theorem zcFreeFoxCoordinatesBifilteredStageMap_transition
    (stageCoeff : ∀ j : J,
      ZCCompletedGroupAlgebra C H →+*
        foxAlgebraicStageTargetGroupAlgebra (X := X) (Nstage j) (nstage j))
    (hcoeff : ∀ {i j : J} (hij : i ≤ j), ∀ a : ZCCompletedGroupAlgebra C H,
      foxAlgebraicStageBifilteredTargetGroupAlgebraMap (X := X) (hN hij) (hn hij)
        (stageCoeff j a) = stageCoeff i a)
    {i j : J} (hij : i ≤ j)
    (v : ZCFreeFoxCoordinates C (X := X) (H := H)) :
    foxAlgebraicStageBifilteredCoordinateVectorMap (X := X) (hN hij) (hn hij)
        (zcFreeFoxCoordinatesBifilteredStageMap
          (C := C) (X := X) (H := H) Nstage nstage stageCoeff j v) =
      zcFreeFoxCoordinatesBifilteredStageMap
        (C := C) (X := X) (H := H) Nstage nstage stageCoeff i v := by
  funext x
  exact hcoeff hij (v x)

omit [TopologicalSpace (ZCCompletedFoxSemidirect C X H)] [IsTopologicalGroup
    (ZCCompletedFoxSemidirect C X H)] [Preorder J] in
omit [DecidableEq X] [∀ (j : J), Fact (0 < nstage j)] in
/--
Group-like compatibility for coefficient maps gives scalar compatibility for the induced
coordinate maps.
-/
theorem zcFreeFoxCoordinatesBifilteredStageMap_smul_groupLike
    (stageCoeff : ∀ j : J,
      ZCCompletedGroupAlgebra C H →+*
        foxAlgebraicStageTargetGroupAlgebra (X := X) (Nstage j) (nstage j))
    (stageRight : ∀ j : J, H →* foxAlgebraicStageTargetQuotient (X := X) (Nstage j))
    (hgroupLike : ∀ j : J, ∀ h : H,
      stageCoeff j (zcGroupLike C H h) =
        MonoidAlgebra.of (ModNCompletedCoeff (nstage j))
          (foxAlgebraicStageTargetQuotient (X := X) (Nstage j)) (stageRight j h))
    (j : J) (h : H)
    (v : ZCFreeFoxCoordinates C (X := X) (H := H)) :
    zcFreeFoxCoordinatesBifilteredStageMap
        (C := C) (X := X) (H := H) Nstage nstage stageCoeff j
        (zcGroupLike C H h • v) =
      (MonoidAlgebra.of (ModNCompletedCoeff (nstage j))
        (foxAlgebraicStageTargetQuotient (X := X) (Nstage j)) (stageRight j h)) •
        zcFreeFoxCoordinatesBifilteredStageMap
          (C := C) (X := X) (H := H) Nstage nstage stageCoeff j v :=
  zcFreeFoxCoordinatesStageMap_smul_groupLike
    (C := C) (X := X) (H := H) (Nstage j) (nstage j)
    (stageCoeff j) (stageRight j) (hgroupLike j) h v

/-- Completed-to-finite semidirect maps induced by coefficient maps. -/
def freeProCZCCompletedFoxSemidirectBifilteredStageMapOfCoeff
    (stageCoeff : ∀ j : J,
      ZCCompletedGroupAlgebra C H →+*
        foxAlgebraicStageTargetGroupAlgebra (X := X) (Nstage j) (nstage j))
    (stageRight : ∀ j : J, H →* foxAlgebraicStageTargetQuotient (X := X) (Nstage j))
    (hgroupLike : ∀ j : J, ∀ h : H,
      stageCoeff j (zcGroupLike C H h) =
        MonoidAlgebra.of (ModNCompletedCoeff (nstage j))
          (foxAlgebraicStageTargetQuotient (X := X) (Nstage j)) (stageRight j h))
    (j : J) :
    ZCCompletedFoxSemidirect C X H →*
      FoxAlgebraicStageSemidirect (X := X) (Nstage j) (nstage j) :=
  freeProCZCCompletedFoxSemidirectStageMapOfCoeff
    (C := C) (X := X) (H := H) (Nstage j) (nstage j)
    (stageCoeff j) (stageRight j) (hgroupLike j)

omit [DecidableEq X] [TopologicalSpace (ZCCompletedFoxSemidirect C X H)] [IsTopologicalGroup
    (ZCCompletedFoxSemidirect C X H)] [∀ (j : J), Fact (0 < nstage j)] in
/-- Transition compatibility of semidirect stage maps induced by coefficient maps. -/
theorem freeProCZCCompletedFoxSemidirectBifilteredStageMapOfCoeff_transition
    (stageCoeff : ∀ j : J,
      ZCCompletedGroupAlgebra C H →+*
        foxAlgebraicStageTargetGroupAlgebra (X := X) (Nstage j) (nstage j))
    (stageRight : ∀ j : J, H →* foxAlgebraicStageTargetQuotient (X := X) (Nstage j))
    (hgroupLike : ∀ j : J, ∀ h : H,
      stageCoeff j (zcGroupLike C H h) =
        MonoidAlgebra.of (ModNCompletedCoeff (nstage j))
          (foxAlgebraicStageTargetQuotient (X := X) (Nstage j)) (stageRight j h))
    (hcoeff : ∀ {i j : J} (hij : i ≤ j), ∀ a : ZCCompletedGroupAlgebra C H,
      foxAlgebraicStageBifilteredTargetGroupAlgebraMap (X := X) (hN hij) (hn hij)
        (stageCoeff j a) = stageCoeff i a)
    (hright : ∀ {i j : J} (hij : i ≤ j), ∀ h : H,
      foxAlgebraicStageTargetQuotientMap (X := X) (hN hij) (stageRight j h) =
        stageRight i h)
    {i j : J} (hij : i ≤ j) :
    (foxAlgebraicStageBifilteredSemidirectFamilyTransition
        (X := X) Nstage nstage hN hn hij).comp
      (freeProCZCCompletedFoxSemidirectBifilteredStageMapOfCoeff
        (C := C) (X := X) (H := H) Nstage nstage stageCoeff stageRight hgroupLike j) =
    freeProCZCCompletedFoxSemidirectBifilteredStageMapOfCoeff
      (C := C) (X := X) (H := H) Nstage nstage stageCoeff stageRight hgroupLike i := by
  exact
    freeProCZCCompletedFoxSemidirectStageMap_bifilteredFamilyTransition
      (C := C) (X := X) (H := H) Nstage nstage hN hn
      (fun k => zcFreeFoxCoordinatesBifilteredStageMap
        (C := C) (X := X) (H := H) Nstage nstage stageCoeff k)
      stageRight
      (fun k => zcFreeFoxCoordinatesBifilteredStageMap_smul_groupLike
        (C := C) (X := X) (H := H) Nstage nstage stageCoeff stageRight hgroupLike k)
      (fun hij v => zcFreeFoxCoordinatesBifilteredStageMap_transition
        (C := C) (X := X) (H := H) Nstage nstage hN hn stageCoeff hcoeff hij v)
      hright hij

/--
The coefficient-map stage family assembled as a map into the bifiltered finite semidirect
inverse limit.
-/
def freeProCZCCompletedFoxSemidirectBifilteredLimitMapOfCoeff
    (stageCoeff : ∀ j : J,
      ZCCompletedGroupAlgebra C H →+*
        foxAlgebraicStageTargetGroupAlgebra (X := X) (Nstage j) (nstage j))
    (stageRight : ∀ j : J, H →* foxAlgebraicStageTargetQuotient (X := X) (Nstage j))
    (hgroupLike : ∀ j : J, ∀ h : H,
      stageCoeff j (zcGroupLike C H h) =
        MonoidAlgebra.of (ModNCompletedCoeff (nstage j))
          (foxAlgebraicStageTargetQuotient (X := X) (Nstage j)) (stageRight j h))
    (hcoeff : ∀ {i j : J} (hij : i ≤ j), ∀ a : ZCCompletedGroupAlgebra C H,
      foxAlgebraicStageBifilteredTargetGroupAlgebraMap (X := X) (hN hij) (hn hij)
        (stageCoeff j a) = stageCoeff i a)
    (hright : ∀ {i j : J} (hij : i ≤ j), ∀ h : H,
      foxAlgebraicStageTargetQuotientMap (X := X) (hN hij) (stageRight j h) =
        stageRight i h) :
    ZCCompletedFoxSemidirect C X H →*
      FoxAlgebraicStageBifilteredSemidirectLimit (X := X) Nstage nstage hN hn :=
  freeProCZCCompletedFoxSemidirectBifilteredLimitMap
    (C := C) (X := X) (H := H) Nstage nstage hN hn
    (fun j =>
      freeProCZCCompletedFoxSemidirectBifilteredStageMapOfCoeff
        (C := C) (X := X) (H := H) Nstage nstage stageCoeff stageRight hgroupLike j)
    (fun hij =>
      freeProCZCCompletedFoxSemidirectBifilteredStageMapOfCoeff_transition
        (C := C) (X := X) (H := H) Nstage nstage hN hn stageCoeff stageRight
        hgroupLike hcoeff hright hij)

omit [DecidableEq X] [∀ j, Fact (0 < nstage j)]
  [TopologicalSpace (ZCCompletedFoxSemidirect C X H)]
  [IsTopologicalGroup (ZCCompletedFoxSemidirect C X H)] in
/--
The coefficient part of the basis-element formula for the free pro-\(C\)
\(\mathbb{Z}_C\)-completed Fox semidirect bifiltered limit map is computed by the finite-stage
coordinate map.
-/
@[simp 900]
theorem freeProCZCCompletedFoxSemidirectBifilteredLimitMapOfCoeff_projection
    (stageCoeff : ∀ j : J,
      ZCCompletedGroupAlgebra C H →+*
        foxAlgebraicStageTargetGroupAlgebra (X := X) (Nstage j) (nstage j))
    (stageRight : ∀ j : J, H →* foxAlgebraicStageTargetQuotient (X := X) (Nstage j))
    (hgroupLike : ∀ j : J, ∀ h : H,
      stageCoeff j (zcGroupLike C H h) =
        MonoidAlgebra.of (ModNCompletedCoeff (nstage j))
          (foxAlgebraicStageTargetQuotient (X := X) (Nstage j)) (stageRight j h))
    (hcoeff : ∀ {i j : J} (hij : i ≤ j), ∀ a : ZCCompletedGroupAlgebra C H,
      foxAlgebraicStageBifilteredTargetGroupAlgebraMap (X := X) (hN hij) (hn hij)
        (stageCoeff j a) = stageCoeff i a)
    (hright : ∀ {i j : J} (hij : i ≤ j), ∀ h : H,
      foxAlgebraicStageTargetQuotientMap (X := X) (hN hij) (stageRight j h) =
        stageRight i h)
    (j : J) (y : ZCCompletedFoxSemidirect C X H) :
    foxAlgebraicStageBifilteredSemidirectLimitProjection
        (X := X) Nstage nstage hN hn j
        (freeProCZCCompletedFoxSemidirectBifilteredLimitMapOfCoeff
          (C := C) (X := X) (H := H) Nstage nstage hN hn
          stageCoeff stageRight hgroupLike hcoeff hright y) =
      freeProCZCCompletedFoxSemidirectBifilteredStageMapOfCoeff
        (C := C) (X := X) (H := H) Nstage nstage stageCoeff stageRight hgroupLike j y :=
  rfl

omit [DecidableEq X] [∀ j, Fact (0 < nstage j)]
  [TopologicalSpace (ZCCompletedFoxSemidirect C X H)]
  [IsTopologicalGroup (ZCCompletedFoxSemidirect C X H)] in
/-- Boundary-cycle preservation for the bifiltered limit map induced by coefficient maps. -/
theorem freeProCZCCompletedFoxSemidirectBifilteredLimitMapOfCoeff_mem_boundaryCycleSet
    [Fintype X] (φ : X → H)
    (stageCoeff : ∀ j : J,
      ZCCompletedGroupAlgebra C H →+*
        foxAlgebraicStageTargetGroupAlgebra (X := X) (Nstage j) (nstage j))
    (stageRight : ∀ j : J, H →* foxAlgebraicStageTargetQuotient (X := X) (Nstage j))
    (hgroupLike : ∀ j : J, ∀ h : H,
      stageCoeff j (zcGroupLike C H h) =
        MonoidAlgebra.of (ModNCompletedCoeff (nstage j))
          (foxAlgebraicStageTargetQuotient (X := X) (Nstage j)) (stageRight j h))
    (hcoeff : ∀ {i j : J} (hij : i ≤ j), ∀ a : ZCCompletedGroupAlgebra C H,
      foxAlgebraicStageBifilteredTargetGroupAlgebraMap (X := X) (hN hij) (hn hij)
        (stageCoeff j a) = stageCoeff i a)
    (hright : ∀ {i j : J} (hij : i ≤ j), ∀ h : H,
      foxAlgebraicStageTargetQuotientMap (X := X) (hN hij) (stageRight j h) =
        stageRight i h)
    (hright_generators : ∀ j : J, ∀ i : X,
      stageRight j (φ i) = QuotientGroup.mk' (Nstage j) (FreeGroup.of i))
    {y : ZCCompletedFoxSemidirect C X H}
    (hy : y ∈ freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ) :
    freeProCZCCompletedFoxSemidirectBifilteredLimitMapOfCoeff
        (C := C) (X := X) (H := H) Nstage nstage hN hn
        stageCoeff stageRight hgroupLike hcoeff hright y ∈
      foxAlgebraicStageBifilteredSemidirectLimitBoundaryCycleSet
        (X := X) Nstage nstage hN hn := by
  intro j
  change
    foxAlgebraicStageBifilteredSemidirectLimitProjection
        (X := X) Nstage nstage hN hn j
        (freeProCZCCompletedFoxSemidirectBifilteredLimitMapOfCoeff
          (C := C) (X := X) (H := H) Nstage nstage hN hn
          stageCoeff stageRight hgroupLike hcoeff hright y) ∈
      foxAlgebraicStageSemidirectBoundaryCycleSet
        (X := X) (Nstage j) (nstage j)
  rw [freeProCZCCompletedFoxSemidirectBifilteredLimitMapOfCoeff_projection]
  exact
    freeProCZCCompletedFoxSemidirectStageMapOfCoeff_mem_finiteBoundaryCycleSet
      (C := C) (X := X) (H := H) (Nstage j) (nstage j) φ
      (stageCoeff j) (stageRight j) (hgroupLike j) (hright_generators j) hy

omit [∀ j, Fact (0 < nstage j)]
  [TopologicalSpace (ZCCompletedFoxSemidirect C X H)]
  [IsTopologicalGroup (ZCCompletedFoxSemidirect C X H)] in
/-- Kernel-word preservation for the bifiltered limit map induced by coefficient maps. -/
theorem freeProCZCCompletedFoxSemidirectBifilteredLimitMapOfCoeff_kernelWordPoint
    (φ : X → H)
    (stageCoeff : ∀ j : J,
      ZCCompletedGroupAlgebra C H →+*
        foxAlgebraicStageTargetGroupAlgebra (X := X) (Nstage j) (nstage j))
    (stageRight : ∀ j : J, H →* foxAlgebraicStageTargetQuotient (X := X) (Nstage j))
    (hgroupLike : ∀ j : J, ∀ h : H,
      stageCoeff j (zcGroupLike C H h) =
        MonoidAlgebra.of (ModNCompletedCoeff (nstage j))
          (foxAlgebraicStageTargetQuotient (X := X) (Nstage j)) (stageRight j h))
    (hcoeff : ∀ {i j : J} (hij : i ≤ j), ∀ a : ZCCompletedGroupAlgebra C H,
      foxAlgebraicStageBifilteredTargetGroupAlgebraMap (X := X) (hN hij) (hn hij)
        (stageCoeff j a) = stageCoeff i a)
    (hright : ∀ {i j : J} (hij : i ≤ j), ∀ h : H,
      foxAlgebraicStageTargetQuotientMap (X := X) (hN hij) (stageRight j h) =
        stageRight i h)
    (hright_generators : ∀ j : J, ∀ i : X,
      stageRight j (φ i) = QuotientGroup.mk' (Nstage j) (FreeGroup.of i))
    (w : FreeGroup X) :
    freeProCZCCompletedFoxSemidirectBifilteredLimitMapOfCoeff
        (C := C) (X := X) (H := H) Nstage nstage hN hn
        stageCoeff stageRight hgroupLike hcoeff hright
        (freeProCZCCompletedFoxSemidirectKernelWordPoint (C := C) φ w) =
      foxAlgebraicStageBifilteredSemidirectKernelWordPointLimit
        (X := X) Nstage nstage hN hn w := by
  apply Subtype.ext
  funext j
  exact
    freeProCZCCompletedFoxSemidirectStageMapOfCoeff_kernelWordPoint
      (C := C) (X := X) (H := H) (Nstage j) (nstage j) φ
      (stageCoeff j) (stageRight j) (hgroupLike j) (hright_generators j) w

omit [Preorder J] [∀ (j : J), Fact (0 < nstage j)] in
/--
Completed density from coefficient-map finite stages. The theorem packages the whole finite
relation-ideal derivative route after the completed projections have been reduced to coefficient
maps and target quotient maps.
-/
theorem freeProCZCFoxBoundaryCycles_subset_kernelCycles_of_biCoeff_relDeriv
    [Fintype X] (φ : X → H)
    (stageCoeff : ∀ j : J,
      ZCCompletedGroupAlgebra C H →+*
        foxAlgebraicStageTargetGroupAlgebra (X := X) (Nstage j) (nstage j))
    (stageRight : ∀ j : J, H →* foxAlgebraicStageTargetQuotient (X := X) (Nstage j))
    (hgroupLike : ∀ j : J, ∀ h : H,
      stageCoeff j (zcGroupLike C H h) =
        MonoidAlgebra.of (ModNCompletedCoeff (nstage j))
          (foxAlgebraicStageTargetQuotient (X := X) (Nstage j)) (stageRight j h))
    (hright_generators : ∀ j : J, ∀ i : X,
      stageRight j (φ i) = QuotientGroup.mk' (Nstage j) (FreeGroup.of i))
    (hidentity_basis :
      HasIdentityQuotientKernelNeighbourhoodBasis
        (Y := ZCCompletedFoxSemidirect C X H)
        (fun j : J =>
          freeProCZCCompletedFoxSemidirectBifilteredStageMapOfCoeff
            (C := C) (X := X) (H := H) Nstage nstage
            stageCoeff stageRight hgroupLike j))
    (hNstage_kernel :
      ∀ j : J, ∀ {w : FreeGroup X}, w ∈ Nstage j → FreeGroup.lift φ w = 1) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ ⊆
      closure (freeProCZCCompletedFoxSemidirectKernelCycleSet (C := C) φ) := by
  exact
    boundaryCycles_subset_kernelClosure_of_biStageMaps
      (C := C) (X := X) (H := H) Nstage nstage φ
      (fun j => zcFreeFoxCoordinatesBifilteredStageMap
        (C := C) (X := X) (H := H) Nstage nstage stageCoeff j)
      stageRight
      (fun j => zcFreeFoxCoordinatesBifilteredStageMap_smul_groupLike
        (C := C) (X := X) (H := H) Nstage nstage stageCoeff stageRight hgroupLike j)
      hidentity_basis
      (fun j => (stageCoeff j).toAddMonoidHom)
      (fun j v => foxAlgebraicStageFoxBoundary_zcFreeFoxCoordinatesStageMap_of_groupLike
        (C := C) (X := X) (H := H) (Nstage j) (nstage j) φ
        (stageCoeff j) (stageRight j) (hgroupLike j) (hright_generators j) v)
      hNstage_kernel
      (fun j w => zcFreeFoxCoordinatesStageMap_derivativeVector_of_generators
        (C := C) (X := X) (H := H) (Nstage j) (nstage j) φ
        (stageCoeff j) (stageRight j) (hgroupLike j) (hright_generators j) w)

omit [Preorder J] [∀ (j : J), Fact (0 < nstage j)] in
/--
Completed graph-word density from coefficient-map finite stages. This is the
finite-quotient-safe version of the preceding kernel-word density theorem: words in
\(N_{\mathrm{stage},j}\) are used only to make the finite right coordinate trivial, not as
actual kernel words for the completed target map.
-/
theorem boundaryCycles_subset_graphWordClosure_of_biCoeffStages
    [Fintype X] (φ : X → H)
    (stageCoeff : ∀ j : J,
      ZCCompletedGroupAlgebra C H →+*
        foxAlgebraicStageTargetGroupAlgebra (X := X) (Nstage j) (nstage j))
    (stageRight : ∀ j : J, H →* foxAlgebraicStageTargetQuotient (X := X) (Nstage j))
    (hgroupLike : ∀ j : J, ∀ h : H,
      stageCoeff j (zcGroupLike C H h) =
        MonoidAlgebra.of (ModNCompletedCoeff (nstage j))
          (foxAlgebraicStageTargetQuotient (X := X) (Nstage j)) (stageRight j h))
    (hright_generators : ∀ j : J, ∀ i : X,
      stageRight j (φ i) = QuotientGroup.mk' (Nstage j) (FreeGroup.of i))
    (hidentity_basis :
      HasIdentityQuotientKernelNeighbourhoodBasis
        (Y := ZCCompletedFoxSemidirect C X H)
        (fun j : J =>
          freeProCZCCompletedFoxSemidirectBifilteredStageMapOfCoeff
            (C := C) (X := X) (H := H) Nstage nstage
            stageCoeff stageRight hgroupLike j)) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ ⊆
      closure (freeProCZCCompletedFoxSemidirectGraphWordSet (C := C) φ) := by
  exact
    boundaryCycles_subset_graphWordClosure_of_stageMaps
      (C := C) (X := X) (H := H) φ Nstage nstage
      (fun j => zcFreeFoxCoordinatesBifilteredStageMap
        (C := C) (X := X) (H := H) Nstage nstage stageCoeff j)
      stageRight
      (fun j => zcFreeFoxCoordinatesBifilteredStageMap_smul_groupLike
        (C := C) (X := X) (H := H) Nstage nstage stageCoeff stageRight hgroupLike j)
      hidentity_basis
      (fun j => (stageCoeff j).toAddMonoidHom)
      (fun j v => foxAlgebraicStageFoxBoundary_zcFreeFoxCoordinatesStageMap_of_groupLike
        (C := C) (X := X) (H := H) (Nstage j) (nstage j) φ
        (stageCoeff j) (stageRight j) (hgroupLike j) (hright_generators j) v)
      (fun j w => finiteStageRight_comp_lift_eq_quotientMk
        (X := X) (H := H) (Nstage j) φ
        (stageRight j) (hright_generators j) w)
      (fun j w => zcFreeFoxCoordinatesStageMap_derivativeVector_of_generators
        (C := C) (X := X) (H := H) (Nstage j) (nstage j) φ
        (stageCoeff j) (stageRight j) (hgroupLike j) (hright_generators j) w)

omit [Preorder J] [∀ (j : J), Fact (0 < nstage j)] in
/--
Closed-generated-target membership from coefficient-map finite stages, without a completed
kernel-word hypothesis.
-/
theorem boundaryCycles_subset_closedGenTarget_of_biCoeffGraph
    [Fintype X] (φ : X → H)
    (stageCoeff : ∀ j : J,
      ZCCompletedGroupAlgebra C H →+*
        foxAlgebraicStageTargetGroupAlgebra (X := X) (Nstage j) (nstage j))
    (stageRight : ∀ j : J, H →* foxAlgebraicStageTargetQuotient (X := X) (Nstage j))
    (hgroupLike : ∀ j : J, ∀ h : H,
      stageCoeff j (zcGroupLike C H h) =
        MonoidAlgebra.of (ModNCompletedCoeff (nstage j))
          (foxAlgebraicStageTargetQuotient (X := X) (Nstage j)) (stageRight j h))
    (hright_generators : ∀ j : J, ∀ i : X,
      stageRight j (φ i) = QuotientGroup.mk' (Nstage j) (FreeGroup.of i))
    (hidentity_basis :
      HasIdentityQuotientKernelNeighbourhoodBasis
        (Y := ZCCompletedFoxSemidirect C X H)
        (fun j : J =>
          freeProCZCCompletedFoxSemidirectBifilteredStageMapOfCoeff
            (C := C) (X := X) (H := H) Nstage nstage
            stageCoeff stageRight hgroupLike j)) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ ⊆
      ((freeProCZCCompletedFoxSemidirectClosedGeneratedTarget (C := C) φ : Subgroup
          (ZCCompletedFoxSemidirect C X H)) : Set
          (ZCCompletedFoxSemidirect C X H)) := by
  exact
    freeProCZCFoxBoundaryCycles_subset_closedGenTarget_of_graphWord_density (C := C) φ
      (boundaryCycles_subset_graphWordClosure_of_biCoeffStages
        (C := C) (X := X) (H := H) Nstage nstage φ stageCoeff stageRight
        hgroupLike hright_generators hidentity_basis)

omit [Preorder J] [∀ (j : J), Fact (0 < nstage j)] in
/-- Closed-generated target membership from coefficient-map finite stages. -/
theorem boundaryCycles_subset_closedGenTarget_of_biCoeffStages
    [Fintype X] (φ : X → H)
    (stageCoeff : ∀ j : J,
      ZCCompletedGroupAlgebra C H →+*
        foxAlgebraicStageTargetGroupAlgebra (X := X) (Nstage j) (nstage j))
    (stageRight : ∀ j : J, H →* foxAlgebraicStageTargetQuotient (X := X) (Nstage j))
    (hgroupLike : ∀ j : J, ∀ h : H,
      stageCoeff j (zcGroupLike C H h) =
        MonoidAlgebra.of (ModNCompletedCoeff (nstage j))
          (foxAlgebraicStageTargetQuotient (X := X) (Nstage j)) (stageRight j h))
    (hright_generators : ∀ j : J, ∀ i : X,
      stageRight j (φ i) = QuotientGroup.mk' (Nstage j) (FreeGroup.of i))
    (hidentity_basis :
      HasIdentityQuotientKernelNeighbourhoodBasis
        (Y := ZCCompletedFoxSemidirect C X H)
        (fun j : J =>
          freeProCZCCompletedFoxSemidirectBifilteredStageMapOfCoeff
            (C := C) (X := X) (H := H) Nstage nstage
            stageCoeff stageRight hgroupLike j))
    (hNstage_kernel :
      ∀ j : J, ∀ {w : FreeGroup X}, w ∈ Nstage j → FreeGroup.lift φ w = 1) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ ⊆
      ((freeProCZCCompletedFoxSemidirectClosedGeneratedTarget (C := C) φ : Subgroup
          (ZCCompletedFoxSemidirect C X H)) : Set
          (ZCCompletedFoxSemidirect C X H)) := by
  exact
    freeProCZCFoxBoundaryCycles_subset_closedGenTarget_of_density (C := C) φ
      (freeProCZCFoxBoundaryCycles_subset_kernelCycles_of_biCoeff_relDeriv
        (C := C) (X := X) (H := H) Nstage nstage φ
        stageCoeff stageRight hgroupLike hright_generators hidentity_basis hNstage_kernel)

end BifilteredCoefficientMaps

end

end FoxDifferential
