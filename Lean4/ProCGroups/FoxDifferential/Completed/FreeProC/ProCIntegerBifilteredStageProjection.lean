import ProCGroups.FoxDifferential.Completed.FreeProC.ProCIntegerStageCoeffProjection

set_option autoImplicit false

/-!
# Fox differential: completed — free pro-\(C\) — pro c integer bifiltered stage projection

The principal declarations in this module are:

- `zcCompletedGroupAlgebraBifilteredStageCoeffMap`
  The completed-to-finite coefficient map at a bifiltered stage, built from an actual
  \(\mathbb{Z}_C\llbracket H\rrbracket\) stage projection.
- `zcCompletedGroupAlgebraBifilteredStageCoeffMap_apply`
  The bifiltered stage coefficient map evaluates a completed element by first projecting to the
  selected completed group-algebra stage and then changing coefficients.
- `zcCompletedGroupAlgebraBifilteredStageCoeffMap_groupLike`
  Group-like formula for a bifiltered stage projection, in terms of the chosen quotient map.
- `zcCompletedGroupAlgebraBifilteredStageCoeffMap_groupLike_eq_stageRight`
  Group-like formula rewritten through the finite right quotient map.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.ProC
open ProCGroups.InverseSystems

universe u v

section BifilteredFromZCStages

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
variable (zcIndex : J → ZCCompletedGroupAlgebraIndex C H)
variable (hzcIndex : ∀ {i j : J}, i ≤ j → zcIndex i ≤ zcIndex j)
variable (hmod : ∀ j : J, nstage j ∣ (zcIndex j).1.modulus)
variable (qmap : ∀ j : J,
  CompletedGroupAlgebraQuotientInClass H C (zcIndex j).2 →*
    foxAlgebraicStageTargetQuotient (X := X) (Nstage j))

/--
The completed-to-finite coefficient map at a bifiltered stage, built from an actual
\(\mathbb{Z}_C\llbracket H\rrbracket\) stage projection.
-/
def zcCompletedGroupAlgebraBifilteredStageCoeffMap
    (j : J) :
    ZCCompletedGroupAlgebra C H →+*
      foxAlgebraicStageTargetGroupAlgebra (X := X) (Nstage j) (nstage j) :=
  zcCompletedGroupAlgebraFoxAlgebraicStageCoeffMap
    (C := C) (X := X) (H := H) (Nstage j) (nstage j) (zcIndex j)
    (hmod j) (qmap j)

omit [DecidableEq X] [TopologicalSpace (ZCCompletedFoxSemidirect C X H)] [IsTopologicalGroup
    (ZCCompletedFoxSemidirect C X H)] [Preorder J] [∀ (j : J), Fact (0 < nstage j)] in
/--
The bifiltered stage coefficient map evaluates a completed element by first projecting to the
selected completed group-algebra stage and then changing coefficients.
-/
@[simp]
theorem zcCompletedGroupAlgebraBifilteredStageCoeffMap_apply
    (j : J) (a : ZCCompletedGroupAlgebra C H) :
    zcCompletedGroupAlgebraBifilteredStageCoeffMap
        (C := C) (X := X) (H := H) Nstage nstage zcIndex hmod qmap j a =
      zcCompletedGroupAlgebraFoxAlgebraicStageCoeffMap
        (C := C) (X := X) (H := H) (Nstage j) (nstage j) (zcIndex j)
        (hmod j) (qmap j) a :=
  rfl

omit [TopologicalSpace (ZCCompletedFoxSemidirect C X H)] [IsTopologicalGroup
    (ZCCompletedFoxSemidirect C X H)] [Preorder J] in
omit [DecidableEq X] [∀ (j : J), Fact (0 < nstage j)] in
/-- Group-like formula for a bifiltered stage projection, in terms of the chosen quotient map. -/
theorem zcCompletedGroupAlgebraBifilteredStageCoeffMap_groupLike
    (j : J) (h : H) :
    zcCompletedGroupAlgebraBifilteredStageCoeffMap
        (C := C) (X := X) (H := H) Nstage nstage zcIndex hmod qmap j
        (zcGroupLike C H h) =
      MonoidAlgebra.of (ModNCompletedCoeff (nstage j))
        (foxAlgebraicStageTargetQuotient (X := X) (Nstage j))
        (qmap j (QuotientGroup.mk h)) := by
  exact zcCompletedGroupAlgebraFoxAlgebraicStageCoeffMap_groupLike
    (C := C) (X := X) (H := H) (Nstage j) (nstage j) (zcIndex j)
    (hmod j) (qmap j) h

omit [TopologicalSpace (ZCCompletedFoxSemidirect C X H)] [IsTopologicalGroup
    (ZCCompletedFoxSemidirect C X H)] [Preorder J] in
omit [DecidableEq X] [∀ (j : J), Fact (0 < nstage j)] in
/-- Group-like formula rewritten through the finite right quotient map. -/
theorem zcCompletedGroupAlgebraBifilteredStageCoeffMap_groupLike_eq_stageRight
    (stageRight : ∀ j : J,
      H →* foxAlgebraicStageTargetQuotient (X := X) (Nstage j))
    (hqmap_groupLike : ∀ j : J, ∀ h : H,
      qmap j (QuotientGroup.mk h) = stageRight j h)
    (j : J) (h : H) :
    zcCompletedGroupAlgebraBifilteredStageCoeffMap
        (C := C) (X := X) (H := H) Nstage nstage zcIndex hmod qmap j
        (zcGroupLike C H h) =
      MonoidAlgebra.of (ModNCompletedCoeff (nstage j))
        (foxAlgebraicStageTargetQuotient (X := X) (Nstage j)) (stageRight j h) := by
  rw [zcCompletedGroupAlgebraBifilteredStageCoeffMap_groupLike]
  rw [hqmap_groupLike j h]

omit [TopologicalSpace (ZCCompletedFoxSemidirect C X H)] [IsTopologicalGroup
    (ZCCompletedFoxSemidirect C X H)] in
omit [DecidableEq X] [∀ (j : J), Fact (0 < nstage j)] in
/-- Compatibility of the completed-to-finite coefficient maps under a bifiltered transition. -/
theorem zcCompletedGroupAlgebraBifilteredStageCoeffMap_transition
    (hcoeff_mod : ∀ {i j : J} (hij : i ≤ j),
      ∀ a : ModNCompletedCoeff (zcIndex j).1.modulus,
        modNCompletedCoeffMap
            (n := nstage i) (m := (zcIndex i).1.modulus) (hmod i)
            (modNCompletedCoeffMap
              (n := (zcIndex i).1.modulus) (m := (zcIndex j).1.modulus)
              (hzcIndex hij).1 a) =
          modNCompletedCoeffMap (n := nstage i) (m := nstage j) (hn hij)
            (modNCompletedCoeffMap
              (n := nstage j) (m := (zcIndex j).1.modulus) (hmod j) a))
    (hqmap_transition : ∀ {i j : J} (hij : i ≤ j),
      ∀ q : CompletedGroupAlgebraQuotientInClass H C (zcIndex j).2,
        qmap i
            ((OpenNormalSubgroupInClass.map
              (C := C) (G := H)
              (U := OrderDual.ofDual (zcIndex i).2)
              (V := OrderDual.ofDual (zcIndex j).2)
              (hzcIndex hij).2) q) =
          foxAlgebraicStageTargetQuotientMap (X := X) (hN hij) (qmap j q))
    {i j : J} (hij : i ≤ j)
    (a : ZCCompletedGroupAlgebra C H) :
    foxAlgebraicStageBifilteredTargetGroupAlgebraMap (X := X) (hN hij) (hn hij)
        (zcCompletedGroupAlgebraBifilteredStageCoeffMap
          (C := C) (X := X) (H := H) Nstage nstage zcIndex hmod qmap j a) =
      zcCompletedGroupAlgebraBifilteredStageCoeffMap
        (C := C) (X := X) (H := H) Nstage nstage zcIndex hmod qmap i a := by
  exact zcCompletedGroupAlgebraFoxAlgebraicStageCoeffMap_transition
    (C := C) (X := X) (H := H) (hN hij) (hn hij) (hzcIndex hij)
    (hmod i) (hmod j) (hcoeff_mod hij) (qmap i) (qmap j)
    (hqmap_transition hij) a

omit [Preorder J] [∀ (j : J), Fact (0 < nstage j)] in
/--
Completed density from actual \(\mathbb{Z}_C\llbracket H\rrbracket\) finite-stage projections.
This is the coefficient-map route with the coefficient maps specialized to genuine finite-stage
projections of the completed group algebra.
-/
theorem freeProCZCFoxBoundaryCycles_subset_closure_kernelCycleSet_of_zcBiStageProj_relDeriv
    [Fintype X] (φ : X → H)
    (stageRight : ∀ j : J, H →* foxAlgebraicStageTargetQuotient (X := X) (Nstage j))
    (hqmap_groupLike : ∀ j : J, ∀ h : H,
      qmap j (QuotientGroup.mk h) = stageRight j h)
    (hright_generators : ∀ j : J, ∀ i : X,
      stageRight j (φ i) = QuotientGroup.mk' (Nstage j) (FreeGroup.of i))
    (hidentity_basis :
      HasIdentityQuotientKernelNeighbourhoodBasis
        (Y := ZCCompletedFoxSemidirect C X H)
        (fun j : J =>
          freeProCZCCompletedFoxSemidirectBifilteredStageMapOfCoeff
            (C := C) (X := X) (H := H) Nstage nstage
            (fun k => zcCompletedGroupAlgebraBifilteredStageCoeffMap
              (C := C) (X := X) (H := H) Nstage nstage zcIndex hmod qmap k)
            stageRight
            (fun k h =>
              zcCompletedGroupAlgebraBifilteredStageCoeffMap_groupLike_eq_stageRight
                (C := C) (X := X) (H := H) Nstage nstage zcIndex hmod qmap
                stageRight hqmap_groupLike k h)
            j))
    (hNstage_kernel :
      ∀ j : J, ∀ {w : FreeGroup X}, w ∈ Nstage j → FreeGroup.lift φ w = 1) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ ⊆
      closure (freeProCZCCompletedFoxSemidirectKernelCycleSet (C := C) φ) := by
  exact
    freeProCZCFoxBoundaryCycles_subset_kernelCycles_of_biCoeff_relDeriv
      (C := C) (X := X) (H := H) Nstage nstage φ
      (fun k => zcCompletedGroupAlgebraBifilteredStageCoeffMap
        (C := C) (X := X) (H := H) Nstage nstage zcIndex hmod qmap k)
      stageRight
      (fun k h =>
        zcCompletedGroupAlgebraBifilteredStageCoeffMap_groupLike_eq_stageRight
          (C := C) (X := X) (H := H) Nstage nstage zcIndex hmod qmap
          stageRight hqmap_groupLike k h)
      hright_generators hidentity_basis hNstage_kernel

omit [Preorder J] [∀ (j : J), Fact (0 < nstage j)] in
/--
Completed graph-word density from actual \(\mathbb{Z}_C\llbracket H\rrbracket\) finite-stage
projections. This variant removes the completed kernel-word assumption from the density step.
Finite-stage relation words are used through their finite right-coordinate equation only.
-/
theorem freeProCZCFoxBoundaryCycles_subset_closure_graphWordSet_of_zcBiStageProj_relDeriv
    [Fintype X] (φ : X → H)
    (stageRight : ∀ j : J, H →* foxAlgebraicStageTargetQuotient (X := X) (Nstage j))
    (hqmap_groupLike : ∀ j : J, ∀ h : H,
      qmap j (QuotientGroup.mk h) = stageRight j h)
    (hright_generators : ∀ j : J, ∀ i : X,
      stageRight j (φ i) = QuotientGroup.mk' (Nstage j) (FreeGroup.of i))
    (hidentity_basis :
      HasIdentityQuotientKernelNeighbourhoodBasis
        (Y := ZCCompletedFoxSemidirect C X H)
        (fun j : J =>
          freeProCZCCompletedFoxSemidirectBifilteredStageMapOfCoeff
            (C := C) (X := X) (H := H) Nstage nstage
            (fun k => zcCompletedGroupAlgebraBifilteredStageCoeffMap
              (C := C) (X := X) (H := H) Nstage nstage zcIndex hmod qmap k)
            stageRight
            (fun k h =>
              zcCompletedGroupAlgebraBifilteredStageCoeffMap_groupLike_eq_stageRight
                (C := C) (X := X) (H := H) Nstage nstage zcIndex hmod qmap
                stageRight hqmap_groupLike k h)
            j)) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ ⊆
      closure (freeProCZCCompletedFoxSemidirectGraphWordSet (C := C) φ) := by
  exact
    boundaryCycles_subset_graphWordClosure_of_biCoeffStages
      (C := C) (X := X) (H := H) Nstage nstage φ
      (fun k => zcCompletedGroupAlgebraBifilteredStageCoeffMap
        (C := C) (X := X) (H := H) Nstage nstage zcIndex hmod qmap k)
      stageRight
      (fun k h =>
        zcCompletedGroupAlgebraBifilteredStageCoeffMap_groupLike_eq_stageRight
          (C := C) (X := X) (H := H) Nstage nstage zcIndex hmod qmap
          stageRight hqmap_groupLike k h)
      hright_generators hidentity_basis

omit [Preorder J] [∀ (j : J), Fact (0 < nstage j)] in
/--
Closed-generated target membership from actual \(\mathbb{Z}_C\llbracket H\rrbracket\)
finite-stage projections, using graph-word density rather than completed kernel-word density.
-/
theorem freeProCZCFoxBoundaryCycles_subset_closedGenTarget_of_zcBiStageProj_graphRelDeriv
    [Fintype X] (φ : X → H)
    (stageRight : ∀ j : J, H →* foxAlgebraicStageTargetQuotient (X := X) (Nstage j))
    (hqmap_groupLike : ∀ j : J, ∀ h : H,
      qmap j (QuotientGroup.mk h) = stageRight j h)
    (hright_generators : ∀ j : J, ∀ i : X,
      stageRight j (φ i) = QuotientGroup.mk' (Nstage j) (FreeGroup.of i))
    (hidentity_basis :
      HasIdentityQuotientKernelNeighbourhoodBasis
        (Y := ZCCompletedFoxSemidirect C X H)
        (fun j : J =>
          freeProCZCCompletedFoxSemidirectBifilteredStageMapOfCoeff
            (C := C) (X := X) (H := H) Nstage nstage
            (fun k => zcCompletedGroupAlgebraBifilteredStageCoeffMap
              (C := C) (X := X) (H := H) Nstage nstage zcIndex hmod qmap k)
            stageRight
            (fun k h =>
              zcCompletedGroupAlgebraBifilteredStageCoeffMap_groupLike_eq_stageRight
                (C := C) (X := X) (H := H) Nstage nstage zcIndex hmod qmap
                stageRight hqmap_groupLike k h)
            j)) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ ⊆
      ((freeProCZCCompletedFoxSemidirectClosedGeneratedTarget (C := C) φ : Subgroup
          (ZCCompletedFoxSemidirect C X H)) : Set
          (ZCCompletedFoxSemidirect C X H)) := by
  exact
    freeProCZCFoxBoundaryCycles_subset_closedGenTarget_of_graphWord_density (C := C) φ
      (freeProCZCFoxBoundaryCycles_subset_closure_graphWordSet_of_zcBiStageProj_relDeriv
        (C := C) (X := X) (H := H) Nstage nstage zcIndex hmod qmap φ
        stageRight hqmap_groupLike hright_generators hidentity_basis)

omit [Preorder J] [∀ (j : J), Fact (0 < nstage j)] in
/--
Closed-generated target membership from actual \(\mathbb{Z}_C\llbracket H\rrbracket\)
finite-stage projections.
-/
theorem freeProCZCFoxBoundaryCycles_subset_closedGenTarget_of_zcBiStageProj_relDeriv
    [Fintype X] (φ : X → H)
    (stageRight : ∀ j : J, H →* foxAlgebraicStageTargetQuotient (X := X) (Nstage j))
    (hqmap_groupLike : ∀ j : J, ∀ h : H,
      qmap j (QuotientGroup.mk h) = stageRight j h)
    (hright_generators : ∀ j : J, ∀ i : X,
      stageRight j (φ i) = QuotientGroup.mk' (Nstage j) (FreeGroup.of i))
    (hidentity_basis :
      HasIdentityQuotientKernelNeighbourhoodBasis
        (Y := ZCCompletedFoxSemidirect C X H)
        (fun j : J =>
          freeProCZCCompletedFoxSemidirectBifilteredStageMapOfCoeff
            (C := C) (X := X) (H := H) Nstage nstage
            (fun k => zcCompletedGroupAlgebraBifilteredStageCoeffMap
              (C := C) (X := X) (H := H) Nstage nstage zcIndex hmod qmap k)
            stageRight
            (fun k h =>
              zcCompletedGroupAlgebraBifilteredStageCoeffMap_groupLike_eq_stageRight
                (C := C) (X := X) (H := H) Nstage nstage zcIndex hmod qmap
                stageRight hqmap_groupLike k h)
            j))
    (hNstage_kernel :
      ∀ j : J, ∀ {w : FreeGroup X}, w ∈ Nstage j → FreeGroup.lift φ w = 1) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ ⊆
      ((freeProCZCCompletedFoxSemidirectClosedGeneratedTarget (C := C) φ : Subgroup
          (ZCCompletedFoxSemidirect C X H)) : Set
          (ZCCompletedFoxSemidirect C X H)) := by
  exact
    freeProCZCFoxBoundaryCycles_subset_closedGenTarget_of_density (C := C) φ
      (freeProCZCFoxBoundaryCycles_subset_closure_kernelCycleSet_of_zcBiStageProj_relDeriv
        (C := C) (X := X) (H := H) Nstage nstage zcIndex hmod qmap φ
        stageRight hqmap_groupLike hright_generators hidentity_basis hNstage_kernel)

end BifilteredFromZCStages

end

end FoxDifferential
