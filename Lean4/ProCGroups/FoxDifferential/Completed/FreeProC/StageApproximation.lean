import ProCGroups.FoxDifferential.Completed.FreeProC.Density
import ProCGroups.FoxDifferential.Completed.FiniteStage.SemidirectCycles

set_option autoImplicit false

/-!
# Fox differential: completed — free pro-\(C\) — stage approximation

The principal declarations in this module are:

- `subset_closure_of_quotientKernel_stage_exact`
  Quotient-kernel density from exact finite-stage images. For each quotient stage \(j\), let
  \(T_{\mathrm{stage}}(j)\) be the image condition satisfied by points of \(T\), and let
  \(S_{\mathrm{stage}}(j)\) be the finite-stage image of algebraic approximants from \(S\). If every
  \(T_{\mathrm{stage}}\) point is in \(S_{\mathrm{stage}}\), and every \(S_{\mathrm{stage}}\) point
  lifts to an actual point of \(S\), then \(T\) is contained in the closure of \(S\).
- `freeProCZCFoxBoundaryCycles_subset_closure_kernelCycleSet_of_stage_exact`
  Completed Fox density under quotient-stage boundary inclusion, finite-stage exactness, and
  kernel-word lifting hypotheses.
- `freeProCZCFoxBoundaryCycles_subset_closure_kernelCycleSet_of_finiteStage_semi_exact`
  Completed Fox density from finite semidirect Fox exactness at every quotient stage. Here the
  finite-stage \(T_{\mathrm{stage}}\) is the set of finite semidirect boundary cycles and the
  finite-stage \(S_{\mathrm{stage}}\) is the set of actual kernel-word derivative points. The
  hypotheses that remain are the actual comparison data between completed stages and finite Fox
  stages.
- `freeProCZCFoxBoundaryCycles_subset_closure_graphWordSet_of_finiteStage_semi_exact`
  Completed Fox graph-word density from finite semidirect Fox exactness at every quotient stage.
  This is the finite-quotient form that does not assume that words in the finite relation subgroup
  \(N_{\mathrm{stage},j}\) to be actual kernel words for \(\varphi\). A word \(w \in
  N_{\mathrm{stage},j}\) only has to project to the trivial right coordinate at the \(j\)-th finite
  stage; the completed approximant remains the genuine graph point \((D w, \varphi(w))\).
-/

namespace FoxDifferential

noncomputable section

universe u v

section GenericStageExactClosureAPI

variable {Y : Type u} [Group Y] [TopologicalSpace Y]
variable {S T : Set Y}

/--
Quotient-kernel density from exact finite-stage images. For each quotient stage \(j\), let
\(T_{\mathrm{stage}}(j)\) be the image condition satisfied by points of \(T\), and let
\(S_{\mathrm{stage}}(j)\) be the finite-stage image of algebraic approximants from \(S\). If
every \(T_{\mathrm{stage}}\) point is in \(S_{\mathrm{stage}}\), and every
\(S_{\mathrm{stage}}\) point lifts to an actual point of \(S\), then \(T\) is contained in the
closure of \(S\).
-/
theorem subset_closure_of_quotientKernel_stage_exact
    {J : Type v} {Q : J → Type*} [∀ j, Group (Q j)]
    (π : ∀ j : J, Y →* Q j)
    (hbasis : HasLeftQuotientKernelNeighbourhoodBasis (Y := Y) π)
    (Sstage Tstage : ∀ j : J, Set (Q j))
    (hTstage : ∀ y : Y, y ∈ T → ∀ j : J, π j y ∈ Tstage j)
    (hstage_exact : ∀ j : J, Tstage j ⊆ Sstage j)
    (hlift_stage : ∀ j : J, ∀ q : Q j, q ∈ Sstage j →
      ∃ s : Y, s ∈ S ∧ π j s = q) :
    T ⊆ closure S := by
  refine subset_closure_of_quotientKernel_approximation π hbasis ?_
  intro y hy j
  exact hlift_stage j (π j y) (hstage_exact j (hTstage y hy j))

end GenericStageExactClosureAPI

section CompletedFoxStageExact

open scoped Topology

variable {C : ProCGroups.FiniteGroupClass}
variable {X H : Type u}
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable [DecidableEq X]
variable [TopologicalSpace (ZCCompletedFoxSemidirect C X H)]
variable [IsTopologicalGroup (ZCCompletedFoxSemidirect C X H)]

omit [IsTopologicalGroup (ZCCompletedFoxSemidirect C X H)] in
/-- Completed Fox density under quotient-stage boundary inclusion, finite-stage exactness, and
kernel-word lifting hypotheses. -/
theorem freeProCZCFoxBoundaryCycles_subset_closure_kernelCycleSet_of_stage_exact
    [Fintype X] (φ : X → H)
    {J : Type v} {Q : J → Type*} [∀ j, Group (Q j)]
    (π : ∀ j : J,
      ZCCompletedFoxSemidirect C X H →* Q j)
    (hbasis :
      HasLeftQuotientKernelNeighbourhoodBasis
        (Y := ZCCompletedFoxSemidirect C X H) π)
    (Sstage Tstage : ∀ j : J, Set (Q j))
    (hboundary_stage :
      ∀ y : ZCCompletedFoxSemidirect C X H,
        y ∈ freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ →
          ∀ j : J, π j y ∈ Tstage j)
    (hstage_exact : ∀ j : J, Tstage j ⊆ Sstage j)
    (hlift_stage :
      ∀ j : J, ∀ q : Q j, q ∈ Sstage j →
        ∃ w : FreeGroup X,
          FreeGroup.lift φ w = 1 ∧
            π j (freeProCZCCompletedFoxSemidirectKernelWordPoint (C := C) φ w) = q) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ ⊆
      closure (freeProCZCCompletedFoxSemidirectKernelCycleSet (C := C) φ) := by
  refine subset_closure_of_quotientKernel_stage_exact
    (Y := ZCCompletedFoxSemidirect C X H)
    (S := freeProCZCCompletedFoxSemidirectKernelCycleSet (C := C) φ)
    (T := freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ)
    π hbasis Sstage Tstage hboundary_stage hstage_exact ?_
  intro j q hq
  rcases hlift_stage j q hq with ⟨w, hw, hπw⟩
  refine ⟨freeProCZCCompletedFoxSemidirectKernelWordPoint (C := C) φ w, ?_, hπw⟩
  exact freeProCZCCompletedFoxSemidirectKernelWordPoint_mem_kernelCycleSet
    (C := C) φ hw

omit [IsTopologicalGroup (ZCCompletedFoxSemidirect C X H)] in
/--
Completed Fox density from finite semidirect Fox exactness at every quotient stage. Here the
finite-stage \(T_{\mathrm{stage}}\) is the set of finite semidirect boundary cycles and the
finite-stage \(S_{\mathrm{stage}}\) is the set of actual kernel-word derivative points. The
hypotheses that remain are the actual comparison data between completed stages and finite Fox
stages.
-/
theorem freeProCZCFoxBoundaryCycles_subset_closure_kernelCycleSet_of_finiteStage_semi_exact
    [Fintype X] (φ : X → H)
    {J : Type v}
    (Nstage : J → Subgroup (FreeGroup X))
    [∀ j, (Nstage j).Normal]
    (nstage : J → ℕ)
    (π : ∀ j : J,
      ZCCompletedFoxSemidirect C X H →*
        FoxAlgebraicStageSemidirect (X := X) (Nstage j) (nstage j))
    (hbasis :
      HasLeftQuotientKernelNeighbourhoodBasis
        (Y := ZCCompletedFoxSemidirect C X H) π)
    (hboundary_stage :
      ∀ y : ZCCompletedFoxSemidirect C X H,
        y ∈ freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ →
          ∀ j : J,
            π j y ∈ foxAlgebraicStageSemidirectBoundaryCycleSet
              (X := X) (Nstage j) (nstage j))
    (hstage_exact :
      ∀ j : J,
        foxAlgebraicStageBoundaryCyclesCoveredBySourceKernel
          (X := X) (Nstage j) (nstage j))
    (hNstage_kernel :
      ∀ j : J, ∀ {w : FreeGroup X}, w ∈ Nstage j → FreeGroup.lift φ w = 1)
    (hkernel_word_projection :
      ∀ j : J, ∀ w : FreeGroup X, w ∈ Nstage j →
        π j (freeProCZCCompletedFoxSemidirectKernelWordPoint (C := C) φ w) =
          foxAlgebraicStageSemidirectKernelWordPoint (X := X) (Nstage j) (nstage j) w) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ ⊆
      closure (freeProCZCCompletedFoxSemidirectKernelCycleSet (C := C) φ) := by
  refine
    freeProCZCFoxBoundaryCycles_subset_closure_kernelCycleSet_of_stage_exact
      (C := C) φ π hbasis
      (fun j => foxAlgebraicStageSemidirectKernelWordDerivativeSet
        (X := X) (Nstage j) (nstage j))
      (fun j => foxAlgebraicStageSemidirectBoundaryCycleSet
        (X := X) (Nstage j) (nstage j))
      hboundary_stage ?_ ?_
  · intro j
    exact
      (foxAlgebraicStageSemidirectBoundaryCyclesCoveredByKernelWords_iff
        (X := X) (N := Nstage j) (n := nstage j)).2 (hstage_exact j)
  · intro j q hq
    rcases hq with ⟨w, hwN, hpoint⟩
    refine ⟨w, hNstage_kernel j hwN, ?_⟩
    calc
      π j (freeProCZCCompletedFoxSemidirectKernelWordPoint (C := C) φ w)
          = foxAlgebraicStageSemidirectKernelWordPoint (X := X) (Nstage j) (nstage j) w :=
            hkernel_word_projection j w hwN
      _ = q := hpoint

omit [IsTopologicalGroup (ZCCompletedFoxSemidirect C X H)] in
/--
Completed Fox graph-word density from finite semidirect Fox exactness at every quotient stage.
This is the finite-quotient form that does not assume that words in the finite relation subgroup
\(N_{\mathrm{stage},j}\) to be actual kernel words for \(\varphi\). A word \(w \in
N_{\mathrm{stage},j}\) only has to project to the trivial right coordinate at the \(j\)-th
finite stage; the completed approximant remains the genuine graph point \((D w, \varphi(w))\).
-/
theorem freeProCZCFoxBoundaryCycles_subset_closure_graphWordSet_of_finiteStage_semi_exact
    [Fintype X] (φ : X → H)
    {J : Type v}
    (Nstage : J → Subgroup (FreeGroup X))
    [∀ j, (Nstage j).Normal]
    (nstage : J → ℕ)
    (π : ∀ j : J,
      ZCCompletedFoxSemidirect C X H →*
        FoxAlgebraicStageSemidirect (X := X) (Nstage j) (nstage j))
    (hbasis :
      HasLeftQuotientKernelNeighbourhoodBasis
        (Y := ZCCompletedFoxSemidirect C X H) π)
    (hboundary_stage :
      ∀ y : ZCCompletedFoxSemidirect C X H,
        y ∈ freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ →
          ∀ j : J,
            π j y ∈ foxAlgebraicStageSemidirectBoundaryCycleSet
              (X := X) (Nstage j) (nstage j))
    (hstage_exact :
      ∀ j : J,
        foxAlgebraicStageBoundaryCyclesCoveredBySourceKernel
          (X := X) (Nstage j) (nstage j))
    (hgraph_word_projection :
      ∀ j : J, ∀ w : FreeGroup X, w ∈ Nstage j →
        π j (freeProCZCCompletedFoxSemidirectGraphWordPoint (C := C) φ w) =
          foxAlgebraicStageSemidirectKernelWordPoint (X := X) (Nstage j) (nstage j) w) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ ⊆
      closure (freeProCZCCompletedFoxSemidirectGraphWordSet (C := C) φ) := by
  refine subset_closure_of_quotientKernel_stage_exact
    (Y := ZCCompletedFoxSemidirect C X H)
    (S := freeProCZCCompletedFoxSemidirectGraphWordSet (C := C) φ)
    (T := freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ)
    π hbasis
    (fun j => foxAlgebraicStageSemidirectKernelWordDerivativeSet
      (X := X) (Nstage j) (nstage j))
    (fun j => foxAlgebraicStageSemidirectBoundaryCycleSet
      (X := X) (Nstage j) (nstage j))
    hboundary_stage ?_ ?_
  · intro j
    exact
      (foxAlgebraicStageSemidirectBoundaryCyclesCoveredByKernelWords_iff
        (X := X) (N := Nstage j) (n := nstage j)).2 (hstage_exact j)
  · intro j q hq
    rcases hq with ⟨w, hwN, hpoint⟩
    refine ⟨freeProCZCCompletedFoxSemidirectGraphWordPoint (C := C) φ w, ?_, ?_⟩
    · exact ⟨w, rfl⟩
    · calc
        π j (freeProCZCCompletedFoxSemidirectGraphWordPoint (C := C) φ w)
            = foxAlgebraicStageSemidirectKernelWordPoint (X := X) (Nstage j) (nstage j) w :=
              hgraph_word_projection j w hwN
        _ = q := hpoint

/--
Finite-stage semidirect exactness places every completed boundary cycle in the closed generated
Fox graph target without assuming that finite relation words are actual kernel words.
-/
theorem freeProCZCFoxBoundaryCycles_subset_closedGenTarget_of_finiteStage_graphWord_semi_exact
    [Fintype X] (φ : X → H)
    {J : Type v}
    (Nstage : J → Subgroup (FreeGroup X))
    [∀ j, (Nstage j).Normal]
    (nstage : J → ℕ)
    (π : ∀ j : J,
      ZCCompletedFoxSemidirect C X H →*
        FoxAlgebraicStageSemidirect (X := X) (Nstage j) (nstage j))
    (hbasis :
      HasLeftQuotientKernelNeighbourhoodBasis
        (Y := ZCCompletedFoxSemidirect C X H) π)
    (hboundary_stage :
      ∀ y : ZCCompletedFoxSemidirect C X H,
        y ∈ freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ →
          ∀ j : J,
            π j y ∈ foxAlgebraicStageSemidirectBoundaryCycleSet
              (X := X) (Nstage j) (nstage j))
    (hstage_exact :
      ∀ j : J,
        foxAlgebraicStageBoundaryCyclesCoveredBySourceKernel
          (X := X) (Nstage j) (nstage j))
    (hgraph_word_projection :
      ∀ j : J, ∀ w : FreeGroup X, w ∈ Nstage j →
        π j (freeProCZCCompletedFoxSemidirectGraphWordPoint (C := C) φ w) =
          foxAlgebraicStageSemidirectKernelWordPoint (X := X) (Nstage j) (nstage j) w) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ ⊆
      ((freeProCZCCompletedFoxSemidirectClosedGeneratedTarget (C := C) φ : Subgroup
          (ZCCompletedFoxSemidirect C X H)) : Set
          (ZCCompletedFoxSemidirect C X H)) := by
  exact
    freeProCZCFoxBoundaryCycles_subset_closedGenTarget_of_graphWord_density (C := C) φ
      (freeProCZCFoxBoundaryCycles_subset_closure_graphWordSet_of_finiteStage_semi_exact
        (C := C) φ Nstage nstage π hbasis hboundary_stage hstage_exact
        hgraph_word_projection)

/--
The finite-stage semidirect exactness route also places every completed boundary cycle in the
closed generated Fox graph target.
-/
theorem freeProCZCFoxBoundaryCycles_subset_closedGenTarget_of_finiteStage_semi_exact
    [Fintype X] (φ : X → H)
    {J : Type v}
    (Nstage : J → Subgroup (FreeGroup X))
    [∀ j, (Nstage j).Normal]
    (nstage : J → ℕ)
    (π : ∀ j : J,
      ZCCompletedFoxSemidirect C X H →*
        FoxAlgebraicStageSemidirect (X := X) (Nstage j) (nstage j))
    (hbasis :
      HasLeftQuotientKernelNeighbourhoodBasis
        (Y := ZCCompletedFoxSemidirect C X H) π)
    (hboundary_stage :
      ∀ y : ZCCompletedFoxSemidirect C X H,
        y ∈ freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ →
          ∀ j : J,
            π j y ∈ foxAlgebraicStageSemidirectBoundaryCycleSet
              (X := X) (Nstage j) (nstage j))
    (hstage_exact :
      ∀ j : J,
        foxAlgebraicStageBoundaryCyclesCoveredBySourceKernel
          (X := X) (Nstage j) (nstage j))
    (hNstage_kernel :
      ∀ j : J, ∀ {w : FreeGroup X}, w ∈ Nstage j → FreeGroup.lift φ w = 1)
    (hkernel_word_projection :
      ∀ j : J, ∀ w : FreeGroup X, w ∈ Nstage j →
        π j (freeProCZCCompletedFoxSemidirectKernelWordPoint (C := C) φ w) =
          foxAlgebraicStageSemidirectKernelWordPoint (X := X) (Nstage j) (nstage j) w) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ ⊆
      ((freeProCZCCompletedFoxSemidirectClosedGeneratedTarget (C := C) φ : Subgroup
          (ZCCompletedFoxSemidirect C X H)) : Set
          (ZCCompletedFoxSemidirect C X H)) := by
  exact
    freeProCZCFoxBoundaryCycles_subset_closedGenTarget_of_density (C := C) φ
      (freeProCZCFoxBoundaryCycles_subset_closure_kernelCycleSet_of_finiteStage_semi_exact
        (C := C) φ Nstage nstage π hbasis hboundary_stage hstage_exact
        hNstage_kernel hkernel_word_projection)

end CompletedFoxStageExact

end

end FoxDifferential
