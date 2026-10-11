/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.CrowellExactSequence.Profinite.KernelInjectivity
import Nyll.ProCGroups.CrowellExactSequence.Profinite.SequenceMaps.Basic
import Nyll.ProCGroups.CrowellExactSequence.Profinite.SequenceMaps.Exactness
import Nyll.ProCGroups.FoxDifferential.Completed.Continuous.ClosedGeneratedCoordinates.Comparison

/-!
# Profinite Crowell middle exactness

This file reduces exactness at the separated completed differential module to integration of
coordinate cycles. It derives the middle image/kernel equality from finite-stage lifts and proves
the required boundary vanishing under the closed-generator graph hypothesis.
-/

namespace CrowellExactSequence

noncomputable section

open FoxDifferential
open ProCGroups.ProC
open ProCGroups.Completion
open ProCGroups.InverseSystems

universe u v

variable {G H : Type u}
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- The separated displayed boundary kills the separated kernel boundary. -/
theorem presentedSepToZC_profiniteKernelAbelianizationBoundaryAddSep
    (C : ProCGroups.FiniteGroupClass.{u})
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (psi : ContinuousMonoidHom G H)
    (x : ProfiniteKernelAbelianizationAdd psi) :
    presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger
        (G := G) (H := H) C hC psi
        (profiniteKernelAbelianizationBoundaryAddProCIntegerSep
          (G := G) (H := H) C psi x) =
      0 := by
  change
    (fun y : ProfiniteKernelAbelianization psi =>
      presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger
          (G := G) (H := H) C hC psi
          (profiniteKernelAbelianizationBoundaryAddProCIntegerSep
            (G := G) (H := H) C psi (Additive.ofMul y)) =
        0) (Additive.toMul x)
  refine QuotientGroup.induction_on (Additive.toMul x) ?_
  intro n
  change
    presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger
        (G := G) (H := H) C hC psi
        (profiniteKernelAbelianizationBoundaryAddProCIntegerSep
          (G := G) (H := H) C psi
          (Additive.ofMul
            (QuotientGroup.mk'
              (Subgroup.topologicalClosure (commutator (ProfiniteKernelSubgroup psi))) n))) =
      0
  rw [profiniteKernelAbelianizationBoundaryAddProCIntegerSep_of,
    presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger_d]
  exact zcCompletedGroupAlgebraBoundary_eq_zero_of_mem_ker
    (C := C) (H := H) psi.toMonoidHom n.2

/--
Exactness of the separated additive boundary is equivalent to integrability of all separated
delta cycles.
-/
theorem exact_boundaryAddZC_sep_iff_delta_cycles_integrate
    {C : ProCGroups.FiniteGroupClass.{u}}
    {hC : ProCGroups.FiniteGroupClass.Hereditary C}
    {psi : ContinuousMonoidHom G H} :
    Function.Exact
        (profiniteKernelAbelianizationBoundaryAddProCIntegerSep
          (G := G) (H := H) C psi)
        (presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger
          (G := G) (H := H) C hC psi) ↔
      ∀ a : ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom,
        presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger
            (G := G) (H := H) C hC psi a = 0 →
          ∃ n : ProfiniteKernelSubgroup psi,
            zcSeparatedUniversalDifferential C psi.toMonoidHom n.1 = a := by
  let dN :=
    profiniteKernelAbelianizationBoundaryAddProCIntegerSep
      (G := G) (H := H) C psi
  let delta :=
    presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger
      (G := G) (H := H) C hC psi
  constructor
  · intro hexact a ha
    rcases (hexact a).1 ha with ⟨x, hx⟩
    revert hx
    change
      (fun q : ProfiniteKernelAbelianization psi =>
        dN (Additive.ofMul q) = a →
          ∃ n : ProfiniteKernelSubgroup psi,
            zcSeparatedUniversalDifferential C psi.toMonoidHom n.1 = a) (Additive.toMul x)
    refine QuotientGroup.induction_on (Additive.toMul x) ?_
    intro n hn
    refine ⟨n, ?_⟩
    calc
      zcSeparatedUniversalDifferential C psi.toMonoidHom n.1 =
          dN
            (Additive.ofMul
              (QuotientGroup.mk'
                (Subgroup.topologicalClosure
                  (commutator (ProfiniteKernelSubgroup psi))) n)) :=
        (profiniteKernelAbelianizationBoundaryAddProCIntegerSep_of
          (G := G) (H := H) C psi n).symm
      _ = a := hn
  · intro hintegrates a
    constructor
    · intro ha
      rcases hintegrates a ha with ⟨n, hn⟩
      refine ⟨Additive.ofMul
        (QuotientGroup.mk'
          (Subgroup.topologicalClosure (commutator (ProfiniteKernelSubgroup psi))) n), ?_⟩
      calc
        dN
            (Additive.ofMul
              (QuotientGroup.mk'
                (Subgroup.topologicalClosure
                  (commutator (ProfiniteKernelSubgroup psi))) n)) =
            zcSeparatedUniversalDifferential C psi.toMonoidHom n.1 :=
          profiniteKernelAbelianizationBoundaryAddProCIntegerSep_of
            (G := G) (H := H) C psi n
        _ = a := hn
    · rintro ⟨x, hx⟩
      rw [← hx]
      exact
        presentedSepToZC_profiniteKernelAbelianizationBoundaryAddSep
          (G := G) (H := H) C hC psi x

/--
A coordinate lift for each cycle gives exactness of the separated additive boundary sequence.
-/
theorem exact_boundaryAddZC_sep_of_coord_cycle_lift
    (C : ProCGroups.FiniteGroupClass.{u})
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (psi : ContinuousMonoidHom G H)
    {X : Type u} [Fintype X] (family : X → G)
    (coords :
      ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom ≃ₗ[ZCCompletedGroupAlgebra C H]
        ZCFreeFoxCoordinates C (X := X) (H := H))
    (hcoords_symm :
      coords.symm.toLinearMap =
        presentedSeparatedDifferentialFamilyMapProCInteger
          (G := G) (H := H) C psi family)
    (Dcoords : G → ZCFreeFoxCoordinates C (X := X) (H := H))
    (hDcoords_kernel :
      ∀ n : ProfiniteKernelSubgroup psi,
        Dcoords n.1 =
          coords (zcSeparatedUniversalDifferential C psi.toMonoidHom n.1))
    (hcycle_lift :
      ∀ v : ZCFreeFoxCoordinates C (X := X) (H := H),
        blanchfieldLyndonFiniteFamilyMap
            (R := ZCCompletedGroupAlgebra C H)
            (fun i : X =>
              presentedCompletedDifferentialBoundaryProCInteger
                (G := G) (H := H) C psi (family i)) v = 0 →
          ∃ n : ProfiniteKernelSubgroup psi, Dcoords n.1 = v) :
    Function.Exact
      (profiniteKernelAbelianizationBoundaryAddProCIntegerSep
        (G := G) (H := H) C psi)
      (presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger
        (G := G) (H := H) C hC psi) := by
  let dN :=
    profiniteKernelAbelianizationBoundaryAddProCIntegerSep
      (G := G) (H := H) C psi
  let delta :=
    presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger
      (G := G) (H := H) C hC psi
  let blDelta :=
    blanchfieldLyndonFiniteFamilyMap
      (R := ZCCompletedGroupAlgebra C H)
      (fun i : X =>
        presentedCompletedDifferentialBoundaryProCInteger
          (G := G) (H := H) C psi (family i))
  have hblDelta_comp : delta.comp coords.symm.toLinearMap = blDelta := by
    rw [hcoords_symm]
    exact
      presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger_comp_familyMap
        (G := G) (H := H) C hC psi family
  have hblDelta_apply (y) : blDelta y = delta (coords.symm y) := by
    have h := congrArg (fun f => f y) hblDelta_comp
    change delta (coords.symm y) = blDelta y at h
    exact h.symm
  change Function.Exact dN delta
  intro a
  constructor
  · intro ha
    have hcoord_cycle : blDelta (coords a) = 0 := by
      calc
        blDelta (coords a) = delta (coords.symm (coords a)) := hblDelta_apply (coords a)
        _ = delta a := by rw [coords.symm_apply_apply]
        _ = 0 := ha
    rcases hcycle_lift (coords a) hcoord_cycle with ⟨n, hncoords⟩
    refine ⟨Additive.ofMul
      (QuotientGroup.mk'
        (Subgroup.topologicalClosure (commutator (ProfiniteKernelSubgroup psi))) n), ?_⟩
    apply coords.injective
    calc
      coords
          (dN (Additive.ofMul
            (QuotientGroup.mk'
              (Subgroup.topologicalClosure (commutator (ProfiniteKernelSubgroup psi))) n))) =
          coords (zcSeparatedUniversalDifferential C psi.toMonoidHom n.1) := by
            rw [profiniteKernelAbelianizationBoundaryAddProCIntegerSep_of]
      _ = Dcoords n.1 := (hDcoords_kernel n).symm
      _ = coords a := hncoords
  · rintro ⟨x, hx⟩
    rw [← hx]
    exact
      presentedSepToZC_profiniteKernelAbelianizationBoundaryAddSep
        (G := G) (H := H) C hC psi x

/--
Agreement of the closed-generated Magnus coordinates with the presented differential
coordinates forces the completed kernel boundary to kill the closed commutator subgroup.
-/
theorem completedBoundaryKillsTopCommZC_of_closedGen_leftGraph
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (C : ProCGroups.FiniteGroupClass.{u}) (psi : ContinuousMonoidHom G H)
    {X : Type u} [Fintype X] [DecidableEq X] (family : X → G)
    [T1Space (ZCFreeFoxCoordinates C (X := X) (H := H))]
    (hbasis_A :
      IsPresentedCompletedDifferentialFamilyBasisProCInteger
        (G := G) (H := H) C psi family)
    (hfree :
      ProCGroups.FreeProC.IsEpimorphicallyFreeProCGroupOnConvergingSet
        (C := C) X G family)
    (htarget :
      HasOpenNormalBasisInClass C
        (freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
          (C := C) (fun i : X => psi (family i)) : Subgroup
            (ZCCompletedFoxSemidirect C X H)))
    (hφconv :
      ProCGroups.FreeProC.FamilyConvergesToOneAlongOpenSubgroups
        (G :=
          (freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
            (C := C) (fun i : X => psi (family i)) : Subgroup
              (ZCCompletedFoxSemidirect C X H)))
        (freeProCZCCompletedFoxSemidirectClosedGeneratedGenerator
          (C := C) (fun i : X => psi (family i))))
    (hleft_graph_eq :
      ∀ g : G,
        freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
            (C := C) hfree (fun i : X => psi (family i)) htarget hφconv g =
          presentedCompletedDifferentialFamilyCoordinatesProCInteger
            (G := G) (H := H) C psi family hbasis_A
            (zcUniversalDifferential C psi.toMonoidHom g)) :
    CompletedBoundaryKillsTopologicalCommutatorProCInteger
      (G := G) (H := H) C psi := by
  let Dclosed : G → ZCFreeFoxCoordinates C (X := X) (H := H) :=
    fun g =>
      freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
        (C := C) hfree (fun i : X => psi (family i)) htarget hφconv g
  refine
    completedBoundaryKillsTopCommZC_of_continuous_ambient_familyCoords_fintype
      (G := G) (H := H) C psi family hbasis_A Dclosed ?_ ?_
  · simpa [Dclosed] using
      continuous_freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
        (C := C) X H hfree (fun i : X => psi (family i)) htarget hφconv
  · intro n
    exact hleft_graph_eq n.1

end

end CrowellExactSequence
