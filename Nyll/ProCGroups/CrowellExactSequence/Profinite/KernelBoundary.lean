/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.CrowellExactSequence.Profinite.SequenceMaps.Basic
import Nyll.ProCGroups.CrowellExactSequence.Profinite.SequenceMaps.Exactness
import Nyll.ProCGroups.ProC.Kernels

/-!
# Boundary maps from the profinite kernel

This file constructs the completed and separated boundary maps on the kernel of a profinite
presentation. It proves that these maps kill commutators and gives continuity criteria ensuring
that they kill the closure of the commutator subgroup, hence factor through topological
abelianization.
-/

namespace CrowellExactSequence

noncomputable section

open scoped BigOperators commutatorElement
open FoxDifferential
open ProCGroups.ProC

universe u

variable {G H : Type u}
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Kernel elements map multiplicatively to the Fox completed differential module. -/
def completedKernelBoundaryProCInteger
    (C : ProCGroups.FiniteGroupClass.{u}) (psi : ContinuousMonoidHom G H) :
    psi.toMonoidHom.ker →*
      Multiplicative (ZCCompletedDifferentialModule C psi.toMonoidHom) where
  toFun n := Multiplicative.ofAdd
    (zcUniversalDifferential C psi.toMonoidHom n.1)
  map_one' := by
    apply Multiplicative.toAdd.injective
    exact ScalarCrossedHom.map_one (zcUniversalDifferential C psi.toMonoidHom)
  map_mul' n₁ n₂ := by
    apply Multiplicative.toAdd.injective
    have hmul :=
      ScalarCrossedHom.map_mul (zcUniversalDifferential C psi.toMonoidHom) n₁.1 n₂.1
    have hpsi : psi.toMonoidHom n₁.1 = 1 := n₁.2
    have hadd :
        zcUniversalDifferential C psi.toMonoidHom ((n₁ * n₂ : psi.toMonoidHom.ker).1) =
          zcUniversalDifferential C psi.toMonoidHom n₁.1 +
            zcUniversalDifferential C psi.toMonoidHom n₂.1 := by
      change
        zcUniversalDifferential C psi.toMonoidHom (n₁.1 * n₂.1) =
          zcUniversalDifferential C psi.toMonoidHom n₁.1 +
            zcUniversalDifferential C psi.toMonoidHom n₂.1
      rw [hmul, zcCompletedGroupAlgebraScalar_apply, hpsi, map_one, one_smul]
    exact hadd

/-- Kernel elements map multiplicatively to the separated completed differential module. -/
def separatedCompletedKernelBoundaryProCInteger
    (C : ProCGroups.FiniteGroupClass.{u}) (psi : ContinuousMonoidHom G H) :
    psi.toMonoidHom.ker →*
      Multiplicative (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom) where
  toFun n := Multiplicative.ofAdd
    (zcSeparatedUniversalDifferential C psi.toMonoidHom n.1)
  map_one' := by
    apply Multiplicative.toAdd.injective
    change zcSeparatedUniversalDifferential C psi.toMonoidHom 1 = 0
    rw [← zcCompletedDifferentialModuleToSeparated_universal
      (C := C) (ψ := psi.toMonoidHom) (g := 1),
      ScalarCrossedHom.map_one (zcUniversalDifferential C psi.toMonoidHom)]
    exact
      (zcCompletedDifferentialModuleToSeparated C psi.toMonoidHom).map_zero
  map_mul' n₁ n₂ := by
    apply Multiplicative.toAdd.injective
    have hmul :=
      ScalarCrossedHom.map_mul
        (zcSeparatedUniversalDifferential C psi.toMonoidHom) n₁.1 n₂.1
    have hpsi : psi.toMonoidHom n₁.1 = 1 := n₁.2
    have hadd :
        zcSeparatedUniversalDifferential C psi.toMonoidHom ((n₁ * n₂ : psi.toMonoidHom.ker).1) =
          zcSeparatedUniversalDifferential C psi.toMonoidHom n₁.1 +
            zcSeparatedUniversalDifferential C psi.toMonoidHom n₂.1 := by
      change
        zcSeparatedUniversalDifferential C psi.toMonoidHom (n₁.1 * n₂.1) =
          zcSeparatedUniversalDifferential C psi.toMonoidHom n₁.1 +
            zcSeparatedUniversalDifferential C psi.toMonoidHom n₂.1
      rw [hmul, zcCompletedGroupAlgebraScalar_apply, hpsi, map_one, one_smul]
    exact hadd

omit [IsTopologicalGroup G] in
/--
Membership in the separated completed kernel-boundary kernel is equivalent to vanishing of the
corresponding finite-stage coordinate.
-/
theorem separatedCompletedKernelBoundaryProCInteger_mem_ker_iff
    {C : ProCGroups.FiniteGroupClass.{u}} {psi : ContinuousMonoidHom G H}
    {n : ProfiniteKernelSubgroup psi} :
    n ∈ (separatedCompletedKernelBoundaryProCInteger
        (G := G) (H := H) C psi).ker ↔
      ∀ i : ZCCompletedDifferentialModuleIndex C psi.toMonoidHom,
        zcCompletedDifferentialModuleStageDifferential C psi.toMonoidHom i n.1 = 0 := by
  constructor
  · intro hn i
    have hsep :
        zcSeparatedUniversalDifferential C psi.toMonoidHom n.1 = 0 := by
      change
        Multiplicative.ofAdd
            (zcSeparatedUniversalDifferential C psi.toMonoidHom n.1) =
          (1 : Multiplicative
            (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom)) at hn
      have htoAdd :=
        congrArg
          (fun x : Multiplicative
              (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom) =>
            Multiplicative.toAdd x) hn
      change
        zcSeparatedUniversalDifferential C psi.toMonoidHom n.1 = 0 at htoAdd
      exact htoAdd
    have hproj := congrArg
      (fun x : ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom =>
        zcSeparatedCompletedDifferentialModuleStageProjectionAdd C psi.toMonoidHom i x) hsep
    rw [zcSeparatedCompletedDifferentialModuleStageProjectionAdd_universal,
      (zcSeparatedCompletedDifferentialModuleStageProjectionAdd
        C psi.toMonoidHom i).map_zero] at hproj
    exact hproj
  · intro hstage
    have hsep :
        zcSeparatedUniversalDifferential C psi.toMonoidHom n.1 = 0 :=
      zcSeparatedCompletedDifferentialModuleStageProjectionsSeparate
        C psi.toMonoidHom
        (zcSeparatedUniversalDifferential C psi.toMonoidHom n.1)
        (by
          intro i
          calc
            zcSeparatedCompletedDifferentialModuleStageProjectionAdd
                C psi.toMonoidHom i
                (zcSeparatedUniversalDifferential C psi.toMonoidHom n.1) =
              zcCompletedDifferentialModuleStageDifferential
                C psi.toMonoidHom i n.1 :=
              zcSeparatedCompletedDifferentialModuleStageProjectionAdd_universal
                C psi.toMonoidHom i n.1
            _ = 0 := hstage i
            _ =
                zcSeparatedCompletedDifferentialModuleStageProjectionAdd
                  C psi.toMonoidHom i 0 :=
              (zcSeparatedCompletedDifferentialModuleStageProjectionAdd
                C psi.toMonoidHom i).map_zero.symm)
    change
      Multiplicative.ofAdd
          (zcSeparatedUniversalDifferential C psi.toMonoidHom n.1) =
        (1 : Multiplicative
          (ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom))
    simpa [hsep]

/--
The separated kernel boundary has closed kernel, because zero can be tested at every finite
stage and each finite-stage boundary is continuous.
-/
theorem isClosed_separatedCompletedKernelBoundaryProCInteger_ker
    (C : ProCGroups.FiniteGroupClass.{u}) (psi : ContinuousMonoidHom G H) :
    IsClosed
      (((separatedCompletedKernelBoundaryProCInteger
          (G := G) (H := H) C psi).ker :
        Subgroup (ProfiniteKernelSubgroup psi)) :
          Set (ProfiniteKernelSubgroup psi)) := by
  have hker_set :
      (((separatedCompletedKernelBoundaryProCInteger
          (G := G) (H := H) C psi).ker :
        Subgroup (ProfiniteKernelSubgroup psi)) :
          Set (ProfiniteKernelSubgroup psi)) =
        ⋂ i : ZCCompletedDifferentialModuleIndex C psi.toMonoidHom,
          (fun n : ProfiniteKernelSubgroup psi =>
            zcCompletedDifferentialModuleStageDifferential C psi.toMonoidHom i n.1) ⁻¹'
              ({0} : Set (ZCCompletedDifferentialModuleStage C psi.toMonoidHom i)) := by
    ext n
    simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
    exact separatedCompletedKernelBoundaryProCInteger_mem_ker_iff
      (G := G) (H := H) (C := C) (psi := psi) (n := n)
  rw [hker_set]
  refine isClosed_iInter fun i => ?_
  exact
    (isClosed_singleton
      (x := (0 : ZCCompletedDifferentialModuleStage C psi.toMonoidHom i))).preimage
      ((continuous_zcCompletedDifferentialModuleStageDifferential C psi.toMonoidHom i).comp
        continuous_subtype_val)

omit [IsTopologicalGroup G] in
/--
Algebraic part of well-definedness for the separated boundary: ordinary commutators already map
to zero.
-/
theorem separatedCompletedKernelBoundaryProCInteger_commutator_le_ker
    (C : ProCGroups.FiniteGroupClass.{u}) (psi : ContinuousMonoidHom G H) :
    commutator (ProfiniteKernelSubgroup psi) <=
      (separatedCompletedKernelBoundaryProCInteger (G := G) (H := H) C psi).ker := by
  refine Subgroup.commutator_le.mpr ?_
  intro a _ha b _hb
  change
    (separatedCompletedKernelBoundaryProCInteger (G := G) (H := H) C psi)
        (⁅a, b⁆ : ProfiniteKernelSubgroup psi) = 1
  rw [map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.2
    (mul_comm
      (separatedCompletedKernelBoundaryProCInteger (G := G) (H := H) C psi a)
      (separatedCompletedKernelBoundaryProCInteger (G := G) (H := H) C psi b))

/--
The separated kernel boundary kills \(\overline{[N,N]}\) without assuming algebraic closedness
of the raw crossed-differential relation submodule.
-/
theorem separatedBoundaryKillsTopologicalCommutatorProCInteger
    (C : ProCGroups.FiniteGroupClass.{u}) (psi : ContinuousMonoidHom G H) :
    Subgroup.topologicalClosure (commutator (ProfiniteKernelSubgroup psi)) <=
      (separatedCompletedKernelBoundaryProCInteger (G := G) (H := H) C psi).ker :=
  Subgroup.topologicalClosure_minimal
    (s := commutator (ProfiniteKernelSubgroup psi))
    (t := (separatedCompletedKernelBoundaryProCInteger (G := G) (H := H) C psi).ker)
    (separatedCompletedKernelBoundaryProCInteger_commutator_le_ker
      (G := G) (H := H) C psi)
    (isClosed_separatedCompletedKernelBoundaryProCInteger_ker
      (G := G) (H := H) C psi)

/--
If the completed kernel boundary is continuous and its target is \(T_1\), then it vanishes on the
topological closure of the kernel's commutator subgroup.
-/
theorem completedBoundaryKillsTopologicalCommutatorProCInteger_of_continuous
    (C : ProCGroups.FiniteGroupClass.{u}) (psi : ContinuousMonoidHom G H)
    [TopologicalSpace (ZCCompletedDifferentialModule C psi.toMonoidHom)]
    [T1Space (ZCCompletedDifferentialModule C psi.toMonoidHom)]
    (hcont :
      Continuous (completedKernelBoundaryProCInteger (G := G) (H := H) C psi)) :
    Subgroup.topologicalClosure (commutator (ProfiniteKernelSubgroup psi)) <=
      (completedKernelBoundaryProCInteger (G := G) (H := H) C psi).ker := by
  let : T1Space (Multiplicative (ZCCompletedDifferentialModule C psi.toMonoidHom)) := by
    change T1Space (ZCCompletedDifferentialModule C psi.toMonoidHom)
    infer_instance
  let f : ProfiniteKernelSubgroup psi →ₜ*
      Multiplicative (ZCCompletedDifferentialModule C psi.toMonoidHom) :=
    { toMonoidHom := completedKernelBoundaryProCInteger (G := G) (H := H) C psi
      continuous_toFun := hcont }
  intro x hx
  have hxmk :
      ProCGroups.Abelian.TopologicalAbelianization.mk
          (ProfiniteKernelSubgroup psi) x = 1 :=
    ProCGroups.Abelian.TopologicalAbelianization.mk_eq_one_iff.2 hx
  have hkill :=
    congrArg (fun y => ProCGroups.Abelian.TopologicalAbelianization.lift f y) hxmk
  rw [ProCGroups.Abelian.TopologicalAbelianization.lift_apply_mk, map_one] at hkill
  change (completedKernelBoundaryProCInteger (G := G) (H := H) C psi) x = 1
  exact hkill

/--
Correct topological boundary factorization condition for the genuine \(N^{\mathrm{ab}}(C)\)
map.
-/
abbrev CompletedBoundaryKillsTopologicalCommutatorProCInteger
    (C : ProCGroups.FiniteGroupClass.{u}) (psi : ContinuousMonoidHom G H) : Prop :=
  Subgroup.topologicalClosure (commutator (ProfiniteKernelSubgroup psi)) <=
    (completedKernelBoundaryProCInteger (G := G) (H := H) C psi).ker

/--
Continuity of the completed kernel boundary supplies the condition required for it to factor
through the profinite kernel's topological abelianization.
-/
theorem completedBoundaryKillsTopologicalCommutatorProCInteger_of_continuousBoundary
    (C : ProCGroups.FiniteGroupClass.{u}) (psi : ContinuousMonoidHom G H)
    [TopologicalSpace (ZCCompletedDifferentialModule C psi.toMonoidHom)]
    [T1Space (ZCCompletedDifferentialModule C psi.toMonoidHom)]
    (hcont :
      Continuous (completedKernelBoundaryProCInteger (G := G) (H := H) C psi)) :
    CompletedBoundaryKillsTopologicalCommutatorProCInteger (G := G) (H := H) C psi :=
  completedBoundaryKillsTopologicalCommutatorProCInteger_of_continuous
    (G := G) (H := H) C psi hcont

omit [IsTopologicalGroup G] in
/--
Algebraic part of well-definedness: the kernel boundary kills the ordinary commutator subgroup
of the profinite kernel. The remaining topological step is to pass from the commutator subgroup
to its closure.
-/
theorem completedKernelBoundaryProCInteger_commutator_le_ker
    (C : ProCGroups.FiniteGroupClass.{u}) (psi : ContinuousMonoidHom G H) :
    commutator (ProfiniteKernelSubgroup psi) <=
      (completedKernelBoundaryProCInteger (G := G) (H := H) C psi).ker := by
  refine Subgroup.commutator_le.mpr ?_
  intro a _ha b _hb
  change
    (completedKernelBoundaryProCInteger (G := G) (H := H) C psi)
        (⁅a, b⁆ : ProfiniteKernelSubgroup psi) = 1
  rw [map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.2
    (mul_comm
      (completedKernelBoundaryProCInteger (G := G) (H := H) C psi a)
      (completedKernelBoundaryProCInteger (G := G) (H := H) C psi b))

/-- Topological form of well-definedness from closedness of the kernel of the boundary map. -/
theorem completedBoundaryKillsTopologicalCommutatorProCInteger_of_closed_ker
    (C : ProCGroups.FiniteGroupClass.{u}) (psi : ContinuousMonoidHom G H)
    (hclosed :
      IsClosed
        (((completedKernelBoundaryProCInteger (G := G) (H := H) C psi).ker :
          Subgroup (ProfiniteKernelSubgroup psi)) : Set (ProfiniteKernelSubgroup psi))) :
    CompletedBoundaryKillsTopologicalCommutatorProCInteger (G := G) (H := H) C psi :=
  Subgroup.topologicalClosure_minimal
    (s := commutator (ProfiniteKernelSubgroup psi))
    (t := (completedKernelBoundaryProCInteger (G := G) (H := H) C psi).ker)
    (completedKernelBoundaryProCInteger_commutator_le_ker
      (G := G) (H := H) C psi)
    hclosed

omit [IsTopologicalGroup G] in
/--
Continuity of the universal completed differential on the ambient group implies continuity of
the kernel boundary.
-/
theorem continuous_completedKernelBoundaryZC_of_continuous_zcUnivDiff
    (C : ProCGroups.FiniteGroupClass.{u}) (psi : ContinuousMonoidHom G H)
    [TopologicalSpace (ZCCompletedDifferentialModule C psi.toMonoidHom)]
    (hD : Continuous (fun g : G => zcUniversalDifferential C psi.toMonoidHom g)) :
    Continuous (completedKernelBoundaryProCInteger (G := G) (H := H) C psi) := by
  change Continuous fun n : ProfiniteKernelSubgroup psi =>
    Multiplicative.ofAdd (zcUniversalDifferential C psi.toMonoidHom n.1)
  exact continuous_ofAdd.comp (hD.comp continuous_subtype_val)

/--
Well-definedness of \(d_N\) from continuity of the universal completed differential on the
ambient group.
-/
theorem completedBoundaryKillsTopCommZC_of_continuous_zcUnivDiff
    (C : ProCGroups.FiniteGroupClass.{u}) (psi : ContinuousMonoidHom G H)
    [TopologicalSpace (ZCCompletedDifferentialModule C psi.toMonoidHom)]
    [T1Space (ZCCompletedDifferentialModule C psi.toMonoidHom)]
    (hD : Continuous (fun g : G => zcUniversalDifferential C psi.toMonoidHom g)) :
    CompletedBoundaryKillsTopologicalCommutatorProCInteger (G := G) (H := H) C psi :=
  completedBoundaryKillsTopologicalCommutatorProCInteger_of_continuousBoundary
    (G := G) (H := H) C psi
    (continuous_completedKernelBoundaryZC_of_continuous_zcUnivDiff
      (G := G) (H := H) C psi hD)

/--
Finite-coordinate form of the topological well-definedness step for \(d_N\). If a finite
coordinate system on \(A_{\psi}(C)\) identifies the universal differential on the kernel with a
continuous coordinate-valued map, then the ordinary commutator-killing identity extends to
\(\overline{[N,N]}\). In paper language, this is the passage from a continuous coordinate
formula for \(D|_N\) to the well-defined map \(N^{\mathrm{ab}}(C) \to A_{\psi}(C)\).
-/
theorem completedBoundaryKillsTopCommZC_of_continuous_kernel_familyCoords_fintype
    (C : ProCGroups.FiniteGroupClass.{u}) (psi : ContinuousMonoidHom G H)
    {X : Type u} [Fintype X] (family : X → G)
    (hbasis_A :
      IsPresentedCompletedDifferentialFamilyBasisProCInteger
        (G := G) (H := H) C psi family)
    [T1Space (ZCFreeFoxCoordinates C (X := X) (H := H))]
    (Dcoords : ProfiniteKernelSubgroup psi →
      ZCFreeFoxCoordinates C (X := X) (H := H))
    (hDcoords_continuous : Continuous Dcoords)
    (hDcoords :
      ∀ n : ProfiniteKernelSubgroup psi,
        Dcoords n =
          presentedCompletedDifferentialFamilyCoordinatesProCInteger
            (G := G) (H := H) C psi family hbasis_A
            (zcUniversalDifferential C psi.toMonoidHom n.1)) :
    CompletedBoundaryKillsTopologicalCommutatorProCInteger (G := G) (H := H) C psi := by
  refine
    completedBoundaryKillsTopologicalCommutatorProCInteger_of_closed_ker
      (G := G) (H := H) C psi ?_
  have hclosed_zero :
      IsClosed ({0} : Set (ZCFreeFoxCoordinates C (X := X) (H := H))) :=
    isClosed_singleton
  have hclosed_preimage :
      IsClosed
        (Dcoords ⁻¹' ({0} : Set (ZCFreeFoxCoordinates C (X := X) (H := H)))) :=
    hclosed_zero.preimage hDcoords_continuous
  have hker_set :
      (((completedKernelBoundaryProCInteger (G := G) (H := H) C psi).ker :
          Subgroup (ProfiniteKernelSubgroup psi)) : Set (ProfiniteKernelSubgroup psi)) =
        Dcoords ⁻¹' ({0} : Set (ZCFreeFoxCoordinates C (X := X) (H := H))) := by
    ext n
    change
      completedKernelBoundaryProCInteger (G := G) (H := H) C psi n = 1 ↔
        Dcoords n = 0
    constructor
    · intro hn
      have hDzero : zcUniversalDifferential C psi.toMonoidHom n.1 = 0 := by
        change Multiplicative.ofAdd
            (zcUniversalDifferential C psi.toMonoidHom n.1) = 1 at hn
        have htoAdd :=
          congrArg
            (fun x : Multiplicative (ZCCompletedDifferentialModule C psi.toMonoidHom) =>
              Multiplicative.toAdd x) hn
        change zcUniversalDifferential C psi.toMonoidHom n.1 = 0 at htoAdd
        exact htoAdd
      rw [hDcoords n, hDzero]
      exact
        (presentedCompletedDifferentialFamilyCoordinatesProCInteger
          (G := G) (H := H) C psi family hbasis_A).map_zero
    · intro hn
      have hcoords_zero :
          presentedCompletedDifferentialFamilyCoordinatesProCInteger
              (G := G) (H := H) C psi family hbasis_A
              (zcUniversalDifferential C psi.toMonoidHom n.1) = 0 := by
        rw [← hDcoords n]
        exact hn
      have hDzero : zcUniversalDifferential C psi.toMonoidHom n.1 = 0 := by
        apply
          (presentedCompletedDifferentialFamilyCoordinatesProCInteger
            (G := G) (H := H) C psi family hbasis_A).injective
        calc
          presentedCompletedDifferentialFamilyCoordinatesProCInteger
              (G := G) (H := H) C psi family hbasis_A
              (zcUniversalDifferential C psi.toMonoidHom n.1) =
            0 := hcoords_zero
          _ =
              presentedCompletedDifferentialFamilyCoordinatesProCInteger
                (G := G) (H := H) C psi family hbasis_A 0 :=
            (presentedCompletedDifferentialFamilyCoordinatesProCInteger
              (G := G) (H := H) C psi family hbasis_A).map_zero.symm
      change Multiplicative.ofAdd
          (zcUniversalDifferential C psi.toMonoidHom n.1) =
        (1 : Multiplicative (ZCCompletedDifferentialModule C psi.toMonoidHom))
      simpa [hDzero]
  rw [hker_set]
  exact hclosed_preimage

/-- Fin-indexed finite-coordinate form of the topological well-definedness step for \(d_N\). -/
theorem completedBoundaryKillsTopCommZC_of_continuous_kernel_familyCoords
    (C : ProCGroups.FiniteGroupClass.{u}) (psi : ContinuousMonoidHom G H)
    {r : Nat} (family : Fin r → G)
    (hbasis_A :
      IsPresentedCompletedDifferentialFamilyBasisProCInteger
        (G := G) (H := H) C psi family)
    [T1Space (Fin r → ZCCompletedGroupAlgebra C H)]
    (Dcoords : ProfiniteKernelSubgroup psi → Fin r → ZCCompletedGroupAlgebra C H)
    (hDcoords_continuous : Continuous Dcoords)
    (hDcoords :
      ∀ n : ProfiniteKernelSubgroup psi,
        Dcoords n =
          presentedCompletedDifferentialFamilyCoordinatesProCInteger
            (G := G) (H := H) C psi family hbasis_A
            (zcUniversalDifferential C psi.toMonoidHom n.1)) :
    CompletedBoundaryKillsTopologicalCommutatorProCInteger (G := G) (H := H) C psi := by
  refine
    completedBoundaryKillsTopologicalCommutatorProCInteger_of_closed_ker
      (G := G) (H := H) C psi ?_
  have hclosed_zero :
      IsClosed ({0} : Set (Fin r → ZCCompletedGroupAlgebra C H)) :=
    isClosed_singleton
  have hclosed_preimage :
      IsClosed (Dcoords ⁻¹' ({0} : Set (Fin r → ZCCompletedGroupAlgebra C H))) :=
    hclosed_zero.preimage hDcoords_continuous
  have hker_set :
      (((completedKernelBoundaryProCInteger (G := G) (H := H) C psi).ker :
          Subgroup (ProfiniteKernelSubgroup psi)) : Set (ProfiniteKernelSubgroup psi)) =
        Dcoords ⁻¹' ({0} : Set (Fin r → ZCCompletedGroupAlgebra C H)) := by
    ext n
    change
      completedKernelBoundaryProCInteger (G := G) (H := H) C psi n = 1 ↔
        Dcoords n = 0
    constructor
    · intro hn
      have hDzero : zcUniversalDifferential C psi.toMonoidHom n.1 = 0 := by
        change Multiplicative.ofAdd
            (zcUniversalDifferential C psi.toMonoidHom n.1) = 1 at hn
        have htoAdd :=
          congrArg
            (fun x : Multiplicative (ZCCompletedDifferentialModule C psi.toMonoidHom) =>
              Multiplicative.toAdd x) hn
        change zcUniversalDifferential C psi.toMonoidHom n.1 = 0 at htoAdd
        exact htoAdd
      rw [hDcoords n, hDzero]
      exact
        (presentedCompletedDifferentialFamilyCoordinatesProCInteger
          (G := G) (H := H) C psi family hbasis_A).map_zero
    · intro hn
      have hcoords_zero :
          presentedCompletedDifferentialFamilyCoordinatesProCInteger
              (G := G) (H := H) C psi family hbasis_A
              (zcUniversalDifferential C psi.toMonoidHom n.1) = 0 := by
        rw [← hDcoords n]
        exact hn
      have hDzero : zcUniversalDifferential C psi.toMonoidHom n.1 = 0 := by
        apply
          (presentedCompletedDifferentialFamilyCoordinatesProCInteger
            (G := G) (H := H) C psi family hbasis_A).injective
        calc
          presentedCompletedDifferentialFamilyCoordinatesProCInteger
              (G := G) (H := H) C psi family hbasis_A
              (zcUniversalDifferential C psi.toMonoidHom n.1) =
            0 := hcoords_zero
          _ =
              presentedCompletedDifferentialFamilyCoordinatesProCInteger
                (G := G) (H := H) C psi family hbasis_A 0 :=
            (presentedCompletedDifferentialFamilyCoordinatesProCInteger
              (G := G) (H := H) C psi family hbasis_A).map_zero.symm
      change Multiplicative.ofAdd
          (zcUniversalDifferential C psi.toMonoidHom n.1) =
        (1 : Multiplicative (ZCCompletedDifferentialModule C psi.toMonoidHom))
      simpa [hDzero]
  rw [hker_set]
  exact hclosed_preimage

/--
Finite-coordinate ambient version of the completed-boundary theorem killing the top commutator
subgroup. This is the form used when a continuous Fox-coordinate formula is constructed on the
whole source and then restricted to \(\ker \psi\).
-/
theorem completedBoundaryKillsTopCommZC_of_continuous_ambient_familyCoords_fintype
    (C : ProCGroups.FiniteGroupClass.{u}) (psi : ContinuousMonoidHom G H)
    {X : Type u} [Fintype X] (family : X → G)
    (hbasis_A :
      IsPresentedCompletedDifferentialFamilyBasisProCInteger
        (G := G) (H := H) C psi family)
    [T1Space (ZCFreeFoxCoordinates C (X := X) (H := H))]
    (Dcoords : G → ZCFreeFoxCoordinates C (X := X) (H := H))
    (hDcoords_continuous : Continuous Dcoords)
    (hDcoords :
      ∀ n : ProfiniteKernelSubgroup psi,
        Dcoords n.1 =
          presentedCompletedDifferentialFamilyCoordinatesProCInteger
            (G := G) (H := H) C psi family hbasis_A
            (zcUniversalDifferential C psi.toMonoidHom n.1)) :
    CompletedBoundaryKillsTopologicalCommutatorProCInteger (G := G) (H := H) C psi := by
  exact
    completedBoundaryKillsTopCommZC_of_continuous_kernel_familyCoords_fintype
      (G := G) (H := H) C psi family hbasis_A
      (fun n : ProfiniteKernelSubgroup psi => Dcoords n.1)
      (hDcoords_continuous.comp continuous_subtype_val)
      hDcoords

/--
\(\operatorname{Fin}\)-indexed ambient-coordinate version of the completed-boundary theorem
killing the top commutator subgroup for continuous kernel-family coordinates.
-/
theorem completedBoundaryKillsTopCommZC_of_continuous_ambient_familyCoords
    (C : ProCGroups.FiniteGroupClass.{u}) (psi : ContinuousMonoidHom G H)
    {r : Nat} (family : Fin r → G)
    (hbasis_A :
      IsPresentedCompletedDifferentialFamilyBasisProCInteger
        (G := G) (H := H) C psi family)
    [T1Space (Fin r → ZCCompletedGroupAlgebra C H)]
    (Dcoords : G → Fin r → ZCCompletedGroupAlgebra C H)
    (hDcoords_continuous : Continuous Dcoords)
    (hDcoords :
      ∀ n : ProfiniteKernelSubgroup psi,
        Dcoords n.1 =
          presentedCompletedDifferentialFamilyCoordinatesProCInteger
            (G := G) (H := H) C psi family hbasis_A
            (zcUniversalDifferential C psi.toMonoidHom n.1)) :
    CompletedBoundaryKillsTopologicalCommutatorProCInteger (G := G) (H := H) C psi := by
  exact
    completedBoundaryKillsTopCommZC_of_continuous_kernel_familyCoords
      (G := G) (H := H) C psi family hbasis_A
      (fun n : ProfiniteKernelSubgroup psi => Dcoords n.1)
      (hDcoords_continuous.comp continuous_subtype_val)
      hDcoords

end

end CrowellExactSequence
