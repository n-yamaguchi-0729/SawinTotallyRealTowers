/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.Continuous.ClosedGeneratedCoordinates.Equiv
import Nyll.ProCGroups.FoxDifferential.Completed.Continuous.SemidirectKernelBasis

/-!
# Fox differential: completed — continuous — closed generated coordinates — comparison

The principal declarations in this module are:

- `continuous_familyCoordinatesZC_zcUnivDiff_of_closedGen_leftGraph`
  The paper coordinate universal differential is continuous once it is identified with the
  closed-generated completed Fox derivative vector.
- `freeProCZCCompletedFoxDerivativeVectorViaClosedGen_eq_presentedCoordinates_zcUnivDiff`
  The left coordinate of the closed-generated completed Fox graph agrees with the paper coordinate
  universal differential.
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

/--
The paper coordinate universal differential is continuous once it is identified with the
closed-generated completed Fox derivative vector.
-/
theorem continuous_familyCoordinatesZC_zcUnivDiff_of_closedGen_leftGraph
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (C : ProCGroups.FiniteGroupClass.{u}) (psi : ContinuousMonoidHom G H)
    {X : Type u} [Fintype X] [DecidableEq X] (family : X → G)
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
    Continuous
      (fun g : G =>
        presentedCompletedDifferentialFamilyCoordinatesProCInteger
          (G := G) (H := H) C psi family hbasis_A
          (zcUniversalDifferential C psi.toMonoidHom g)) := by
  let Dclosed : G → ZCFreeFoxCoordinates C (X := X) (H := H) :=
    fun g =>
      freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
        (C := C) hfree (fun i : X => psi (family i)) htarget hφconv g
  have hclosed_continuous : Continuous Dclosed := by
    simpa [Dclosed] using
      continuous_freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
        (C := C) X H hfree (fun i : X => psi (family i)) htarget hφconv
  have hcoords_eq :
      (fun g : G =>
        presentedCompletedDifferentialFamilyCoordinatesProCInteger
          (G := G) (H := H) C psi family hbasis_A
          (zcUniversalDifferential C psi.toMonoidHom g)) = Dclosed := by
    funext g
    exact (hleft_graph_eq g).symm
  rw [hcoords_eq]
  exact hclosed_continuous

/--
The left coordinate of the closed-generated completed Fox graph agrees with the paper
coordinate universal differential.
-/
theorem freeProCZCCompletedFoxDerivativeVectorViaClosedGen_eq_presentedCoordinates_zcUnivDiff
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (C : ProCGroups.FiniteGroupClass.{u}) (psi : ContinuousMonoidHom G H)
    {X : Type u} [Fintype X] [DecidableEq X] (family : X → G)
    (hbasis_A :
      IsPresentedCompletedDifferentialFamilyBasisProCInteger
        (G := G) (H := H) C psi family)
    (hfree :
      ProCGroups.FreeProC.IsEpimorphicallyFreeProCGroupOnConvergingSet
        (C := C) X G family)
    (hH : ProCGroups.ProC.HasOpenNormalBasisInClass C (H))
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
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOneAlongOpenSubgroups
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i)))) :
    ∀ g : G,
      freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
          (C := C) hfree (fun i : X => psi (family i)) htarget hφconv g =
        presentedCompletedDifferentialFamilyCoordinatesProCInteger
          (G := G) (H := H) C psi family hbasis_A
          (zcUniversalDifferential C psi.toMonoidHom g) := by
  let coords :=
    presentedCompletedDifferentialFamilyCoordinatesProCInteger
      (G := G) (H := H) C psi family hbasis_A
  let f :
      (X → ZCCompletedGroupAlgebra C H) →ₗ[
        ZCCompletedGroupAlgebra C H]
        ZCCompletedDifferentialModule C psi.toMonoidHom :=
    presentedCompletedDifferentialFamilyMapProCInteger
      (G := G) (H := H) C psi family
  let L :
      ZCCompletedDifferentialModule C psi.toMonoidHom →ₗ[
        ZCCompletedGroupAlgebra C H]
        ZCFreeFoxCoordinates C (X := X) (H := H) :=
    closedGeneratedDerivativeCoordinatesLinearMapProCInteger
      (G := G) (H := H) C psi family hfree htarget hφconv hH hφHconv hφHgen
  have hL_comp : L.comp f = LinearMap.id := by
    exact
      closedGeneratedDerivativeCoordinatesLinearMapProCInteger_comp_familyMap
        (G := G) (H := H) C psi family hfree htarget hφconv hH hφHconv hφHgen
  have hL_eq_coords : L = coords.toLinearMap := by
    exact
      presentedCompletedDifferentialFamilyCoordinatesProCInteger_eq_of_leftInverse
        (G := G) (H := H) C psi family hbasis_A L hL_comp
  intro g
  calc
    freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
        (C := C) hfree (fun i : X => psi (family i)) htarget hφconv g =
        L (zcUniversalDifferential C psi.toMonoidHom g) := by
        rw [closedGeneratedDerivativeCoordinatesLinearMapProCInteger_universal
          (G := G) (H := H) C psi family hfree htarget hφconv hH hφHconv hφHgen g]
    _ = coords
        (zcUniversalDifferential C psi.toMonoidHom g) := by
        rw [hL_eq_coords]
        rfl

end

end CrowellExactSequence
