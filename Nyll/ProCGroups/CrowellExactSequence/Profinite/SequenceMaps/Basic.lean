/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.Continuous.Universal.NaturalTopology

/-!
# Basic maps in the profinite Crowell sequence

This file defines the completed differential boundary and the maps from completed and separated
differential modules to the completed \(\mathbb Z_C\)-group algebra. It proves their values on
universal differentials and compatibility with separation.
-/

namespace CrowellExactSequence

noncomputable section

open scoped BigOperators
open FoxDifferential

universe u v w

variable {G H : Type u}
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/--
The displayed boundary map \(A_{\psi}(C) \to \mathbb{Z}_C\llbracket H\rrbracket\) sends the
generator \(dg\) to \(\psi(g)-1\).
-/
def presentedCompletedDifferentialBoundaryProCInteger
    (C : ProCGroups.FiniteGroupClass.{u}) (psi : ContinuousMonoidHom G H) (g : G) :
    ZCCompletedGroupAlgebra C H :=
  zcCompletedGroupAlgebraBoundary C psi.toMonoidHom g

/-- The displayed Crowell map \(A_{\psi}(C) \to \mathbb{Z}_C\llbracket H\rrbracket\). -/
def presentedCompletedDifferentialToCompletedGroupAlgebraProCInteger
    (C : ProCGroups.FiniteGroupClass.{u}) (psi : ContinuousMonoidHom G H) :
    ZCCompletedDifferentialModule C psi.toMonoidHom →ₗ[ZCCompletedGroupAlgebra C H]
      ZCCompletedGroupAlgebra C H :=
  zcToCompletedGroupAlgebra C psi.toMonoidHom

/--
The displayed Crowell boundary \(A_{\psi}(C)_{\mathrm{sep}} \to \mathbb{Z}_C\llbracket
H\rrbracket\) from the separated completed middle term.
-/
def presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger
    (C : ProCGroups.FiniteGroupClass.{u})
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (psi : ContinuousMonoidHom G H) :
    ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom →ₗ[ZCCompletedGroupAlgebra C H]
      ZCCompletedGroupAlgebra C H :=
  zcSeparatedCompletedDifferentialModuleToCompletedGroupAlgebra C hC psi

omit [IsTopologicalGroup G] in
/-- The displayed Crowell map sends the universal differential \(dg\) to \(\psi(g)-1\). -/
@[simp]
theorem presentedCompletedDifferentialToCompletedGroupAlgebraProCInteger_d
    (C : ProCGroups.FiniteGroupClass.{u}) (psi : ContinuousMonoidHom G H) (g : G) :
    presentedCompletedDifferentialToCompletedGroupAlgebraProCInteger (G := G) (H := H) C psi
        (zcUniversalDifferential C psi.toMonoidHom g) =
      presentedCompletedDifferentialBoundaryProCInteger (G := G) (H := H) C psi g := by
  exact zcToCompletedGroupAlgebra_universal C psi.toMonoidHom g

omit [IsTopologicalGroup G] in
/--
The separated Crowell boundary sends the separated universal differential \(dg\) to
\(\psi(g)-1\).
-/
@[simp]
theorem presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger_d
    (C : ProCGroups.FiniteGroupClass.{u})
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (psi : ContinuousMonoidHom G H) (g : G) :
    presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger
        (G := G) (H := H) C hC psi
        (zcSeparatedUniversalDifferential C psi.toMonoidHom g) =
      presentedCompletedDifferentialBoundaryProCInteger (G := G) (H := H) C psi g := by
  exact zcSeparatedCompletedDifferentialModuleToCompletedGroupAlgebra_universal
    (G := G) (H := H) C hC psi g

omit [IsTopologicalGroup G] in
/--
Passing the completed differential module to its separated quotient before applying the
separated Crowell map recovers the completed Crowell map.
-/
theorem presentedSepToZC_comp_toSep
    (C : ProCGroups.FiniteGroupClass.{u})
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (psi : ContinuousMonoidHom G H) :
    (presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger
        (G := G) (H := H) C hC psi).comp
      (zcCompletedDifferentialModuleToSeparated C psi.toMonoidHom) =
    presentedCompletedDifferentialToCompletedGroupAlgebraProCInteger
      (G := G) (H := H) C psi := by
  exact zcSeparatedCompletedDifferentialModuleToCompletedGroupAlgebra_comp_toSeparated
    (G := G) (H := H) C hC psi

end

end CrowellExactSequence
