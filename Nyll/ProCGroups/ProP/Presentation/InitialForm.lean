/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.ProP.Presentation.RelatorDepth

/-!
# Initial forms in the augmentation filtration

The degree-`n` initial form is constructed in the concrete quotient
`Iⁿ/Iⁿ⁺¹`.  A supplied depth witness produces the numerator element, and the
quotient criterion identifies vanishing with membership one layer deeper.
-/

open scoped Topology

namespace ClassFieldTower.ProP

open ProCGroups

noncomputable section

universe u

variable {p : ℕ} [Fact p.Prime]
variable {sourceData :
  FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u}
    (FiniteGroupClass.pGroup p)}

/-- The next closed augmentation layer, viewed inside the current layer. -/
def nextClosedAugmentationLayerIn (n : ℕ) :
    Submodule (ModPCompletedGroupAlgebra p sourceData.carrier)
      (closedAugmentationPower p sourceData.carrier n) :=
  Submodule.comap
    (closedAugmentationPower p sourceData.carrier n).subtype
    (closedAugmentationPower p sourceData.carrier (n + 1))

/-- The degree-`n` associated-graded augmentation piece `Iⁿ/Iⁿ⁺¹`. -/
abbrev AugmentationInitialFormSpace (n : ℕ) :=
  (closedAugmentationPower p sourceData.carrier n) ⧸
    nextClosedAugmentationLayerIn (p := p) (sourceData := sourceData) n

/-- The degree-`n` initial form of an element with a depth-`n` witness. -/
def zassenhausInitialFormAt
    (n : ℕ) (g : sourceData.carrier)
    (hg : ZassenhausDepthAtLeast p n g) :
    AugmentationInitialFormSpace (p := p) (sourceData := sourceData) n :=
  Submodule.Quotient.mk
    ⟨groupLikeDifference p sourceData.carrier g, hg⟩

/-- The initial form vanishes exactly when the element lies one layer
deeper. -/
theorem zassenhausInitialFormAt_eq_zero_iff
    (n : ℕ) (g : sourceData.carrier)
    (hg : ZassenhausDepthAtLeast p n g) :
    zassenhausInitialFormAt (sourceData := sourceData) n g hg = 0 ↔
      ZassenhausDepthAtLeast p (n + 1) g := by
  unfold zassenhausInitialFormAt
  rw [Submodule.Quotient.mk_eq_zero]
  rfl

namespace FiniteProPPresentation

variable {d r : ℕ}
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- Initial form of one displayed relator. -/
def relatorInitialFormAt
    (P : FiniteProPPresentation p d r sourceData G)
    (n : ℕ) (i : Fin r) (hi : P.RelatorZassenhausDepthAtLeast n i) :
    AugmentationInitialFormSpace (p := p) (sourceData := sourceData) n :=
  zassenhausInitialFormAt (sourceData := sourceData) n (P.relator i) hi

/-- The displayed relation family in one associated-graded degree. -/
def relatorInitialFormFamilyAt
    (P : FiniteProPPresentation p d r sourceData G)
    (n : ℕ) (hrel : ∀ i, P.RelatorZassenhausDepthAtLeast n i) :
    Fin r → AugmentationInitialFormSpace (p := p) (sourceData := sourceData) n :=
  fun i => P.relatorInitialFormAt n i (hrel i)

/-- Minimality canonically produces the degree-two initial-form family. -/
def minimalRelatorInitialFormFamily
    (P : FiniteProPPresentation p d r sourceData G) (hP : P.IsMinimal) :
    Fin r → AugmentationInitialFormSpace (p := p) (sourceData := sourceData) 2 :=
  P.relatorInitialFormFamilyAt 2 (P.relatorZassenhausDepthAtLeast_two hP)

end FiniteProPPresentation

end


end ClassFieldTower.ProP
