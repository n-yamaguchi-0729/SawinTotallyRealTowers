/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Ramification.GaloisValuation.AbsoluteGalois.FiniteExtensionCorrespondence
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.FiniteGaloisLevel

/-!
# Finite-level ramification intersections for a complete discretely valued field

At each finite Galois level, this file uses the chosen integral-closure
valuation from `FiniteGaloisLevel` and intersects the inverse images of its
ramification groups.  Independence from the chosen complete-DVF realization is
proved in FiniteGaloisLevelIndependence.  Finite-quotient compatibility has not
been proved, so neither intersection is identified with a canonical absolute
ramification filtration.
-/


noncomputable section

universe u v

namespace RamificationTheory.Field.absoluteGaloisGroup

open ValuationTheory.DiscreteValuationField

variable (K : Type u) [Field K]

/-- The raw intersection of the inverse images of the chosen upper
ramification groups over all finite Galois levels.  Choice-independence is
proved by the companion FiniteGaloisLevelIndependence module; no
finite-quotient compatibility is asserted here. -/
noncomputable def finiteLevelUpperIntersection
    (base : CompleteDVF.{u, v} K) (t : ℝ) :
    Subgroup (Field.absoluteGaloisGroup K) :=
  ⨅ E : FiniteGaloisIntermediateField K (AlgebraicClosure K),
    Subgroup.comap
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := AlgebraicClosure K)
        E.toIntermediateField)
      (HilbertRamification.FiniteGaloisLevel.chosenUpperRamificationGroup base E t)

/-- States the theorem `mem_finiteLevelUpperIntersection_iff`. -/
@[simp]
theorem mem_finiteLevelUpperIntersection_iff
    (base : CompleteDVF.{u, v} K) (t : ℝ)
    (sigma : Field.absoluteGaloisGroup K) :
    sigma ∈ finiteLevelUpperIntersection K base t ↔
      ∀ E : FiniteGaloisIntermediateField K (AlgebraicClosure K),
        AlgEquiv.restrictNormalHom (F := K) (K₁ := AlgebraicClosure K)
          E.toIntermediateField sigma ∈
          HilbertRamification.FiniteGaloisLevel.chosenUpperRamificationGroup
            base E t := by
  simp only [finiteLevelUpperIntersection, Subgroup.mem_iInf]
  constructor
  · intro h E
    exact h E
  · intro h E
    exact h E

/-- The raw same-index intersection of the integral lower groups at all finite
Galois levels.  This is not presented as a canonical absolute lower numbering:
lower numbering is not quotient-compatible in the way upper numbering is. -/
noncomputable def finiteLevelLowerIntersection
    (base : CompleteDVF.{u, v} K) (n : ℕ) :
    Subgroup (Field.absoluteGaloisGroup K) :=
  ⨅ E : FiniteGaloisIntermediateField K (AlgebraicClosure K),
    Subgroup.comap
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := AlgebraicClosure K)
        E.toIntermediateField)
      ((HilbertRamification.FiniteGaloisLevel.chosenLowerRamificationFiltration
        base E).lower n)

/-- States the theorem `mem_finiteLevelLowerIntersection_iff`. -/
@[simp]
theorem mem_finiteLevelLowerIntersection_iff
    (base : CompleteDVF.{u, v} K) (n : ℕ)
    (sigma : Field.absoluteGaloisGroup K) :
    sigma ∈ finiteLevelLowerIntersection K base n ↔
      ∀ E : FiniteGaloisIntermediateField K (AlgebraicClosure K),
        AlgEquiv.restrictNormalHom (F := K) (K₁ := AlgebraicClosure K)
          E.toIntermediateField sigma ∈
          (HilbertRamification.FiniteGaloisLevel.chosenLowerRamificationFiltration
            base E).lower n := by
  simp only [finiteLevelLowerIntersection, Subgroup.mem_iInf]
  constructor
  · intro h E
    exact h E
  · intro h E
    exact h E

/-- States the theorem `finiteLevelUpperIntersection_normal`. -/
theorem finiteLevelUpperIntersection_normal
    (base : CompleteDVF.{u, v} K) (t : ℝ) :
    (finiteLevelUpperIntersection K base t).Normal := by
  apply Subgroup.normal_iInf_normal
  intro E
  exact
    (HilbertRamification.FiniteGaloisLevel.chosenUpperRamificationGroup_normal
      base E t).comap
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := AlgebraicClosure K)
          E.toIntermediateField)

/-- States the theorem `finiteLevelLowerIntersection_normal`. -/
theorem finiteLevelLowerIntersection_normal
    (base : CompleteDVF.{u, v} K) (n : ℕ) :
    (finiteLevelLowerIntersection K base n).Normal := by
  apply Subgroup.normal_iInf_normal
  intro E
  exact
    (HilbertRamification.FiniteGaloisLevel.chosenLowerRamificationGroup_normal
      base E n).comap
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := AlgebraicClosure K)
          E.toIntermediateField)

/-- A finite-level upper group has closed inverse image in the absolute Galois
group. -/
theorem finiteLevelUpperComap_isClosed
    (base : CompleteDVF.{u, v} K)
    (E : FiniteGaloisIntermediateField K (AlgebraicClosure K))
    (t : ℝ) :
    IsClosed
      (Subgroup.comap
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := AlgebraicClosure K)
          E.toIntermediateField)
        (HilbertRamification.FiniteGaloisLevel.chosenUpperRamificationGroup
          base E t)).carrier := by
  change IsClosed
    ((AlgEquiv.restrictNormalHom (F := K) (K₁ := AlgebraicClosure K)
      E.toIntermediateField) ⁻¹'
      (HilbertRamification.FiniteGaloisLevel.chosenUpperRamificationGroup
        base E t : Set Gal(E / K)))
  exact IsClosed.preimage
    (InfiniteGalois.restrictNormalHom_continuous E.toIntermediateField)
    (HilbertRamification.FiniteGaloisLevel.chosenUpperRamificationGroup_isClosed
      base E t)

/-- A finite-level integral lower group has closed inverse image in the
absolute Galois group. -/
theorem finiteLevelLowerComap_isClosed
    (base : CompleteDVF.{u, v} K)
    (E : FiniteGaloisIntermediateField K (AlgebraicClosure K))
    (n : ℕ) :
    IsClosed
      (Subgroup.comap
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := AlgebraicClosure K)
          E.toIntermediateField)
        ((HilbertRamification.FiniteGaloisLevel.chosenLowerRamificationFiltration
          base E).lower n)).carrier := by
  change IsClosed
    ((AlgEquiv.restrictNormalHom (F := K) (K₁ := AlgebraicClosure K)
      E.toIntermediateField) ⁻¹'
      ((HilbertRamification.FiniteGaloisLevel.chosenLowerRamificationFiltration
        base E).lower n : Set Gal(E / K)))
  exact IsClosed.preimage
    (InfiniteGalois.restrictNormalHom_continuous E.toIntermediateField)
    (HilbertRamification.FiniteGaloisLevel.chosenLowerRamificationGroup_isClosed
      base E n)

/-- The finite-level upper intersection is closed. -/
theorem finiteLevelUpperIntersection_isClosed
    (base : CompleteDVF.{u, v} K) (t : ℝ) :
    IsClosed
      (finiteLevelUpperIntersection K base t :
        Set (Field.absoluteGaloisGroup K)) := by
  rw [finiteLevelUpperIntersection, Subgroup.coe_iInf]
  exact isClosed_iInter fun E => finiteLevelUpperComap_isClosed K base E t

/-- The finite-level lower intersection is closed. -/
theorem finiteLevelLowerIntersection_isClosed
    (base : CompleteDVF.{u, v} K) (n : ℕ) :
    IsClosed
      (finiteLevelLowerIntersection K base n :
        Set (Field.absoluteGaloisGroup K)) := by
  rw [finiteLevelLowerIntersection, Subgroup.coe_iInf]
  exact isClosed_iInter fun E => finiteLevelLowerComap_isClosed K base E n

end RamificationTheory.Field.absoluteGaloisGroup
