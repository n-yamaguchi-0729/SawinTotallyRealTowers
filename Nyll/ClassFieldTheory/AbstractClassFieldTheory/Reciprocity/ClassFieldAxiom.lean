/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UnitCohomologyAxiom
public import Nyll.GaloisCohomology.Cyclic.IntegralUniverseCohomology

/-!
# Abstract reciprocity: the class field axiom

The coefficient group for a finite cyclic extension `L / K` is the actual fixed module `A_L`,
descended to the actual quotient `G_K / G_L`. Its integral Tate cohomology is constructed in the
working universe of that quotient and coefficient carrier. These two universes are independent.

The comparison with the literal integer Tate complex proves that the universe-zero condition
has exactly its original finiteness and cardinality meaning. The original concrete local and
global class-field constructions enter through that proved comparison.
-/

@[expose] public section

namespace ClassFormation

open CyclicCohomology CategoryTheory

noncomputable section

universe u v

section Generic

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- The finite cohomology data asserted at one finite cyclic extension.
Finiteness is stored before either natural-valued cardinality is formed. -/
structure ClassFieldAxiomCohomologyData (A : Rep.{v} ℤ G)
    (K : FiniteAbstractField G) (E : FiniteCyclicSubextension K) : Prop where
  /-- The degree-zero integral Tate cohomology group is finite. -/
  finiteTateHZero : Finite (IntegralGroupCohomology.Universe.tate (E.fixedRepresentation A) 0)
  /-- The degree-minus-one integral Tate cohomology group is finite. -/
  finiteTateHMinusOne :
    Finite (IntegralGroupCohomology.Universe.tate (E.fixedRepresentation A) (-1))
  /-- Degree-zero Tate cohomology has cardinality equal to the extension degree. -/
  tateHZero_card :
    Nat.card (IntegralGroupCohomology.Universe.tate (E.fixedRepresentation A) 0) =
      (E.toFiniteAbstractExtension.degree : ℕ)
  /-- Degree-minus-one Tate cohomology is trivial by cardinality. -/
  tateHMinusOne_card :
    Nat.card (IntegralGroupCohomology.Universe.tate (E.fixedRepresentation A) (-1)) = 1

/-- **The class-field axiom.** For every finite cyclic extension `L / K` with `K` finite over the
base, the actual integral Tate groups have orders `[L : K]` and `1` in degrees zero and minus one.
The original subgroup, quotient action and coefficient carrier determine these groups. -/
def SatisfiesClassFieldAxiom (A : Rep.{v} ℤ G) : Prop :=
  ∀ (K : FiniteAbstractField G) (E : FiniteCyclicSubextension K),
    ClassFieldAxiomCohomologyData A K E

namespace SatisfiesClassFieldAxiom

variable {A : Rep.{v} ℤ G}

/-- The degree-zero cardinality in the actual independent-universe integral owner. -/
theorem integralTateHZero_card (hcf : SatisfiesClassFieldAxiom A)
    (K : FiniteAbstractField G) (E : FiniteCyclicSubextension K) :
    Nat.card (IntegralGroupCohomology.Universe.tate (E.fixedRepresentation A) 0) =
      (E.toFiniteAbstractExtension.degree : ℕ) :=
  (hcf K E).tateHZero_card

/-- The degree-minus-one cardinality in the same actual integral owner. -/
theorem integralTateHMinusOne_card (hcf : SatisfiesClassFieldAxiom A)
    (K : FiniteAbstractField G) (E : FiniteCyclicSubextension K) :
    Nat.card (IntegralGroupCohomology.Universe.tate (E.fixedRepresentation A) (-1)) = 1 :=
  (hcf K E).tateHMinusOne_card

/-- The order-one axiom is actual Tate vanishing for independent group and carrier universes. -/
theorem integralTateHMinusOne_isZero (hcf : SatisfiesClassFieldAxiom A)
    (K : FiniteAbstractField G) (E : FiniteCyclicSubextension K) :
    Limits.IsZero (IntegralGroupCohomology.Universe.tate (E.fixedRepresentation A) (-1)) := by
  let H := IntegralGroupCohomology.Universe.tate (E.fixedRepresentation A) (-1)
  let : Finite H := (hcf K E).finiteTateHMinusOne
  have hcard : Nat.card H = 1 := hcf.integralTateHMinusOne_card K E
  let : Subsingleton H := (Nat.card_eq_one_iff_unique.mp hcard).1
  exact ModuleCat.isZero_of_subsingleton H

end SatisfiesClassFieldAxiom

end Generic

section Original

variable {G : Type} [Group G] [TopologicalSpace G]
  {A : Rep.{0} ℤ G} {K : FiniteAbstractField G} {E : FiniteCyclicSubextension K}

namespace ClassFieldAxiomCohomologyData

/-- The new degree-zero finiteness assertion supplies the original literal one. -/
theorem finiteTateHZero_original (h : ClassFieldAxiomCohomologyData A K E) :
    Finite (tateCohomology (E.fixedRepresentation A) 0) :=
  (IntegralGroupCohomology.Universe.finite_tate_iff_original (E.fixedRepresentation A) 0).mp
    h.finiteTateHZero

/-- The new degree-minus-one finiteness assertion supplies the original literal one. -/
theorem finiteTateHMinusOne_original (h : ClassFieldAxiomCohomologyData A K E) :
    Finite (tateCohomology (E.fixedRepresentation A) (-1)) :=
  (IntegralGroupCohomology.Universe.finite_tate_iff_original
    (E.fixedRepresentation A) (-1)).mp h.finiteTateHMinusOne

/-- The original concrete Tate calculation supplies the same class-field axiom data. -/
theorem ofOriginal
    (h0 : Finite (tateCohomology (E.fixedRepresentation A) 0))
    (hm : Finite (tateCohomology (E.fixedRepresentation A) (-1)))
    (hc0 : Nat.card (tateCohomology (E.fixedRepresentation A) 0) =
      (E.toFiniteAbstractExtension.degree : ℕ))
    (hcm : Nat.card (tateCohomology (E.fixedRepresentation A) (-1)) = 1) :
    ClassFieldAxiomCohomologyData A K E where
  finiteTateHZero :=
    (IntegralGroupCohomology.Universe.finite_tate_iff_original (E.fixedRepresentation A) 0).mpr h0
  finiteTateHMinusOne :=
    (IntegralGroupCohomology.Universe.finite_tate_iff_original
      (E.fixedRepresentation A) (-1)).mpr hm
  tateHZero_card :=
    (IntegralGroupCohomology.Universe.card_tate_eq_original (E.fixedRepresentation A) 0).trans hc0
  tateHMinusOne_card :=
    (IntegralGroupCohomology.Universe.card_tate_eq_original
      (E.fixedRepresentation A) (-1)).trans hcm

/-- In universe zero all four class-field conditions are exactly the original conditions. -/
theorem iff_original :
    ClassFieldAxiomCohomologyData A K E ↔
      Finite (tateCohomology (E.fixedRepresentation A) 0) ∧
      Finite (tateCohomology (E.fixedRepresentation A) (-1)) ∧
      Nat.card (tateCohomology (E.fixedRepresentation A) 0) =
        (E.toFiniteAbstractExtension.degree : ℕ) ∧
      Nat.card (tateCohomology (E.fixedRepresentation A) (-1)) = 1 := by
  constructor
  · intro h
    exact ⟨h.finiteTateHZero_original, h.finiteTateHMinusOne_original,
      (IntegralGroupCohomology.Universe.card_tate_eq_original
        (E.fixedRepresentation A) 0).symm.trans h.tateHZero_card,
      (IntegralGroupCohomology.Universe.card_tate_eq_original
        (E.fixedRepresentation A) (-1)).symm.trans h.tateHMinusOne_card⟩
  · rintro ⟨h0, hm, hc0, hcm⟩
    exact ofOriginal h0 hm hc0 hcm

end ClassFieldAxiomCohomologyData

namespace SatisfiesClassFieldAxiom

/-- The original degree-zero conclusion follows from the same proved Tate comparison. -/
theorem tateHZero_card (hcf : SatisfiesClassFieldAxiom A)
    (K : FiniteAbstractField G) (E : FiniteCyclicSubextension K) :
    Nat.card (tateCohomology (E.fixedRepresentation A) 0) =
      (E.toFiniteAbstractExtension.degree : ℕ) :=
  (IntegralGroupCohomology.Universe.card_tate_eq_original
    (E.fixedRepresentation A) 0).symm.trans (hcf K E).tateHZero_card

/-- The original degree-minus-one conclusion follows from the same comparison. -/
theorem tateHMinusOne_card (hcf : SatisfiesClassFieldAxiom A)
    (K : FiniteAbstractField G) (E : FiniteCyclicSubextension K) :
    Nat.card (tateCohomology (E.fixedRepresentation A) (-1)) = 1 :=
  (IntegralGroupCohomology.Universe.card_tate_eq_original
    (E.fixedRepresentation A) (-1)).symm.trans (hcf K E).tateHMinusOne_card

/-- The original literal Tate vanishing follows from the actual integral Tate axiom. -/
theorem tateHMinusOne_isZero (hcf : SatisfiesClassFieldAxiom A)
    (K : FiniteAbstractField G) (E : FiniteCyclicSubextension K) :
    Limits.IsZero (tateCohomology (E.fixedRepresentation A) (-1)) :=
  (IntegralGroupCohomology.Universe.isZero_tate_iff_original
    (E.fixedRepresentation A) (-1)).mp (hcf.integralTateHMinusOne_isZero K E)

/-- Universe-zero satisfaction is equivalent to the full original literal Tate condition. -/
theorem iff_original :
    SatisfiesClassFieldAxiom A ↔
      ∀ (K : FiniteAbstractField G) (E : FiniteCyclicSubextension K),
        Finite (tateCohomology (E.fixedRepresentation A) 0) ∧
        Finite (tateCohomology (E.fixedRepresentation A) (-1)) ∧
        Nat.card (tateCohomology (E.fixedRepresentation A) 0) =
          (E.toFiniteAbstractExtension.degree : ℕ) ∧
        Nat.card (tateCohomology (E.fixedRepresentation A) (-1)) = 1 := by
  constructor
  · intro h K E
    exact ClassFieldAxiomCohomologyData.iff_original.mp (h K E)
  · intro h K E
    exact ClassFieldAxiomCohomologyData.iff_original.mpr (h K E)

end SatisfiesClassFieldAxiom

end Original

end
end ClassFormation
