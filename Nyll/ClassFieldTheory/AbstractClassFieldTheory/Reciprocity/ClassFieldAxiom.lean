/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UnitCohomologyAxiom
public import Nyll.GaloisCohomology.Cyclic.IntegralUniverseCohomology
public import Nyll.GaloisCohomology.Cyclic.IntegralCyclicNormTransport

/-!
# Abstract reciprocity: the class field axiom

The coefficient group for a finite cyclic extension `L / K` is the actual fixed module `A_L`,
descended to the actual quotient `G_K / G_L`. Its integral Tate cohomology is constructed in the
working universe of that quotient and coefficient carrier. These two universes are independent.

The comparison with the literal integer Tate complex preserves the finiteness and cardinality
statements at universe zero. The integral norm complexes also transport the arithmetic
calculations along the actual coefficient representation and quotient action.
-/

@[expose] public section

namespace ClassFormation

open CyclicCohomology CategoryTheory

noncomputable section

universe u v w

section Generic

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- The cohomology data at one finite cyclic extension. Degree zero retains
its finite cardinality; degree minus one stores vanishing of the actual object. -/
structure ClassFieldAxiomCohomologyData (A : Rep.{v} ℤ G)
    (K : FiniteAbstractField G) (E : FiniteCyclicSubextension K) : Prop where
  /-- The degree-zero integral Tate cohomology group is finite. -/
  finiteTateHZero : Finite (IntegralGroupCohomology.Universe.tate (E.fixedRepresentation A) 0)
  /-- Degree-zero Tate cohomology has cardinality equal to the extension degree. -/
  tateHZero_card :
    Nat.card (IntegralGroupCohomology.Universe.tate (E.fixedRepresentation A) 0) =
      (E.toFiniteAbstractExtension.degree : ℕ)
  /-- Degree-minus-one integral Tate cohomology vanishes. -/
  tateHMinusOne_isZero :
    Limits.IsZero (IntegralGroupCohomology.Universe.tate (E.fixedRepresentation A) (-1))

namespace ClassFieldAxiomCohomologyData

variable {A : Rep.{v} ℤ G} {K : FiniteAbstractField G} {E : FiniteCyclicSubextension K}

/-- Vanishing supplies finiteness without storing a second degree-minus-one input. -/
theorem finiteTateHMinusOne (h : ClassFieldAxiomCohomologyData A K E) :
    Finite (IntegralGroupCohomology.Universe.tate (E.fixedRepresentation A) (-1)) := by
  let : Subsingleton
      (IntegralGroupCohomology.Universe.tate (E.fixedRepresentation A) (-1)) :=
    ModuleCat.subsingleton_of_isZero h.tateHMinusOne_isZero
  infer_instance

/-- The order-one statement is a consequence of the same vanishing field. -/
theorem tateHMinusOne_card (h : ClassFieldAxiomCohomologyData A K E) :
    Nat.card (IntegralGroupCohomology.Universe.tate (E.fixedRepresentation A) (-1)) = 1 := by
  let : Subsingleton
      (IntegralGroupCohomology.Universe.tate (E.fixedRepresentation A) (-1)) :=
    ModuleCat.subsingleton_of_isZero h.tateHMinusOne_isZero
  exact Nat.card_unique

end ClassFieldAxiomCohomologyData

/-- **The class-field axiom.** For every finite cyclic extension `L / K` with `K` finite over the
base, the actual integral Tate groups have orders `[L : K]` and `1` in degrees zero and minus one.
The original subgroup, quotient action and coefficient carrier determine these groups. -/
def SatisfiesClassFieldAxiom (A : Rep.{v} ℤ G) : Prop :=
  ∀ (K : FiniteAbstractField G) (E : FiniteCyclicSubextension K),
    ClassFieldAxiomCohomologyData A K E

open IntegralGroupCohomology.Universe in
/-- Transport the finite cyclic Tate cardinalities along the actual quotient action. -/
theorem ClassFieldAxiomCohomologyData.of_repIso
    {P : Type v} [Group P] [Fintype P]
    (A : Rep.{w} ℤ G) (B : FiniteAbstractField G) (C : FiniteCyclicSubextension B)
    (g : B.field.toSubgroup ⧸ extensionSubgroup B.field C.field C.below)
    (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (e : (B.field.toSubgroup ⧸ extensionSubgroup B.field C.field C.below) ≃* P)
    (hg' : ∀ σ : P, σ ∈ Subgroup.zpowers (e g))
    (U : Rep.{w} ℤ P) (eM : C.fixedRepresentation A ≅ Rep.res e.toMonoidHom U)
    (hfinite : Finite (tate U 0)) (hcard0 : Nat.card (tate U 0) = Nat.card P)
    (hcardm : Nat.card (tate U (-1)) = 1) :
    ClassFieldAxiomCohomologyData A B C := by
  let Q := B.field.toSubgroup ⧸ extensionSubgroup B.field C.field C.below
  let g' : P := e g
  let M : Rep.{w} ℤ Q := C.fixedRepresentation A
  let eH0 : (normHomCompSub M g).homology ≅ (normHomCompSub U g').homology :=
    normHomCompSubHomologyIsoOfRepIso eM g ≪≫ normHomCompSubHomologyResEquivIso e U g
  let eHm : (subCompNormHom M g).homology ≅ (subCompNormHom U g').homology :=
    subCompNormHomHomologyIsoOfRepIso eM g ≪≫ subCompNormHomHomologyResEquivIso e U g
  let e0 : tate M 0 ≃+ tate U 0 :=
    (normHomologyEquivTateZero M g hg).symm.trans
      (eH0.toLinearEquiv.toAddEquiv.trans (normHomologyEquivTateZero U g' hg'))
  let em : tate M (-1) ≃+ tate U (-1) :=
    (subNormHomologyEquivTateMinusOne M g hg).symm.trans
      (eHm.toLinearEquiv.toAddEquiv.trans (subNormHomologyEquivTateMinusOne U g' hg'))
  let : Finite (tate U 0) := hfinite
  have hdegree : Nat.card Q = (C.toFiniteAbstractExtension.degree : ℕ) :=
    (Subgroup.index_eq_card (extensionSubgroup B.field C.field C.below)).symm.trans
      C.toFiniteAbstractExtension.extensionSubgroup_index_eq_degree
  refine ⟨Finite.of_equiv (tate U 0) e0.symm.toEquiv,
    (Nat.card_congr e0.toEquiv).trans (hcard0.trans
      ((Nat.card_congr e.toEquiv).symm.trans hdegree)), ?_⟩
  let : Subsingleton (tate U (-1)) := (Nat.card_eq_one_iff_unique.mp hcardm).1
  let : Subsingleton (tate M (-1)) := Function.Injective.subsingleton em.injective
  exact ModuleCat.isZero_of_subsingleton _

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
    Limits.IsZero (IntegralGroupCohomology.Universe.tate (E.fixedRepresentation A) (-1)) :=
  (hcf K E).tateHMinusOne_isZero

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
    (hc0 : Nat.card (tateCohomology (E.fixedRepresentation A) 0) =
      (E.toFiniteAbstractExtension.degree : ℕ))
    (hm : Limits.IsZero (tateCohomology (E.fixedRepresentation A) (-1))) :
    ClassFieldAxiomCohomologyData A K E where
  finiteTateHZero :=
    (IntegralGroupCohomology.Universe.finite_tate_iff_original (E.fixedRepresentation A) 0).mpr h0
  tateHZero_card :=
    (IntegralGroupCohomology.Universe.card_tate_eq_original (E.fixedRepresentation A) 0).trans hc0
  tateHMinusOne_isZero :=
    (IntegralGroupCohomology.Universe.isZero_tate_iff_original
      (E.fixedRepresentation A) (-1)).mpr hm

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
  · rintro ⟨h0, _, hc0, hcm⟩
    apply ofOriginal h0 hc0
    let : Subsingleton (tateCohomology (E.fixedRepresentation A) (-1)) :=
      (Nat.card_eq_one_iff_unique.mp hcm).1
    exact ModuleCat.isZero_of_subsingleton _

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
