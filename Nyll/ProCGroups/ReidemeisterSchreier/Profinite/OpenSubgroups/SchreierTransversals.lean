/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FreeProC.Basic
import Nyll.ProCGroups.WreathProducts
import Nyll.ProCGroups.ReidemeisterSchreier.Profinite.OpenSubgroups.RightQuotient

/-!
# Schreier sections and oriented cocycles

The source of truth is `SchreierCocycleData`: it stores a left/right
orientation, a section map, the next-coset operation, and the proof that the
resulting cocycle lands in the open subgroup.  `ActualSchreierSection` and
`ActualRightSchreierSection` add equivalences with the genuine quotient and the
projection/next-coset coherence laws.  `FiniteSchreierCocycleData` carries the
finiteness evidence used by `Nat.card`.

The concrete left- and right-coset constructions below feed this common API.
Continuity, closure, generation, and cardinality are proved once for the
oriented data rather than repeated as chosen-left/chosen-right wrapper
families.
-/

open Set
open scoped Topology Pointwise

namespace ReidemeisterSchreier
namespace Profinite

open ProCGroups
open ProCGroups.ProC
open ProCGroups.FreeProC
open ProCGroups.WreathProducts

universe u v

section LeftQuotientSections

variable {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]

/-- The normalized continuous section of the left quotient by an open subgroup. -/
noncomputable abbrev openSubgroupLeftSchreierSection (H : OpenSubgroup F) :
    F ⧸ (H : Subgroup F) → F :=
  ProCGroups.ProC.quotientOpenSubgroupSection (H : Subgroup F)

omit [IsTopologicalGroup F] in
/--
The normalized section of the left quotient is a right inverse to the quotient projection.
-/
theorem openSubgroupLeftSchreierSection_rightInverse (H : OpenSubgroup F) :
    Function.RightInverse (openSubgroupLeftSchreierSection (F := F) H)
      (QuotientGroup.mk (s := (H : Subgroup F))) := by
  simpa [openSubgroupLeftSchreierSection] using
    (ProCGroups.ProC.quotientOpenSubgroupSection_rightInverse
      (G := F) (U := (H : Subgroup F)))

/-- The corresponding Schreier section is continuous. -/
theorem continuous_openSubgroupLeftSchreierSection (H : OpenSubgroup F) :
    Continuous (openSubgroupLeftSchreierSection (F := F) H) := by
  simpa [openSubgroupLeftSchreierSection] using
    (ProCGroups.ProC.continuous_quotientOpenSubgroupSection
      (G := F) (U := (H : Subgroup F)) H.isOpen')

omit [IsTopologicalGroup F] in
/-- The Schreier generator component of the corresponding rewriting map. -/
@[simp] theorem openSubgroupLeftSchreierSection_mk
    (H : OpenSubgroup F) (q : F ⧸ (H : Subgroup F)) :
    QuotientGroup.mk (s := (H : Subgroup F))
        (openSubgroupLeftSchreierSection (F := F) H q) = q :=
  openSubgroupLeftSchreierSection_rightInverse (F := F) H q

omit [IsTopologicalGroup F] in
/-- The normalized left-quotient section sends the identity coset to the identity. -/
@[simp] theorem openSubgroupLeftSchreierSection_one
    (H : OpenSubgroup F) :
    openSubgroupLeftSchreierSection (F := F) H
        (QuotientGroup.mk (s := (H : Subgroup F)) (1 : F)) = 1 := by
  simp only [openSubgroupLeftSchreierSection, quotientOpenSubgroupSection_one]

end LeftQuotientSections

section AbstractSchreierSections

variable {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
variable {X : Type v}
variable (H : OpenSubgroup F)

/-- The two cocycle orientations used by left- and right-coset Schreier generators. -/
inductive SchreierOrientation where
  /-- The left-oriented cocycle places the inverse of the next representative first. -/
  | left
  /-- The right-oriented cocycle places the inverse of the next representative last. -/
  | right
deriving DecidableEq

namespace SchreierOrientation

/-- The oriented Schreier cocycle associated to a section and a next-coset operation. -/
def cocycle {Q : Type u} (o : SchreierOrientation)
    (sec : Q → F) (next : Q → X → Q) (ι : X → F) (q : Q) (x : X) : F :=
  match o with
  | left => (sec (next q x))⁻¹ * sec q * ι x
  | right => sec q * ι x * (sec (next q x))⁻¹

end SchreierOrientation

/--
A section-level Schreier generator package. It abstracts over the quotient type, the left/right
cocycle orientation, and the next-coset operation, so the common generator-set, continuity,
closure, and cardinality formulation can be formulated once.
-/
structure SchreierCocycleData where
  /-- The abstract type indexing the chosen coset representatives. -/
  Q : Type u
  /-- Whether the associated Schreier cocycle uses the left- or right-coset formula. -/
  orientation : SchreierOrientation
  /-- The representative in \(F\) assigned to each abstract quotient index. -/
  sectionMap : Q → F
  /-- The quotient index reached after multiplying a representative by a chosen generator. -/
  next : (X → F) → Q → X → Q
  /-- Every oriented cocycle value belongs to the open subgroup \(H\). -/
  cocycle_mem :
    ∀ (ι : X → F) (q : Q) (x : X),
      orientation.cocycle sectionMap (next ι) ι q x ∈ (H : Subgroup F)

/-- Genuine left-quotient Schreier section data.

The equivalence identifies the abstract cocycle index with the actual quotient
`F ⧸ H`; the remaining fields state that both the representative and the
next-coset operation project to that quotient.  Thus no arbitrary raw map can
masquerade as a quotient projection. -/
structure ActualSchreierSection where
  /-- The abstract cocycle and section data. -/
  cocycleData : SchreierCocycleData (F := F) (X := X) H
  /-- Identification of the abstract index type with the left quotient \(F/H\). -/
  quotientEquiv : cocycleData.Q ≃ F ⧸ (H : Subgroup F)
  /-- Each chosen representative projects to its corresponding quotient index. -/
  section_projects :
    ∀ q : cocycleData.Q,
      QuotientGroup.mk (s := (H : Subgroup F)) (cocycleData.sectionMap q) =
        quotientEquiv q
  /-- The next-index operation projects the representative multiplied by the chosen generator. -/
  next_projects :
    ∀ (ι : X → F) (q : cocycleData.Q) (x : X),
      quotientEquiv (cocycleData.next ι q x) =
        QuotientGroup.mk (s := (H : Subgroup F))
          (cocycleData.sectionMap q * ι x)

/-- Genuine right-quotient Schreier section data.

This is the right-coset counterpart of `ActualSchreierSection`; its index type
is explicitly identified with `OpenSubgroupRightQuotient H`. -/
structure ActualRightSchreierSection where
  /-- The abstract cocycle and section data. -/
  cocycleData : SchreierCocycleData (F := F) (X := X) H
  /-- Identification of the abstract index type with the right quotient by \(H\). -/
  quotientEquiv : cocycleData.Q ≃ OpenSubgroupRightQuotient H
  /-- Each chosen representative maps to its corresponding right-quotient index. -/
  section_projects :
    ∀ q : cocycleData.Q,
      (Quotient.mk'' (cocycleData.sectionMap q) :
        OpenSubgroupRightQuotient H) = quotientEquiv q
  /-- The next-index operation maps the representative multiplied by the chosen generator. -/
  next_projects :
    ∀ (ι : X → F) (q : cocycleData.Q) (x : X),
      quotientEquiv (cocycleData.next ι q x) =
        (Quotient.mk'' (cocycleData.sectionMap q * ι x) :
          OpenSubgroupRightQuotient H)

/-- A cocycle package together with the finiteness data required by its
`Nat.card` estimates.  This prevents a finite-index formula from silently
using `Nat.card = 0` on an infinite quotient. -/
structure FiniteSchreierCocycleData where
  /-- The underlying abstract Schreier cocycle package. -/
  cocycleData : SchreierCocycleData (F := F) (X := X) H
  /-- Finiteness of the generator-index type. -/
  finiteGeneratorIndex : Finite X
  /-- Finiteness of the abstract quotient-index type. -/
  finiteQuotient : Finite cocycleData.Q

namespace SchreierCocycleData

variable {H}

/-- The subgroup-valued generator attached to an abstract Schreier section. -/
noncomputable def generator (S : SchreierCocycleData (F := F) (X := X) H)
    (ι : X → F) (q : S.Q) (x : X) : ↥(H : Subgroup F) :=
  ⟨S.orientation.cocycle S.sectionMap (S.next ι) ι q x, S.cocycle_mem ι q x⟩

omit [IsTopologicalGroup F] in
/-- Forgetting the subgroup proof from a Schreier generator yields its defining cocycle
value. -/
@[simp] theorem generator_coe (S : SchreierCocycleData (F := F) (X := X) H)
    (ι : X → F) (q : S.Q) (x : X) :
    ((S.generator ι q x : ↥(H : Subgroup F)) : F) =
      S.orientation.cocycle S.sectionMap (S.next ι) ι q x :=
  rfl

/-- Nontrivial generator values of an abstract Schreier section. -/
def generatorSet (S : SchreierCocycleData (F := F) (X := X) H)
    (ι : X → F) : Set ↥(H : Subgroup F) :=
  {z | ∃ q : S.Q, ∃ x : X, z = S.generator ι q x ∧ z ≠ 1}

/--
This type records the nontrivial Schreier pairs whose cocycle values form the abstract Schreier
generator set.
-/
def NontrivialPairs (S : SchreierCocycleData (F := F) (X := X) H)
    (ι : X → F) : Type (max u v) :=
  {p : S.Q × X // S.generator ι p.1 p.2 ≠ 1}

omit [IsTopologicalGroup F] in
/--
The abstract Schreier generator or next-coset formula is obtained by evaluating the chosen
section cocycle.
-/
instance finite_nontrivialPairs
    (S : SchreierCocycleData (F := F) (X := X) H) (ι : X → F)
    [Finite X] [Finite S.Q] :
    Finite (S.NontrivialPairs ι) :=
  Finite.of_injective (fun p : S.NontrivialPairs ι => p.1) (by
    intro a b h
    exact Subtype.ext h)

omit [IsTopologicalGroup F] in
/-- The tautological map from nontrivial abstract Schreier pairs to the generator value set. -/
noncomputable def nontrivialPairsToGeneratorSet
    (S : SchreierCocycleData (F := F) (X := X) H) (ι : X → F) :
    S.NontrivialPairs ι → ↥(S.generatorSet ι) := fun p =>
  ⟨S.generator ι p.1.1 p.1.2, ⟨p.1.1, p.1.2, rfl, p.2⟩⟩

omit [IsTopologicalGroup F] in
/--
The map from nontrivial abstract Schreier pairs onto the abstract Schreier generator set is
surjective.
-/
theorem surjective_nontrivialPairsToGeneratorSet
    (S : SchreierCocycleData (F := F) (X := X) H) (ι : X → F) :
    Function.Surjective (S.nontrivialPairsToGeneratorSet ι) := by
  intro z
  rcases z.2 with ⟨q, x, hz, hz_ne⟩
  refine ⟨⟨(q, x), ?_⟩, ?_⟩
  · simpa [hz] using hz_ne
  · apply Subtype.ext
    exact hz.symm

omit [IsTopologicalGroup F] in
/--
Surjectivity of the map from nontrivial Schreier pairs bounds the cardinality of the abstract
Schreier generator set by the number of nontrivial pairs.
-/
theorem natCard_generatorSet_le_nontrivialPairs
    (S : SchreierCocycleData (F := F) (X := X) H) (ι : X → F)
    [Finite X] [Finite S.Q] :
    Nat.card (S.generatorSet ι) ≤ Nat.card (S.NontrivialPairs ι) :=
  Nat.card_le_card_of_surjective (S.nontrivialPairsToGeneratorSet ι)
    (S.surjective_nontrivialPairsToGeneratorSet ι)

omit [IsTopologicalGroup F] in
/--
The number of nontrivial abstract Schreier pairs is bounded by the corresponding finite
coset-generator product.
-/
theorem natCard_nontrivialPairs_le
    (S : SchreierCocycleData (F := F) (X := X) H) (ι : X → F)
    [Finite X] [Finite S.Q] :
    Nat.card (S.NontrivialPairs ι) ≤ Nat.card S.Q * Nat.card X := by
  have hle : Nat.card (S.NontrivialPairs ι) ≤ Nat.card (S.Q × X) :=
    Nat.card_le_card_of_injective (fun p : S.NontrivialPairs ι => p.1) (by
      intro a b h
      exact Subtype.ext h)
  simpa [Nat.card_prod] using hle

omit [IsTopologicalGroup F] in
/-- The Schreier generator set has cardinality at most the number of quotient cosets times the
number of original generators. -/
theorem natCard_generatorSet_le
    (S : SchreierCocycleData (F := F) (X := X) H) (ι : X → F)
    [Finite X] [Finite S.Q] :
    Nat.card (S.generatorSet ι) ≤ Nat.card S.Q * Nat.card X :=
  (S.natCard_generatorSet_le_nontrivialPairs ι).trans (S.natCard_nontrivialPairs_le ι)

omit [IsTopologicalGroup F] in
/--
The subgroup closure of the abstract Schreier generator set is the closure of the corresponding
generator-map range.
-/
theorem subgroupClosure_generatorSet_eq_closure_range
    (S : SchreierCocycleData (F := F) (X := X) H) (ι : X → F) :
    Subgroup.closure (S.generatorSet ι) =
      Subgroup.closure (Set.range fun p : S.Q × X => S.generator ι p.1 p.2) := by
  simpa [generatorSet] using
    (ProCGroups.Generation.closure_nontrivial_range_eq_closure_range
      (G := ↥(H : Subgroup F))
      (fun p : S.Q × X => S.generator ι p.1 p.2))

/--
The Schreier generator family topologically generates precisely when the corresponding
subgroup-generation condition holds.
-/
theorem topologicallyGenerates_generatorSet_iff
    {S : SchreierCocycleData (F := F) (X := X) H} {ι : X → F} :
    ProCGroups.Generation.TopologicallyGenerates (G := ↥(H : Subgroup F))
        (S.generatorSet ι) ↔
      ProCGroups.Generation.TopologicallyGenerates (G := ↥(H : Subgroup F))
        (Set.range fun p : S.Q × X => S.generator ι p.1 p.2) := by
  rw [ProCGroups.Generation.topologicallyGenerates_iff_dense,
    ProCGroups.Generation.topologicallyGenerates_iff_dense,
    S.subgroupClosure_generatorSet_eq_closure_range ι]

omit [IsTopologicalGroup F] in
/--
It characterizes exactly when generator identity with the unit equivalence left is equal to the
unit for the chosen Schreier transversal and induced coset representatives.
-/
theorem generator_eq_one_iff_left
    {S : SchreierCocycleData (F := F) (X := X) H}
    (hleft : S.orientation = SchreierOrientation.left)
    {ι : X → F} {q : S.Q} {x : X} :
    S.generator ι q x = 1 ↔ S.sectionMap (S.next ι q x) = S.sectionMap q * ι x := by
  constructor
  · intro h
    have hval := congrArg Subtype.val h
    change S.orientation.cocycle S.sectionMap (S.next ι) ι q x = 1 at hval
    exact inv_mul_eq_one.mp (by
      simpa [SchreierOrientation.cocycle, hleft, mul_assoc] using hval)
  · intro hrep
    apply Subtype.ext
    simp only [generator, SchreierOrientation.cocycle, hleft, hrep, mul_inv_rev, mul_assoc,
        inv_mul_cancel,
  mul_one, OneMemClass.coe_one]

omit [IsTopologicalGroup F] in
/--
The right Schreier generator is trivial exactly in the corresponding unit-representative case.
-/
theorem generator_eq_one_iff_right
    {S : SchreierCocycleData (F := F) (X := X) H}
    (hright : S.orientation = SchreierOrientation.right)
    {ι : X → F} {q : S.Q} {x : X} :
    S.generator ι q x = 1 ↔ S.sectionMap (S.next ι q x) = S.sectionMap q * ι x := by
  constructor
  · intro h
    have hval := congrArg Subtype.val h
    change S.orientation.cocycle S.sectionMap (S.next ι) ι q x = 1 at hval
    exact (mul_inv_eq_one.mp
      (by simpa [SchreierOrientation.cocycle, hright, mul_assoc] using hval)).symm
  · intro hrep
    apply Subtype.ext
    simp only [generator, SchreierOrientation.cocycle, hright, hrep, mul_inv_rev, mul_assoc,
        mul_inv_cancel_left,
  mul_inv_cancel, OneMemClass.coe_one]

omit [IsTopologicalGroup F] in
/--
The rewritten Reidemeister--Schreier generator evaluates to the identity when the next section
value is the basepoint.
-/
theorem generator_eq_of_section_next_eq_one
    (S : SchreierCocycleData (F := F) (X := X) H)
    (ι : X → F) (q : S.Q) (x : X)
    (hnext : S.sectionMap (S.next ι q x) = 1)
    (hmem : S.sectionMap q * ι x ∈ (H : Subgroup F)) :
    S.generator ι q x = ⟨S.sectionMap q * ι x, hmem⟩ := by
  apply Subtype.ext
  cases hside : S.orientation with
  | left =>
      simp only [generator, SchreierOrientation.cocycle, hside, hnext, inv_one, one_mul]
  | right =>
      simp only [generator, SchreierOrientation.cocycle, hside, hnext, inv_one, mul_one]

/--
The abstract Schreier section generator is the cocycle value determined by the chosen section
and next coset.
-/
theorem continuous_generator
    (S : SchreierCocycleData (F := F) (X := X) H)
    [TopologicalSpace S.Q] [TopologicalSpace X]
    (ι : X → F)
    (hsection : Continuous S.sectionMap)
    (hnext : Continuous (fun p : S.Q × X => S.next ι p.1 p.2))
    (hι : Continuous ι) :
    Continuous (fun p : S.Q × X => S.generator ι p.1 p.2) := by
  refine Continuous.subtype_mk ?_ ?_
  cases hside : S.orientation with
  | left =>
      have hcont :
          Continuous (fun p : S.Q × X =>
            (S.sectionMap (S.next ι p.1 p.2))⁻¹ * (S.sectionMap p.1 * ι p.2)) :=
        ((hsection.comp hnext).inv).mul
          ((hsection.comp continuous_fst).mul (hι.comp continuous_snd))
      simpa [generator, SchreierOrientation.cocycle, hside, mul_assoc] using hcont
  | right =>
      have hcont :
          Continuous (fun p : S.Q × X =>
            (S.sectionMap p.1 * ι p.2) * (S.sectionMap (S.next ι p.1 p.2))⁻¹) :=
        ((hsection.comp continuous_fst).mul (hι.comp continuous_snd)).mul
          ((hsection.comp hnext).inv)
      simpa [generator, SchreierOrientation.cocycle, hside, mul_assoc] using hcont

end SchreierCocycleData

namespace FiniteSchreierCocycleData

omit [IsTopologicalGroup F] in
/-- The generator-cardinality bound with all finiteness evidence carried by the
data object rather than repeated as ambient typeclass assumptions. -/
theorem natCard_generatorSet_le
    (S : FiniteSchreierCocycleData (F := F) (X := X) H) (ι : X → F) :
    Nat.card (S.cocycleData.generatorSet ι) ≤
      Nat.card S.cocycleData.Q * Nat.card X := by
  let : Finite X := S.finiteGeneratorIndex
  let : Finite S.cocycleData.Q := S.finiteQuotient
  exact S.cocycleData.natCard_generatorSet_le ι

end FiniteSchreierCocycleData

end AbstractSchreierSections

section LeftSchreierGenerators

variable {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
variable (H : OpenSubgroup F)
variable {X : Type v}
variable (σ : F ⧸ (H : Subgroup F) → F)
variable (hσ : Function.RightInverse σ (QuotientGroup.mk (s := (H : Subgroup F))))
variable (ι : X → F)

/-- The next left coset obtained from a chosen representative and a generator. -/
def leftSchreierNextCoset (q : F ⧸ (H : Subgroup F)) (x : X) : F ⧸ (H : Subgroup F) :=
  QuotientGroup.mk (s := (H : Subgroup F)) (σ q * ι x)

/-- Left-coset Schreier generator attached to a section of the quotient by an open subgroup. -/
noncomputable def leftSchreierGenerator
    (hσ : Function.RightInverse σ (QuotientGroup.mk (s := (H : Subgroup F))))
    (q : F ⧸ (H : Subgroup F)) (x : X) :
    ↥(H : Subgroup F) := by
  let qx := leftSchreierNextCoset (F := F) H σ ι q x
  refine ⟨SchreierOrientation.left.cocycle σ
    (leftSchreierNextCoset (F := F) H σ ι) ι q x, ?_⟩
  have hqx :
      QuotientGroup.mk (s := (H : Subgroup F)) (σ qx) =
        QuotientGroup.mk (s := (H : Subgroup F)) (σ q * ι x) := by
    simpa [qx, leftSchreierNextCoset] using hσ qx
  simpa [SchreierOrientation.cocycle, mul_assoc] using (QuotientGroup.eq.1 hqx)

/-- The left-coset Schreier data as an instance of the abstract section formulation. -/
noncomputable def leftSchreierSection :
    SchreierCocycleData (F := F) (X := X) H where
  Q := F ⧸ (H : Subgroup F)
  orientation := SchreierOrientation.left
  sectionMap := σ
  next := fun ι q x => leftSchreierNextCoset (F := F) H σ ι q x
  cocycle_mem := by
    intro ι q x
    exact (leftSchreierGenerator (F := F) (H := H) (σ := σ) (hσ := hσ) (ι := ι) q x).property

/-- The left quotient construction with its projection, section law, and
next-coset coherence retained in the type. -/
noncomputable def actualLeftSchreierSection :
    ActualSchreierSection (F := F) (X := X) H where
  cocycleData := leftSchreierSection (F := F) (H := H) (σ := σ) (hσ := hσ)
  quotientEquiv := Equiv.refl _
  section_projects := hσ
  next_projects := by
    intro ι q x
    rfl

omit [IsTopologicalGroup F] in
/--
The left Schreier section generator is the cocycle value determined by the chosen section and
next coset.
-/
@[simp] theorem leftSchreierSection_generator
    (q : F ⧸ (H : Subgroup F)) (x : X) :
    (leftSchreierSection (F := F) (H := H) (σ := σ) (hσ := hσ) :
        SchreierCocycleData (F := F) (X := X) H).generator ι q x =
      leftSchreierGenerator (F := F) (H := H) (σ := σ) (hσ := hσ) (ι := ι) q x := by
  apply Subtype.ext
  rfl

end LeftSchreierGenerators

section RightSchreierGenerators

variable {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
variable (H : OpenSubgroup F)
variable {X : Type v}
variable (τ : OpenSubgroupRightQuotient H → F)
variable (hτ : ∀ q, Quotient.mk'' (τ q) = q)
variable (ι : X → F)

/-- The right quotient by an open subgroup carries the natural multiplication action. -/
instance instMulActionOpenSubgroupRightQuotient :
    MulAction F (OpenSubgroupRightQuotient H) :=
  rightCosetMulAction (H : Subgroup F)

attribute [-instance] instMulActionOpenSubgroupRightQuotient

/--
The next right Schreier coset is obtained by acting on the current right coset by the inverse of
the chosen generator image.
-/
def rightSchreierNextCoset (q : OpenSubgroupRightQuotient H) (x : X) :
    OpenSubgroupRightQuotient H :=
  (ι x)⁻¹ • q

/--
The Schreier generator formula records the element determined by the chosen representative
associated to the chosen transversal and letter.
-/
noncomputable def rightSchreierGenerator (q : OpenSubgroupRightQuotient H) (x : X) :
    ↥(H : Subgroup F) :=
  rightQuotientSectionCocycle (H := (H : Subgroup F)) τ hτ (ι x) q

/-- The right-coset Schreier data as an instance of the abstract section formulation. -/
@[reducible] noncomputable def rightSchreierSection :
    SchreierCocycleData (F := F) (X := X) H where
  Q := OpenSubgroupRightQuotient H
  orientation := SchreierOrientation.right
  sectionMap := τ
  next := fun ι q x => rightSchreierNextCoset (F := F) H ι q x
  cocycle_mem := by
    intro ι q x
    exact (rightSchreierGenerator (F := F) (H := H) (τ := τ) (hτ := hτ) (ι := ι) q x).property

/-- The right quotient construction with its projection, section law, and
next-coset coherence retained in the type. -/
noncomputable def actualRightSchreierSection :
    ActualRightSchreierSection (F := F) (X := X) H where
  cocycleData := rightSchreierSection (F := F) (H := H) (τ := τ) (hτ := hτ)
  quotientEquiv := Equiv.refl _
  section_projects := hτ
  next_projects := by
    change ∀ (ι : X → F) (q : OpenSubgroupRightQuotient H) (x : X),
      rightSchreierNextCoset (F := F) H ι q x = Quotient.mk'' (τ q * ι x)
    intro ι q x
    calc
      (ι x)⁻¹ • q =
          (ι x)⁻¹ • (Quotient.mk'' (τ q) : OpenSubgroupRightQuotient H) := by
            rw [hτ q]
      _ = Quotient.mk'' (τ q * ι x) := by
            rw [rightCosetMulAction_inv_mk_smul (H := (H : Subgroup F))]

omit [IsTopologicalGroup F] in
/--
The right Schreier section generator is the cocycle value determined by the chosen section and
next coset.
-/
@[simp] theorem rightSchreierSection_generator
    (q : OpenSubgroupRightQuotient H) (x : X) :
    (rightSchreierSection (F := F) (H := H) (τ := τ) (hτ := hτ) :
        SchreierCocycleData (F := F) (X := X) H).generator ι q x =
      rightSchreierGenerator (F := F) (H := H) (τ := τ) (hτ := hτ) (ι := ι) q x := by
  apply Subtype.ext
  rfl

omit [IsTopologicalGroup F] in
/-- The right Schreier generator evaluates to the identity in the target subgroup presentation. -/
theorem rightSchreierGenerator_eq_one
    {q : OpenSubgroupRightQuotient H} {x : X}
    (hx : ι x = 1) :
    rightSchreierGenerator (F := F) (H := H) (τ := τ) (hτ := hτ) (ι := ι) q x = 1 := by
  apply Subtype.ext
  simp only [rightSchreierGenerator, rightQuotientSectionCocycle, hx, mul_one, inv_one, one_smul,
  mul_inv_cancel, OneMemClass.coe_one]

section Topological

variable [TopologicalSpace X]
variable [TopologicalSpace (OpenSubgroupRightQuotient H)]
variable [DiscreteTopology (OpenSubgroupRightQuotient H)]

/-- The corresponding Schreier next-coset map is continuous. -/
theorem continuous_rightSchreierNextCoset
    (hιcont : Continuous ι) :
    Continuous (fun p : OpenSubgroupRightQuotient H × X =>
      rightSchreierNextCoset (F := F) H ι p.1 p.2) := by
  refine (continuous_prod_of_discrete_left).2 ?_
  intro q
  have hqcont :
      Continuous fun x : X => ((ι x)⁻¹ • q : OpenSubgroupRightQuotient H) := by
    rw [continuous_discrete_rng]
    intro q'
    classical
    let a : F := q.out
    let b : F := q'.out
    have hpre :
        (fun x : X => ((ι x)⁻¹ • q : OpenSubgroupRightQuotient H)) ⁻¹' ({q'} :
            Set (OpenSubgroupRightQuotient H)) =
          (fun x : X => b * (ι x)⁻¹ * a⁻¹) ⁻¹' ((H : Subgroup F) : Set F) := by
      ext x
      constructor
      · intro hx
        have hEq :
            (Quotient.mk'' (a * ι x) : OpenSubgroupRightQuotient H) = Quotient.mk'' b := by
          calc
            (Quotient.mk'' (a * ι x) : OpenSubgroupRightQuotient H)
                = (ι x)⁻¹ • (Quotient.mk'' a : OpenSubgroupRightQuotient H) := by
                    rw [rightCosetMulAction_inv_mk_smul (H := (H : Subgroup F)) (ι x) a]
            _ = (ι x)⁻¹ • q := by rw [Quotient.out_eq' q]
            _ = q' := hx
            _ = Quotient.mk'' b := (Quotient.out_eq' q').symm
        have hrel :
            QuotientGroup.rightRel (H : Subgroup F) (a * ι x) b := Quotient.eq''.mp hEq
        simpa [a, b, mul_inv_rev, mul_assoc] using (QuotientGroup.rightRel_apply.mp hrel)
      · intro hx
        change b * (ι x)⁻¹ * a⁻¹ ∈ (H : Subgroup F) at hx
        have hrel :
            QuotientGroup.rightRel (H : Subgroup F) (a * ι x) b := by
          rw [QuotientGroup.rightRel_apply]
          simpa only [a, b, mul_inv_rev, mul_assoc] using hx
        calc
          ((ι x)⁻¹ • q : OpenSubgroupRightQuotient H)
              = (ι x)⁻¹ • (Quotient.mk'' a : OpenSubgroupRightQuotient H) := by
                  rw [Quotient.out_eq' q]
          _ = Quotient.mk'' (a * ι x) := by
                rw [rightCosetMulAction_inv_mk_smul (H := (H : Subgroup F)) (ι x) a]
          _ = Quotient.mk'' b := Quotient.eq''.mpr hrel
          _ = q' := Quotient.out_eq' q'
    rw [show
      (fun x : X => ((ι x)⁻¹ • q : OpenSubgroupRightQuotient H)) ⁻¹' ({q'} :
          Set (OpenSubgroupRightQuotient H)) =
        (fun x : X => b * (ι x)⁻¹ * a⁻¹) ⁻¹' ((H : Subgroup F) : Set F) by
          simpa using hpre]
    exact H.isOpen'.preimage ((continuous_const.mul (hιcont.inv)).mul continuous_const)
  simpa [rightSchreierNextCoset] using hqcont

/-- The corresponding Schreier generator map is continuous. -/
theorem continuous_rightSchreierGenerator
    (hτcont : Continuous τ) (hιcont : Continuous ι) :
    Continuous (fun p : OpenSubgroupRightQuotient H × X =>
      rightSchreierGenerator (F := F) (H := H) (τ := τ) (hτ := hτ) (ι := ι) p.1 p.2) := by
  let : TopologicalSpace
      (rightSchreierSection (F := F) (H := H) (τ := τ) (hτ := hτ) :
        SchreierCocycleData (F := F) (X := X) H).Q :=
    inferInstanceAs (TopologicalSpace (OpenSubgroupRightQuotient H))
  simpa using
    ((rightSchreierSection (F := F) (H := H) (τ := τ) (hτ := hτ) :
        SchreierCocycleData (F := F) (X := X) H).continuous_generator
      ι hτcont
      (continuous_rightSchreierNextCoset (F := F) (H := H) (ι := ι) hιcont)
      hιcont)

end Topological


omit [IsTopologicalGroup F] in
/--
The basepoint projection induced by a wreath-product homomorphism evaluates a right Schreier
generator by the corresponding left coordinate.
-/
theorem rightQuotientBasepointProjectionHom_rightSchreierGenerator
    {A : Type*} [Group A]
    (ψ : F →* PermutationalWreathProduct A (OpenSubgroupRightQuotient H) F)
    (hψ :
      (SemidirectProduct.rightHom :
          PermutationalWreathProduct A (OpenSubgroupRightQuotient H) F →* F).comp ψ =
        MonoidHom.id F)
    (hτpure :
      ∀ q : OpenSubgroupRightQuotient H,
        wreathLeftCoordinate ψ
            (openSubgroupRightCoset H (1 : F)) (τ q) = 1)
    (q : OpenSubgroupRightQuotient H) (x : X) :
    rightQuotientBasepointProjectionHom (H : Subgroup F) ψ hψ
        (rightSchreierGenerator (F := F) (H := H) (τ := τ) (hτ := hτ) (ι := ι) q x) =
      wreathLeftCoordinate ψ q (ι x) := by
  exact rightQuotientBasepointProjectionHom_apply_cocycle
    (H : Subgroup F) τ hτ ψ hψ hτpure (ι x) q

end RightSchreierGenerators

end Profinite
end ReidemeisterSchreier
