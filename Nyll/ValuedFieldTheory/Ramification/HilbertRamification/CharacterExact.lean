/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.CharacterMap

/-!
# Hilbert ramification theory: character exactness

This file contains the exactness and quotient consequences of the character
constructed in `CharacterMap`.  It is the exactness part of
the inertia-character exact sequence that does not require the finite-cardinality
surjectivity argument onto the full group `Hom(Delta/Gamma, lambda*)`.
-/

namespace RamificationTheory


noncomputable section

universe u v

namespace HilbertRamification
namespace ValuationSubring


variable (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]

/-- The ramification subgroup, viewed inside the value-trivial inertia group
that carries the residue-unit character. -/
abbrev ramificationGroupInValueTrivialInertiaGroup
    (A : _root_.ValuationSubring L) :
    Subgroup (valueTrivialInertiaGroup K A) :=
  (ramificationGroup K A).subgroupOf (valueTrivialInertiaGroup K A)

/-- States the theorem `mem_ramificationGroupInValueTrivialInertiaGroup_iff`. -/
@[simp] theorem mem_ramificationGroupInValueTrivialInertiaGroup_iff
    (A : _root_.ValuationSubring L) (σ : valueTrivialInertiaGroup K A) :
    σ ∈ ramificationGroupInValueTrivialInertiaGroup K A ↔
      (σ : inertiaGroup K A) ∈ ramificationGroup K A := by
  rfl

/-- Provides the instance `ramificationGroupInValueTrivialInertiaGroup_normal`. -/
instance ramificationGroupInValueTrivialInertiaGroup_normal
    (A : _root_.ValuationSubring L) :
    (ramificationGroupInValueTrivialInertiaGroup K A).Normal := by
  infer_instance

/-- Inertia-character exactness:
inside value-trivial inertia, the kernel of the character map is exactly
`R_w`. -/
theorem ramificationGroupInValueTrivialInertiaGroup_eq_characterHom_ker
    (A : _root_.ValuationSubring L) :
    ramificationGroupInValueTrivialInertiaGroup K A =
      (valueTrivialInertiaCharacterHom K A).ker := by
  ext σ
  rw [mem_ramificationGroupInValueTrivialInertiaGroup_iff,
    valueTrivialInertiaCharacterHom_mem_ker_iff]

/-- Inertia-character exactness:
`R_w -> I_w -> Hom(Delta/Gamma, lambda*)` is exact at value-trivial inertia.
The target is the concrete character group produced in `CharacterMap`. -/
theorem valueTrivialCharacter_mulExact
    (A : _root_.ValuationSubring L) :
    Function.MulExact
      (ramificationGroupInValueTrivialInertiaGroup K A).subtype
      (valueTrivialInertiaCharacterHom K A) := by
  rw [MonoidHom.mulExact_iff,
    ← ramificationGroupInValueTrivialInertiaGroup_eq_characterHom_ker
      (K := K) A]
  exact (Subgroup.range_subtype _).symm

/-- Inertia-character exactness:
the same exactness after restricting the target to the range of the character
map. -/
theorem valueTrivialCharacter_mulExactRange
    (A : _root_.ValuationSubring L) :
    Function.MulExact
      (ramificationGroupInValueTrivialInertiaGroup K A).subtype
      (valueTrivialInertiaCharacterHom K A).rangeRestrict := by
  rw [MonoidHom.mulExact_iff, MonoidHom.ker_rangeRestrict,
    ← ramificationGroupInValueTrivialInertiaGroup_eq_characterHom_ker
      (K := K) A]
  exact (Subgroup.range_subtype _).symm

/-- The character map, with codomain restricted to its range. -/
abbrev valueTrivialInertiaCharacterRange
    (A : _root_.ValuationSubring L) :
    Subgroup
      ((Lˣ ⧸ A.unitGroup) ⧸ baseUnitValueClassSubgroup K A →*
        (IsLocalRing.ResidueField A)ˣ) :=
  (valueTrivialInertiaCharacterHom K A).range

/-- The value-trivial character map is onto its range. -/
theorem valueTrivialInertiaCharacter_rangeRestrict_surjective
    (A : _root_.ValuationSubring L) :
    Function.Surjective
      (valueTrivialInertiaCharacterHom K A).rangeRestrict := by
  rintro ⟨χ, σ, rfl⟩
  exact ⟨σ, rfl⟩

/-- The inertia-character exact sequence range form:
`1 -> R_w -> I_w^{value=1} -> im(χ) -> 1`. -/
theorem valueTrivialCharacter_shortExactRange
    (A : _root_.ValuationSubring L) :
    Function.Injective
        (ramificationGroupInValueTrivialInertiaGroup K A).subtype ∧
      Function.MulExact
        (ramificationGroupInValueTrivialInertiaGroup K A).subtype
        (valueTrivialInertiaCharacterHom K A).rangeRestrict ∧
      Function.Surjective
        (valueTrivialInertiaCharacterHom K A).rangeRestrict := by
  exact
    ⟨Subtype.coe_injective,
      valueTrivialCharacter_mulExactRange (K := K) A,
      valueTrivialInertiaCharacter_rangeRestrict_surjective
        (K := K) A⟩

/-- The inertia-character exact sequence first-isomorphism form:
`I_w^{value=1}/R_w` is canonically the range of the character map. -/
def valueTrivialInertiaQuotientRamificationEquivCharacterRange
    (A : _root_.ValuationSubring L) :
    valueTrivialInertiaGroup K A ⧸
        ramificationGroupInValueTrivialInertiaGroup K A ≃*
      valueTrivialInertiaCharacterRange K A :=
  (QuotientGroup.quotientMulEquivOfEq
      (ramificationGroupInValueTrivialInertiaGroup_eq_characterHom_ker
        (K := K) A)).trans
    (QuotientGroup.quotientKerEquivRange
      (valueTrivialInertiaCharacterHom K A))

/-- States the theorem `valueTrivialInertiaQuotientRamificationEquivCharacterRange_mk`. -/
@[simp] theorem valueTrivialInertiaQuotientRamificationEquivCharacterRange_mk
    (A : _root_.ValuationSubring L) (σ : valueTrivialInertiaGroup K A) :
    valueTrivialInertiaQuotientRamificationEquivCharacterRange
        (K := K) A
        (QuotientGroup.mk'
          (ramificationGroupInValueTrivialInertiaGroup K A) σ) =
      (valueTrivialInertiaCharacterHom K A).rangeRestrict σ :=
  rfl

end ValuationSubring
end HilbertRamification

end
end RamificationTheory
