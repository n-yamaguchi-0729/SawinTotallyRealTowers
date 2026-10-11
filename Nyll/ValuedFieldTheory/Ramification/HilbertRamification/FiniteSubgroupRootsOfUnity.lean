/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Finite multiplicative subgroups and roots of unity

Identifies a finite subgroup of field units with all roots of unity of its order and produces a
primitive root. Finite characters are then expressed as surjections onto these root groups with
the corresponding kernel quotient.
-/

noncomputable section

namespace RamificationTheory.HilbertRamification

universe u v

variable {k : Type u} [Field k]

/-- A finite subgroup of field units is the full root group of its order. -/
theorem finiteSubgroup_eq_rootsOfUnity (H : Subgroup kˣ) [Finite H] :
    H = rootsOfUnity (Nat.card H) k := by
  apply Subgroup.eq_of_le_of_card_ge
  · intro ζ hζ
    rw [mem_rootsOfUnity]
    have hpow : (⟨ζ, hζ⟩ : H) ^ Nat.card H = 1 := pow_card_eq_one'
    exact congrArg (fun a : H => (a : kˣ)) hpow
  · exact card_rootsOfUnity k (Nat.card H)

/-- A finite multiplicative subgroup yields an actual primitive root in the field. -/
theorem exists_primitiveRoot_card_finiteSubgroup (H : Subgroup kˣ) [Finite H] :
    ∃ ζ : k, IsPrimitiveRoot ζ (Nat.card H) := by
  apply card_rootsOfUnity_eq_iff_exists_isPrimitiveRoot.mp
  rw [← finiteSubgroup_eq_rootsOfUnity H]

variable {G : Type v} [Group G] [Finite G]

/-- Any actual finite residue-unit homomorphism lands onto all roots of its image order. -/
def finiteImageRootsCharacter (f : G →* kˣ) :
    G →* rootsOfUnity (Nat.card f.range) k := by
  have : Finite f.range :=
    Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  exact f.codRestrict (rootsOfUnity (Nat.card f.range) k)
    (fun g => finiteSubgroup_eq_rootsOfUnity f.range ▸ ⟨g, rfl⟩)

theorem finiteImageRootsCharacter_surjective (f : G →* kˣ) :
    Function.Surjective (finiteImageRootsCharacter f) := by
  have : Finite f.range :=
    Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  intro ζ
  have hζ : (ζ : kˣ) ∈ f.range :=
    (finiteSubgroup_eq_rootsOfUnity f.range).ge ζ.property
  obtain ⟨g, hg⟩ := hζ
  exact ⟨g, Subtype.ext hg⟩

theorem finiteImageRootsCharacter_ker (f : G →* kˣ) :
    (finiteImageRootsCharacter f).ker = f.ker := by
  apply Subgroup.ext
  intro g
  exact Subtype.ext_iff

omit [Finite G] in
/-- The actual image order is the order of the actual kernel quotient. -/
theorem finiteImageRootsCharacter_degree (f : G →* kˣ) :
    Nat.card f.range = Nat.card (G ⧸ f.ker) :=
  (Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv).symm

/-- A finite image in the units of a field identifies the kernel quotient with
the full roots-of-unity group of the image order. -/
noncomputable def finiteImageQuotientEquivRootsOfUnity (f : G →* kˣ) :
    (G ⧸ f.ker) ≃* rootsOfUnity (Nat.card f.range) k :=
  (QuotientGroup.quotientMulEquivOfEq (finiteImageRootsCharacter_ker f).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (finiteImageRootsCharacter f)
      (finiteImageRootsCharacter_surjective f))

end RamificationTheory.HilbertRamification

end
