/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.CharP.Reduced
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Data.Fintype.Card

/-!
# Scaling finite residue characters by characteristic powers

Proves injectivity of exponential-characteristic-power maps on field units and surjectivity on
finite subgroups. Scaling a character by such a power preserves its kernel and, for a finite
source group, its range.
-/

namespace RamificationTheory.HilbertRamification

universe u v

variable {k : Type u} [Field k]

/-- Residue-characteristic-power maps are injective on field units. -/
theorem residueUnits_expCharPow_injective (p a : ℕ) [ExpChar k p] :
    Function.Injective (fun x : kˣ => x ^ (p ^ a)) := by
  intro x y h
  apply Units.ext
  apply iterateFrobenius_inj k p a
  exact congrArg (fun z : kˣ => (z : k)) h

/-- Such power maps are onto every actual finite subgroup of field units. -/
theorem finiteSubgroup_expCharPow_surjective
    (H : Subgroup kˣ) [Finite H] (p a : ℕ) [ExpChar k p] :
    Function.Surjective (fun x : H => x ^ (p ^ a)) := by
  apply Finite.surjective_of_injective
  intro x y h
  apply Subtype.ext
  apply residueUnits_expCharPow_injective p a
  exact congrArg (fun z : H => (z : kˣ)) h

variable {G : Type v} [Group G]

/-- Scaling an actual residue-unit character by a residue-characteristic power
preserves its actual kernel. -/
theorem residueCharacter_expCharPow_ker (f : G →* kˣ) (p a : ℕ) [ExpChar k p] :
    ((powMonoidHom (p ^ a)).comp f).ker = f.ker := by
  apply Subgroup.ext
  intro g
  change (f g) ^ (p ^ a) = 1 ↔ f g = 1
  constructor
  · intro h
    apply residueUnits_expCharPow_injective p a
    exact h.trans (one_pow (p ^ a)).symm
  · intro h
    rw [h, one_pow]

/-- Scaling an actual finite residue-unit character preserves its entire image. -/
theorem finiteResidueCharacter_expCharPow_range
    [Finite G] (f : G →* kˣ) (p a : ℕ) [ExpChar k p] :
    ((powMonoidHom (p ^ a)).comp f).range = f.range := by
  have : Finite f.range :=
    Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  apply Subgroup.ext
  intro z
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g ^ (p ^ a), map_pow f g (p ^ a)⟩
  · intro hz
    obtain ⟨w, hw⟩ := finiteSubgroup_expCharPow_surjective f.range p a ⟨z, hz⟩
    obtain ⟨g, hg⟩ := w.property
    refine ⟨g, ?_⟩
    exact (congrArg (fun t : kˣ => t ^ (p ^ a)) hg).trans
      (congrArg (fun t : f.range => (t : kˣ)) hw)

end RamificationTheory.HilbertRamification
