/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Finite normal restriction kernels

The kernel of restriction to a finite normal extension is the fixing
subgroup of its actual image in the upper field. If the upper extension
is normal and the finite extension is Galois, restriction is surjective
and this kernel has index equal to the field degree.
-/

namespace KummerTheory

universe u

variable {K M Ω : Type u} [Field K] [Field M] [Field Ω]
  [Algebra K M] [Algebra M Ω] [Algebra K Ω] [IsScalarTower K M Ω]

/-- Restriction to a finite normal extension has open kernel in the actual
upper Galois group, without algebraicity assumptions on the upper field. -/
theorem normalRestrictionKernel_isOpen [FiniteDimensional K M] [Normal K M] :
    IsOpen (((AlgEquiv.restrictNormalHom M : Gal(Ω/K) →* Gal(M/K)).ker :
      Subgroup Gal(Ω/K)) : Set Gal(Ω/K)) := by
  let i : M →ₐ[K] Ω := IsScalarTower.toAlgHom K M Ω
  let S : IntermediateField K Ω := i.fieldRange
  have : FiniteDimensional K S :=
    LinearEquiv.finiteDimensional i.equivFieldRange.toLinearEquiv
  have hker : (AlgEquiv.restrictNormalHom M : Gal(Ω/K) →* Gal(M/K)).ker =
      S.fixingSubgroup := by
    ext σ
    change σ.restrictNormal M = 1 ↔ σ ∈ S.fixingSubgroup
    constructor
    · intro hσ
      apply (IntermediateField.mem_fixingSubgroup_iff S σ).mpr
      intro x hx
      obtain ⟨m, rfl⟩ := hx
      change σ (algebraMap M Ω m) = algebraMap M Ω m
      rw [← σ.restrictNormal_commutes M m, hσ]
      rfl
    · intro hσ
      apply AlgEquiv.ext
      intro m
      apply (algebraMap M Ω).injective
      change algebraMap M Ω (σ.restrictNormal M m) = algebraMap M Ω m
      rw [σ.restrictNormal_commutes M m]
      exact (IntermediateField.mem_fixingSubgroup_iff S σ).mp hσ
        (algebraMap M Ω m) ⟨m, rfl⟩
  rw [hker]
  exact S.fixingSubgroup_isOpen

/-- In a normal upper extension, the kernel of restriction to a finite
Galois extension has index equal to that extension's degree. -/
theorem normalRestrictionKernel_index [FiniteDimensional K M] [IsGalois K M]
    [Normal K Ω] :
    (AlgEquiv.restrictNormalHom M : Gal(Ω/K) →* Gal(M/K)).ker.index =
      Module.finrank K M := by
  let q : Gal(Ω/K) →* Gal(M/K) := AlgEquiv.restrictNormalHom M
  have hsurj : Function.Surjective q := AlgEquiv.restrictNormalHom_surjective Ω
  exact q.ker.index_eq_card.trans
    ((Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective q hsurj).toEquiv).trans
      (IsGalois.card_aut_eq_finrank K M))

end KummerTheory
