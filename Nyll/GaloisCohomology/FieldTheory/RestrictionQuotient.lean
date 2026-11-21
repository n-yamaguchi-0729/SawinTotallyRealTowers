/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # Restriction quotients and fixed units in a Galois tower -/

@[expose] public section

noncomputable section

namespace ClassFieldTower.Cohomology

universe u v

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
variable (E : IntermediateField K L)

/-- The quotient by the restriction kernel identifies with the lower-field Galois group. -/
def restrictionQuotientEquiv [Normal K L] [Normal K E] :
    Gal(L/K) ⧸ (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E).ker ≃* Gal(E/K) :=
  QuotientGroup.quotientKerEquivOfSurjective (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E)
    (AlgEquiv.restrictNormalHom_surjective L (F := K) (K₁ := E))

/-- A unit fixed by the relative Galois group descends to a unit of the intermediate field. -/
theorem exists_unit_map_eq_of_fixed [FiniteDimensional K L] [IsGalois K L]
    (a : Lˣ) (ha : ∀ σ : Gal(L/E), σ (a : L) = (a : L)) :
    ∃ b : Eˣ, Units.map E.val.toMonoidHom b = a := by
  obtain ⟨b, hb⟩ := (IsGalois.mem_range_algebraMap_iff_fixed
    (F := E) (E := L) (a : L)).mpr ha
  have hb0 : b ≠ 0 := by
    intro h
    apply Units.ne_zero a
    rw [← hb, h, map_zero]
  exact ⟨Units.mk0 b hb0, Units.ext hb⟩

end ClassFieldTower.Cohomology
