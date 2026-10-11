/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.LocalField.Analytic.RepresentationCharacterTwist
import Mathlib.RepresentationTheory.Invariants

/-!
# Lifting character eigenvectors by averaging

The inverse character twist turns character eigenvectors into invariants.
The standard averaging projection commutes with an actual intertwining map,
so every eigenvector in its image has an eigenvector preimage.
-/

noncomputable section

namespace LocalFieldTheory.DiscreteValuationField

open scoped BigOperators

variable {R Δ A B : Type*} [CommRing R] [Group Δ]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]

variable [Fintype Δ] [Invertible (Fintype.card Δ : R)]

/-- The averaging projection onto vectors transforming by `χ`. -/
def characterAverage (χ : Δ →* Rˣ) (ρ : Representation R Δ A) : A →ₗ[R] A :=
  (inverseCharacterTwist χ ρ).averageMap

/-- The character projection is the usual inverse-character weighted average. -/
theorem characterAverage_apply (χ : Δ →* Rˣ) (ρ : Representation R Δ A) (a : A) :
    characterAverage χ ρ a =
      ⅟(Fintype.card Δ : R) • ∑ g : Δ, (((χ g)⁻¹ : Rˣ) : R) • ρ g a := by
  simp only [characterAverage, Representation.averageMap, GroupAlgebra.average,
    map_smul, map_sum, Representation.asAlgebraHom_of, LinearMap.smul_apply,
    LinearMap.sum_apply, inverseCharacterTwist, MonoidHom.coe_mk, OneHom.coe_mk]

/-- The weighted average transforms by the original character. -/
theorem characterAverage_eigen (χ : Δ →* Rˣ) (ρ : Representation R Δ A) (a : A)
    (g : Δ) :
    ρ g (characterAverage χ ρ a) = (χ g : R) • characterAverage χ ρ a :=
  (inverseCharacterTwist_mem_invariants_iff χ ρ (characterAverage χ ρ a)).mp
    ((inverseCharacterTwist χ ρ).averageMap_invariant a) g

/-- Averaging fixes every character eigenvector. -/
theorem characterAverage_eq_self (χ : Δ →* Rˣ) (ρ : Representation R Δ A) (a : A)
    (ha : ∀ g : Δ, ρ g a = (χ g : R) • a) :
    characterAverage χ ρ a = a :=
  (inverseCharacterTwist χ ρ).averageMap_id a
    ((inverseCharacterTwist_mem_invariants_iff χ ρ a).mpr ha)

/-- Intertwining maps commute with the character projection. -/
theorem map_characterAverage (χ : Δ →* Rˣ) {ρ : Representation R Δ A}
    {σ : Representation R Δ B} (f : Representation.IntertwiningMap ρ σ) (a : A) :
    f (characterAverage χ ρ a) = characterAverage χ σ (f a) := by
  rw [characterAverage_apply, characterAverage_apply]
  simp only [map_smul, map_sum, f.isIntertwining]

/-- A character eigenvector in the image of an intertwining map has an
eigenvector preimage, obtained by averaging any preimage. -/
theorem exists_eigen_preimage (χ : Δ →* Rˣ) {ρ : Representation R Δ A}
    {σ : Representation R Δ B} (f : Representation.IntertwiningMap ρ σ) (b : B)
    (hb : ∀ g : Δ, σ g b = (χ g : R) • b) (hrange : b ∈ Set.range f) :
    ∃ a : A, f a = b ∧ ∀ g : Δ, ρ g a = (χ g : R) • a := by
  obtain ⟨a, ha⟩ := hrange
  refine ⟨characterAverage χ ρ a, ?_, characterAverage_eigen χ ρ a⟩
  rw [map_characterAverage, ha]
  exact characterAverage_eq_self χ σ b hb

end LocalFieldTheory.DiscreteValuationField
