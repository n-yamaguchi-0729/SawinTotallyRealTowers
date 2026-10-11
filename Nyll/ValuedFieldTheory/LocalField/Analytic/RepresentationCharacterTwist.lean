/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RepresentationTheory.Invariants

/-!
# Inverse-character twists and their actual invariant submodules

Character eigenvectors are fixed points of the representation twisted by
the inverse character. The same construction is shared by averaging and
by restriction to invariant submodules.
-/

namespace LocalFieldTheory.DiscreteValuationField

variable {R Δ A : Type*} [CommRing R] [Group Δ]
  [AddCommGroup A] [Module R A]

/-- Multiply the given action by the inverse of the given character. -/
def inverseCharacterTwist (χ : Δ →* Rˣ) (ρ : Representation R Δ A) :
    Representation R Δ A where
  toFun g := (((χ g)⁻¹ : Rˣ) : R) • ρ g
  map_one' := by
    simp only [map_one, inv_one, Units.val_one, one_smul]
  map_mul' g h := by
    ext a
    simp only [map_mul, mul_inv_rev, Units.val_mul, LinearMap.smul_apply,
      Module.End.mul_apply, map_smul, smul_smul]

/-- The actual fixed vectors of the twist are the original character eigenvectors. -/
theorem inverseCharacterTwist_mem_invariants_iff
    (χ : Δ →* Rˣ) (ρ : Representation R Δ A) (a : A) :
    a ∈ (inverseCharacterTwist χ ρ).invariants ↔
      ∀ g : Δ, ρ g a = (χ g : R) • a := by
  constructor
  · intro ha g
    have h := congrArg (fun x : A => (χ g : R) • x) (ha g)
    change (χ g : R) • (((χ g)⁻¹ : Rˣ) • ρ g a) = (χ g : R) • a at h
    simpa only [Units.smul_def, smul_smul, Units.mul_inv, one_smul] using h
  · intro ha g
    change ((χ g)⁻¹ : Rˣ) • ρ g a = a
    rw [Units.smul_def, ha g, smul_smul, Units.inv_mul, one_smul]

end LocalFieldTheory.DiscreteValuationField
