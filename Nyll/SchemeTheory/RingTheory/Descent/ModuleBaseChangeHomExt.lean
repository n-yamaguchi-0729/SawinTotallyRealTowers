/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Localization.Module
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Extensionality for homomorphisms between base-changed modules

Maps between tensor extensions are determined on elements `1 ⊗ m`, and maps
between localized modules are determined on fractions with denominator one.
These are the two componentwise extensionality lemmas used by mixed formal
gluing.
-/


noncomputable section

namespace EtaleFundamentalGroups

open scoped TensorProduct

universe u v w w'

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module R M]
variable {N : Type w'} [AddCommGroup N] [Module R N]

/-- An `S`-linear map between scalar extensions is determined by its values
on the canonical generators `1 ⊗ m`. -/
theorem tensorProduct_linearMap_ext_of_one_tmul
    {F G : (S ⊗[R] M) →ₗ[S] (S ⊗[R] N)}
    (h : ∀ m : M, F (1 ⊗ₜ[R] m) = G (1 ⊗ₜ[R] m)) :
    F = G := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | tmul s m =>
      calc
        F (s ⊗ₜ[R] m) = F (s • (1 ⊗ₜ[R] m)) := by
          rw [TensorProduct.smul_tmul']
          simp
        _ = s • F (1 ⊗ₜ[R] m) := by rw [map_smul]
        _ = s • G (1 ⊗ₜ[R] m) := by rw [h m]
        _ = G (s • (1 ⊗ₜ[R] m)) := (G.map_smul s _).symm
        _ = G (s ⊗ₜ[R] m) := by
          rw [TensorProduct.smul_tmul']
          simp

/-- A linear map between localized modules is determined by the images of
the source elements with denominator one. -/
theorem localizedModule_linearMap_ext_of_mk_one
    (T : Submonoid R)
    {F G : LocalizedModule T M →ₗ[Localization T]
      LocalizedModule T N}
    (h : ∀ m : M,
      F (LocalizedModule.mk m 1) = G (LocalizedModule.mk m 1)) :
    F = G := by
  apply LinearMap.restrictScalars_injective R
  apply IsLocalizedModule.linearMap_ext T
    (LocalizedModule.mkLinearMap T M)
    (LocalizedModule.mkLinearMap T N)
  apply LinearMap.ext
  intro m
  exact h m

end EtaleFundamentalGroups

end
