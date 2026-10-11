/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.ArtinSchreier.FieldMapApproximation
import Mathlib.FieldTheory.Galois.Infinite

/-!
# Detecting a field automorphism by an Artin--Schreier character

A moved additive class gives a moved continuous absolute Galois character.
The construction uses the separable closure and therefore does not require
that the field be perfect.
-/

namespace ArtinSchreierTheory

open Field.absoluteGaloisGroup ValuationTheory.Completion

variable (p : ℕ) [Fact p.Prime] {K : Type*} [Field K] [CharP K p]

/-- A nonzero difference of Artin--Schreier classes detects the actual absolute
Galois map associated to the field automorphism. -/
theorem exists_character_moved_by_map_of_pow_sub_ne
    (τ : K ≃+* K) (a : K) (ha : ∀ y : K, y ^ p - y ≠ τ a - a) :
    ∃ χ : Gal(AlgebraicClosure K/K) →ₜ* Multiplicative (ZMod p),
      ∃ σ : Gal(AlgebraicClosure K/K),
        χ (map τ.toRingHom σ) ≠ χ σ := by
  classical
  by_contra! hfixed
  obtain ⟨β, hβ⟩ := exists_root p (SeparableClosure K)
    (algebraMap K (SeparableClosure K) a)
  let γ := separableClosureLift τ.toRingHom β
  have hγ : γ ^ p - γ = algebraMap K (SeparableClosure K) (τ a) := by
    rw [← map_pow, ← map_sub, hβ, separableClosureLift_algebraMap]
    rfl
  let χ : Gal(AlgebraicClosure K/K) →ₜ* Multiplicative (ZMod p) :=
    (rootCharacter p (SeparableClosure K) a β hβ).comp
      (ContinuousMonoidHom.toContinuousMonoidHom (separableClosureAutContinuousEquiv K))
  have hchars (σ : Gal(SeparableClosure K/K)) :
      rootCharacter p (SeparableClosure K) (τ a) γ hγ σ =
        rootCharacter p (SeparableClosure K) a β hβ σ := by
    obtain ⟨ρ, rfl⟩ := (separableClosureAutEquiv K).surjective σ
    exact (rootCharacter_fieldMap p τ.toRingHom a β hβ hγ ρ).symm.trans
      (hfixed χ ρ)
  have hdiff (σ : Gal(SeparableClosure K/K)) : σ (γ - β) = γ - β := by
    have h := congrArg
      (fun z : Multiplicative (ZMod p) =>
        (ZMod.castHom (dvd_refl p) (SeparableClosure K)) z.toAdd) (hchars σ)
    rw [rootCharacter_cast, rootCharacter_cast] at h
    rw [map_sub]
    linear_combination h
  obtain ⟨x, hx⟩ :=
    (InfiniteGalois.mem_range_algebraMap_iff_fixed (γ - β)).mpr hdiff
  apply ha x
  apply (algebraMap K (SeparableClosure K)).injective
  rw [map_sub, map_pow, hx, sub_pow_char, map_sub]
  linear_combination hγ - hβ

end ArtinSchreierTheory
