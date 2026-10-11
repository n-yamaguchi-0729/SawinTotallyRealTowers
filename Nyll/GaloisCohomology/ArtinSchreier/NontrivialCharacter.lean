/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.ArtinSchreier.RootCharacter
import Mathlib.FieldTheory.Galois.Infinite

/-! # Nontrivial cyclic characters from Artin–Schreier obstructions -/

namespace ArtinSchreierTheory
universe u v
variable (p : ℕ) [Fact p.Prime]
variable {K : Type u} {Ω : Type v} [Field K] [Field Ω]
  [CharP Ω p] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]

/-- A failed Artin–Schreier equation gives a nontrivial continuous prime cyclic character. -/
theorem exists_nontrivial_character_of_artinSchreier_not_surjective
    (hAS : ∃ a : K, ∀ x : K, x ^ p - x ≠ a) :
    ∃ χ : Gal(Ω/K) →ₜ* Multiplicative (ZMod p), ∃ σ : Gal(Ω/K), χ σ ≠ 1 := by
  classical
  obtain ⟨a, ha⟩ := hAS
  obtain ⟨β, hβ⟩ := exists_root p Ω (algebraMap K Ω a)
  let χ := rootCharacter p Ω a β hβ
  refine ⟨χ, ?_⟩
  by_contra! h
  have hfixed (σ : Gal(Ω/K)) : σ β = β := by
    have hc := rootCharacter_cast p Ω a β hβ σ
    change (ZMod.castHom (dvd_refl p) Ω) (χ σ).toAdd = σ β - β at hc
    rw [h σ] at hc
    change (ZMod.castHom (dvd_refl p) Ω) 0 = σ β - β at hc
    rw [map_zero] at hc
    exact sub_eq_zero.mp hc.symm
  obtain ⟨x, hx⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed β).mpr hfixed
  apply ha x
  apply (algebraMap K Ω).injective
  rw [map_sub, map_pow, hx]
  exact hβ

end ArtinSchreierTheory
