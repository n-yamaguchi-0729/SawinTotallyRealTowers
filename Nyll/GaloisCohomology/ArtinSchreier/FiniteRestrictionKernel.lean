/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.ArtinSchreier.RootCharacter
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # Finite kernels of restriction on Artin–Schreier classes -/

namespace ArtinSchreierTheory

universe u v
variable (p : ℕ) [Fact p.Prime]
variable {K : Type u} {L : Type v} [Field K] [Field L]
  [CharP K p] [CharP L p]

/-- Restrict additive Artin–Schreier classes along a field embedding. -/
def classMap (f : K →+* L) :
    K ⧸ ((frobenius K p).toAddMonoidHom - AddMonoidHom.id K).range →+
      L ⧸ ((frobenius L p).toAddMonoidHom - AddMonoidHom.id L).range :=
  QuotientAddGroup.map _ _ f.toAddMonoidHom (by
    intro a ha
    obtain ⟨b, rfl⟩ := ha
    refine ⟨f b, ?_⟩
    change (f b) ^ p - f b = f (b ^ p - b)
    rw [map_sub, map_pow])

theorem classMap_mk (f : K →+* L) (a : K) :
    classMap p f (a : K ⧸
      ((frobenius K p).toAddMonoidHom - AddMonoidHom.id K).range) =
        (f a : L ⧸ ((frobenius L p).toAddMonoidHom - AddMonoidHom.id L).range) := rfl

/-- In a finite Galois extension, restriction kills only finitely many
Artin–Schreier classes. Such a class injects into its root-difference
character on the finite relative Galois group. -/
theorem finite_classMap_kernel [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    Finite (classMap p (algebraMap K L)).ker := by
  classical
  let R := (classMap p (algebraMap K L)).ker
  have hroot (q : R) : ∃ (a : K) (β : L),
      (a : K ⧸ ((frobenius K p).toAddMonoidHom - AddMonoidHom.id K).range) = q.val ∧
        β ^ p - β = algebraMap K L a := by
    obtain ⟨a, ha⟩ := QuotientAddGroup.mk'_surjective
      ((frobenius K p).toAddMonoidHom - AddMonoidHom.id K).range q.val
    change (a : K ⧸ ((frobenius K p).toAddMonoidHom - AddMonoidHom.id K).range) = q.val at ha
    have hz : (algebraMap K L a : L ⧸
        ((frobenius L p).toAddMonoidHom - AddMonoidHom.id L).range) = 0 := by
      change classMap p (algebraMap K L) a = 0
      rw [ha]
      exact q.property
    obtain ⟨β, hβ⟩ := (QuotientAddGroup.eq_zero_iff (algebraMap K L a)).mp hz
    exact ⟨a, β, ha, hβ⟩
  choose a β ha hβ using hroot
  let e : R → (Gal(L/K) → ZMod p) :=
    fun q σ => (rootCharacter p L (a q) (β q) (hβ q) σ).toAdd
  apply Finite.of_injective e
  intro q r heq
  have hfixed (σ : Gal(L/K)) : σ (β q - β r) = β q - β r := by
    have h := congrArg (ZMod.castHom (dvd_refl p) L) (congrFun heq σ)
    change (ZMod.castHom (dvd_refl p) L)
      ((rootCharacter p L (a q) (β q) (hβ q) σ).toAdd) =
        (ZMod.castHom (dvd_refl p) L)
          ((rootCharacter p L (a r) (β r) (hβ r) σ).toAdd) at h
    rw [rootCharacter_cast, rootCharacter_cast] at h
    rw [map_sub]
    linear_combination h
  obtain ⟨x, hx⟩ :=
    (InfiniteGalois.mem_range_algebraMap_iff_fixed (β q - β r)).mpr hfixed
  have hxAS : x ^ p - x = a q - a r := by
    apply (algebraMap K L).injective
    rw [map_sub, map_pow, hx, sub_pow_char, map_sub]
    linear_combination hβ q - hβ r
  apply Subtype.ext
  rw [← ha q, ← ha r]
  apply QuotientAddGroup.eq.mpr
  refine ⟨-x, ?_⟩
  change (-x) ^ p - (-x) = -(a q) + a r
  have hneg := map_neg
    ((frobenius K p).toAddMonoidHom - AddMonoidHom.id K) x
  change (-x) ^ p - (-x) = -(x ^ p - x) at hneg
  rw [hneg, hxAS]
  ring

end ArtinSchreierTheory
