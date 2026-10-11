/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Kummer.Concrete.SeparableAbsoluteKummer
import Nyll.GaloisCohomology.Kummer.Concrete.SeparableClosureConjugation
import Nyll.GaloisCohomology.Kummer.Concrete.SeparableKummerH1
import Nyll.GaloisCohomology.Kummer.Concrete.SemilinearConjugation
import Nyll.GaloisCohomology.Kummer.Concrete.RootCharacters

/-!
# Constant-coefficient Kummer naturality in arbitrary characteristic

The chosen lift restricts to the separable closure and carries each radical
root to a root of the transformed unit. If the base automorphism fixes the
roots of unity, the actual absolute Kummer character has constant coefficients.
-/

namespace ClassFieldTower.Martinet.Shafarevich

open KummerTheory

variable (K : Type*) [Field K]

private theorem separableKummer_naturality
    (n : ℕ+) [NeZero ((n : ℕ) : K)]
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (τ : K ≃+* K) (a : Kˣ) (σ : Gal(SeparableClosure K/K)) :
    ((separableKummerContinuousNthRootsCharacterEquiv K n hmu
        ((Units.map τ.toMonoidHom a : Kˣ) :
          Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range)
        (semilinearGaloisConjugate τ (separableClosureEquivOfEquiv τ)
          (separableClosureEquivOfEquiv_algebraMap τ) σ) :
      DiscreteNthRootsSubgroup (SeparableClosure K) (n : ℕ)) :
        (SeparableClosure K)ˣ) =
      Units.map (separableClosureEquivOfEquiv τ).toMonoidHom
        ((separableKummerContinuousNthRootsCharacterEquiv K n hmu
            (a : Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range) σ :
          DiscreteNthRootsSubgroup (SeparableClosure K) (n : ℕ)) :
            (SeparableClosure K)ˣ) := by
  obtain ⟨β, hβ⟩ : ∃ β : (SeparableClosure K)ˣ,
      β ^ (n : ℕ) = Units.map (algebraMap K (SeparableClosure K)).toMonoidHom a := by
    apply (mem_finiteKummerRadicalSubgroup_iff
      (K := K) (L := SeparableClosure K) n).mp
    rw [finiteKummerRadicalSubgroup_separableClosure_eq_top K n]
    exact Subgroup.mem_top a
  let e : SeparableClosure K ≃+* SeparableClosure K := separableClosureEquivOfEquiv τ
  have hβτ : (Units.map e.toMonoidHom β) ^ (n : ℕ) =
      Units.map (algebraMap K (SeparableClosure K)).toMonoidHom
        (Units.map τ.toMonoidHom a) := by
    rw [← map_pow, hβ]
    apply Units.ext
    exact separableClosureEquivOfEquiv_algebraMap τ (a : K)
  rw [separableKummerContinuousNthRootsCharacterEquiv_apply_of_pow_eq
    K n hmu (Units.map τ.toMonoidHom a) (Units.map e.toMonoidHom β) hβτ,
    separableKummerContinuousNthRootsCharacterEquiv_apply_of_pow_eq K n hmu a β hβ]
  apply Units.ext
  simp only [rootQuotient, AlgEquiv.smul_units_def, Units.val_div_eq_div_val, Units.coe_map]
  change semilinearGaloisConjugate τ e
      (separableClosureEquivOfEquiv_algebraMap τ) σ (e (β : SeparableClosure K)) /
        e (β : SeparableClosure K) =
      e (σ (β : SeparableClosure K) / (β : SeparableClosure K))
  rw [semilinearGaloisConjugate_apply, RingEquiv.symm_apply_apply, map_div₀]

/-- If the base automorphism acts by a power on roots of unity, the
constant-coefficient Kummer pairing transforms by the same power. -/
theorem separableAbsoluteKummerContinuousZModCharacterEquiv_naturality_of_pow_roots
    (n : ℕ+) [NeZero ((n : ℕ) : K)]
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (τ : K ≃+* K) (m : ℕ)
    (hτ : ∀ ξ : K, ξ ^ (n : ℕ) = 1 → τ ξ = ξ ^ m)
    (a : Kˣ) (σ : Field.absoluteGaloisGroup K) :
    separableAbsoluteKummerContinuousZModCharacterEquiv K n hmu
        ((Units.map τ.toMonoidHom a : Kˣ) :
          Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range)
        (absoluteGaloisConjugate τ σ) =
      separableAbsoluteKummerContinuousZModCharacterEquiv K n hmu
        (a : Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range) σ ^ m := by
  refine (separableAbsoluteKummerContinuousZModCharacterEquiv_apply K n hmu
    (((Units.map τ.toMonoidHom a : Kˣ) :
      Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range))
    (absoluteGaloisConjugate τ σ)).trans ?_
  rw [separableAbsoluteKummerContinuousZModCharacterEquiv_apply K n hmu
    (a : Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range) σ, ← map_pow]
  apply congrArg (separableDiscreteNthRootsContinuousMulEquivMultiplicativeZMod K n hmu)
  change Gal(AlgebraicClosure K/K) at σ
  change separableKummerContinuousNthRootsCharacterEquiv K n hmu
      ((Units.map τ.toMonoidHom a : Kˣ) :
        Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range)
      (ValuationTheory.Completion.separableClosureAutEquiv K
        (absoluteGaloisConjugate τ σ)) =
    separableKummerContinuousNthRootsCharacterEquiv K n hmu
      (a : Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range)
      (ValuationTheory.Completion.separableClosureAutEquiv K σ) ^ m
  rw [separableClosureAutEquiv_absoluteGaloisConjugate]
  apply Subtype.ext
  rw [separableKummer_naturality K n hmu τ a]
  let u : DiscreteNthRootsSubgroup (SeparableClosure K) (n : ℕ) :=
    separableKummerContinuousNthRootsCharacterEquiv K n hmu
      (a : Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range)
      (ValuationTheory.Completion.separableClosureAutEquiv K σ)
  obtain ⟨ζ, hζ⟩ := nthRootsOfUnityInBase_of_primitiveRoots
    (K := K) (L := SeparableClosure K) n hmu (u : (SeparableClosure K)ˣ) u.property
  have hζpow : ζ ^ (n : ℕ) = 1 := by
    apply Units.map_injective (algebraMap K (SeparableClosure K)).injective
    rw [map_pow, map_one, hζ]
    exact u.property
  change Units.map (separableClosureEquivOfEquiv τ).toMonoidHom
    (u : (SeparableClosure K)ˣ) = (u : (SeparableClosure K)ˣ) ^ m
  rw [← hζ]
  apply Units.ext
  change separableClosureEquivOfEquiv τ
      (algebraMap K (SeparableClosure K) (ζ : K)) =
    (algebraMap K (SeparableClosure K) (ζ : K)) ^ m
  rw [separableClosureEquivOfEquiv_algebraMap,
    hτ (ζ : K) (congrArg Units.val hζpow), map_pow]

/-- If the base automorphism fixes the `n`-th roots of unity, its actual
absolute conjugation preserves the constant-coefficient Kummer pairing. -/
theorem separableAbsoluteKummerContinuousZModCharacterEquiv_naturality_of_fixes_roots
    (n : ℕ+) [NeZero ((n : ℕ) : K)]
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (τ : K ≃+* K)
    (hτ : ∀ ξ : K, ξ ^ (n : ℕ) = 1 → τ ξ = ξ)
    (a : Kˣ) (σ : Field.absoluteGaloisGroup K) :
    separableAbsoluteKummerContinuousZModCharacterEquiv K n hmu
        ((Units.map τ.toMonoidHom a : Kˣ) :
          Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range)
        (absoluteGaloisConjugate τ σ) =
      separableAbsoluteKummerContinuousZModCharacterEquiv K n hmu
        (a : Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range) σ := by
  simpa only [pow_one] using
    separableAbsoluteKummerContinuousZModCharacterEquiv_naturality_of_pow_roots
      K n hmu τ 1 (fun ξ hξ => (hτ ξ hξ).trans (pow_one ξ).symm) a σ

end ClassFieldTower.Martinet.Shafarevich
