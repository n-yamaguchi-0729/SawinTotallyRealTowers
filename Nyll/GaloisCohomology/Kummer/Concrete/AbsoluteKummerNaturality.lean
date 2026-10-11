/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Kummer.Concrete.AbsoluteConjugation
import Nyll.GaloisCohomology.Kummer.Concrete.AbsoluteKummerEvaluation
import Nyll.GaloisCohomology.Kummer.Concrete.LastPrimePowerRoot

/-!
# Naturality of absolute Kummer characters

The Kummer character of a transformed unit, evaluated at the conjugated
Galois automorphism, is the transformed original character value. When the
base automorphism fixes the roots of unity, the coefficient value is unchanged.
-/

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open KummerTheory

variable (K : Type*) [Field K] [CharZero K]

/-- Absolute Kummer characters commute pointwise with the chosen extension
of a base-field automorphism and its conjugation on the Galois group. -/
theorem absoluteKummerContinuousNthRootsCharacterEquiv_naturality
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (τ : K ≃+* K) (a : Kˣ) (σ : Gal(AlgebraicClosure K/K)) :
    ((absoluteKummerContinuousNthRootsCharacterEquiv K n hmu
        ((Units.map τ.toMonoidHom a : Kˣ) :
          Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range)
        (absoluteGaloisConjugate τ σ) :
      DiscreteNthRootsSubgroup (AlgebraicClosure K) (n : ℕ)) :
        (AlgebraicClosure K)ˣ) =
      Units.map (IsAlgClosure.equivOfEquiv (AlgebraicClosure K)
        (AlgebraicClosure K) τ).toMonoidHom
        ((absoluteKummerContinuousNthRootsCharacterEquiv K n hmu
            (a : Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range) σ :
          DiscreteNthRootsSubgroup (AlgebraicClosure K) (n : ℕ)) :
            (AlgebraicClosure K)ˣ) := by
  obtain ⟨β, hβ⟩ : ∃ β : (AlgebraicClosure K)ˣ,
      β ^ (n : ℕ) =
        Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom a := by
    apply (mem_finiteKummerRadicalSubgroup_iff
      (K := K) (L := AlgebraicClosure K) n).mp
    rw [finiteKummerRadicalSubgroup_algebraicClosure_eq_top K n]
    exact Subgroup.mem_top a
  let e : AlgebraicClosure K ≃+* AlgebraicClosure K :=
    IsAlgClosure.equivOfEquiv (AlgebraicClosure K) (AlgebraicClosure K) τ
  have hβτ : (Units.map e.toMonoidHom β) ^ (n : ℕ) =
      Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom
        (Units.map τ.toMonoidHom a) := by
    rw [← map_pow, hβ]
    apply Units.ext
    exact IsAlgClosure.equivOfEquiv_algebraMap
      (AlgebraicClosure K) (AlgebraicClosure K) τ (a : K)
  exact (absoluteKummerContinuousNthRootsCharacterEquiv_apply_of_pow_eq
      K n hmu (Units.map τ.toMonoidHom a) (Units.map e.toMonoidHom β) hβτ
      (absoluteGaloisConjugate τ σ)).trans
    ((rootQuotient_absoluteGaloisConjugate τ β σ).trans
      (congrArg (Units.map e.toMonoidHom)
        (absoluteKummerContinuousNthRootsCharacterEquiv_apply_of_pow_eq
          K n hmu a β hβ σ).symm))

/-- When the base-field automorphism fixes the `n`-th roots of unity,
Kummer naturality has constant coefficients. -/
theorem absoluteKummerContinuousNthRootsCharacterEquiv_naturality_of_fixes_roots
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (τ : K ≃+* K)
    (hτ : ∀ ζ : K, ζ ^ (n : ℕ) = 1 → τ ζ = ζ)
    (a : Kˣ) (σ : Gal(AlgebraicClosure K/K)) :
    absoluteKummerContinuousNthRootsCharacterEquiv K n hmu
        ((Units.map τ.toMonoidHom a : Kˣ) :
          Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range)
        (absoluteGaloisConjugate τ σ) =
      absoluteKummerContinuousNthRootsCharacterEquiv K n hmu
        (a : Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range) σ := by
  apply Subtype.ext
  rw [absoluteKummerContinuousNthRootsCharacterEquiv_naturality K n hmu τ a σ]
  let u : DiscreteNthRootsSubgroup (AlgebraicClosure K) (n : ℕ) :=
    absoluteKummerContinuousNthRootsCharacterEquiv K n hmu
      (a : Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range) σ
  have hu : (u : (AlgebraicClosure K)ˣ) ^ (n : ℕ) = 1 := u.property
  obtain ⟨ζ, hζ⟩ := nthRootsOfUnityInBase_of_primitiveRoots
    (K := K) (L := AlgebraicClosure K) n hmu (u : (AlgebraicClosure K)ˣ) hu
  have hζpow : ζ ^ (n : ℕ) = 1 := by
    apply Units.map_injective (algebraMap K (AlgebraicClosure K)).injective
    rw [map_pow, map_one, hζ, hu]
  have hζfield : (ζ : K) ^ (n : ℕ) = 1 := congrArg Units.val hζpow
  change Units.map (IsAlgClosure.equivOfEquiv (AlgebraicClosure K)
      (AlgebraicClosure K) τ).toMonoidHom (u : (AlgebraicClosure K)ˣ) =
    (u : (AlgebraicClosure K)ˣ)
  rw [← hζ]
  apply Units.ext
  change IsAlgClosure.equivOfEquiv (AlgebraicClosure K) (AlgebraicClosure K) τ
      (algebraMap K (AlgebraicClosure K) (ζ : K)) =
    algebraMap K (AlgebraicClosure K) (ζ : K)
  rw [IsAlgClosure.equivOfEquiv_algebraMap, hτ (ζ : K) hζfield]

/-- An eigenunit with primitive prime-order multiplier yields a continuous
character moved by conjugation when the prime-power roots form a finite set
fixed by the base automorphism. The detecting exponent and character are
constructed from the last available root level. -/
theorem exists_moved_absoluteKummerCharacter_of_finite_primePowerRoots
    {p : ℕ} (hp : p.Prime)
    (hfinite : Set.Finite {ξ : K | ∃ m : ℕ, ξ ^ (p ^ m) = 1})
    (ζ : Kˣ) (hζ : IsPrimitiveRoot ζ p)
    (τ : K ≃+* K)
    (hτ : ∀ ξ : K, (∃ m : ℕ, ξ ^ (p ^ m) = 1) → τ ξ = ξ)
    (α : Kˣ) (hα : Units.map τ.toMonoidHom α = ζ * α) :
    ∃ s : ℕ, 1 ≤ s ∧ (primitiveRoots (p ^ s) K).Nonempty ∧
      (∀ m : ℕ, (primitiveRoots (p ^ m) K).Nonempty → m ≤ s) ∧
      ∃ χ : Field.absoluteGaloisGroup K →ₜ*
          DiscreteNthRootsSubgroup (AlgebraicClosure K) (p ^ s),
        ∃ σ : Gal(AlgebraicClosure K/K),
          χ (absoluteGaloisConjugate τ σ) ≠ χ σ := by
  obtain ⟨s, hs, hmu, hmax, _, hζclass⟩ :=
    exists_last_primePowerRoot_nontrivial_class hp hfinite hζ
  let n : ℕ+ := ⟨p ^ s, pow_pos hp.pos s⟩
  let κ := absoluteKummerContinuousNthRootsCharacterEquiv K n hmu
  have hαclass :
      ((Units.map τ.toMonoidHom α : Kˣ) :
        Kˣ ⧸ (powMonoidHom (p ^ s) : Kˣ →* Kˣ).range) ≠
      (α : Kˣ ⧸ (powMonoidHom (p ^ s) : Kˣ →* Kˣ).range) := by
    intro heq
    apply hζclass
    rw [hα] at heq
    apply (QuotientGroup.eq_one_iff ζ).mpr
    have hmem := QuotientGroup.eq_iff_div_mem.mp heq
    rw [mul_div_cancel_right] at hmem
    exact hmem
  have hcharacters :
      κ ((Units.map τ.toMonoidHom α : Kˣ) :
        Kˣ ⧸ (powMonoidHom (p ^ s) : Kˣ →* Kˣ).range) ≠
      κ (α : Kˣ ⧸ (powMonoidHom (p ^ s) : Kˣ →* Kˣ).range) :=
    κ.injective.ne hαclass
  obtain ⟨σ, hσ⟩ := DFunLike.exists_ne hcharacters
  refine ⟨s, hs, hmu, hmax, κ ((Units.map τ.toMonoidHom α : Kˣ) :
    Kˣ ⧸ (powMonoidHom (p ^ s) : Kˣ →* Kˣ).range), σ, ?_⟩
  have hnatural :=
    absoluteKummerContinuousNthRootsCharacterEquiv_naturality_of_fixes_roots
      K n hmu τ (fun ξ hξ => hτ ξ ⟨s, hξ⟩) α σ
  intro hfixed
  exact hσ (hfixed.symm.trans hnatural)

end ClassFieldTower.Martinet.Shafarevich
