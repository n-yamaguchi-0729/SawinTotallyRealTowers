/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Kummer.Concrete.AbsoluteKummerNaturality
import Nyll.GaloisCohomology.Kummer.Concrete.AbsoluteRootPowerAction
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Actual power witnesses from invariant Kummer characters

Kummer naturality and invariance identify the transformed unit class with
the power prescribed by the action on roots. Injectivity of the Kummer
equivalence gives a witness in the original field unit group. This direction
does not require the power exponent to be coprime to the coefficient modulus.
-/

namespace ClassFieldTower.Martinet.Shafarevich

open KummerTheory

variable (K : Type*) [Field K] [CharZero K]

/-- An invariant Kummer character and the actual power action on roots
produce a power witness in the base field. No coprimality is needed. -/
theorem exists_power_witness_of_invariant_absoluteKummerCharacter
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (τ : K ≃+* K) (u : Kˣ) (a : ℕ)
    (hτ : ∀ ζ : K, ζ ^ (n : ℕ) = 1 → τ ζ = ζ ^ a)
    (hinv : ∀ σ : Gal(AlgebraicClosure K/K),
      absoluteKummerContinuousNthRootsCharacterEquiv K n hmu
          (u : Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range)
          (absoluteGaloisConjugate τ σ) =
        absoluteKummerContinuousNthRootsCharacterEquiv K n hmu
          (u : Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range) σ) :
    ∃ y : Kˣ, Units.map τ.toMonoidHom u / u ^ a = y ^ (n : ℕ) := by
  let Q := Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range
  let κ := absoluteKummerContinuousNthRootsCharacterEquiv K n hmu
  let c : Field.absoluteGaloisGroup K →ₜ*
      DiscreteNthRootsSubgroup (AlgebraicClosure K) (n : ℕ) := κ (u : Q)
  have hcharacters : κ ((Units.map τ.toMonoidHom u : Kˣ) : Q) = c ^ a := by
    apply ContinuousMonoidHom.ext
    intro ρ
    obtain ⟨σ, hσ⟩ := (absoluteGaloisConjugateEquiv τ).surjective ρ
    rw [absoluteGaloisConjugateEquiv_apply] at hσ
    have hcσ : c (absoluteGaloisConjugate τ σ) = c σ := hinv σ
    have hnatural :
        κ ((Units.map τ.toMonoidHom u : Kˣ) : Q) (absoluteGaloisConjugate τ σ) =
          (c σ) ^ a := by
      apply Subtype.ext
      exact (absoluteKummerContinuousNthRootsCharacterEquiv_naturality K n hmu τ u σ).trans
        (absoluteGaloisLift_nthRoot_eq_pow K n hmu τ a hτ (c σ))
    calc
      κ ((Units.map τ.toMonoidHom u : Kˣ) : Q) ρ =
          κ ((Units.map τ.toMonoidHom u : Kˣ) : Q) (absoluteGaloisConjugate τ σ) :=
        congrArg (κ ((Units.map τ.toMonoidHom u : Kˣ) : Q)) hσ.symm
      _ = (c σ) ^ a := hnatural
      _ = (c (absoluteGaloisConjugate τ σ)) ^ a :=
        congrArg (fun z : DiscreteNthRootsSubgroup (AlgebraicClosure K) (n : ℕ) => z ^ a)
          hcσ.symm
      _ = (c ^ a) (absoluteGaloisConjugate τ σ) :=
        (ContinuousMonoidHom.pow_apply c a (absoluteGaloisConjugate τ σ)).symm
      _ = (c ^ a) ρ := congrArg (c ^ a) hσ
  have hclass : ((Units.map τ.toMonoidHom u : Kˣ) : Q) = (u : Q) ^ a := by
    apply κ.injective
    rw [map_pow]
    exact hcharacters
  rw [← QuotientGroup.mk_pow] at hclass
  obtain ⟨y, hy⟩ := QuotientGroup.eq_iff_div_mem.mp hclass
  exact ⟨y, hy.symm⟩

end ClassFieldTower.Martinet.Shafarevich
