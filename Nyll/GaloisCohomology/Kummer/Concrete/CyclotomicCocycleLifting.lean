/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Kummer.Concrete.PrimitiveRootCoordinates
import Nyll.GaloisCohomology.Kummer.Concrete.ContinuousRootCocycleLifting
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Lifting finite cyclotomic cocycles

Hilbert 90 and compatible primitive-root coordinates lift actual locally
constant cocycles from modulo p to modulo every positive power of p.
-/

namespace KummerTheory
open groupCohomology
universe u v
variable {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω]
  [IsGalois K Ω] [IsSepClosed Ω]

/-- Every locally constant mod-p cyclotomic cocycle lifts through reduction. -/
theorem exists_cyclotomic_cocycle_lift
    (p : ℕ) [Fact p.Prime] [NeZero (p : Ω)]
    (k : ℕ) (c : Gal(Ω/K) → ZMod (p ^ 1))
    (hc : ∀ σ τ : Gal(Ω/K), c (σ * τ) = c σ +
      ((cyclotomicCharacter Ω p σ.toRingEquiv : PadicInt p).toZModPow 1) * c τ)
    (hlc : IsLocallyConstant c) :
    ∃ d : Gal(Ω/K) → ZMod (p ^ (k + 1)),
      IsLocallyConstant d ∧
      (∀ σ τ : Gal(Ω/K), d (σ * τ) = d σ +
        ((cyclotomicCharacter Ω p σ.toRingEquiv : PadicInt p).toZModPow (k + 1)) * d τ) ∧
      ∀ σ : Gal(Ω/K),
        ZMod.castHom (pow_dvd_pow p (by omega : 1 ≤ k + 1))
          (ZMod (p ^ 1)) (d σ) = c σ := by
  classical
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (p ^ (k + 1))
  let z : Ωˣ := hζ.isUnit (NeZero.ne (p ^ (k + 1))) |>.unit'
  have hz : IsPrimitiveRoot z (p ^ (k + 1)) := hζ.isUnit_unit' (NeZero.ne _)
  have hN : p ^ (k + 1) = p ^ 1 * p ^ k := by
    rw [pow_one, pow_succ, mul_comm]
  have hz₁ : IsPrimitiveRoot (z ^ (p ^ k)) (p ^ 1) :=
    hz.pow (Nat.pos_of_neZero _) (hN.trans (Nat.mul_comm _ _))
  let C : Gal(Ω/K) → Ωˣ := fun σ => primitiveRootCoordinate hz₁ (c σ)
  have hC : IsMulCocycle₁ C := by
    intro σ τ
    change primitiveRootCoordinate hz₁ (c (σ * τ)) =
      σ • primitiveRootCoordinate hz₁ (c τ) * primitiveRootCoordinate hz₁ (c σ)
    rw [hc, primitiveRootCoordinate_add]
    have hact := primitiveRootCoordinate_cyclotomic p 1 hz₁ σ.toRingEquiv (c τ)
    change σ • primitiveRootCoordinate hz₁ (c τ) =
      primitiveRootCoordinate hz₁
        ((cyclotomicCharacter Ω p σ.toRingEquiv : PadicInt p).toZModPow 1 * c τ) at hact
    rw [hact, mul_comm]
  have hClc : IsLocallyConstant C := hlc.comp (primitiveRootCoordinate hz₁)
  have hCpow (σ : Gal(Ω/K)) : C σ ^ (p ^ 1) = 1 :=
    primitiveRootCoordinate_pow_eq_one hz₁ (c σ)
  have : NeZero ((p ^ k : ℕ) : Ω) :=
    ⟨by rw [Nat.cast_pow]; exact pow_ne_zero k (NeZero.ne (p : Ω))⟩
  obtain ⟨D, hD, hDlc, hDpow, hDm⟩ :=
    exists_mulCocycle_rootsOfUnity_lift C hC hClc (p ^ 1) (p ^ k) hCpow
  have hDmem (σ : Gal(Ω/K)) : D σ ^ (p ^ (k + 1)) = 1 := by
    rw [hN]
    exact hDpow σ
  choose d hd using fun σ => primitiveRootCoordinate_surjective_roots hz (D σ) (hDmem σ)
  have hdlc : IsLocallyConstant d := by
    rw [IsLocallyConstant.iff_eventually_eq] at hDlc ⊢
    intro σ
    filter_upwards [hDlc σ] with τ hτ
    apply primitiveRootCoordinate_injective hz
    rw [hd, hd]
    exact hτ
  refine ⟨d, hdlc, ?_, ?_⟩
  · intro σ τ
    apply primitiveRootCoordinate_injective hz
    rw [primitiveRootCoordinate_add, hd, hd]
    rw [← primitiveRootCoordinate_cyclotomic p (k + 1) hz σ.toRingEquiv (d τ), hd]
    exact (hD σ τ).trans (mul_comm _ _)
  · intro σ
    apply primitiveRootCoordinate_injective hz₁
    have hred := primitiveRootCoordinate_reduction (p ^ (k + 1)) (p ^ 1)
      (p ^ k) hN hz (d σ)
    rw [← hred, hd]
    exact hDm σ

end KummerTheory
