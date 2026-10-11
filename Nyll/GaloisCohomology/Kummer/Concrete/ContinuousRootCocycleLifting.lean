/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Kummer.Concrete.ContinuousHilbert90
import Nyll.GaloisCohomology.Kummer.Concrete.RootCharacters
import Nyll.GaloisCohomology.Topology.AlgebraicGaloisOrbits
import Mathlib.FieldTheory.IsSepClosed

/-!
# Lifting continuous cocycles through power maps

Over a separably closed Galois extension, Hilbert 90 writes a continuous
multiplicative cocycle as a coboundary. Taking a root of that actual coboundary
parameter lifts the cocycle, preserving local constancy and the root-of-unity
coefficient bound.
-/

namespace KummerTheory
open groupCohomology
universe u v
variable {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω]
  [IsGalois K Ω]

/-- A root quotient is locally constant in the Krull topology. -/
theorem isLocallyConstant_rootQuotient (γ : Ωˣ) :
    IsLocallyConstant (rootQuotient (K := K) γ) := by
  exact (GaloisCohomology.isLocallyConstant_galois_units (K := K) γ).comp
    (fun z : Ωˣ => z / γ)

variable [IsSepClosed Ω]

/-- Every continuous multiplicative cocycle has a continuous root of an
exponent invertible in the separably closed coefficient field. -/
theorem exists_mulCocycle_root_of_isLocallyConstant
    (c : Gal(Ω/K) → Ωˣ) (hc : IsMulCocycle₁ c)
    (hlc : IsLocallyConstant c) (m : ℕ) [NeZero (m : Ω)] :
    ∃ d : Gal(Ω/K) → Ωˣ, IsMulCocycle₁ d ∧ IsLocallyConstant d ∧
      ∀ σ : Gal(Ω/K), d σ ^ m = c σ := by
  obtain ⟨β, hβ⟩ := noetherHilbert90_of_isLocallyConstant c hc hlc
  obtain ⟨γ, hγ⟩ := IsSepClosed.exists_pow_nat_eq (β : Ω) m
  have hm : m ≠ 0 := by
    intro h
    exact (NeZero.ne (m : Ω)) (by rw [h, Nat.cast_zero])
  have hγ0 : γ ≠ 0 := by
    intro h
    rw [h, zero_pow hm] at hγ
    exact Units.ne_zero β hγ.symm
  let u : Ωˣ := Units.mk0 γ hγ0
  have hu : u ^ m = β := Units.ext hγ
  refine ⟨rootQuotient (K := K) u, isMulCocycle₁_rootQuotient u,
    isLocallyConstant_rootQuotient u, ?_⟩
  intro σ
  change (σ • u / u) ^ m = c σ
  have hpow : (σ • u) ^ m = σ • (u ^ m) :=
    (map_pow (MulDistribMulAction.toMonoidHom Ωˣ σ) u m).symm
  rw [div_pow, hpow, hu]
  exact hβ σ

/-- A cocycle in n-th roots lifts to a cocycle in (n*m)-th roots, compatibly
with the m-th-power reduction. -/
theorem exists_mulCocycle_rootsOfUnity_lift
    (c : Gal(Ω/K) → Ωˣ) (hc : IsMulCocycle₁ c)
    (hlc : IsLocallyConstant c) (n m : ℕ) [NeZero (m : Ω)]
    (hcn : ∀ σ : Gal(Ω/K), c σ ^ n = 1) :
    ∃ d : Gal(Ω/K) → Ωˣ, IsMulCocycle₁ d ∧ IsLocallyConstant d ∧
      (∀ σ : Gal(Ω/K), d σ ^ (n * m) = 1) ∧
      ∀ σ : Gal(Ω/K), d σ ^ m = c σ := by
  obtain ⟨d, hd, hlcd, hpow⟩ :=
    exists_mulCocycle_root_of_isLocallyConstant c hc hlc m
  refine ⟨d, hd, hlcd, ?_, hpow⟩
  intro σ
  rw [Nat.mul_comm n m, pow_mul, hpow, hcn]

end KummerTheory
