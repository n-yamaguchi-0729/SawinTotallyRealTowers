/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.FieldTheory.ContinuousAdditiveHilbert90

/-! # Explicit vanishing of additive H² on a finite Galois extension -/

namespace GaloisCohomology
universe u v
variable {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω]
  [IsGalois K Ω] [FiniteDimensional K Ω]

/-- A trace-one element gives a primitive for every additive two-cocycle. -/
theorem additiveH2_finite
    (z : Gal(Ω/K) → Gal(Ω/K) → Ω)
    (hz : ∀ σ τ υ : Gal(Ω/K),
      z σ (τ * υ) + σ (z τ υ) = z (σ * τ) υ + z σ τ) :
    ∃ b : Gal(Ω/K) → Ω, ∀ σ τ : Gal(Ω/K),
      σ (b τ) - b (σ * τ) + b σ = z σ τ := by
  classical
  obtain ⟨a, ha⟩ := Algebra.trace_surjective K Ω 1
  have htrace : ∑ υ : Gal(Ω/K), υ a = 1 := by
    rw [← trace_eq_sum_automorphisms, ha, map_one]
  have htrace_mul (σ : Gal(Ω/K)) : (∑ υ : Gal(Ω/K), (σ * υ) a) = 1 := by
    rw [Fintype.sum_bijective (fun υ : Gal(Ω/K) => σ * υ)
      (Group.mulLeft_bijective σ) _ (fun υ => υ a) (fun _ => rfl)]
    exact htrace
  let b : Gal(Ω/K) → Ω := fun σ => ∑ υ : Gal(Ω/K), z σ υ * (σ * υ) a
  refine ⟨b, ?_⟩
  intro σ τ
  have hperm : b σ =
      ∑ υ : Gal(Ω/K), z σ (τ * υ) * (σ * (τ * υ)) a :=
    (Fintype.sum_bijective (fun υ : Gal(Ω/K) => τ * υ)
      (Group.mulLeft_bijective τ) _ (fun υ => z σ υ * (σ * υ) a) (fun _ => rfl)).symm
  have hσb : σ (b τ) = ∑ υ : Gal(Ω/K), σ (z τ υ) * ((σ * τ) * υ) a := by
    dsimp only [b]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro υ _
    rw [map_mul]
    rfl
  calc
    σ (b τ) - b (σ * τ) + b σ =
        ∑ υ : Gal(Ω/K),
          (σ (z τ υ) - z (σ * τ) υ + z σ (τ * υ)) * ((σ * τ) * υ) a := by
      rw [hσb, hperm]
      dsimp only [b]
      simp only [mul_assoc, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        add_mul, sub_mul]
    _ = ∑ υ : Gal(Ω/K), z σ τ * ((σ * τ) * υ) a := by
      apply Finset.sum_congr rfl
      intro υ _
      congr 1
      calc
        σ (z τ υ) - z (σ * τ) υ + z σ (τ * υ) =
            (z σ (τ * υ) + σ (z τ υ)) - z (σ * τ) υ := by ring
        _ = (z (σ * τ) υ + z σ τ) - z (σ * τ) υ := by rw [hz]
        _ = z σ τ := by ring
    _ = z σ τ := by rw [← Finset.mul_sum, htrace_mul, mul_one]

end GaloisCohomology
