/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Normalization.HenselianIntegralSection
public import Nyll.SchemeTheory.RingTheory.JacobsonIntegral
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.Henselian

/-!
# Henselian pairs under integral extension

For a monic polynomial with an approximate simple root, the standard étale
algebra obtained by inverting its derivative has a section over the quotient.
The integral-base section theorem lifts that section and hence the root.
This proves Henselian ascent without a finiteness or locality hypothesis.
-/

@[expose] public section

open Polynomial

universe u

namespace HenselianRing

/-- Integral extension preserves Henselian pairs. The integral algebra need
not be finite as a module, local, or complete. -/
theorem of_isIntegral
    {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    [Algebra.IsIntegral R B] (I : Ideal R) [HenselianRing R I] :
    HenselianRing B (I.map (algebraMap R B)) := by
  let J : Ideal B := I.map (algebraMap R B)
  refine ⟨Ideal.map_le_jacobson_bot_of_isIntegral
    (HenselianRing.jac (R := R) (I := I)), ?_⟩
  intro f hf a₀ ha₀ hd
  let P : StandardEtalePair B := {
    f := f
    monic_f := hf
    g := f.derivative
    cond := ⟨1, 0, 1, by rw [mul_one, mul_zero, add_zero, pow_one]⟩
  }
  have hP : P.HasMap (algebraMap B (B ⧸ J) a₀) := by
    constructor
    · change aeval (algebraMap B (B ⧸ J) a₀) f = 0
      rw [aeval_algebraMap_apply_eq_algebraMap_eval]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr ha₀
    · change IsUnit (aeval (algebraMap B (B ⧸ J) a₀) f.derivative)
      rw [aeval_algebraMap_apply_eq_algebraMap_eval]
      exact hd
  obtain ⟨τ, hτ⟩ := Algebra.Etale.exists_lift_section_of_isIntegral_henselian_base
    I (P.lift (algebraMap B (B ⧸ J) a₀) hP)
  refine ⟨τ P.X, (P.hasMap_X.map τ).1, ?_⟩
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem (I := J) _ _).mp
  simpa only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
    StandardEtalePair.lift_X, Ideal.Quotient.algebraMap_eq]
    using congrArg (fun ψ : P.Ring →ₐ[B] B ⧸ J ↦ ψ P.X) hτ

end HenselianRing
