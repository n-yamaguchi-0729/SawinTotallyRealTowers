/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.LinearAlgebra.SModEq.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# Henselian pairs defined by nil ideals

For a polynomial with an approximate simple root modulo a nil ideal, its
initial error generates a nilpotent principal ideal. The adic filtration for
this smaller ideal terminates, so completeness supplies a root whose correction
lies in the original ideal. The original nil ideal need not be nilpotent.
-/

@[expose] public section

universe u

namespace HenselianRing

private theorem isAdicComplete_of_pow_eq_bot
    {R : Type u} [CommRing R] (J : Ideal R) (n : ℕ) (hn : J ^ n = ⊥) :
    IsAdicComplete J R where
  haus' x hx := by
    simpa only [Ideal.smul_eq_mul, Ideal.mul_top, hn, SModEq.bot] using hx n
  prec' f hf := by
    refine ⟨f n, fun m ↦ ?_⟩
    obtain hmn | hnm := le_total m n
    · exact hf hmn
    · have h : f n = f m := by
        simpa only [Ideal.smul_eq_mul, Ideal.mul_top, hn, SModEq.bot] using hf hnm
      rw [h]

/-- Every nil ideal defines a Henselian pair. No uniform nilpotence exponent
for the ideal is required. -/
theorem of_le_nilradical
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I ≤ nilradical R) :
    HenselianRing R I := by
  have hJac : I ≤ Ideal.jacobson ⊥ := hI.trans Ideal.radical_le_jacobson
  refine ⟨hJac, ?_⟩
  intro f hf a₀ ha₀ hd
  let J : Ideal R := Ideal.span {f.eval a₀}
  have hJI : J ≤ I := by
    dsimp only [J]
    exact Ideal.span_le.mpr (by simpa using ha₀)
  obtain ⟨n, hn⟩ := mem_nilradical.mp (hI ha₀)
  have hJn : J ^ n = ⊥ := by
    dsimp only [J]
    rw [Ideal.span_singleton_pow, hn, Ideal.span_singleton_zero]
  let : IsAdicComplete J R := isAdicComplete_of_pow_eq_bot J n hJn
  let : IsLocalHom (Ideal.Quotient.mk I) := isLocalHom_of_le_jacobson_bot I hJac
  have hderiv : IsUnit (f.derivative.eval a₀) :=
    IsUnit.of_map (Ideal.Quotient.mk I) (f.derivative.eval a₀) hd
  obtain ⟨a, ha, hamem⟩ := HenselianRing.is_henselian (I := J) f hf a₀
    (Ideal.subset_span (Set.mem_singleton_iff.mpr rfl))
    (hderiv.map (Ideal.Quotient.mk J))
  exact ⟨a, ha, hJI hamem⟩

end HenselianRing
