/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Ideal.Defs
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Defs
import Mathlib.Tactic.Choose


/-!
# Extending finite relations from a principal open

Suppose a finite relation ideal vanishes under an algebra map after inverting
one element. Multiplying its finitely many generators by suitable powers of
that element gives a smaller finitely generated ideal in the actual kernel.
The two ideals have equal extensions to the localization.

For a finite, finitely presented source algebra, its quotient by the new
ideal is still finite and finitely presented and has an actual map to the
target. Thus the relation correction preserves both the prescribed local
relations and the target map. No Noetherian or integral-target hypothesis is
needed for this step.

This is a ring-local ingredient for finite algebra approximation as used in
Stacks, Tags 0817 and 09YZ. It does not assert the existence of compatible
global algebra models or an extension of every algebra on an open subscheme.
-/

noncomputable section

universe u v w

namespace AlgHom

/-- Finitely many relations which vanish after localization can be replaced
by relations in the actual kernel, without changing their localized ideal.
The resulting finite-FP quotient carries the original map to the target. -/
theorem exists_finitePresentation_quotient_eq_map_away
    (R : Type u) [CommRing R] (A : Type v) [CommRing A] [Algebra R A]
    [Module.Finite R A] [Algebra.FinitePresentation R A]
    (B : Type w) [CommRing B] [Algebra R B]
    (φ : A →ₐ[R] B) (r : A) (I : Ideal A) (hI : I.FG)
    (hzero : ∀ a : A, a ∈ I →
      algebraMap B (Localization.Away (φ r)) (φ a) = 0) :
    ∃ J : Ideal A, J.FG ∧ J ≤ I ∧
      Module.Finite R (A ⧸ J) ∧ Algebra.FinitePresentation R (A ⧸ J) ∧
      ∃ ψ : A ⧸ J →ₐ[R] B,
        ψ.comp (Ideal.Quotient.mkₐ R J) = φ ∧
        J.map (algebraMap A (Localization.Away r)) =
          I.map (algebraMap A (Localization.Away r)) := by
  classical
  obtain ⟨s, hs⟩ := hI
  have hsI (a : s) : (a : A) ∈ I := by
    rw [← hs]
    exact Ideal.subset_span a.property
  have hpow (a : s) : ∃ n : ℕ, φ (r ^ n * (a : A)) = 0 := by
    obtain ⟨m, hm⟩ :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers (φ r))
        (Localization.Away (φ r)) (φ a)).mp (hzero a (hsI a))
    obtain ⟨n, hn⟩ := m.property
    refine ⟨n, ?_⟩
    rw [map_mul, map_pow]
    rw [← hn] at hm
    exact hm
  choose n hn using hpow
  let t : s → A := fun a => r ^ n a * (a : A)
  let J : Ideal A := Ideal.span (Set.range t)
  have hJfg : J.FG := Submodule.fg_span (Set.finite_range t)
  have hJI : J ≤ I := by
    apply Ideal.span_le.mpr
    rintro _ ⟨a, rfl⟩
    exact I.mul_mem_left (r ^ n a) (hsI a)
  have hJker : J ≤ RingHom.ker φ.toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨a, rfl⟩
    change φ (r ^ n a * (a : A)) = 0
    exact hn a
  have hmap : J.map (algebraMap A (Localization.Away r)) =
      I.map (algebraMap A (Localization.Away r)) := by
    apply le_antisymm (Ideal.map_mono hJI)
    apply Ideal.map_le_iff_le_comap.mpr
    rw [← hs]
    apply Ideal.span_le.mpr
    intro a ha
    change algebraMap A (Localization.Away r) a ∈
      J.map (algebraMap A (Localization.Away r))
    have ht : t ⟨a, ha⟩ ∈ J := Ideal.subset_span ⟨⟨a, ha⟩, rfl⟩
    have hmem := Ideal.mem_map_of_mem (algebraMap A (Localization.Away r)) ht
    have hu : IsUnit (algebraMap A (Localization.Away r) r ^ n ⟨a, ha⟩) :=
      IsLocalization.Away.algebraMap_pow_isUnit r (n ⟨a, ha⟩)
    apply (Ideal.unit_mul_mem_iff_mem
      (J.map (algebraMap A (Localization.Away r))) hu).mp
    simpa only [t, map_mul, map_pow] using hmem
  have hz (a : A) (ha : a ∈ J) : φ a = 0 := hJker ha
  let q : A →ₐ[R] A ⧸ J := Ideal.Quotient.mkₐ R J
  let ψ : A ⧸ J →ₐ[R] B := Ideal.Quotient.liftₐ J φ hz
  have hq : Function.Surjective q := Ideal.Quotient.mkₐ_surjective R J
  have hfinite : Module.Finite R (A ⧸ J) :=
    Module.Finite.of_surjective q.toLinearMap hq
  have hfp : Algebra.FinitePresentation R (A ⧸ J) :=
    Algebra.FinitePresentation.quotient hJfg
  exact ⟨J, hJfg, hJI, hfinite, hfp, ψ, Ideal.Quotient.liftₐ_comp J φ hz, hmap⟩

end AlgHom
