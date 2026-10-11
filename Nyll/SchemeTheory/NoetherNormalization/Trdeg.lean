/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.NoetherNormalization.GeneratorReduction
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.NoetherNormalization

/-!
# Field Arithmetic, Proposition 6.2.1: Noether normalization

This file connects mathlib's Noether normalization theorem with the
transcendence degree of the quotient field.  This is the first source-producing
step toward the full generator-sensitive statement in Fried--Jarden.
-/

noncomputable section

namespace FieldArithmetic
namespace Chapter06

open Algebra Function

universe u

variable (K A : Type u)
variable [Field K] [CommRing A] [IsDomain A] [Algebra K A]

/-- Passing from a domain to its fraction field does not change transcendence degree. -/
theorem trdeg_fractionRing :
    trdeg K (FractionRing A) = trdeg K A := by
  let : Algebra.IsAlgebraic A (FractionRing A) :=
    IsLocalization.isAlgebraic (FractionRing A) (nonZeroDivisors A)
  have hzero : trdeg A (FractionRing A) = 0 := trdeg_eq_zero
  have h : trdeg K A + trdeg A (FractionRing A) = trdeg K (FractionRing A) :=
    trdeg_add_eq K A (A := FractionRing A)
  rw [hzero, add_zero] at h
  exact h.symm

/--
An injective integral map from a polynomial ring has as many variables as the
transcendence degree of its target.
-/
theorem trdeg_eq_of_injective_isIntegral {r : ℕ}
    (g : MvPolynomial (Fin r) K →ₐ[K] A) (hg : Injective g) (hint : g.IsIntegral) :
    trdeg K A = r := by
  algebraize [g.toRingHom]
  let : FaithfulSMul (MvPolynomial (Fin r) K) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hg
  let : Algebra.IsIntegral (MvPolynomial (Fin r) K) A := ⟨hint⟩
  have hzero : trdeg (MvPolynomial (Fin r) K) A = 0 := trdeg_eq_zero
  have h : trdeg K (MvPolynomial (Fin r) K) +
      trdeg (MvPolynomial (Fin r) K) A = trdeg K A :=
    trdeg_add_eq K (MvPolynomial (Fin r) K) (A := A)
  rw [hzero, add_zero] at h
  simpa using h.symm

/--
A Noether normalization whose number of variables is the transcendence degree
of the quotient field.

The remaining part of Fried--Jarden Proposition 6.2.1 is the refinement relative
to a prescribed finite generating family, including the linear choice over an
infinite field.
-/
theorem exists_normalization_with_trdeg [Algebra.FiniteType K A] :
    Exists fun r : ℕ =>
      Exists fun g : MvPolynomial (Fin r) K →ₐ[K] A =>
        Injective g ∧ g.IsIntegral ∧ trdeg K (FractionRing A) = r := by
  obtain ⟨r, g, hg, hint⟩ := exists_integral_inj_algHom_of_fg K A
  refine ⟨r, g, hg, hint, ?_⟩
  rw [trdeg_fractionRing K A]
  exact trdeg_eq_of_injective_isIntegral K A g hg hint

/--
Element-family form of Noether normalization over an arbitrary field.

The chosen elements are algebraically independent, their number is the
transcendence degree of the quotient field, and the ambient algebra is
integral over the subalgebra they generate.
-/
theorem exists_normalizing_family_with_trdeg [Algebra.FiniteType K A] :
    ∃ r : ℕ, ∃ t : Fin r → A,
      AlgebraicIndependent K t ∧
        Algebra.IsIntegral (Algebra.adjoin K (Set.range t)) A ∧
          trdeg K (FractionRing A) = r := by
  obtain ⟨r, g, hg, hint, htr⟩ := exists_normalization_with_trdeg K A
  let t : Fin r → A := fun i => g (MvPolynomial.X i)
  have hgt : MvPolynomial.aeval t = g := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [t]
  have ht : AlgebraicIndependent K t := by
    rw [algebraicIndependent_iff_injective_aeval, hgt]
    exact hg
  have hS : Algebra.adjoin K (Set.range t) = g.range := by
    rw [← MvPolynomial.aeval_range, hgt]
  have hg_range : (Subalgebra.val g.range).toRingHom.IsIntegral := by
    apply RingHom.IsIntegral.tower_top g.rangeRestrict.toRingHom
    rw [show
      (Subalgebra.val g.range).toRingHom.comp g.rangeRestrict.toRingHom =
        g.toRingHom from
      congrArg AlgHom.toRingHom (AlgHom.val_comp_rangeRestrict g)]
    exact hint
  have hA : Algebra.IsIntegral g.range A := by
    apply algebraMap_isIntegral_iff.mp
    simpa [Subalgebra.algebraMap_eq] using hg_range
  refine ⟨r, t, ht, ?_, htr⟩
  rw [hS]
  exact hA

/--
The quotient presentation form of Noether normalization, retaining the bound
on the number of normalizing variables supplied by the given presentation.
-/
theorem exists_quotient_normalization_with_trdeg {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime] :
    Exists fun r : ℕ =>
      r ≤ n ∧
        Exists fun g : MvPolynomial (Fin r) K →ₐ[K] (MvPolynomial (Fin n) K ⧸ I) =>
          Injective g ∧ g.IsIntegral ∧
            trdeg K (FractionRing (MvPolynomial (Fin n) K ⧸ I)) = r := by
  obtain ⟨r, hr, g, hg, hint⟩ :=
    exists_integral_inj_algHom_of_quotient I Ideal.IsPrime.ne_top'
  refine ⟨r, hr, g, hg, hint, ?_⟩
  rw [trdeg_fractionRing K (MvPolynomial (Fin n) K ⧸ I)]
  exact trdeg_eq_of_injective_isIntegral K (MvPolynomial (Fin n) K ⧸ I) g hg hint

/--
Bridge from the generator-sensitive induction output to a polynomial
normalization map, transcendence degree, and integrality of the ambient
algebra.
-/
theorem linearNormalization_bridges
    {n r : ℕ} (x : Fin n → A) (t : Fin r → A)
    (ht : AlgebraicIndependent K t)
    (hint : ∀ y ∈ Algebra.adjoin K (Set.range x),
      IsIntegral (Algebra.adjoin K (Set.range t)) y)
    (hx : Algebra.adjoin K (Set.range x) = ⊤) :
    ∃ g : MvPolynomial (Fin r) K →ₐ[K]
        Algebra.adjoin K (Set.range t),
      Injective g ∧ Surjective g ∧ g.IsIntegral ∧
        trdeg K (FractionRing A) = r ∧
          Algebra.IsIntegral (Algebra.adjoin K (Set.range t)) A := by
  let S : Subalgebra K A := Algebra.adjoin K (Set.range t)
  change ∀ y ∈ Algebra.adjoin K (Set.range x), IsIntegral S y at hint
  have hSA : Algebra.IsIntegral S A :=
    (Algebra.isIntegral_def).2 fun y => hint y (by
      rw [hx]
      simp)
  let g : MvPolynomial (Fin r) K →ₐ[K] S :=
    (MvPolynomial.aeval t).codRestrict S fun P => by
      change MvPolynomial.aeval t P ∈ Algebra.adjoin K (Set.range t)
      rw [← MvPolynomial.aeval_range]
      exact ⟨P, rfl⟩
  have hginj : Injective g := by
    intro P Q hPQ
    apply algebraicIndependent_iff_injective_aeval.mp ht
    have hPQ' := congrArg Subtype.val hPQ
    change MvPolynomial.aeval t P = MvPolynomial.aeval t Q at hPQ'
    exact hPQ'
  have hgsurj : Surjective g := by
    intro y
    have hy : (y : A) ∈
        (MvPolynomial.aeval t : MvPolynomial (Fin r) K →ₐ[K] A).range := by
      rw [MvPolynomial.aeval_range]
      exact y.property
    obtain ⟨P, hP⟩ := hy
    refine ⟨P, ?_⟩
    apply Subtype.ext
    change MvPolynomial.aeval t P = (y : A)
    exact hP
  have hgint : g.IsIntegral :=
    g.toRingHom.isIntegral_of_surjective hgsurj
  let gA : MvPolynomial (Fin r) K →ₐ[K] A := S.val.comp g
  have hgAinj : Injective gA :=
    Subtype.val_injective.comp hginj
  have hvalint : S.val.toRingHom.IsIntegral := by
    have hmap : (algebraMap S A).IsIntegral :=
      algebraMap_isIntegral_iff.mpr hSA
    simpa [Subalgebra.algebraMap_eq] using hmap
  have hgAint : gA.IsIntegral := by
    change (S.val.toRingHom.comp g.toRingHom).IsIntegral
    exact RingHom.IsIntegral.trans g.toRingHom S.val.toRingHom hgint hvalint
  have htrA : trdeg K A = r :=
    trdeg_eq_of_injective_isIntegral K A gA hgAinj hgAint
  have htrFrac : trdeg K (FractionRing A) = r :=
    (trdeg_fractionRing K A).trans htrA
  exact ⟨g, hginj, hgsurj, hgint, htrFrac, hSA⟩

/--
The infinite-field linear form of Noether normalization relative to a
prescribed finite generating family.

The normalizing elements are `K`-linear combinations of the prescribed
generators, are algebraically independent, have cardinality equal to the
transcendence degree of the quotient field, and make the ambient domain
integral over their generated polynomial subalgebra.
-/
theorem exists_linear_normalization_with_trdeg
    [Infinite K] {n : ℕ} (x : Fin n → A)
    (hx : Algebra.adjoin K (Set.range x) = ⊤) :
    ∃ r : ℕ, r ≤ n ∧
      ∃ t : Fin r → A,
        (∀ i, t i ∈ Submodule.span K (Set.range x)) ∧
          AlgebraicIndependent K t ∧
            Algebra.IsIntegral (Algebra.adjoin K (Set.range t)) A ∧
              trdeg K (FractionRing A) = r := by
  obtain ⟨r, hr, t, htspan, htind, hint⟩ :=
    exists_linearNormalization_span_integral (K := K) x
  obtain ⟨_, _, _, _, htr, hintA⟩ :=
    linearNormalization_bridges K A x t htind hint hx
  exact ⟨r, hr, t, htspan, htind, hintA, htr⟩

end Chapter06
end FieldArithmetic
