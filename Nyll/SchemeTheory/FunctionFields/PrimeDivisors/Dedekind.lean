/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.FunctionFields.PrimeDivisors.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-!
# Prime divisors finite on a Dedekind model

This file identifies a prime divisor of a fraction field which is finite on a
Dedekind model with the height-one prime at its center.  In particular, the
center is automatically nonzero and determines the valuation subring.
-/

noncomputable section

namespace FieldArithmetic
namespace Chapter06
namespace FunctionFieldPrimeDivisor

open IsLocalRing

universe u v w

variable {K : Type u} {S : Type v} {F : Type w}
  [Field K] [CommRing S] [IsDedekindDomain S] [Field F]
  [Algebra K S] [Algebra K F] [Algebra S F] [IsScalarTower K S F]
  [IsFractionRing S F]

/--
The center on a Dedekind model cannot be the zero ideal.

Indeed, if it were zero, every nonzero denominator from `S` would become a
unit in the valuation ring.  Since `F` is the fraction field of `S`, this
would put every element of `F` in the valuation ring, contradicting the
properness forced by its DVR structure.
-/
theorem centerAlong_ne_bot
    (v : FunctionFieldPrimeDivisor K F)
    (hfinite : v.FiniteAlong (IsScalarTower.toAlgHom K S F)) :
    v.centerAlong (IsScalarTower.toAlgHom K S F) hfinite ≠ ⊥ := by
  intro hcenter
  apply v.valuationSubring_ne_top
  apply top_unique
  intro x _
  obtain ⟨⟨a, s⟩, hxs⟩ :=
    IsLocalization.surj (nonZeroDivisors S) x
  have hs0 : (s : S) ≠ 0 :=
    (mem_nonZeroDivisors_iff_ne_zero.mp s.property)
  have hs_not_center :
      (s : S) ∉ v.centerAlong (IsScalarTower.toAlgHom K S F) hfinite := by
    rw [hcenter, Ideal.mem_bot]
    exact hs0
  have hs_not_nonunit :
      algebraMap S F (s : S) ∉ v.valuationSubring.nonunits := by
    intro hs
    apply hs_not_center
    exact
      (v.mem_centerAlong_iff_mem_nonunits
        (IsScalarTower.toAlgHom K S F) hfinite (s : S)).2 hs
  have hs_inv :
      (algebraMap S F (s : S))⁻¹ ∈ v.valuationSubring := by
    by_contra hs
    exact hs_not_nonunit
      (v.valuationSubring.mem_nonunits_iff_or.mpr (Or.inr hs))
  have ha : algebraMap S F a ∈ v.valuationSubring :=
    hfinite a
  have hquot :
      algebraMap S F a * (algebraMap S F (s : S))⁻¹ ∈
        v.valuationSubring :=
    mul_mem ha hs_inv
  rw [← hxs] at hquot
  simpa [mul_assoc, hs0] using hquot

/-- The nonzero prime of a Dedekind model obtained as the center of `v`. -/
def centerHeightOneSpectrum
    (v : FunctionFieldPrimeDivisor K F)
    (hfinite : v.FiniteAlong (IsScalarTower.toAlgHom K S F)) :
    IsDedekindDomain.HeightOneSpectrum S :=
  ⟨v.centerAlong (IsScalarTower.toAlgHom K S F) hfinite,
    v.centerAlong_isPrime (IsScalarTower.toAlgHom K S F) hfinite,
    v.centerAlong_ne_bot hfinite⟩

@[simp]
theorem centerHeightOneSpectrum_asIdeal
    (v : FunctionFieldPrimeDivisor K F)
    (hfinite : v.FiniteAlong (IsScalarTower.toAlgHom K S F)) :
    (v.centerHeightOneSpectrum hfinite).asIdeal =
      v.centerAlong (IsScalarTower.toAlgHom K S F) hfinite :=
  rfl

/--
The canonical valuation subring obtained by localizing the Dedekind model at
the center is contained in the valuation subring of `v`.
-/
theorem valuationSubringAtCenter_le
    (v : FunctionFieldPrimeDivisor K F)
    (hfinite : v.FiniteAlong (IsScalarTower.toAlgHom K S F)) :
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F
        (v.centerHeightOneSpectrum hfinite) ≤
      v.valuationSubring := by
  rintro x ⟨a, s, hs, rfl⟩
  have hs_not_nonunit :
      algebraMap S F s ∉ v.valuationSubring.nonunits := by
    intro hs_nonunit
    exact hs
      ((v.mem_centerAlong_iff_mem_nonunits
        (IsScalarTower.toAlgHom K S F) hfinite s).2 hs_nonunit)
  have hs_inv :
      (algebraMap S F s)⁻¹ ∈ v.valuationSubring := by
    by_contra hs_not_mem
    exact hs_not_nonunit
      (v.valuationSubring.mem_nonunits_iff_or.mpr (Or.inr hs_not_mem))
  simpa [div_eq_mul_inv] using
    (mul_mem (hfinite a) hs_inv)

/--
The valuation subring of a prime divisor finite on a Dedekind model is exactly
the canonical localization at its center.
-/
theorem valuationSubringAtCenter_eq
    (v : FunctionFieldPrimeDivisor K F)
    (hfinite : v.FiniteAlong (IsScalarTower.toAlgHom K S F)) :
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F
        (v.centerHeightOneSpectrum hfinite) =
      v.valuationSubring :=
  ValuationSubring.eq_of_le_of_ne_top _
    (v.valuationSubringAtCenter_le hfinite)
    v.valuationSubring_ne_top

/-- Prime-divisor structures are determined by their valuation subrings. -/
theorem ext_valuationSubring
    {v₁ v₂ : FunctionFieldPrimeDivisor K F}
    (h : v₁.valuationSubring = v₂.valuationSubring) :
    v₁ = v₂ := by
  rcases v₁ with ⟨⟨V₁, hDvr₁, hK₁⟩, hfinite₁⟩
  rcases v₂ with ⟨⟨V₂, hDvr₂, hK₂⟩, hfinite₂⟩
  change V₁ = V₂ at h
  subst V₂
  rfl

/--
Two prime divisors finite on the same Dedekind model and having the same
center have the same valuation subring.
-/
theorem valuationSubring_eq_of_centerAlong_eq
    (v₁ v₂ : FunctionFieldPrimeDivisor K F)
    (hfinite₁ : v₁.FiniteAlong (IsScalarTower.toAlgHom K S F))
    (hfinite₂ : v₂.FiniteAlong (IsScalarTower.toAlgHom K S F))
    (hcenter :
      v₁.centerAlong (IsScalarTower.toAlgHom K S F) hfinite₁ =
        v₂.centerAlong (IsScalarTower.toAlgHom K S F) hfinite₂) :
    v₁.valuationSubring = v₂.valuationSubring := by
  have hheight :
      v₁.centerHeightOneSpectrum hfinite₁ =
        v₂.centerHeightOneSpectrum hfinite₂ := by
    apply IsDedekindDomain.HeightOneSpectrum.ext
    exact hcenter
  calc
    v₁.valuationSubring =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F
          (v₁.centerHeightOneSpectrum hfinite₁) :=
      (v₁.valuationSubringAtCenter_eq hfinite₁).symm
    _ =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F
          (v₂.centerHeightOneSpectrum hfinite₂) := by
      rw [hheight]
    _ = v₂.valuationSubring :=
      v₂.valuationSubringAtCenter_eq hfinite₂

/--
On a Dedekind model, a finite prime divisor is uniquely determined by its
center.
-/
theorem eq_of_centerAlong_eq
    (v₁ v₂ : FunctionFieldPrimeDivisor K F)
    (hfinite₁ : v₁.FiniteAlong (IsScalarTower.toAlgHom K S F))
    (hfinite₂ : v₂.FiniteAlong (IsScalarTower.toAlgHom K S F))
    (hcenter :
      v₁.centerAlong (IsScalarTower.toAlgHom K S F) hfinite₁ =
        v₂.centerAlong (IsScalarTower.toAlgHom K S F) hfinite₂) :
    v₁ = v₂ :=
  ext_valuationSubring
    (v₁.valuationSubring_eq_of_centerAlong_eq v₂ hfinite₁ hfinite₂ hcenter)

end FunctionFieldPrimeDivisor
end Chapter06
end FieldArithmetic
