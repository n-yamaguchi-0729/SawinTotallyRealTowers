/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.AbhyankarLemma.Kummer.RadicalGeneration
import Nyll.ValuedFieldTheory.LocalField.Unramified.HenselianAlgebraicExtension

/-!
# Norm control of value cosets

For a finite extension of a Henselian valued field, the norm formula says
that the extension degree times the value of an element is
the value of its norm.  Thus the order of every value-group coset divides the
field degree, as required by the tame radical-generation argument.
-/

noncomputable section

namespace AlgebraicNumberTheory
namespace Valuations

section NormValue

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [FiniteDimensional K L]

local instance exponentialValueGroupQuotientAddCommGroupNorm
    (v : LubinTate.Valuations.ExponentialValuation K)
    (w : LubinTate.Valuations.ExponentialValuation L) :
    AddCommGroup (ExponentialValueGroupQuotient v w) := by
  unfold ExponentialValueGroupQuotient
  infer_instance

/-- Additive exponential form of the finite Henselian norm formula. -/
theorem exponentialValuation_norm_eq_finrank_nsmul
    (v : LubinTate.Valuations.ExponentialValuation K)
    (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v).valuation)
    (x : L) (hx : x ≠ 0) :
    v (Algebra.norm K x) = Module.finrank K L • w x := by
  let av := exponentialAssociatedAbsoluteValue v
  let aw := exponentialAssociatedAbsoluteValue w
  have hav : LubinTate.Valuations.AssociatedAbsoluteValue v (Real.exp 1) av :=
    exponentialAssociatedAbsoluteValue_associated v
  have haw : LubinTate.Valuations.AssociatedAbsoluteValue w (Real.exp 1) aw :=
    exponentialAssociatedAbsoluteValue_associated w
  have havNonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue av :=
    associatedAbsoluteValue_nonarchimedean v (Real.exp 1) av hav
  have hawNonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue aw :=
    associatedAbsoluteValue_nonarchimedean w (Real.exp 1) aw haw
  have hV :
      LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v =
        absoluteValueValuationSubring av havNonarch :=
    associatedAbsoluteValue_valuationSubring_eq
      v (Real.exp 1) av havNonarch hav
  have hhensAv : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (absoluteValueValuationSubring av havNonarch).valuation := by
    rw [← hV]
    exact hhens
  obtain ⟨_hextNonarch, _hextBase, hnorm, hunique⟩ :=
    normFormula_finite_extension_norm_formula
      (K := K) (L := L) av havNonarch hhensAv
  have hawExt : ∀ a : K, aw (algebraMap K L a) = av a :=
    associatedAbsoluteValue_extends
      v w hExt (Real.exp 1) av aw hav haw
  have hawEq := hunique aw hawNonarch hawExt
  have hformula :
      aw x = av (Algebra.norm K x) ^
        (1 / (Module.finrank K L : ℝ)) := by
    rw [hawEq]
    exact hnorm x
  have hnorm0 : Algebra.norm K x ≠ 0 :=
    (Algebra.norm_ne_zero_iff).2 hx
  obtain ⟨s, hws, haws⟩ := haw.2 x hx
  obtain ⟨r, hvr, havr⟩ := hav.2 (Algebra.norm K x) hnorm0
  have hnpos : 0 < Module.finrank K L := Module.finrank_pos
  have hnreal : (Module.finrank K L : ℝ) ≠ 0 := by positivity
  have hexp :
      Real.exp (-s) =
        Real.exp ((-r) * (1 / (Module.finrank K L : ℝ))) := by
    have hf := hformula
    rw [haws, havr] at hf
    change Real.rpow (Real.exp 1) (-s) =
      Real.rpow (Real.rpow (Real.exp 1) (-r))
        (1 / (Module.finrank K L : ℝ)) at hf
    have hmul := Real.rpow_mul (x := Real.exp 1) (Real.exp_pos 1).le
      (-r) (1 / (Module.finrank K L : ℝ))
    change Real.rpow (Real.exp 1)
        ((-r) * (1 / (Module.finrank K L : ℝ))) =
      Real.rpow (Real.rpow (Real.exp 1) (-r))
        (1 / (Module.finrank K L : ℝ)) at hmul
    have hf' := hf.trans hmul.symm
    calc
      Real.exp (-s) = Real.rpow (Real.exp 1) (-s) :=
        (Real.exp_one_rpow (-s)).symm
      _ = Real.rpow (Real.exp 1)
          ((-r) * (1 / (Module.finrank K L : ℝ))) := hf'
      _ = Real.exp ((-r) * (1 / (Module.finrank K L : ℝ))) :=
        Real.exp_one_rpow _
  have hrs : -s = (-r) * (1 / (Module.finrank K L : ℝ)) :=
    Real.exp_injective hexp
  have hreal : r = (Module.finrank K L : ℝ) * s := by
    field_simp [hnreal] at hrs
    linarith
  rw [hvr, hws]
  apply WithTop.coe_eq_coe.mpr
  simpa [nsmul_eq_mul] using hreal

/-- The order of every actual value-group coset divides the field degree. -/
theorem exponentialValueGroupQuotient_addOrderOf_dvd_finrank
    (v : LubinTate.Valuations.ExponentialValuation K)
    (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v).valuation)
    (q : ExponentialValueGroupQuotient v w) :
    addOrderOf q ∣ Module.finrank K L := by
  let : Finite (ExponentialValueGroupQuotient v w) :=
    exponentialValueGroupQuotient_finite_of_finiteDimensional v w hExt
  rw [addOrderOf_dvd_iff_nsmul_eq_zero]
  obtain ⟨gamma, rfl⟩ := QuotientAddGroup.mk_surjective q
  rcases gamma.property with ⟨x, hx, hvalue⟩
  apply (QuotientAddGroup.eq_zero_iff _).2
  change Module.finrank K L • (gamma : ℝ) ∈
    exponentialValueSubgroup v
  have hnorm :=
    exponentialValuation_norm_eq_finrank_nsmul
      v w hExt hhens x hx
  have hnorm0 : Algebra.norm K x ≠ 0 :=
    (Algebra.norm_ne_zero_iff).2 hx
  refine ⟨Algebra.norm K x, hnorm0, ?_⟩
  rw [hnorm, hvalue, WithTop.coe_nsmul]

end NormValue

end Valuations
end AlgebraicNumberTheory

end
