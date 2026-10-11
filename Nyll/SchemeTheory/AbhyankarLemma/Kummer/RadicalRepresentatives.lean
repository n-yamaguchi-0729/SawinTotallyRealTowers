/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.AbhyankarLemma.Kummer.ImmediateExtensions

/-!
# Corrected radical representatives for tame extensions

This file carries out the second concrete step in the tame-generation proof.  A
representative of each actual value-group coset is corrected first by a base
element and then by a principal-unit root.  The result has the same value
coset and a prime-to-residue-characteristic power in the base field.
-/

noncomputable section

universe u

namespace AlgebraicNumberTheory
namespace Valuations

section CorrectedRadicals

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

@[reducible] local instance exponentialValueGroupQuotientAddCommGroupRadicals
    (v : LubinTate.Valuations.ExponentialValuation K)
    (w : LubinTate.Valuations.ExponentialValuation L) :
    AddCommGroup (ExponentialValueGroupQuotient v w) :=
  QuotientAddGroup.Quotient.addCommGroup _

/-- Exact extensions of exponential valuations have the same actual
residue characteristic. -/
theorem residueCharacteristic_eq_of_exact_extension
    (v : LubinTate.Valuations.ExponentialValuation K)
    (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a) :
    residueCharacteristic v = residueCharacteristic w := by
  let V := LubinTate.Valuations.exponentialValuationSubring v
  let W := LubinTate.Valuations.exponentialValuationSubring w
  let k := IsLocalRing.ResidueField V
  let ell := IsLocalRing.ResidueField W
  let f : k →+* ell := tameResidueFieldMap v w hExt
  let : Algebra k ell := f.toAlgebra
  change ringChar k = ringChar ell
  exact Algebra.ringChar_eq k ell

/-- Equality of actual value cosets can be cross-multiplied by a nonzero base
element.  This is the converse direction needed when the corrected radical
representatives are used to recover the whole target value group. -/
theorem exists_base_element_mul_value_eq_of_exponentialValueCoset_eq
    (v : LubinTate.Valuations.ExponentialValuation K)
    (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    {x y : L} (hx : x ≠ 0) (hy : y ≠ 0)
    (hcoset : exponentialValueCoset v w x hx = exponentialValueCoset v w y hy) :
    ∃ t : K, t ≠ 0 ∧ w x = w (algebraMap K L t * y) := by
  let Gamma := exponentialValueSubgroup w
  let H : AddSubgroup Gamma :=
    (exponentialValueSubgroup v).comap Gamma.subtype
  have hmem := QuotientAddGroup.eq_iff_sub_mem.mp hcoset
  change (w x).untop₀ - (w y).untop₀ ∈
    exponentialValueSubgroup v at hmem
  rcases hmem with ⟨t, ht0, htValue⟩
  refine ⟨t, ht0, ?_⟩
  have hxTop : w x ≠ ⊤ :=
    LubinTate.Valuations.exponentialValuation_ne_top_of_ne_zero w hx
  have hyTop : w y ≠ ⊤ :=
    LubinTate.Valuations.exponentialValuation_ne_top_of_ne_zero w hy
  rw [w.map_mul, hExt, htValue]
  rw [show w x = (((w x).untop₀ : ℝ) : WithTop ℝ) from
    (WithTop.coe_untop₀_of_ne_top hxTop).symm]
  rw [show w y = (((w y).untop₀ : ℝ) : WithTop ℝ) from
    (WithTop.coe_untop₀_of_ne_top hyTop).symm]
  rw [← WithTop.coe_add]
  congr
  simp only [WithTop.untop₀_coe]
  ring

/-- Every actual value-group coset in a finite prime-to-`p` extension has a
representative `alpha` whose positive prime-to-`p` power lies in the base
field.  This is the corrected radical used in tame generation. -/
theorem exists_prime_to_radical_representing_valueCoset
    [FiniteDimensional K L]
    (v : LubinTate.Valuations.ExponentialValuation K)
    (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v).valuation)
    (hp : PositiveResidueCharacteristic v)
    (hdegree : Nat.Coprime (Module.finrank K L)
      (residueCharacteristic v))
    (hresidue : Function.Surjective (tameResidueFieldMap v w hExt))
    (q : ExponentialValueGroupQuotient v w) :
    ∃ (m : ℕ) (a : K) (alpha : L),
      0 < m ∧
        Nat.Coprime m (residueCharacteristic v) ∧
          alpha ^ m = algebraMap K L a ∧
            ∃ halpha0 : alpha ≠ 0,
              exponentialValueCoset v w alpha halpha0 = q := by
  classical
  let V := LubinTate.Valuations.exponentialValuationSubring v
  let W := LubinTate.Valuations.exponentialValuationSubring w
  let i := unramifiedValuationRingValuationRingMap v w hExt
  let : IsLocalHom i :=
    unramifiedValuationRingValuationRingMap_isLocalHom v w hExt
  let k := IsLocalRing.ResidueField V
  let ell := IsLocalRing.ResidueField W
  let f : k →+* ell := tameResidueFieldMap v w hExt
  let : Algebra k ell := f.toAlgebra
  let m := addOrderOf q
  have hmpos : 0 < m :=
    exponentialValueGroupQuotient_addOrderOf_pos v w hExt q
  have hmdvd : m ∣ Module.finrank K L :=
    exponentialValueGroupQuotient_addOrderOf_dvd_finrank
      v w hExt hhens q
  have hmcop : Nat.Coprime m (residueCharacteristic v) :=
    Nat.Coprime.of_dvd_left hmdvd hdegree
  obtain ⟨gammaUnit, hgammaClass⟩ :=
    exponentialValueCoset_units_surjective v w q
  let gamma : L := (gammaUnit : L)
  have hgamma0 : gamma ≠ 0 := gammaUnit.ne_zero
  have hgammaClass' : exponentialValueCoset v w gamma hgamma0 = q :=
    hgammaClass
  obtain ⟨a0, ha0, _haValue, huValue⟩ :=
    exists_base_element_and_value_zero_radical_correction
      v w hExt gamma hgamma0
  let u : L := gamma ^ m / algebraMap K L a0
  have ha0Map : algebraMap K L a0 ≠ 0 :=
    (map_ne_zero (algebraMap K L)).2 ha0
  have hu0 : u ≠ 0 := div_ne_zero (pow_ne_zero m hgamma0) ha0Map
  have huValue' : w u = 0 := by
    rw [hgammaClass'] at huValue
    simpa [u, m] using huValue
  let uW : W :=
    ⟨u, by
      change (0 : WithTop ℝ) ≤ w u
      rw [huValue']⟩
  have huWUnit : IsUnit uW :=
    LubinTate.Valuations.isUnit_of_exponentialValuation_eq_zero w huValue'
  have huResidue0 : IsLocalRing.residue W uW ≠ 0 :=
    (IsLocalRing.residue_ne_zero_iff_isUnit uW).2 huWUnit
  change Function.Surjective f at hresidue
  obtain ⟨c, hc⟩ := hresidue (IsLocalRing.residue W uW)
  have hc0 : c ≠ 0 := by
    intro hcZero
    apply huResidue0
    rw [← hc, hcZero, map_zero]
  obtain ⟨bV, hbVresidue⟩ := IsLocalRing.residue_surjective c
  have hbVUnit : IsUnit bV :=
    (IsLocalRing.residue_ne_zero_iff_isUnit bV).1 (by
      rw [hbVresidue]
      exact hc0)
  let b : K := (bV : K)
  have hb0 : b ≠ 0 := by
    intro hb
    exact hbVUnit.ne_zero (Subtype.ext hb)
  let bW : W := i bV
  have hbWUnit : IsUnit bW := hbVUnit.map i
  let ub : Wˣ := hbWUnit.unit
  have hub : (ub : W) = bW := hbWUnit.unit_spec
  let bWinv : W := (ub⁻¹ : Wˣ)
  let u1W : W := uW * bWinv
  have hbWResidue : IsLocalRing.residue W bW = f c := by
    calc
      IsLocalRing.residue W bW =
          IsLocalRing.ResidueField.map i (IsLocalRing.residue V bV) :=
        (IsLocalRing.ResidueField.map_residue i bV).symm
      _ = f c := by rw [hbVresidue]; rfl
  have hbMulInv : bW * bWinv = 1 := by
    dsimp [bWinv]
    rw [← hub]
    exact Units.mul_inv ub
  have hbResidueMulInv :
      IsLocalRing.residue W bW * IsLocalRing.residue W bWinv = 1 := by
    rw [← map_mul, hbMulInv, map_one]
  have hu1Residue : IsLocalRing.residue W u1W = 1 := by
    dsimp [u1W]
    rw [map_mul, ← hc, ← hbWResidue]
    exact hbResidueMulInv
  have hHenselianW : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring w).valuation :=
    henselianValuation_of_algebraic_extension v w hExt hhens
  have hchar : residueCharacteristic v = residueCharacteristic w :=
    residueCharacteristic_eq_of_exact_extension v w hExt
  have hpW : PositiveResidueCharacteristic w := by
    change residueCharacteristic w ≠ 0
    rw [← hchar]
    exact hp
  have hmcopW : Nat.Coprime m (residueCharacteristic w) := by
    rw [← hchar]
    exact hmcop
  obtain ⟨betaW, hbetaPow, hbetaResidue⟩ :=
    exists_pow_eq_of_residue_eq_one_of_coprime
      w hHenselianW hpW m hmcopW u1W hu1Residue
  have hbetaWUnit : IsUnit betaW :=
    (IsLocalRing.residue_ne_zero_iff_isUnit betaW).1 (by
      rw [hbetaResidue]
      exact one_ne_zero)
  let beta : L := (betaW : L)
  have hbeta0 : beta ≠ 0 := by
    intro hbeta
    exact hbetaWUnit.ne_zero (Subtype.ext hbeta)
  have hbetaValue : w beta = 0 :=
    LubinTate.Valuations.exponentialValuation_eq_zero_of_isUnit w hbetaWUnit
  have hbWinvCoe : (bWinv : L) = (algebraMap K L b)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    have hmulW : bWinv * bW = 1 := by
      rw [mul_comm, hbMulInv]
    have hmulL := congrArg (fun z : W ↦ (z : L)) hmulW
    change (bWinv : L) * (bW : L) = 1
    exact hmulL
  have hu1Coe : (u1W : L) = u / algebraMap K L b := by
    dsimp [u1W]
    change u * (bWinv : L) = u / algebraMap K L b
    rw [hbWinvCoe, div_eq_mul_inv]
  have hbetaPowL : beta ^ m = u / algebraMap K L b := by
    have hcoe := congrArg (fun z : W ↦ (z : L)) hbetaPow
    simpa [beta, hu1Coe] using hcoe
  let alpha : L := gamma / beta
  have halpha0 : alpha ≠ 0 := div_ne_zero hgamma0 hbeta0
  have halphaPow : alpha ^ m = algebraMap K L (a0 * b) := by
    dsimp [alpha]
    rw [div_pow, hbetaPowL]
    dsimp [u]
    rw [map_mul]
    field_simp
  have hbetaInvValue : w beta⁻¹ = 0 := by
    have := LubinTate.Valuations.exponentialValuation_inv_value w hbeta0
      (show w beta = ((0 : ℝ) : WithTop ℝ) by simpa using hbetaValue)
    simpa using this
  have halphaValue : w alpha = w gamma := by
    dsimp [alpha]
    rw [div_eq_mul_inv, w.map_mul, hbetaInvValue, add_zero]
  have halphaClass : exponentialValueCoset v w alpha halpha0 = q := by
    rw [← hgammaClass']
    unfold exponentialValueCoset
    apply congrArg QuotientAddGroup.mk
    apply Subtype.ext
    exact congrArg WithTop.untop₀ halphaValue
  exact ⟨m, a0 * b, alpha, hmpos, hmcop, halphaPow,
    ⟨halpha0, halphaClass⟩⟩

end CorrectedRadicals

section MaximalUnramifiedResidue

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
variable [Algebra.IsAlgebraic K L]

/-- If the ambient residue extension is separable, the maximal-residue theorem says that
the residue map from the maximal unramified subextension onto the ambient
residue field is surjective. -/
theorem maximalUnramifiedSubextension_residueMap_surjective_of_separable
    (v : LubinTate.Valuations.ExponentialValuation K)
    (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v).valuation)
    (hsep : ResidueExtensionIsSeparable v w hExt) :
    let T := maximalUnramifiedSubextension v w hExt
    let wT := exponentialValuationRestrict w T
    let hT : ∀ a : T, w (algebraMap T L a) = wT a := by
      intro a
      rfl
    Function.Surjective (tameResidueFieldMap wT w hT) := by
  classical
  let T := maximalUnramifiedSubextension v w hExt
  let wT := exponentialValuationRestrict w T
  let hT : ∀ a : T, w (algebraMap T L a) = wT a := by
    intro a
    rfl
  let V := LubinTate.Valuations.exponentialValuationSubring v
  let VT := LubinTate.Valuations.exponentialValuationSubring wT
  let W := LubinTate.Valuations.exponentialValuationSubring w
  let i := unramifiedValuationRingValuationRingMap v wT
    (exponentialValuationRestrict_extends v w hExt T)
  let b := unramifiedValuationRingValuationRingMap v w hExt
  let : IsLocalHom i :=
    unramifiedValuationRingValuationRingMap_isLocalHom v wT
      (exponentialValuationRestrict_extends v w hExt T)
  let : IsLocalHom b :=
    unramifiedValuationRingValuationRingMap_isLocalHom v w hExt
  let k := IsLocalRing.ResidueField V
  let kT := IsLocalRing.ResidueField VT
  let ell := IsLocalRing.ResidueField W
  let : Algebra k kT := (IsLocalRing.ResidueField.map i).toAlgebra
  let : Algebra k ell := (IsLocalRing.ResidueField.map b).toAlgebra
  have hrange :=
    maximalUnramifiedSubextension_residue_fieldRange_eq_separableClosure
      v w hExt hhens
  simp only at hrange
  have htop : separableClosure k ell = ⊤ :=
    (separableClosure.eq_top_iff (F := k) (E := ell)).2 hsep
  rw [htop] at hrange
  have hsur : Function.Surjective
      (restrictedResidueAlgHomToAmbient v w hExt T) :=
    AlgHom.fieldRange_eq_top.mp hrange
  simp only
  exact hsur

end MaximalUnramifiedResidue

end Valuations
end AlgebraicNumberTheory

end
