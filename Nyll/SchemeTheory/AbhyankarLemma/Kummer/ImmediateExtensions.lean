/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.AbhyankarLemma.Kummer.NormValue
import Nyll.ValuedFieldTheory.LocalField.Unramified.ResidueLifting

/-!
# The immediate prime-to-p step in tame ramification

This file develops the primary-reduction calculation used in the trace
argument: a monic polynomial whose reduction admits no nontrivial coprime
factorization and has a residue root is a pure power of the corresponding
linear factor.
-/

noncomputable section

universe u

namespace AlgebraicNumberTheory
namespace Valuations


/-- A monic primary polynomial over a field which has a root is the full
power of that root's linear factor. -/
theorem monic_eq_X_sub_C_pow_natDegree_of_primary_of_isRoot
    {k : Type*} [Field k]
    (q : Polynomial k) (hqmonic : q.Monic)
    (hprimary : ∀ a b : Polynomial k,
      q = a * b → IsCoprime a b →
        a.natDegree = 0 ∨ b.natDegree = 0)
    (c : k) (hc : q.IsRoot c) :
    q = (Polynomial.X - Polynomial.C c) ^ q.natDegree := by
  classical
  have hq0 : q ≠ 0 := hqmonic.ne_zero
  obtain ⟨R, hfactor, hnotdiv⟩ :=
    q.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hq0 c
  let r := q.rootMultiplicity c
  let linear : Polynomial k := Polynomial.X - Polynomial.C c
  have hrpos : 0 < r := by
    exact (Polynomial.rootMultiplicity_pos hq0).2 hc
  have hfactor' : q = linear ^ r * R := by
    simpa [r, linear] using hfactor
  have hnotlinear : ¬linear ∣ R := by
    simpa [r, linear] using hnotdiv
  have hlinearPrime : Prime linear :=
    Polynomial.prime_X_sub_C c
  have hcoprimeLinear : IsCoprime linear R :=
    hlinearPrime.coprime_iff_not_dvd.2 hnotlinear
  have hcoprime : IsCoprime (linear ^ r) R :=
    hcoprimeLinear.pow_left
  have hlinearMonic : linear.Monic := Polynomial.monic_X_sub_C c
  have hlinearDegree : linear.natDegree = 1 := by
    simp [linear]
  have hpowMonic : (linear ^ r).Monic := hlinearMonic.pow r
  have hRmonic : R.Monic :=
    hpowMonic.of_mul_monic_left (hfactor' ▸ hqmonic)
  have hdegrees := hprimary (linear ^ r) R hfactor' hcoprime
  have hpowDegree : (linear ^ r).natDegree = r := by
    simp [Polynomial.natDegree_pow, hlinearDegree]
  have hRdegree : R.natDegree = 0 := by
    rcases hdegrees with hpow0 | hR0
    · rw [hpowDegree] at hpow0
      exact (Nat.ne_of_gt hrpos hpow0).elim
    · exact hR0
  have hRone : R = 1 := hRmonic.natDegree_eq_zero.mp hRdegree
  have hrDegree : r = q.natDegree := by
    rw [hRone, mul_one] at hfactor'
    rw [hfactor']
    simp [Polynomial.natDegree_pow, hlinearDegree]
  have hqpow : q = linear ^ r := by
    simpa [hRone] using hfactor'
  calc
    q = linear ^ r := hqpow
    _ = linear ^ q.natDegree := by rw [hrDegree]
    _ = (Polynomial.X - Polynomial.C c) ^ q.natDegree := by rfl



/-- An integer prime to the positive residue characteristic remains nonzero
in the valued field.  This is the small characteristic argument used twice
in the trace proof for an immediate prime-to-characteristic extension. -/
theorem natCast_ne_zero_of_coprime_residueCharacteristic
    {K : Type*} [Field K]
    (v : LubinTate.Valuations.ExponentialValuation K)
    (hp : PositiveResidueCharacteristic v)
    (m : ℕ)
    (hcop : Nat.Coprime m (residueCharacteristic v)) :
    (m : K) ≠ 0 := by
  intro hmK
  have hmV : (m : LubinTate.Valuations.exponentialValuationSubring v) = 0 := by
    apply Subtype.ext
    exact hmK
  have hmk :
      (m : IsLocalRing.ResidueField
        (LubinTate.Valuations.exponentialValuationSubring v)) = 0 := by
    simpa using congrArg
      (IsLocalRing.residue (LubinTate.Valuations.exponentialValuationSubring v)) hmV
  have hpDiv : residueCharacteristic v ∣ m := by
    rw [← CharP.cast_eq_zero_iff
      (IsLocalRing.ResidueField (LubinTate.Valuations.exponentialValuationSubring v))
      (residueCharacteristic v) m]
    exact hmk
  exact
    ((residueCharacteristic_prime v hp).coprime_iff_not_dvd.mp hcop.symm)
      hpDiv


section TraceCentering

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [FiniteDimensional K L]

/-- In a finite extension of degree prime to the positive residue
characteristic, trace zero forces the next coefficient of the minimal
polynomial to vanish.  The possible multiplicity coming from the ambient
extension is again prime to the residue characteristic. -/
theorem minpoly_nextCoeff_eq_zero_of_trace_eq_zero_of_coprime
    (v : LubinTate.Valuations.ExponentialValuation K)
    (hp : PositiveResidueCharacteristic v)
    (hdegree : Nat.Coprime (Module.finrank K L)
      (residueCharacteristic v))
    (x : L) (htrace : Algebra.trace K L x = 0) :
    (minpoly K x).nextCoeff = 0 := by
  let E : IntermediateField K L :=
    IntermediateField.adjoin K ({x} : Set L)
  let d := Module.finrank E L
  have hdvd : d ∣ Module.finrank K L := by
    refine ⟨Module.finrank K E, ?_⟩
    dsimp [d]
    rw [mul_comm, Module.finrank_mul_finrank]
  have hdcop : Nat.Coprime d (residueCharacteristic v) :=
    Nat.Coprime.of_dvd_left hdvd hdegree
  have hdK : (d : K) ≠ 0 :=
    natCast_ne_zero_of_coprime_residueCharacteristic v hp d hdcop
  have hformula :=
    trace_eq_finrank_mul_minpoly_nextCoeff K x
  rw [htrace] at hformula
  change (0 : K) = (d : K) * -(minpoly K x).nextCoeff at hformula
  have hneg : -(minpoly K x).nextCoeff = 0 :=
    (mul_eq_zero.mp hformula.symm).resolve_left hdK
  exact neg_eq_zero.mp hneg

/-- Trace centering for an immediate prime-to-characteristic extension.  If an element is not
already in the base field, subtracting its normalized trace produces a
nonzero element of trace zero. -/
theorem exists_nonzero_trace_zero_of_not_mem_bot_of_coprime
    (v : LubinTate.Valuations.ExponentialValuation K)
    (hp : PositiveResidueCharacteristic v)
    (hdegree : Nat.Coprime (Module.finrank K L)
      (residueCharacteristic v))
    (alpha : L) (halpha : alpha ∉ (⊥ : IntermediateField K L)) :
    ∃ beta : L, beta ≠ 0 ∧ Algebra.trace K L beta = 0 := by
  let n := Module.finrank K L
  have hnK : (n : K) ≠ 0 :=
    natCast_ne_zero_of_coprime_residueCharacteristic
      v hp n hdegree
  let c : K := (n : K)⁻¹ * Algebra.trace K L alpha
  let beta : L := alpha - algebraMap K L c
  have hbetaTrace : Algebra.trace K L beta = 0 := by
    dsimp [beta, c]
    rw [map_sub, Algebra.trace_algebraMap]
    simp [Algebra.smul_def, n, hnK]
  have hbeta0 : beta ≠ 0 := by
    intro hbeta
    apply halpha
    have halphaEq : alpha = algebraMap K L c := by
      exact sub_eq_zero.mp hbeta
    rw [halphaEq]
    simp
  exact ⟨beta, hbeta0, hbetaTrace⟩

end TraceCentering

section ImmediateInvariants

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The actual residue-field map attached to an exact extension of
exponential valuations. -/
def tameResidueFieldMap
    (v : LubinTate.Valuations.ExponentialValuation K)
    (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a) :
    IsLocalRing.ResidueField (LubinTate.Valuations.exponentialValuationSubring v) →+*
      IsLocalRing.ResidueField (LubinTate.Valuations.exponentialValuationSubring w) := by
  let i := unramifiedValuationRingValuationRingMap v w hExt
  letI : IsLocalHom i :=
    unramifiedValuationRingValuationRingMap_isLocalHom v w hExt
  exact IsLocalRing.ResidueField.map i

omit [Algebra K L] in
/-- Equality of the actual value subgroups means that every nonzero target
element has the value of a nonzero base element. -/
theorem exists_base_element_value_eq_of_valueSubgroup_eq
    (v : LubinTate.Valuations.ExponentialValuation K)
    (w : LubinTate.Valuations.ExponentialValuation L)
    (hvalue : exponentialValueSubgroup w =
      exponentialValueSubgroup v)
    (x : L) (hx : x ≠ 0) :
    ∃ b : K, b ≠ 0 ∧ v b = w x := by
  have hxTop : w x ≠ ⊤ :=
    LubinTate.Valuations.exponentialValuation_ne_top_of_ne_zero w hx
  let r : ℝ := (w x).untop₀
  have hrw : w x = (r : WithTop ℝ) := by
    exact (WithTop.coe_untop₀_of_ne_top hxTop).symm
  have hrmem : r ∈ exponentialValueSubgroup w :=
    ⟨x, hx, hrw⟩
  rw [hvalue] at hrmem
  rcases hrmem with ⟨b, hb, hbval⟩
  exact ⟨b, hb, hbval.trans hrw.symm⟩

end ImmediateInvariants

section ImmediatePrimeToP

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
variable [FiniteDimensional K L]

/-- The immediate prime-to-`p` lemma for tame ramification.

If the value groups agree, the residue map is onto, and the finite degree is
prime to the positive residue characteristic, then the extension is trivial.
The proof uses a trace argument and does not assume discreteness or a
fundamental identity. -/
theorem finrank_eq_one_of_valueSubgroup_eq_of_residue_surjective_of_coprime
    (v : LubinTate.Valuations.ExponentialValuation K)
    (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v).valuation)
    (hp : PositiveResidueCharacteristic v)
    (hdegree : Nat.Coprime (Module.finrank K L)
      (residueCharacteristic v))
    (hvalue : exponentialValueSubgroup w =
      exponentialValueSubgroup v)
    (hresidue : Function.Surjective (tameResidueFieldMap v w hExt)) :
    Module.finrank K L = 1 := by
  classical
  let Vv := LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v
  let Wv := LubinTate.Valuations.exponentialValuationSubringAsValuationSubring w
  let V := LubinTate.Valuations.exponentialValuationSubring v
  let W := LubinTate.Valuations.exponentialValuationSubring w
  let i := unramifiedValuationRingValuationRingMap v w hExt
  let : IsLocalHom i :=
    unramifiedValuationRingValuationRingMap_isLocalHom v w hExt
  let : Algebra V W := i.toAlgebra
  let k := IsLocalRing.ResidueField V
  let ell := IsLocalRing.ResidueField W
  let f : k →+* ell := tameResidueFieldMap v w hExt
  let : Algebra k ell := f.toAlgebra
  apply IntermediateField.bot_eq_top_iff_finrank_eq_one.mp
  apply top_unique
  intro alpha _halphaTop
  by_contra halphaBase
  obtain ⟨beta, hbeta0, hbetaTrace⟩ :=
    exists_nonzero_trace_zero_of_not_mem_bot_of_coprime
      v hp hdegree alpha halphaBase
  obtain ⟨b, hb0, hbValue⟩ :=
    exists_base_element_value_eq_of_valueSubgroup_eq
      v w hvalue beta hbeta0
  let epsilon : L := beta / algebraMap K L b
  have hbMap0 : algebraMap K L b ≠ 0 :=
    (map_ne_zero (algebraMap K L)).2 hb0
  have hepsilon0 : epsilon ≠ 0 := div_ne_zero hbeta0 hbMap0
  obtain ⟨r, hbetaValue⟩ :=
    LubinTate.Valuations.exponentialValuation_exists_real_of_ne_zero w hbeta0
  have hbMapValue : w (algebraMap K L b) = (r : WithTop ℝ) := by
    rw [hExt, hbValue]
    exact hbetaValue
  have hbMapInvValue :
      w (algebraMap K L b)⁻¹ = ((-r : ℝ) : WithTop ℝ) :=
    LubinTate.Valuations.exponentialValuation_inv_value w hbMap0 hbMapValue
  have hepsilonValue : w epsilon = 0 := by
    dsimp [epsilon]
    rw [div_eq_mul_inv, w.map_mul, hbetaValue, hbMapInvValue]
    simp
  have hepsilonTrace : Algebra.trace K L epsilon = 0 := by
    have hepsilonSmul : epsilon = b⁻¹ • beta := by
      dsimp [epsilon]
      simp [Algebra.smul_def, div_eq_mul_inv, mul_comm]
    rw [hepsilonSmul, map_smul, hbetaTrace, smul_zero]
  have hepsilonNext : (minpoly K epsilon).nextCoeff = 0 :=
    minpoly_nextCoeff_eq_zero_of_trace_eq_zero_of_coprime
      v hp hdegree epsilon hepsilonTrace
  let epsilonW : W :=
    ⟨epsilon, by
      change (0 : WithTop ℝ) ≤ w epsilon
      rw [hepsilonValue]⟩
  have hepsilonUnit : IsUnit epsilonW :=
    LubinTate.Valuations.isUnit_of_exponentialValuation_eq_zero w hepsilonValue
  have hepsilonResidue0 : IsLocalRing.residue W epsilonW ≠ 0 :=
    (IsLocalRing.residue_ne_zero_iff_isUnit epsilonW).2 hepsilonUnit
  let algVL : Algebra V L :=
    ((algebraMap K L).comp V.subtype).toAlgebra
  let : Algebra V L := algVL
  let : SMul V L := algVL.toSMul
  let : SMul V K := (inferInstance : Algebra V K).toSMul
  let : IsScalarTower V K L :=
    IsScalarTower.of_algebraMap_eq
      (R := V) (S := K) (A := L) (by intro x; rfl)
  let : IsFractionRing V K := by
    change IsFractionRing Vv K
    have hfr : IsFractionRing Vv.valuation.valuationSubring K :=
      (Valuation.valuationSubring.integers
        (v := Vv.valuation)).isFractionRing
    rw [Vv.valuationSubring_valuation] at hfr
    exact hfr
  let : IsIntegrallyClosed V := by
    change IsIntegrallyClosed Vv
    infer_instance
  have hclosureVv :
      Wv.toSubring = (integralClosure Vv L).toSubring :=
    exponentialValuationSubring_eq_integralClosure_of_henselian
      v w hExt hhens
  have hclosure : W = (integralClosure V L).toSubring := by
    change Wv.toSubring = (integralClosure Vv L).toSubring
    exact hclosureVv
  have hepsilonIntegralV : IsIntegral V epsilon := by
    change epsilon ∈ (integralClosure V L).toSubring
    rw [← hclosure]
    exact epsilonW.property
  let pV : Polynomial V := minpoly V epsilon
  let pbar : Polynomial k := pV.map (IsLocalRing.residue V)
  have hpVMonic : pV.Monic := minpoly.monic hepsilonIntegralV
  have hpbarMonic : pbar.Monic := hpVMonic.map _
  have hpKmap : minpoly K epsilon = pV.map (algebraMap V K) := by
    exact minpoly.isIntegrallyClosed_eq_field_fractions' K hepsilonIntegralV
  have hpVIrreducible : Irreducible (pV.map (algebraMap V K)) := by
    rw [← hpKmap]
    exact minpoly.irreducible (Algebra.IsIntegral.isIntegral epsilon)
  have hpVPrimitive : pV.IsPrimitive := hpVMonic.isPrimitive
  have hfactorization : ValuationTheory.DiscreteValuationField.HenselFactorizationProperty Vv := by
    change ValuationTheory.DiscreteValuationField.HenselFactorizationProperty
      Vv.valuation.valuationSubring at hhens
    rw [ValuationSubring.valuationSubring_valuation] at hhens
    exact hhens
  have hlift : DiscreteValuationField.MonicResidualCoprimeFactorLifting Vv :=
    DiscreteValuationField.monicResidualCoprimeFactorLifting_of_henselFactorization
      hfactorization
  have hprimitiveProperty :
      DiscreteValuationField.PrimitiveIrreducibleReductionProperty Vv :=
    (open _root_.DiscreteValuationField in
      primitiveIrreducibleReductionProperty_of_monicResidualCoprimeFactorLifting
        Vv hlift)
  have hprimary : ∀ a b : Polynomial k,
      pbar = a * b → IsCoprime a b →
        a.natDegree = 0 ∨ b.natDegree = 0 := by
    exact (hprimitiveProperty pV hpVPrimitive hpVIrreducible).2
  have hpW : Polynomial.aeval epsilonW pV = 0 := by
    change pV.eval₂ i epsilonW = 0
    apply W.subtype_injective
    rw [map_zero, Polynomial.hom_eval₂]
    change pV.eval₂ (algebraMap V L) epsilon = 0
    exact minpoly.aeval V epsilon
  have hred :=
    unramifiedValuationRing_polynomial_aeval_residue_eq
      v w hExt pV epsilonW
  simp only at hred
  rw [hpW, map_zero] at hred
  have htargetRoot :
      (pbar.map f).eval (IsLocalRing.residue W epsilonW) = 0 := by
    have hf : f = IsLocalRing.ResidueField.map i := by
      rfl
    rw [hf]
    change
      ((pV.map (IsLocalRing.residue V)).map
        (IsLocalRing.ResidueField.map i)).eval
          (IsLocalRing.residue W epsilonW) = 0
    exact hred.symm
  change Function.Surjective f at hresidue
  obtain ⟨c, hc⟩ := hresidue (IsLocalRing.residue W epsilonW)
  have hc0 : c ≠ 0 := by
    intro hcZero
    apply hepsilonResidue0
    rw [← hc, hcZero, map_zero]
  have hpbarRoot : pbar.IsRoot c := by
    rw [Polynomial.IsRoot.def]
    apply f.injective
    calc
      f (pbar.eval c) = (pbar.map f).eval (f c) := by simp
      _ = (pbar.map f).eval (IsLocalRing.residue W epsilonW) := by rw [hc]
      _ = 0 := htargetRoot
      _ = f 0 := (map_zero f).symm
  have hpbarPower :
      pbar = (Polynomial.X - Polynomial.C c) ^ pbar.natDegree :=
    monic_eq_X_sub_C_pow_natDegree_of_primary_of_isRoot
      pbar hpbarMonic hprimary c hpbarRoot
  have hpVNext : pV.nextCoeff = 0 := by
    have hpVLeadingUnit : IsUnit pV.leadingCoeff := by
      rw [hpVMonic]
      exact isUnit_one
    have hnext := congrArg Polynomial.nextCoeff hpKmap
    rw [hepsilonNext,
      Polynomial.nextCoeff_map_eq_of_isUnit_leadingCoeff
        (algebraMap V K) hpVLeadingUnit] at hnext
    exact V.subtype_injective hnext.symm
  have hpbarNext : pbar.nextCoeff = 0 := by
    have hpVLeadingUnit : IsUnit pV.leadingCoeff := by
      rw [hpVMonic]
      exact isUnit_one
    dsimp [pbar]
    rw [Polynomial.nextCoeff_map_eq_of_isUnit_leadingCoeff
      (IsLocalRing.residue V) hpVLeadingUnit,
      hpVNext, map_zero]
  have hpbarDegree :
      pbar.natDegree = (minpoly K epsilon).natDegree := by
    calc
      pbar.natDegree = pV.natDegree := hpVMonic.natDegree_map _
      _ = (minpoly K epsilon).natDegree := by
        rw [hpKmap, hpVMonic.natDegree_map]
  have hdegreeDvd : pbar.natDegree ∣ Module.finrank K L := by
    rw [hpbarDegree]
    exact minpoly.degree_dvd (Algebra.IsIntegral.isIntegral epsilon)
  have hpbarDegreeCoprime :
      Nat.Coprime pbar.natDegree (residueCharacteristic v) :=
    Nat.Coprime.of_dvd_left hdegreeDvd hdegree
  have hpbarDegreeCast : (pbar.natDegree : k) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff k
      (residueCharacteristic v) pbar.natDegree]
    exact (residueCharacteristic_prime v hp).coprime_iff_not_dvd.mp
      hpbarDegreeCoprime.symm
  have hcoefficient : pbar.natDegree • (-c) = 0 := by
    have hnextPower := congrArg Polynomial.nextCoeff hpbarPower
    rw [hpbarNext,
      (Polynomial.monic_X_sub_C c).nextCoeff_pow,
      Polynomial.nextCoeff_X_sub_C] at hnextPower
    exact hnextPower.symm
  rw [nsmul_eq_mul] at hcoefficient
  exact (mul_ne_zero hpbarDegreeCast (neg_ne_zero.mpr hc0)) hcoefficient

end ImmediatePrimeToP

end Valuations
end AlgebraicNumberTheory

end
