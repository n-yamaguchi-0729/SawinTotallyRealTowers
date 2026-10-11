/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.AbhyankarLemma.Kummer.TameRadicalGeneration

/-!
# A single radical in a tame extension

This file proves the root-of-unity descent used in the converse and degree
calculation for a single prime-to-residue-characteristic radical.
-/

noncomputable section

universe u

namespace AlgebraicNumberTheory
namespace Valuations


/-- A simple root in a fixed residue class is unique in any local domain.
This is the elementary uniqueness half of Hensel's lemma. -/
theorem eq_of_isRoot_of_isRoot_of_residue_eq_of_derivative_isUnit
    {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    {f : Polynomial R} {a b : R}
    (ha : f.IsRoot a) (hb : f.IsRoot b)
    (hres : IsLocalRing.residue R b = IsLocalRing.residue R a)
    (hderiv : IsUnit (f.derivative.eval a)) :
    b = a := by
  let q : Polynomial R :=
    f /ₘ (Polynomial.X - Polynomial.C a)
  have hfactor : (Polynomial.X - Polynomial.C a) * q = f := by
    dsimp [q]
    rw [Polynomial.mul_divByMonic_eq_iff_isRoot]
    exact ha
  have hqEval : q.eval a = f.derivative.eval a := by
    simpa [q] using
      ValuationTheory.DiscreteValuationField.divByMonic_X_sub_C_eval_eq_derivative_eval
        (p := f) a
  have hqUnit : IsUnit (q.eval a) := by
    simpa [hqEval] using hderiv
  have hqResidue :
      IsLocalRing.residue R (q.eval b) =
        IsLocalRing.residue R (q.eval a) := by
    calc
      IsLocalRing.residue R (q.eval b) =
          (q.map (IsLocalRing.residue R)).eval
            (IsLocalRing.residue R b) := by
        exact (Polynomial.eval_map_apply
          (f := IsLocalRing.residue R) (p := q) b).symm
      _ = (q.map (IsLocalRing.residue R)).eval
          (IsLocalRing.residue R a) := by rw [hres]
      _ = IsLocalRing.residue R (q.eval a) := by
        exact Polynomial.eval_map_apply
          (f := IsLocalRing.residue R) (p := q) a
  have hqResidue0 : IsLocalRing.residue R (q.eval b) ≠ 0 := by
    rw [hqResidue]
    exact (IsLocalRing.residue_ne_zero_iff_isUnit (q.eval a)).2 hqUnit
  have hq0 : q.eval b ≠ 0 := by
    intro hzero
    exact hqResidue0 (by rw [hzero, map_zero])
  have hmul : (b - a) * q.eval b = 0 := by
    have hbEval : ((Polynomial.X - Polynomial.C a) * q).eval b = 0 := by
      rw [hfactor]
      exact Polynomial.IsRoot.def.mp hb
    simpa [Polynomial.eval_mul, Polynomial.eval_sub] using hbEval
  exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right hq0)


section RootOfUnityLift

variable {K : Type u} [Field K]

/-- Every prime-to-`p` residue root of unity has a root-of-unity lift in a
Henselian valued field. -/
theorem exists_rootOfUnity_lift_of_coprime
    (v : LubinTate.Valuations.ExponentialValuation K)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v).valuation)
    (hp : PositiveResidueCharacteristic v)
    (d : ℕ) (hcop : Nat.Coprime d (residueCharacteristic v))
    (c : IsLocalRing.ResidueField (LubinTate.Valuations.exponentialValuationSubring v))
    (hc : c ^ d = 1) :
    ∃ z : LubinTate.Valuations.exponentialValuationSubring v,
      z ^ d = 1 ∧ IsLocalRing.residue
        (LubinTate.Valuations.exponentialValuationSubring v) z = c := by
  classical
  let V := LubinTate.Valuations.exponentialValuationSubring v
  have hc0 : c ≠ 0 := by
    intro hcZero
    rw [hcZero, zero_pow] at hc
    · exact zero_ne_one hc
    · intro hd0
      subst d
      have hpone : residueCharacteristic v = 1 := by
        simpa using hcop
      exact (residueCharacteristic_prime v hp).ne_one hpone
  obtain ⟨t, htResidue⟩ := IsLocalRing.residue_surjective c
  have htUnit : IsUnit t :=
    (IsLocalRing.residue_ne_zero_iff_isUnit t).1 (by
      rw [htResidue]
      exact hc0)
  let ut : Vˣ := htUnit.unit
  have hut : (ut : V) = t := htUnit.unit_spec
  let tInv : V := (ut⁻¹ : Vˣ)
  have htMulInv : t * tInv = 1 := by
    dsimp [tInv]
    rw [← hut]
    exact Units.mul_inv ut
  have htInvResidue : IsLocalRing.residue V tInv = c⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← htResidue, ← map_mul, mul_comm, htMulInv, map_one]
  let principal : V := tInv ^ d
  have hprincipalResidue : IsLocalRing.residue V principal = 1 := by
    dsimp [principal]
    rw [map_pow, htInvResidue, inv_pow, hc, inv_one]
  obtain ⟨beta, hbetaPow, hbetaResidue⟩ :=
    exists_pow_eq_of_residue_eq_one_of_coprime
      v hhens hp d hcop principal hprincipalResidue
  let z : V := t * beta
  have hunitPowers : t ^ d * tInv ^ d = 1 := by
    rw [← mul_pow, htMulInv, one_pow]
  have hzPow : z ^ d = 1 := by
    dsimp [z]
    rw [mul_pow, hbetaPow]
    exact hunitPowers
  have hzResidue : IsLocalRing.residue V z = c := by
    dsimp [z]
    rw [map_mul, htResidue, hbetaResidue, mul_one]
  exact ⟨z, hzPow, hzResidue⟩

end RootOfUnityLift

section RootOfUnityDescent

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-- A prime-to-`p` root of unity whose residue class comes from the base
already lies in the Henselian base field. -/
theorem exists_base_rootOfUnity_eq_of_residue_preimage
    (v : LubinTate.Valuations.ExponentialValuation K)
    (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v).valuation)
    (hp : PositiveResidueCharacteristic v)
    (d : ℕ) (hcop : Nat.Coprime d (residueCharacteristic v))
    (zeta : LubinTate.Valuations.exponentialValuationSubring w)
    (hzetaPow : zeta ^ d = 1)
    (c : IsLocalRing.ResidueField (LubinTate.Valuations.exponentialValuationSubring v))
    (hc : tameResidueFieldMap v w hExt c =
      IsLocalRing.residue (LubinTate.Valuations.exponentialValuationSubring w) zeta) :
    ∃ z : LubinTate.Valuations.exponentialValuationSubring v,
      (unramifiedValuationRingValuationRingMap v w hExt) z = zeta := by
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
  have hd0 : d ≠ 0 := by
    intro hd
    subst d
    have hpone : residueCharacteristic v = 1 := by
      simpa using hcop
    exact (residueCharacteristic_prime v hp).ne_one hpone
  have hzetaResidue0 : IsLocalRing.residue W zeta ≠ 0 := by
    intro hz
    have hpow := congrArg (IsLocalRing.residue W) hzetaPow
    rw [map_pow, hz, zero_pow hd0, map_one] at hpow
    exact zero_ne_one hpow
  have hc0 : c ≠ 0 := by
    intro hcZero
    apply hzetaResidue0
    rw [← hc, hcZero, map_zero]
  have hcPow : c ^ d = 1 := by
    apply f.injective
    calc
      f (c ^ d) = (f c) ^ d := map_pow f c d
      _ = (IsLocalRing.residue W zeta) ^ d := by rw [hc]
      _ = IsLocalRing.residue W (zeta ^ d) := (map_pow _ _ _).symm
      _ = 1 := by rw [hzetaPow, map_one]
      _ = f 1 := (map_one f).symm
  obtain ⟨z, hzPow, hzResidue⟩ :=
    exists_rootOfUnity_lift_of_coprime v hhens hp d hcop c hcPow
  let zW : W := i z
  have hzWPow : zW ^ d = 1 := by
    dsimp [zW]
    rw [← map_pow, hzPow, map_one]
  have hzWResidue : IsLocalRing.residue W zW =
      IsLocalRing.residue W zeta := by
    calc
      IsLocalRing.residue W zW =
          IsLocalRing.ResidueField.map i (IsLocalRing.residue V z) :=
        (IsLocalRing.ResidueField.map_residue i z).symm
      _ = f c := by rw [hzResidue]; rfl
      _ = IsLocalRing.residue W zeta := hc
  have hzWUnit : IsUnit zW :=
    (IsLocalRing.residue_ne_zero_iff_isUnit zW).1 (by
      rw [hzWResidue]
      exact hzetaResidue0)
  have hchar : residueCharacteristic v = residueCharacteristic w :=
    residueCharacteristic_eq_of_exact_extension v w hExt
  have hcopW : Nat.Coprime d (residueCharacteristic w) := by
    rw [← hchar]
    exact hcop
  have hdResidue : (d : ell) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff ell
      (residueCharacteristic w) d]
    exact (residueCharacteristic_prime w (by
      change residueCharacteristic w ≠ 0
      rw [← hchar]
      exact hp)).coprime_iff_not_dvd.mp hcopW.symm
  have hdWUnit :
      IsUnit (d : LubinTate.Valuations.exponentialValuationSubring w) :=
    (IsLocalRing.residue_ne_zero_iff_isUnit
      (d : LubinTate.Valuations.exponentialValuationSubring w)).1 (by
        change (d : IsLocalRing.ResidueField
          (LubinTate.Valuations.exponentialValuationSubring w)) ≠ 0
        exact hdResidue)
  let P : Polynomial W := Polynomial.X ^ d - Polynomial.C 1
  have hzRoot : P.IsRoot zW := by
    rw [Polynomial.IsRoot.def]
    simp [P, hzWPow]
  have hzetaRoot : P.IsRoot zeta := by
    rw [Polynomial.IsRoot.def]
    simp [P, hzetaPow]
  have hderivative : IsUnit (P.derivative.eval zW) := by
    have hform : P.derivative.eval zW = (d : W) * zW ^ (d - 1) := by
      simp [P, Polynomial.derivative_X_pow]
    rw [hform]
    exact hdWUnit.mul (hzWUnit.pow (d - 1))
  have hzetaEq : zeta = zW :=
    eq_of_isRoot_of_isRoot_of_residue_eq_of_derivative_isUnit
      hzRoot hzetaRoot hzWResidue.symm hderivative
  exact ⟨z, hzetaEq.symm⟩

/-- A prime-to-`p` root of unity in an extension with no residue-field
extension already lies in the Henselian base field. -/
theorem exists_base_rootOfUnity_eq
    (v : LubinTate.Valuations.ExponentialValuation K)
    (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v).valuation)
    (hp : PositiveResidueCharacteristic v)
    (hresidue : Function.Surjective (tameResidueFieldMap v w hExt))
    (d : ℕ) (hcop : Nat.Coprime d (residueCharacteristic v))
    (zeta : LubinTate.Valuations.exponentialValuationSubring w)
    (hzetaPow : zeta ^ d = 1) :
    ∃ z : LubinTate.Valuations.exponentialValuationSubring v,
      (unramifiedValuationRingValuationRingMap v w hExt) z = zeta := by
  obtain ⟨c, hc⟩ := hresidue
    (IsLocalRing.residue (LubinTate.Valuations.exponentialValuationSubring w) zeta)
  exact exists_base_rootOfUnity_eq_of_residue_preimage
    v w hExt hhens hp d hcop zeta hzetaPow c hc

end RootOfUnityDescent

section UnitRootDescent

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-- If a base unit acquires a prime-to-`p` root whose residue class comes
from the base, it already has such a root in the Henselian base. -/
theorem exists_base_unit_root_of_target_root_of_residue_preimage
    (v : LubinTate.Valuations.ExponentialValuation K)
    (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v).valuation)
    (hp : PositiveResidueCharacteristic v)
    (d : ℕ) (hcop : Nat.Coprime d (residueCharacteristic v))
    (u : LubinTate.Valuations.exponentialValuationSubring v)
    (huUnit : IsUnit u)
    (delta : LubinTate.Valuations.exponentialValuationSubring w)
    (hdeltaPow : delta ^ d =
      unramifiedValuationRingValuationRingMap v w hExt u)
    (c : IsLocalRing.ResidueField (LubinTate.Valuations.exponentialValuationSubring v))
    (hc : tameResidueFieldMap v w hExt c =
      IsLocalRing.residue (LubinTate.Valuations.exponentialValuationSubring w) delta) :
    ∃ z : LubinTate.Valuations.exponentialValuationSubring v, z ^ d = u := by
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
  have huResidue : IsLocalRing.residue V u = c ^ d := by
    apply f.injective
    calc
      f (IsLocalRing.residue V u) = IsLocalRing.residue W (i u) :=
        IsLocalRing.ResidueField.map_residue i u
      _ = IsLocalRing.residue W (delta ^ d) := by rw [hdeltaPow]
      _ = (IsLocalRing.residue W delta) ^ d := map_pow _ _ _
      _ = (f c) ^ d := by rw [hc]
      _ = f (c ^ d) := (map_pow f c d).symm
  have hd0 : d ≠ 0 := by
    intro hd
    subst d
    have hpone : residueCharacteristic v = 1 := by
      simpa using hcop
    exact (residueCharacteristic_prime v hp).ne_one hpone
  have hc0 : c ≠ 0 := by
    intro hcZero
    have hu0 : IsLocalRing.residue V u = 0 := by
      rw [huResidue, hcZero, zero_pow hd0]
    exact (IsLocalRing.residue_ne_zero_iff_isUnit u).2 huUnit hu0
  obtain ⟨t, htResidue⟩ := IsLocalRing.residue_surjective c
  have htUnit : IsUnit t :=
    (IsLocalRing.residue_ne_zero_iff_isUnit t).1 (by
      rw [htResidue]
      exact hc0)
  let ut : Vˣ := htUnit.unit
  have hut : (ut : V) = t := htUnit.unit_spec
  let tInv : V := (ut⁻¹ : Vˣ)
  have htMulInv : t * tInv = 1 := by
    dsimp [tInv]
    rw [← hut]
    exact Units.mul_inv ut
  have htInvResidue : IsLocalRing.residue V tInv = c⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← htResidue, ← map_mul, mul_comm, htMulInv, map_one]
  let principal : V := u * tInv ^ d
  have hprincipalResidue : IsLocalRing.residue V principal = 1 := by
    dsimp [principal]
    rw [map_mul, map_pow, huResidue, htInvResidue, inv_pow,
      mul_inv_cancel₀ (pow_ne_zero d hc0)]
  obtain ⟨beta, hbetaPow, _hbetaResidue⟩ :=
    exists_pow_eq_of_residue_eq_one_of_coprime
      v hhens hp d hcop principal hprincipalResidue
  let z : V := t * beta
  refine ⟨z, ?_⟩
  dsimp [z]
  rw [mul_pow, hbetaPow]
  dsimp [principal]
  rw [← mul_assoc, mul_comm (t ^ d) u, mul_assoc]
  have hcancel : t ^ d * tInv ^ d = 1 := by
    rw [← mul_pow, htMulInv, one_pow]
  rw [hcancel, mul_one]

/-- If a base unit acquires a prime-to-`p` root in an extension with the same
residue field, it already has such a root in the Henselian base. -/
theorem exists_base_unit_root_of_target_root
    (v : LubinTate.Valuations.ExponentialValuation K)
    (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v).valuation)
    (hp : PositiveResidueCharacteristic v)
    (hresidue : Function.Surjective (tameResidueFieldMap v w hExt))
    (d : ℕ) (hcop : Nat.Coprime d (residueCharacteristic v))
    (u : LubinTate.Valuations.exponentialValuationSubring v)
    (huUnit : IsUnit u)
    (delta : LubinTate.Valuations.exponentialValuationSubring w)
    (hdeltaPow : delta ^ d =
      unramifiedValuationRingValuationRingMap v w hExt u) :
    ∃ z : LubinTate.Valuations.exponentialValuationSubring v, z ^ d = u := by
  obtain ⟨c, hc⟩ := hresidue
    (IsLocalRing.residue (LubinTate.Valuations.exponentialValuationSubring w) delta)
  exact exists_base_unit_root_of_target_root_of_residue_preimage
    v w hExt hhens hp d hcop u huUnit delta hdeltaPow c hc

end UnitRootDescent

section SingleRadicalDegree

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

@[reducible] local instance exponentialValueGroupQuotientAddCommGroupSingle
    (v : LubinTate.Valuations.ExponentialValuation K)
    (w : LubinTate.Valuations.ExponentialValuation L) :
    AddCommGroup (ExponentialValueGroupQuotient v w) :=
  QuotientAddGroup.Quotient.addCommGroup _

/-- Every target residue element which is a root of a separable polynomial
over the base residue field already comes from the base.  A purely
inseparable residue extension has this property, and surjectivity is a
stronger special case. -/
def SeparableResidueRootLifts
    (v : LubinTate.Valuations.ExponentialValuation K)
    (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a) : Prop :=
  let k := IsLocalRing.ResidueField (LubinTate.Valuations.exponentialValuationSubring v)
  let ell := IsLocalRing.ResidueField (LubinTate.Valuations.exponentialValuationSubring w)
  let f := tameResidueFieldMap v w hExt
  ∀ (y : ell) (P : Polynomial k), P.Separable →
    (P.map f).eval y = 0 → ∃ c : k, f c = y

/-- If a power of a nonzero element lies in the base, the order of its actual
value coset divides that exponent. -/
theorem exponentialValueCoset_addOrderOf_dvd_exponent_of_pow_eq_base
    (v : LubinTate.Valuations.ExponentialValuation K)
    (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (alpha : L) (halpha0 : alpha ≠ 0)
    (m : ℕ) (a : K) (hpow : alpha ^ m = algebraMap K L a) :
    addOrderOf (exponentialValueCoset v w alpha halpha0) ∣ m := by
  rw [addOrderOf_dvd_iff_nsmul_eq_zero]
  let Gamma := exponentialValueSubgroup w
  let H : AddSubgroup Gamma :=
    (exponentialValueSubgroup v).comap Gamma.subtype
  apply (QuotientAddGroup.eq_zero_iff _).2
  have ha0 : a ≠ 0 := by
    intro ha
    have hpow0 : alpha ^ m = 0 := by rw [hpow, ha, map_zero]
    exact pow_ne_zero m halpha0 hpow0
  change m • (w alpha).untop₀ ∈ exponentialValueSubgroup v
  refine ⟨a, ha0, ?_⟩
  have halphaTop : w alpha ≠ ⊤ :=
    LubinTate.Valuations.exponentialValuation_ne_top_of_ne_zero w halpha0
  have hvalPow : w (alpha ^ m) = m • w alpha := by
    clear hpow
    induction m with
    | zero => simp [LubinTate.Valuations.exponentialValuation_one]
    | succ m ih =>
        rw [pow_succ, w.map_mul, ih, succ_nsmul]
  rw [← hExt, ← hpow, hvalPow]
  rw [show w alpha = (((w alpha).untop₀ : ℝ) : WithTop ℝ) from
    (WithTop.coe_untop₀_of_ne_top halphaTop).symm]
  rw [WithTop.coe_nsmul]
  simp only [WithTop.untop₀_coe]

/-- If all separable target residue elements descend, a one-generator
prime-to-`p` radical extension has degree equal to the order of the
generator's value coset. -/
theorem finrank_eq_addOrderOf_valueCoset_of_single_radical_of_separableResidue
    [FiniteDimensional K L]
    (v : LubinTate.Valuations.ExponentialValuation K)
    (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v).valuation)
    (hp : PositiveResidueCharacteristic v)
    (hresidue : SeparableResidueRootLifts v w hExt)
    (alpha : L) (halpha0 : alpha ≠ 0)
    (hgen : IntermediateField.adjoin K ({alpha} : Set L) = ⊤)
    (m : ℕ) (hmpos : 0 < m)
    (hmcop : Nat.Coprime m (residueCharacteristic v))
    (a : K) (hpow : alpha ^ m = algebraMap K L a) :
    Module.finrank K L = addOrderOf (exponentialValueCoset v w alpha halpha0) := by
  classical
  let V := LubinTate.Valuations.exponentialValuationSubring v
  let W := LubinTate.Valuations.exponentialValuationSubring w
  let i := unramifiedValuationRingValuationRingMap v w hExt
  let : IsLocalHom i :=
    unramifiedValuationRingValuationRingMap_isLocalHom v w hExt
  let k := IsLocalRing.ResidueField V
  let ell := IsLocalRing.ResidueField W
  let f : k →+* ell := tameResidueFieldMap v w hExt
  change ∀ (y : ell) (P : Polynomial k), P.Separable →
    (P.map f).eval y = 0 → ∃ c : k, f c = y at hresidue
  let q := exponentialValueCoset v w alpha halpha0
  let n := addOrderOf q
  have hnpos : 0 < n :=
    exponentialValueGroupQuotient_addOrderOf_pos v w hExt q
  have hndvd : n ∣ m :=
    exponentialValueCoset_addOrderOf_dvd_exponent_of_pow_eq_base
      v w hExt alpha halpha0 m a hpow
  let d := m / n
  have hnm : n * d = m := by
    exact Nat.mul_div_cancel' hndvd
  have hdDvd : d ∣ m := by
    refine ⟨n, ?_⟩
    rw [mul_comm, hnm]
  have hdcop : Nat.Coprime d (residueCharacteristic v) :=
    Nat.Coprime.of_dvd_left hdDvd hmcop
  have hdpos : 0 < d := by
    exact Nat.div_pos (Nat.le_of_dvd hmpos hndvd) hnpos
  obtain ⟨b, hb0, hbValue⟩ :=
    exists_base_element_value_eq_pow_addOrderOf_valueCoset
      v w alpha halpha0
  have hbMap0 : algebraMap K L b ≠ 0 :=
    (map_ne_zero (algebraMap K L)).2 hb0
  let delta : L := alpha ^ n / algebraMap K L b
  have hdelta0 : delta ≠ 0 :=
    div_ne_zero (pow_ne_zero n halpha0) hbMap0
  have hdeltaValue : w delta = 0 := by
    obtain ⟨r, hr⟩ :=
      LubinTate.Valuations.exponentialValuation_exists_real_of_ne_zero w
        (pow_ne_zero n halpha0)
    have hbMapValue : w (algebraMap K L b) = (r : WithTop ℝ) := by
      rw [hExt, hbValue]
      exact hr
    have hbInvValue : w (algebraMap K L b)⁻¹ = ((-r : ℝ) : WithTop ℝ) :=
      LubinTate.Valuations.exponentialValuation_inv_value w hbMap0 hbMapValue
    dsimp [delta]
    rw [div_eq_mul_inv, w.map_mul, hr, hbInvValue]
    simp
  let uK : K := a / b ^ d
  have hbPow0 : b ^ d ≠ 0 := pow_ne_zero d hb0
  have huK0 : uK ≠ 0 := by
    dsimp [uK]
    apply div_ne_zero
    · intro ha
      have hzero : alpha ^ m = 0 := by rw [hpow, ha, map_zero]
      exact pow_ne_zero m halpha0 hzero
    · exact hbPow0
  have hdeltaPow : delta ^ d = algebraMap K L uK := by
    dsimp [delta, uK]
    rw [div_pow, ← pow_mul, hnm, hpow, map_div₀, map_pow]
  have huKValue : v uK = 0 := by
    have hmapValue : w (algebraMap K L uK) = 0 := by
      rw [← hdeltaPow]
      have hpowValue : w (delta ^ d) = d • w delta := by
        induction d with
        | zero => simp [LubinTate.Valuations.exponentialValuation_one]
        | succ d ih =>
            rw [pow_succ, w.map_mul, ih, succ_nsmul]
      rw [hpowValue, hdeltaValue, nsmul_zero]
    rw [hExt] at hmapValue
    exact hmapValue
  let uV : LubinTate.Valuations.exponentialValuationSubring v :=
    ⟨uK, by
      change (0 : WithTop ℝ) ≤ v uK
      rw [huKValue]⟩
  have huVUnit : IsUnit uV :=
    LubinTate.Valuations.isUnit_of_exponentialValuation_eq_zero v huKValue
  let deltaW : LubinTate.Valuations.exponentialValuationSubring w :=
    ⟨delta, by
      change (0 : WithTop ℝ) ≤ w delta
      rw [hdeltaValue]⟩
  have hdeltaPowW : deltaW ^ d =
      unramifiedValuationRingValuationRingMap v w hExt uV := by
    apply Subtype.ext
    exact hdeltaPow
  have hdCast : (d : k) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff k
      (residueCharacteristic v) d]
    exact (residueCharacteristic_prime v hp).coprime_iff_not_dvd.mp
      hdcop.symm
  have huResidue0 : IsLocalRing.residue V uV ≠ 0 :=
    (IsLocalRing.residue_ne_zero_iff_isUnit uV).2 huVUnit
  let Pdelta : Polynomial k :=
    Polynomial.X ^ d - Polynomial.C (IsLocalRing.residue V uV)
  have hPdeltaSep : Pdelta.Separable := by
    exact Polynomial.separable_X_pow_sub_C
      (IsLocalRing.residue V uV) hdCast huResidue0
  have hdeltaResiduePow :
      (IsLocalRing.residue W deltaW) ^ d =
        f (IsLocalRing.residue V uV) := by
    calc
      (IsLocalRing.residue W deltaW) ^ d =
          IsLocalRing.residue W (deltaW ^ d) :=
        (map_pow _ _ _).symm
      _ = IsLocalRing.residue W (i uV) := by rw [hdeltaPowW]
      _ = f (IsLocalRing.residue V uV) :=
        (IsLocalRing.ResidueField.map_residue i uV).symm
  have hPdeltaRoot :
      (Pdelta.map f).eval (IsLocalRing.residue W deltaW) = 0 := by
    rw [Polynomial.eval_map]
    simp only [Pdelta, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow]
    rw [Polynomial.eval₂_C]
    exact sub_eq_zero.mpr hdeltaResiduePow
  obtain ⟨cdelta, hcdelta⟩ := hresidue
    (IsLocalRing.residue W deltaW) Pdelta hPdeltaSep hPdeltaRoot
  obtain ⟨cV, hcPow⟩ :=
    exists_base_unit_root_of_target_root_of_residue_preimage
      v w hExt hhens hp d hdcop uV huVUnit deltaW hdeltaPowW
        cdelta hcdelta
  let c : K := (cV : K)
  have hcPowK : c ^ d = uK := by
    exact congrArg Subtype.val hcPow
  let b' : K := b * c
  have hb'0 : b' ≠ 0 := by
    apply mul_ne_zero hb0
    intro hc0
    have hu0 : uK = 0 := by rw [← hcPowK, hc0, zero_pow hdpos.ne']
    exact huK0 hu0
  have hb'Pow : b' ^ d = a := by
    dsimp [b']
    rw [mul_pow, hcPowK]
    dsimp [uK]
    field_simp
  let zeta : L := alpha ^ n / algebraMap K L b'
  have hb'Map0 : algebraMap K L b' ≠ 0 :=
    (map_ne_zero (algebraMap K L)).2 hb'0
  have hzeta0 : zeta ≠ 0 :=
    div_ne_zero (pow_ne_zero n halpha0) hb'Map0
  have hzetaPow : zeta ^ d = 1 := by
    dsimp [zeta]
    rw [div_pow, ← pow_mul, hnm, hpow, ← map_pow, hb'Pow]
    have ha0 : a ≠ 0 := by
      intro ha
      exact pow_ne_zero m halpha0 (by rw [hpow, ha, map_zero])
    exact div_self ((map_ne_zero (algebraMap K L)).2 ha0)
  have hzetaValue : w zeta = 0 := by
    have hb'Value : v b' = w (alpha ^ n) := by
      have hcValue : v c = 0 := by
        have hc0 : c ≠ 0 := by
          intro hc0
          exact huK0 (by rw [← hcPowK, hc0, zero_pow hdpos.ne'])
        have hcTop : v c ≠ ⊤ :=
          LubinTate.Valuations.exponentialValuation_ne_top_of_ne_zero v hc0
        have hpowValue : v (c ^ d) = d • v c := by
          induction d with
          | zero => simp [LubinTate.Valuations.exponentialValuation_one]
          | succ d ih =>
              rw [pow_succ, v.map_mul, ih, succ_nsmul]
        have hpowValueEq := congrArg v hcPowK
        rw [hpowValue, huKValue] at hpowValueEq
        rw [show v c = (((v c).untop₀ : ℝ) : WithTop ℝ) from
          (WithTop.coe_untop₀_of_ne_top hcTop).symm] at hpowValueEq
        have hrealNsmul : d • (v c).untop₀ = 0 := by
          apply WithTop.coe_eq_coe.mp
          simpa only [WithTop.coe_nsmul, WithTop.coe_zero] using hpowValueEq
        have hreal : (d : ℝ) * (v c).untop₀ = 0 := by
          simpa [nsmul_eq_mul] using hrealNsmul
        have hdReal : (d : ℝ) ≠ 0 := by positivity
        rw [show v c = (((v c).untop₀ : ℝ) : WithTop ℝ) from
          (WithTop.coe_untop₀_of_ne_top hcTop).symm]
        exact WithTop.coe_eq_zero.mpr
          ((mul_eq_zero.mp hreal).resolve_left hdReal)
      dsimp [b']
      rw [v.map_mul, hcValue, add_zero, hbValue]
    obtain ⟨r, hr⟩ :=
      LubinTate.Valuations.exponentialValuation_exists_real_of_ne_zero w
        (pow_ne_zero n halpha0)
    have hb'MapValue : w (algebraMap K L b') = (r : WithTop ℝ) := by
      rw [hExt, hb'Value]
      exact hr
    have hb'InvValue :
        w (algebraMap K L b')⁻¹ = ((-r : ℝ) : WithTop ℝ) :=
      LubinTate.Valuations.exponentialValuation_inv_value w hb'Map0 hb'MapValue
    dsimp [zeta]
    rw [div_eq_mul_inv, w.map_mul, hr, hb'InvValue]
    simp
  let zetaW : LubinTate.Valuations.exponentialValuationSubring w :=
    ⟨zeta, by
      change (0 : WithTop ℝ) ≤ w zeta
      rw [hzetaValue]⟩
  have hzetaPowW : zetaW ^ d = 1 := by
    apply Subtype.ext
    exact hzetaPow
  let Pzeta : Polynomial k := Polynomial.X ^ d - Polynomial.C 1
  have hPzetaSep : Pzeta.Separable := by
    exact Polynomial.separable_X_pow_sub_C (1 : k) hdCast one_ne_zero
  have hzetaResiduePow :
      (IsLocalRing.residue W zetaW) ^ d = 1 := by
    calc
      (IsLocalRing.residue W zetaW) ^ d =
          IsLocalRing.residue W (zetaW ^ d) :=
        (map_pow _ _ _).symm
      _ = 1 := by rw [hzetaPowW, map_one]
  have hPzetaRoot :
      (Pzeta.map f).eval (IsLocalRing.residue W zetaW) = 0 := by
    rw [Polynomial.eval_map]
    simp only [Pzeta, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow]
    rw [Polynomial.eval₂_C, map_one]
    exact sub_eq_zero.mpr hzetaResiduePow
  obtain ⟨czeta, hczeta⟩ := hresidue
    (IsLocalRing.residue W zetaW) Pzeta hPzetaSep hPzetaRoot
  obtain ⟨zV, hzetaBase⟩ :=
    exists_base_rootOfUnity_eq_of_residue_preimage
      v w hExt hhens hp d hdcop zetaW hzetaPowW czeta hczeta
  let z : K := (zV : K)
  have hzetaEq : zeta = algebraMap K L z := by
    exact congrArg Subtype.val hzetaBase.symm
  have halphaNPowBase : alpha ^ n = algebraMap K L (b' * z) := by
    have := congrArg (fun x : L ↦ x * algebraMap K L b') hzetaEq
    dsimp [zeta] at this
    field_simp [hb'Map0] at this
    simpa [map_mul, mul_comm] using this
  have hnle : n ≤ Module.finrank K L := by
    let : Finite (ExponentialValueGroupQuotient v w) :=
      exponentialValueGroupQuotient_finite_of_finiteDimensional v w hExt
    have hndvdE : n ∣ exponentialRamificationIndex v w :=
      exponentialValueGroupQuotient_addOrderOf_dvd_ramificationIndex
        v w hExt q
    have hepos : 0 < exponentialRamificationIndex v w := by
      unfold exponentialRamificationIndex
      exact Nat.card_pos
    have hne : n ≤ exponentialRamificationIndex v w :=
      Nat.le_of_dvd hepos hndvdE
    have hfund := ramificationInvariants_fundamental_inequality v w hExt
    have hfpos : 0 < exponentialResidueDegree v w hExt :=
      exponentialResidueDegree_pos_of_finiteDimensional v w hExt
    exact hne.trans ((Nat.le_mul_of_pos_right _ hfpos).trans hfund)
  have hfieldDegree :
      Module.finrank K L = (minpoly K alpha).natDegree := by
    calc
      Module.finrank K L = Module.finrank K
          (IntermediateField.adjoin K ({alpha} : Set L)) := by
        rw [hgen]
        simp
      _ = (minpoly K alpha).natDegree :=
        IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral alpha)
  have hminle : (minpoly K alpha).natDegree ≤ n := by
    let P : Polynomial K := Polynomial.X ^ n - Polynomial.C (b' * z)
    have hPmonic : P.Monic :=
      Polynomial.monic_X_pow_sub_C (b' * z) hnpos.ne'
    have hProot : Polynomial.aeval alpha P = 0 := by
      rw [Polynomial.aeval_def]
      dsimp [P]
      simp [halphaNPowBase]
    have hdvd := minpoly.dvd K alpha hProot
    have := Polynomial.natDegree_le_of_dvd hdvd hPmonic.ne_zero
    calc
      (minpoly K alpha).natDegree ≤ P.natDegree := this
      _ = n := Polynomial.natDegree_X_pow_sub_C
  exact le_antisymm (hfieldDegree.trans_le hminle) hnle

/-- A one-generator prime-to-`p` radical extension with unchanged residue
field has degree equal to the order of the generator's value coset. -/
theorem finrank_eq_addOrderOf_valueCoset_of_single_radical
    [FiniteDimensional K L]
    (v : LubinTate.Valuations.ExponentialValuation K)
    (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v).valuation)
    (hp : PositiveResidueCharacteristic v)
    (hresidue : Function.Surjective (tameResidueFieldMap v w hExt))
    (alpha : L) (halpha0 : alpha ≠ 0)
    (hgen : IntermediateField.adjoin K ({alpha} : Set L) = ⊤)
    (m : ℕ) (hmpos : 0 < m)
    (hmcop : Nat.Coprime m (residueCharacteristic v))
    (a : K) (hpow : alpha ^ m = algebraMap K L a) :
    Module.finrank K L = addOrderOf (exponentialValueCoset v w alpha halpha0) := by
  have hlifts : SeparableResidueRootLifts v w hExt := by
    intro y P _hP _hy
    exact hresidue y
  exact
    finrank_eq_addOrderOf_valueCoset_of_single_radical_of_separableResidue
      v w hExt hhens hp hlifts alpha halpha0 hgen
      m hmpos hmcop a hpow

/-- Under descent of separable residue elements, a one-generator
prime-to-`p` radical extension is totally ramified: its actual value-group
index equals its field degree. -/
theorem exponentialRamificationIndex_eq_finrank_of_single_radical_of_separableResidue
    [FiniteDimensional K L]
    (v : LubinTate.Valuations.ExponentialValuation K)
    (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v).valuation)
    (hp : PositiveResidueCharacteristic v)
    (hresidue : SeparableResidueRootLifts v w hExt)
    (alpha : L) (halpha0 : alpha ≠ 0)
    (hgen : IntermediateField.adjoin K ({alpha} : Set L) = ⊤)
    (m : ℕ) (hmpos : 0 < m)
    (hmcop : Nat.Coprime m (residueCharacteristic v))
    (a : K) (hpow : alpha ^ m = algebraMap K L a) :
    exponentialRamificationIndex v w = Module.finrank K L := by
  let q := exponentialValueCoset v w alpha halpha0
  have hdegree : Module.finrank K L = addOrderOf q :=
    finrank_eq_addOrderOf_valueCoset_of_single_radical_of_separableResidue
      v w hExt hhens hp hresidue alpha halpha0 hgen
      m hmpos hmcop a hpow
  have horderDvd : addOrderOf q ∣ exponentialRamificationIndex v w :=
    exponentialValueGroupQuotient_addOrderOf_dvd_ramificationIndex
      v w hExt q
  have hepos : 0 < exponentialRamificationIndex v w := by
    let : Finite (ExponentialValueGroupQuotient v w) :=
      exponentialValueGroupQuotient_finite_of_finiteDimensional v w hExt
    unfold exponentialRamificationIndex
    exact Nat.card_pos
  have hdegreeLe : Module.finrank K L ≤ exponentialRamificationIndex v w := by
    rw [hdegree]
    exact Nat.le_of_dvd hepos horderDvd
  have hfund := ramificationInvariants_fundamental_inequality v w hExt
  have hfpos : 0 < exponentialResidueDegree v w hExt :=
    exponentialResidueDegree_pos_of_finiteDimensional v w hExt
  have heLe : exponentialRamificationIndex v w ≤ Module.finrank K L :=
    (Nat.le_mul_of_pos_right _ hfpos).trans hfund
  exact Nat.le_antisymm heLe hdegreeLe

/-- Under descent of separable residue elements, a single prime-to-`p`
radical creates no residue-field extension. -/
theorem tameResidueFieldMap_surjective_of_single_radical_of_separableResidue
    [FiniteDimensional K L]
    (v : LubinTate.Valuations.ExponentialValuation K)
    (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v).valuation)
    (hp : PositiveResidueCharacteristic v)
    (hresidue : SeparableResidueRootLifts v w hExt)
    (alpha : L) (halpha0 : alpha ≠ 0)
    (hgen : IntermediateField.adjoin K ({alpha} : Set L) = ⊤)
    (m : ℕ) (hmpos : 0 < m)
    (hmcop : Nat.Coprime m (residueCharacteristic v))
    (a : K) (hpow : alpha ^ m = algebraMap K L a) :
    Function.Surjective (tameResidueFieldMap v w hExt) := by
  have he :=
    exponentialRamificationIndex_eq_finrank_of_single_radical_of_separableResidue
      v w hExt hhens hp hresidue alpha halpha0 hgen
      m hmpos hmcop a hpow
  have hfund := ramificationInvariants_fundamental_inequality v w hExt
  rw [he] at hfund
  have hdegreePos : 0 < Module.finrank K L := Module.finrank_pos
  have hfLe : exponentialResidueDegree v w hExt ≤ 1 := by
    nlinarith
  let V := LubinTate.Valuations.exponentialValuationSubring v
  let W := LubinTate.Valuations.exponentialValuationSubring w
  let i := unramifiedValuationRingValuationRingMap v w hExt
  let : IsLocalHom i :=
    unramifiedValuationRingValuationRingMap_isLocalHom v w hExt
  let k := IsLocalRing.ResidueField V
  let ell := IsLocalRing.ResidueField W
  let f : k →+* ell := tameResidueFieldMap v w hExt
  let : Algebra k ell := f.toAlgebra
  let algebraModule : Module k ell :=
    (inferInstance : Algebra k ell).toModule
  let : Algebra V W := i.toAlgebra
  let residueModule : Module k ell :=
    @IsLocalRing.ResidueField.instModule
      V W _ _ _ _ (i.toAlgebra) inferInstance
  have hfinite :
      @FiniteDimensional k ell _ _ residueModule :=
    residueExtension_finiteDimensional_of_finiteDimensional v w hExt
  have hmodule : residueModule = algebraModule := by
    apply Module.ext
    funext r x
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective r
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
    rfl
  have hfiniteAlgebra :
      @FiniteDimensional k ell _ _ algebraModule := by
    rw [← hmodule]
    exact hfinite
  let : Module k ell := algebraModule
  let : FiniteDimensional k ell := hfiniteAlgebra
  have hdegreeFinrank :
      exponentialResidueDegree v w hExt = Module.finrank k ell := by
    let ib := exponentialValuationRingMap v w hExt
    let : IsLocalHom ib :=
      exponentialValuationRingMap_isLocalHom v w hExt
    let : Algebra V W := ib.toAlgebra
    let residueModule : Module k ell :=
      @IsLocalRing.ResidueField.instModule
        V W _ _ _ _ (ib.toAlgebra) inferInstance
    have hResidueModule : residueModule = algebraModule := by
      apply Module.ext
      funext r x
      obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective r
      obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
      rfl
    change @Module.finrank k ell _ _ residueModule =
      @Module.finrank k ell _ _ algebraModule
    rw [hResidueModule]
  have hfpos : 0 < exponentialResidueDegree v w hExt :=
    exponentialResidueDegree_pos_of_finiteDimensional v w hExt
  have hf : exponentialResidueDegree v w hExt = 1 :=
    Nat.le_antisymm hfLe (Nat.succ_le_of_lt hfpos)
  change Function.Surjective f
  intro y
  have hfinrank : Module.finrank k ell = 1 :=
    hdegreeFinrank.symm.trans hf
  obtain ⟨c, hc⟩ :=
    (finrank_eq_one_iff_of_nonzero' (1 : ell) one_ne_zero).mp
      hfinrank y
  refine ⟨c, ?_⟩
  change algebraMap k ell c = y
  simpa [Algebra.smul_def] using hc

/-- A one-generator prime-to-`p` radical extension with unchanged residue
field is totally ramified. -/
theorem exponentialRamificationIndex_eq_finrank_of_single_radical
    [FiniteDimensional K L]
    (v : LubinTate.Valuations.ExponentialValuation K)
    (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v).valuation)
    (hp : PositiveResidueCharacteristic v)
    (hresidue : Function.Surjective (tameResidueFieldMap v w hExt))
    (alpha : L) (halpha0 : alpha ≠ 0)
    (hgen : IntermediateField.adjoin K ({alpha} : Set L) = ⊤)
    (m : ℕ) (hmpos : 0 < m)
    (hmcop : Nat.Coprime m (residueCharacteristic v))
    (a : K) (hpow : alpha ^ m = algebraMap K L a) :
    exponentialRamificationIndex v w = Module.finrank K L := by
  have hlifts : SeparableResidueRootLifts v w hExt := by
    intro y P _hP _hy
    exact hresidue y
  exact
    exponentialRamificationIndex_eq_finrank_of_single_radical_of_separableResidue
      v w hExt hhens hp hlifts alpha halpha0 hgen
      m hmpos hmcop a hpow

end SingleRadicalDegree

end Valuations
end AlgebraicNumberTheory

end
