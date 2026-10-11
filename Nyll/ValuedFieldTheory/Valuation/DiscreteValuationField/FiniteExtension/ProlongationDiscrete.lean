/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Localization
import Nyll.ValuedFieldTheory.Valuation.DiscreteEquivalence
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.Algebra.CharP.Algebra

/-!
# Discrete prolongations to finite separable extensions

Finite separable field extensions carry discrete prolongations of the original
valuation. These can use the original value-group universe and preserve the
residue characteristic.
-/

namespace ValuationTheory.DiscreteValuationField

universe u v w z

/-- Every prolongation to a finite separable extension remains discrete of rank one.
The integral closure localized at the prolongation's center supplies its DVR. -/
theorem DVF.isRankOneDiscrete_of_finite_separable
    {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (base : DVF.{u, v} K) {Γ : Type z} [LinearOrderedCommGroupWithZero Γ]
    (vL : _root_.Valuation L Γ) [base.valuation.HasExtension vL] :
    vL.IsRankOneDiscrete := by
  let B := FiniteExtensionLocalization.Normalization (L := L) base
  have : IsDedekindDomain B := FiniteExtensionLocalization.normalization_isDedekindDomain base
  have : IsFractionRing B L := FiniteExtensionLocalization.normalization_isFractionRing base
  have hB (b : B) : vL (b : L) ≤ 1 :=
    ((_root_.Valuation.valuationSubring.integers vL).isIntegral_iff_v_le_one).mp
      b.property.tower_top
  let f : B →+* vL.valuationSubring :=
    { toFun := fun b => ⟨b, hB b⟩
      map_zero' := rfl
      map_one' := rfl
      map_add' := fun _ _ => rfl
      map_mul' := fun _ _ => rfl }
  let P : Ideal B := (IsLocalRing.maximalIdeal vL.valuationSubring).comap f
  have : P.IsPrime := Ideal.comap_isPrime f _
  obtain ⟨x, hx0, hx1⟩ :=
    (_root_.Valuation.isNontrivial_iff_exists_lt_one base.valuation).mp inferInstance
  have hxL : vL (algebraMap K L x) < 1 :=
    (_root_.Valuation.HasExtension.val_map_lt_one_iff (vR := base.valuation) (vA := vL) x).mpr hx1
  have hP : P ≠ ⊥ := by
    let b : B := algebraMap base.valuationSubring B ⟨x, hx1.le⟩
    have hb : b ∈ P := by
      change f b ∈ IsLocalRing.maximalIdeal vL.valuationSubring
      exact _root_.Valuation.Integer.not_isUnit_iff_valuation_lt_one.mpr hxL
    intro heq
    have hb0 : b = 0 := by simpa only [heq, Ideal.mem_bot] using hb
    have heqL : algebraMap K L x = 0 := congrArg (fun c : B => (c : L)) hb0
    exact hx0 ((map_eq_zero_iff (algebraMap K L) (algebraMap K L).injective).mp heqL)
  let A := Localization.subalgebra.ofField L P.primeCompl P.primeCompl_le_nonZeroDivisors
  have : IsDiscreteValuationRing A :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hP A
  let vA : _root_.Valuation L (WithZero (Multiplicative ℤ)) :=
    (IsDiscreteValuationRing.maximalIdeal A).valuation L
  have hA (a : A) : vL (a : L) ≤ 1 := by
    obtain ⟨b, s, hs, heq⟩ := a.property
    have hsunit : IsUnit (f s) := by
      exact not_not.mp hs
    have hsval : vL (s : L) = 1 :=
      ((_root_.Valuation.valuationSubring.integers vL).isUnit_iff_valuation_eq_one).mp hsunit
    change vL (a : L) ≤ 1
    rw [heq, map_mul, map_inv₀]
    change vL (b : L) * (vL (s : L))⁻¹ ≤ 1
    rw [hsval, inv_one, mul_one]
    exact hB b
  have hle : vA.valuationSubring ≤ vL.valuationSubring := by
    intro y hy
    obtain ⟨a, ha⟩ := IsDiscreteValuationRing.exists_lift_of_le_one (A := A) hy
    exact ha ▸ hA a
  have htop : vL.valuationSubring ≠ ⊤ := by
    intro h
    have hinv : (algebraMap K L x)⁻¹ ∈ vL.valuationSubring := h ▸ Set.mem_univ _
    have hinvle : vL ((algebraMap K L x)⁻¹) ≤ 1 := hinv
    have hxval : 0 < vL (algebraMap K L x) :=
      zero_lt_iff.mpr ((map_ne_zero vL).mpr ((map_ne_zero (algebraMap K L)).mpr hx0))
    rw [map_inv₀, inv_le_one₀ hxval] at hinvle
    exact (not_le_of_gt hxL) hinvle
  have heq : vA.valuationSubring = vL.valuationSubring :=
    ValuationSubring.eq_of_le_of_ne_top vA.valuationSubring hle htop
  exact ((_root_.Valuation.isEquiv_iff_valuationSubring vA vL).mpr heq).isRankOneDiscrete

/-- A finite separable extension admits a discrete valuation in the original
value-group universe. -/
theorem DVF.exists_extension_on_valueGroup
    {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (base : DVF.{u, v} K) :
    ∃ vL : _root_.Valuation L base.ValueGroup,
      vL.IsRankOneDiscrete ∧ base.valuation.HasExtension vL := by
  let source := FiniteExtensionLocalization.dvf (L := L) base
  let e := _root_.Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt base.valuation
  let f : WithZero (Multiplicative ℤ) →*₀o base.ValueGroup :=
    { toMonoidWithZeroHom := MonoidWithZeroHom.ValueGroup₀.embedding.comp
        (e.symm : WithZero (Multiplicative ℤ) →*₀ base.valuation.ValueGroup₀)
      monotone' := by
        intro a b hab
        change MonoidWithZeroHom.ValueGroup₀.embedding (e.symm a) ≤
          MonoidWithZeroHom.ValueGroup₀.embedding (e.symm b)
        exact (MonoidWithZeroHom.ValueGroup₀.embedding_strictMono
          (f := base.valuation.toMonoidWithZeroHom)).monotone
            (e.symm.toOrderIso.monotone hab) }
  have hf : Function.Injective f :=
    MonoidWithZeroHom.ValueGroup₀.embedding_injective.comp e.symm.injective
  have heq : (source.valuation.map f).IsEquiv source.valuation :=
    source.valuation.isEquiv_map_self_of_strictMono f hf
  refine ⟨source.valuation.map f, heq.symm.isRankOneDiscrete, ?_⟩
  have : base.valuation.HasExtension source.valuation :=
    FiniteExtensionLocalization.dvf_hasExtension base
  exact ⟨(_root_.Valuation.HasExtension.val_isEquiv_comap
    (vR := base.valuation) (vA := source.valuation)).trans
      (heq.symm.comap (algebraMap K L))⟩

/-- A finite separable extension carries a discrete prolongation with the same
residue characteristic. -/
theorem DVF.exists_extension_residueChar
    {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (base : DVF.{u, v} K) (p : ℕ) [CharP base.residueField p] :
    ∃ target : DVF.{w,v} L, base.valuation.HasExtension target.valuation ∧
      CharP target.residueField p := by
  obtain ⟨vL, hdisc, hExt⟩ := base.exists_extension_on_valueGroup (L := L)
  let target : DVF.{w,v} L := { ValueGroup := base.ValueGroup, valuation := vL }
  have : base.valuation.HasExtension target.valuation := hExt
  exact ⟨target, hExt,
    (Algebra.charP_iff base.residueField target.residueField p).mp inferInstance⟩

end ValuationTheory.DiscreteValuationField
