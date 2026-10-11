/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.EisensteinIntegralClosure
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Extensions
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Henselian
import Nyll.ValuedFieldTheory.Valuation.Henselian.AlgebraicExtensionUniqueness
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.RingTheory.Adjoin.Polynomial.Basic
import Mathlib.RingTheory.Ideal.Prime
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.PowerBasis

/-!
# Residue fields of Eisenstein root extensions

In an actual extension of a Henselian discrete valuation, an Eisenstein
power-basis generator generates the target valuation ring. Its residue is
zero, so every target residue is the image of a constant coefficient from
the base valuation ring.
-/

namespace ValuationTheory.DiscreteValuationField

open scoped Polynomial

universe u v w x

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]

private theorem residue_eq_zero_of_weaklyEisenstein_root
    (base : DVF.{u, v} K) (target : DVF.{w, x} L)
    [base.valuation.HasExtension target.valuation]
    (f : base.valuationSubring[X]) (hf : f.Monic)
    (hE : f.IsWeaklyEisensteinAt base.maximalIdeal)
    (a : target.valuationSubring)
    (ha : (f.map (ValuedExtension.integerMap base target)).IsRoot a) :
    target.residueMap a = 0 := by
  have hpow :=
    (hE.map (ValuedExtension.integerMap base target)).pow_natDegree_le_of_root_of_monic_mem
      ha (hf.map (ValuedExtension.integerMap base target))
      (f.map (ValuedExtension.integerMap base target)).natDegree le_rfl
  apply (target.residue_eq_zero_iff a).mpr
  exact (IsLocalRing.maximalIdeal.isMaximal target.valuationSubring).isPrime.mem_of_pow_mem
    (f.map (ValuedExtension.integerMap base target)).natDegree
    (ValuedExtension.maximalIdeal_map_integerMap_le base target hpow)

/-- An Eisenstein power-basis extension of a Henselian DVF has surjective
actual residue-field map. The valuation ring and its polynomial
representatives are generated from Henselianity and the Eisenstein condition. -/
theorem residueMap_surjective_of_minpoly_isEisensteinAt
    (base : HenselianDVF.{u, v} K) (target : DVF.{w, x} L)
    [base.valuation.HasExtension target.valuation]
    (B : PowerBasis K L)
    (hE : (minpoly base.valuationSubring B.gen).IsEisensteinAt base.maximalIdeal) :
    Function.Surjective (ValuedExtension.residueMap base.toDVF target) := by
  classical
  have : FiniteDimensional K L := B.finite
  have : IsDiscreteValuationRing base.valuationSubring :=
    base.toDVF.valuationSubring_isDiscreteValuationRing
  have hIC : target.valuation.valuationSubring.toSubring =
      (integralClosure base.valuationSubring L).toSubring := by
    have : base.valuation.valuationSubring.valuation.HasExtension target.valuation :=
      ⟨(_root_.Valuation.isEquiv_valuation_valuationSubring base.valuation).symm.trans
        (_root_.Valuation.HasExtension.val_isEquiv_comap
          (vR := base.valuation) (vA := target.valuation))⟩
    exact ValuationTheory.Henselian.valuationSubring_eq_integralClosure_of_henselianRing
      base.valuation.valuationSubring target.valuation
  have hIntegral (z : L) :
      z ∈ target.valuation.valuationSubring ↔ IsIntegral base.valuationSubring z := by
    change z ∈ target.valuation.valuationSubring.toSubring ↔ _
    rw [hIC]
    exact mem_integralClosure_iff base.valuationSubring L
  have hB : IsIntegral base.valuationSubring B.gen := minpoly.ne_zero_iff.mp (by
    intro hzero
    apply hE.leading
    rw [hzero, Polynomial.leadingCoeff_zero]
    exact base.maximalIdeal.zero_mem)
  let a : target.valuationSubring := ⟨B.gen, (hIntegral B.gen).mpr hB⟩
  have hEval (f : base.valuationSubring[X]) :
      (((f.map (ValuedExtension.integerMap base.toDVF target)).eval a :
          target.valuationSubring) : L) =
        Polynomial.aeval B.gen f := by
    change algebraMap target.valuationSubring L
      ((f.map (algebraMap base.valuationSubring target.valuationSubring)).eval a) = _
    rw [Polynomial.eval_map_algebraMap]
    exact (Polynomial.aeval_algHom_apply
      (IsScalarTower.toAlgHom base.valuationSubring target.valuationSubring L) a f).symm
  have hroot :
      ((minpoly base.valuationSubring B.gen).map
        (ValuedExtension.integerMap base.toDVF target)).IsRoot a := by
    change ((minpoly base.valuationSubring B.gen).map
      (ValuedExtension.integerMap base.toDVF target)).eval a = 0
    apply Subtype.ext
    change ((((minpoly base.valuationSubring B.gen).map
      (ValuedExtension.integerMap base.toDVF target)).eval a : target.valuationSubring) : L) = 0
    rw [hEval]
    exact minpoly.aeval base.valuationSubring B.gen
  have hred : target.residueMap a = 0 :=
    residue_eq_zero_of_weaklyEisenstein_root base.toDVF target
      (minpoly base.valuationSubring B.gen) (minpoly.monic hB)
      hE.isWeaklyEisensteinAt a hroot
  intro y
  obtain ⟨z, rfl⟩ := target.residue_surjective y
  have hz : (z : L) ∈ Algebra.adjoin base.valuationSubring ({B.gen} : Set L) :=
    mem_adjoin_of_isIntegral_of_minpoly_isEisensteinAt B hE
      ((hIntegral (z : L)).mp z.property)
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hz
  obtain ⟨q, hq⟩ := hz
  have hqEval : (q.map (ValuedExtension.integerMap base.toDVF target)).eval a = z := by
    apply Subtype.ext
    rw [hEval]
    exact hq
  refine ⟨base.toDVF.residueMap (q.coeff 0), ?_⟩
  rw [ValuedExtension.residueMap_residue]
  calc
    target.residueMap (ValuedExtension.integerMap base.toDVF target (q.coeff 0)) =
        ((q.map (ValuedExtension.integerMap base.toDVF target)).map target.residueMap).eval
          (target.residueMap a) := by
      rw [hred, ← Polynomial.coeff_zero_eq_eval_zero,
        Polynomial.coeff_map, Polynomial.coeff_map]
    _ = target.residueMap ((q.map (ValuedExtension.integerMap base.toDVF target)).eval a) :=
      Polynomial.eval_map_apply target.residueMap a
    _ = target.residueMap z := congrArg target.residueMap hqEval

end ValuationTheory.DiscreteValuationField
