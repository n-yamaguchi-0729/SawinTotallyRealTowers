/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.TorsionReductionPrimary
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FinitePrimePowerRoots
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.CharP.Reduced

/-!
# Finiteness of all roots of unity in mixed characteristic

The actual torsion-reduction kernel is a p-group. Its elements inject into
the finite set of p-power roots of the original field. Finiteness of the
residue-field torsion then gives finiteness of all field torsion, without
assuming the valuation is Henselian or complete.
-/

namespace ValuationTheory.DiscreteValuationField.DVF

universe u v

/-- Finite residue torsion implies finite field torsion for any
mixed-characteristic discrete valuation. -/
theorem finite_torsion_of_finite_residueTorsion_mixedChar
    {K : Type u} [Field K] [CharZero K] (D : DVF.{u, v} K)
    (p : ℕ) [Fact p.Prime] [CharP D.residueField p]
    [Finite (CommGroup.torsion D.residueFieldˣ)] :
    Finite (CommGroup.torsion Kˣ) := by
  have hf : Set.Finite {z : K | ∃ n : ℕ, z ^ (p ^ n) = 1} :=
    D.finite_primePowerRoots p
  have : Finite {z : K | ∃ n : ℕ, z ^ (p ^ n) = 1} := hf.to_subtype
  let i : D.torsionReduction.ker → {z : K | ∃ n : ℕ, z ^ (p ^ n) = 1} :=
    fun z => ⟨(((z : CommGroup.torsion Kˣ) : Kˣ) : K), by
      obtain ⟨n, hn⟩ := D.torsionReduction_ker_isPGroup p z
      refine ⟨n, ?_⟩
      exact congrArg
        (fun a : D.torsionReduction.ker => (((a : CommGroup.torsion Kˣ) : Kˣ) : K)) hn⟩
  have hi : Function.Injective i := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    exact congrArg (fun z : {z : K | ∃ n : ℕ, z ^ (p ^ n) = 1} => (z : K)) hab
  have : Finite D.torsionReduction.ker := Finite.of_injective i hi
  exact D.torsionReduction.finite_iff_finite_ker_range.mpr ⟨inferInstance, inferInstance⟩

/-- In equal positive characteristic the reduction kernel has no
nontrivial torsion, so finite residue torsion implies finite field torsion. -/
theorem finite_torsion_of_finite_residueTorsion_charP
    {K : Type u} [Field K] (D : DVF.{u, v} K)
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [Finite (CommGroup.torsion D.residueFieldˣ)] :
    Finite (CommGroup.torsion Kˣ) := by
  have : CharP D.residueField p :=
    (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr (by
      rw [← map_natCast D.residueMap p, CharP.cast_eq_zero D.valuationSubring p, map_zero])
  have hinj : Function.Injective D.torsionReduction := by
    apply D.torsionReduction.ker_eq_bot_iff.mp
    apply bot_unique
    intro z hz
    change z = 1
    let zker : D.torsionReduction.ker := ⟨z, hz⟩
    obtain ⟨a, ha⟩ := D.torsionReduction_ker_isPGroup p zker
    have hpow : ((z : Kˣ) : K) ^ (p ^ a) = 1 :=
      congrArg
        (fun b : D.torsionReduction.ker => (((b : CommGroup.torsion Kˣ) : Kˣ) : K)) ha
    apply Subtype.ext
    apply Units.ext
    have heq := (ExpChar.pow_prime_pow_mul_eq_one_iff p a 1 (((z : Kˣ) : K))).mp
      (by simpa only [mul_one] using hpow)
    simpa only [pow_one, OneMemClass.coe_one, Units.val_one] using heq
  exact Finite.of_injective D.torsionReduction hinj

end ValuationTheory.DiscreteValuationField.DVF
