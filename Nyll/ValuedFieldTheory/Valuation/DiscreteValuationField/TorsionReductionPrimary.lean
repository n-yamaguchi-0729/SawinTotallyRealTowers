/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.PrincipalUnitTorsion
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.HenselianTorsionRoots
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.CharP.Defs
import Mathlib.GroupTheory.PGroup

/-!
# The actual torsion-reduction kernel is primary for the residue prime

Factor a finite annihilating exponent as p^a times an integer prime to p.
A kernel element is an actual principal unit. Its p^a-th power is killed
by the prime-to-p factor, hence is one by the geometric-sum argument.
This needs neither Henselianity nor characteristic zero of the field.
-/

namespace ValuationTheory.DiscreteValuationField.DVF

universe u v

variable {K : Type u} [Field K]

/-- The kernel of the canonical reduction map on all roots of unity is a
p-group in residue characteristic p, for an arbitrary discrete valuation field. -/
theorem torsionReduction_ker_isPGroup (D : DVF.{u, v} K)
    (p : ℕ) [Fact p.Prime] [CharP D.residueField p] :
    IsPGroup p D.torsionReduction.ker := by
  intro x
  let A : ValuationSubring K := D.valuation.valuationSubring
  let z : Kˣ := x.val.val
  obtain ⟨n, hn, hzn⟩ := x.val.property.exists_pow_eq_one
  have hzunit : z ∈ A.unitGroup := by
    apply (_root_.Valuation.mem_unitGroup_iff (v := D.valuation) (x := z)).mpr
    have hvalpow : D.valuation (z : K) ^ n = 1 := by
      rw [← map_pow]
      have hzpow : (z : K) ^ n = 1 :=
        congrArg (fun t : Kˣ => (t : K)) hzn
      rw [hzpow, map_one]
    exact (pow_eq_one_iff_of_nonneg zero_le hn.ne').mp hvalpow
  let zA : A.unitGroup := ⟨z, hzunit⟩
  have hred : A.unitGroupToResidueFieldUnits zA = 1 :=
    congrArg (fun t : CommGroup.torsion D.residueFieldˣ => (t : D.residueFieldˣ))
      x.property
  have hzprincipal : z ∈ A.principalUnitGroup := by
    have hker : zA ∈ A.unitGroupToResidueFieldUnits.ker := hred
    rw [A.ker_unitGroupToResidueFieldUnits] at hker
    exact hker
  let w : A.principalUnitGroup := ⟨z, hzprincipal⟩
  have hwn : w ^ n = 1 := Subtype.ext hzn
  obtain ⟨a, m, hm, hfactor⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd hn.ne' p (Fact.out : p.Prime).ne_one
  have hmres : (m : IsLocalRing.ResidueField A) ≠ 0 :=
    (CharP.cast_eq_zero_iff (IsLocalRing.ResidueField A) p m).not.mpr hm
  have hwprime : w ^ (p ^ a) = 1 :=
    A.principalUnit_eq_one_of_pow_eq_one_of_residue_natCast_ne_zero
      (w ^ (p ^ a)) m hmres (by rw [← pow_mul, ← hfactor]; exact hwn)
  refine ⟨a, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun t : A.principalUnitGroup => (t : Kˣ)) hwprime

end ValuationTheory.DiscreteValuationField.DVF
