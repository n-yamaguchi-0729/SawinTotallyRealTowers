/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.FieldTheory.FiniteFrobeniusTower
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.Algebra.Polynomial.Splits

/-!
# Fixed values of powers of finite-field Frobenius

The first theorem is relocated, with its existing declaration name, from
`ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueAlgebraicClosureDegree`.
The finite-field tower theorem identifies the fixed values of each degree power
with the image of the specified finite extension.
-/

@[expose] public section

namespace LocalClassFieldTheory

open Polynomial

universe u v

/-- In an algebraic extension of a finite field, the fixed points of arithmetic
Frobenius are exactly the image of the base field. -/
theorem mem_range_algebraMap_iff_frobenius_fixed_in
    (k : Type u) [Field k] [Fintype k]
    (Omega : Type v) [Field Omega] [Algebra k Omega]
    [Algebra.IsAlgebraic k Omega] (x : Omega) :
    x ∈ Set.range (algebraMap k Omega) ↔
      FiniteField.frobeniusAlgEquivOfAlgebraic k Omega x = x := by
  constructor
  · rintro ⟨a, rfl⟩
    simp only [FiniteField.coe_frobeniusAlgEquivOfAlgebraic]
    rw [← map_pow, FiniteField.pow_card]
  · intro hx
    have hxpow : x ^ Fintype.card k = x := by
      simpa only [FiniteField.coe_frobeniusAlgEquivOfAlgebraic] using hx
    let p : k[X] := X ^ Fintype.card k - X
    have hpne : p ≠ 0 :=
      FiniteField.X_pow_card_sub_X_ne_zero k Fintype.one_lt_card
    have hxroot : x ∈ p.rootSet Omega := by
      rw [Polynomial.mem_rootSet_of_ne hpne]
      simp only [p, map_sub, map_pow, aeval_X, hxpow, sub_self]
    have hsplits : (p.map (algebraMap k k)).Splits := by
      simpa only [p] using (FiniteField.isSplittingField_sub k k).splits
    have himage := hsplits.image_rootSet (Algebra.ofId k Omega)
    rw [← himage] at hxroot
    rcases hxroot with ⟨a, _ha, hax⟩
    exact ⟨a, hax⟩

end LocalClassFieldTheory

namespace FiniteField

variable (k E Ω : Type*) [Field k] [Fintype k] [Field E] [Finite E]
    [Algebra k E] [Field Ω] [Algebra k Ω] [Algebra E Ω] [IsScalarTower k E Ω]
    [Algebra.IsAlgebraic k Ω]

/-- The image of a specified finite constant extension is exactly the fixed
field of the corresponding power of the original arithmetic Frobenius. -/
theorem mem_range_algebraMap_iff_frobenius_pow_fixed
    (m : ℕ) (hm : Module.finrank k E = m) (x : Ω) :
    x ∈ Set.range (algebraMap E Ω) ↔
      (frobeniusAlgEquivOfAlgebraic k Ω ^ m) x = x := by
  classical
  have : Fintype E := Fintype.ofFinite E
  have : Algebra.IsAlgebraic E Ω := Algebra.IsAlgebraic.tower_top (K := k) E
  rw [LocalClassFieldTheory.mem_range_algebraMap_iff_frobenius_fixed_in E Ω x]
  change (frobeniusAlgEquivOfAlgebraic E Ω).restrictScalars k x = x ↔ _
  rw [frobeniusAlgEquiv_restrictScalars k E Ω, hm]

end FiniteField
