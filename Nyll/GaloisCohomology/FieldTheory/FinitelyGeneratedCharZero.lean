/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.GaloisCohomology.FieldTheory.FiniteAlgebraicConstants
import Nyll.GaloisCohomology.FieldTheory.IntegralClosureTorsion
import Mathlib.NumberTheory.NumberField.Units.Basic
import Mathlib.FieldTheory.PrimeField

/-!
# Roots of unity in finitely generated fields of characteristic zero
-/

namespace FieldTheory

universe u v

/-- Finitely generated fields of characteristic zero are finitely generated
extensions of the rational numbers. -/
theorem essFiniteType_rat_of_fg
    (K : Type u) [Field K] [CharZero K] (hfg : Field.FG K) :
    Algebra.EssFiniteType ℚ K := by
  let F := (⊥ : Subfield K)
  have hs : Function.Surjective (algebraMap ℚ F) := by
    intro x
    have hx : (x : K) ∈ (algebraMap ℚ K).fieldRange := by
      rw [← Subfield.bot_eq_of_charZero]
      exact x.property
    obtain ⟨r, hr⟩ := hx
    exact ⟨r, Subtype.ext hr⟩
  have : Module.Finite ℚ F := Module.Finite.of_surjective (Algebra.linearMap ℚ F) hs
  have : Algebra.EssFiniteType ℚ F := Algebra.EssFiniteType.of_finiteType ℚ F
  have : Algebra.EssFiniteType F K := Field.fg_iff_essFiniteType.mp hfg
  exact Algebra.EssFiniteType.comp ℚ F K

/-- The roots of unity of a number field are exactly the torsion units of its
ring of integers, hence form a finite group. -/
theorem finite_torsion_units_numberField
    (K : Type u) [Field K] [NumberField K] : Finite (CommGroup.torsion Kˣ) := by
  have : Finite (CommGroup.torsion (integralClosure ℤ K)ˣ) :=
    inferInstanceAs (Finite (NumberField.Units.torsion K))
  exact Finite.of_injective (torsionUnitsIntegralClosureEquiv ℤ K)
    (torsionUnitsIntegralClosureEquiv ℤ K).injective

/-- All roots of unity in a finitely generated extension of the rational
numbers lie in its number field of algebraic constants. -/
theorem finite_torsion_units_of_essFiniteType_rat
    (K : Type u) [Field K] [CharZero K] [Algebra.EssFiniteType ℚ K] :
    Finite (CommGroup.torsion Kˣ) := by
  let C := algebraicClosure ℚ K
  have : Module.Finite ℚ C := finite_algebraic_subextension ℚ C K
  have : NumberField C := {}
  have : Finite (CommGroup.torsion Cˣ) := finite_torsion_units_numberField C
  have : Finite (CommGroup.torsion (integralClosure ℚ K)ˣ) :=
    inferInstanceAs (Finite (CommGroup.torsion Cˣ))
  exact Finite.of_injective (torsionUnitsIntegralClosureEquiv ℚ K)
    (torsionUnitsIntegralClosureEquiv ℚ K).injective

/-- Every finite extension of a finitely generated characteristic-zero field
has finite prime-primary roots of unity. -/
theorem finite_primaryComponent_finiteExtension_of_fg_charZero
    (K : Type u) [Field K] [CharZero K] (hfg : Field.FG K)
    (L : Type v) [Field L] [Algebra K L] [FiniteDimensional K L]
    (p : ℕ) [Fact p.Prime] : Finite (CommGroup.primaryComponent Lˣ p) := by
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  have : Algebra.EssFiniteType ℚ K := essFiniteType_rat_of_fg K hfg
  have : Algebra.EssFiniteType K L := Algebra.EssFiniteType.of_finiteType K L
  have : Algebra.EssFiniteType ℚ L := Algebra.EssFiniteType.comp ℚ K L
  have : Finite (CommGroup.torsion Lˣ) := finite_torsion_units_of_essFiniteType_rat L
  have hle : CommGroup.primaryComponent Lˣ p ≤ CommGroup.torsion Lˣ := by
    intro z hz
    obtain ⟨n, hn⟩ := hz
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨p ^ n, pow_pos (Fact.out : p.Prime).pos n, hn⟩
  exact Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)

end FieldTheory
