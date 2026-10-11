/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.GaloisCohomology.FieldTheory.FiniteAlgebraicConstants
import Nyll.GaloisCohomology.FieldTheory.FiniteConstants
import Mathlib.FieldTheory.Finite.Basic

/-!
# Constants in finitely generated fields of positive characteristic
-/

namespace FieldTheory

universe u v

/-- The prime subfield of a field of positive characteristic is finite. -/
theorem finite_primeSubfield_of_ringChar_ne_zero
    (K : Type u) [Field K] (hchar : ringChar K ≠ 0) :
    Finite (⊥ : Subfield K) := by
  have : Fact (ringChar K).Prime :=
    ⟨(CharP.char_is_prime_or_zero K (ringChar K)).resolve_right hchar⟩
  rw [← ZMod.fieldRange_castHom_eq_bot (ringChar K)]
  exact Finite.of_surjective (ZMod.castHom (m := ringChar K) dvd_rfl K).rangeRestrictField
    (ZMod.castHom (m := ringChar K) dvd_rfl K).rangeRestrictField_bijective.surjective

/-- The algebraic constants in a finitely generated field of positive
characteristic form a finite field. -/
theorem finite_constants_of_fg_posChar
    (K : Type u) [Field K] (hfg : Field.FG K) (hchar : ringChar K ≠ 0) :
    Finite (algebraicClosure (⊥ : Subfield K) K) := by
  have : Finite (⊥ : Subfield K) := finite_primeSubfield_of_ringChar_ne_zero K hchar
  have : Algebra.EssFiniteType (⊥ : Subfield K) K := Field.fg_iff_essFiniteType.mp hfg
  exact finite_algebraicClosure_of_finite_base (⊥ : Subfield K) K

/-- Every root of unity is contained in the finite field of algebraic constants. -/
theorem finite_torsion_units_of_fg_posChar
    (K : Type u) [Field K] (hfg : Field.FG K) (hchar : ringChar K ≠ 0) :
    Finite (CommGroup.torsion Kˣ) := by
  have : Finite (algebraicClosure (⊥ : Subfield K) K) :=
    finite_constants_of_fg_posChar K hfg hchar
  exact finite_torsion_units_of_finite_algebraicClosure (⊥ : Subfield K) K

/-- The Artin--Schreier map on a finitely generated field of positive
characteristic is not surjective. -/
theorem exists_not_artinSchreier_of_fg_posChar
    (K : Type u) [Field K] (hfg : Field.FG K) (hchar : ringChar K ≠ 0) :
    ∃ a : K, ∀ x : K, x ^ ringChar K - x ≠ a := by
  have : Finite (algebraicClosure (⊥ : Subfield K) K) :=
    finite_constants_of_fg_posChar K hfg hchar
  exact exists_not_pow_sub_of_finite_algebraicClosure (⊥ : Subfield K) K (ringChar K)
    ((CharP.char_is_prime_or_zero K (ringChar K)).resolve_right hchar).one_lt

/-- The primary roots of unity in every finite extension are finite. -/
theorem finite_primaryComponent_finiteExtension_of_fg_posChar
    (K : Type u) [Field K] (hfg : Field.FG K) (hchar : ringChar K ≠ 0)
    (L : Type v) [Field L] [Algebra K L] [FiniteDimensional K L]
    (p : ℕ) [Fact p.Prime] : Finite (CommGroup.primaryComponent Lˣ p) := by
  let F := (⊥ : Subfield K)
  have : Finite F := finite_primeSubfield_of_ringChar_ne_zero K hchar
  have : Algebra.EssFiniteType F K := Field.fg_iff_essFiniteType.mp hfg
  have : Algebra.EssFiniteType K L := Algebra.EssFiniteType.of_finiteType K L
  have : Algebra.EssFiniteType F L := Algebra.EssFiniteType.comp F K L
  have : Finite (algebraicClosure F L) := finite_algebraicClosure_of_finite_base F L
  exact finite_primaryComponent_of_finite_algebraicClosure F L p

end FieldTheory
