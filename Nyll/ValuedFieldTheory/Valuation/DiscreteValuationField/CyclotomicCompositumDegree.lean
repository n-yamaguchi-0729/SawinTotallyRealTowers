/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.CyclotomicGaloisCard
import Mathlib.FieldTheory.LinearDisjoint

/-!
# Degrees of actual cyclotomic composita

A common primitive root proves that the upper cyclotomic field is generated
over the lower cyclotomic field by the other field's image. Coprime degrees
then give the original prime degree after this base extension.
-/

namespace ValuationTheory.DiscreteValuationField

/-- The lower cyclotomic field already contains a primitive generator of
the upper cyclotomic extension, so adjoining the other field's image suffices. -/
theorem cyclotomic_compositum_adjoin_range_eq_top
    (F K L E : Type*) [Field F] [Field K] [Field L] [Field E]
    [Algebra F L] [Algebra K E] [Algebra L E]
    (n : ℕ) [NeZero n]
    [IsCyclotomicExtension {n} F L] [IsCyclotomicExtension {n} K E] :
    Algebra.adjoin L (Set.range (algebraMap K E)) = ⊤ := by
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot F L
    (Set.mem_singleton n) (NeZero.ne n)
  have hgen : Algebra.adjoin K ({algebraMap L E ζ} : Set E) = ⊤ :=
    IsCyclotomicExtension.adjoin_primitive_root_eq_top
      (hζ.map_of_injective (algebraMap L E).injective)
  let S : Subalgebra L E := Algebra.adjoin L (Set.range (algebraMap K E))
  let T : Subalgebra K E :=
    { S.toSubsemiring with
      algebraMap_mem' := fun k => Algebra.subset_adjoin ⟨k, rfl⟩ }
  have hT : Algebra.adjoin K ({algebraMap L E ζ} : Set E) ≤ T := by
    apply Algebra.adjoin_le
    intro x hx
    have hxζ : x = algebraMap L E ζ := Set.mem_singleton_iff.mp hx
    rw [hxζ]
    exact S.algebraMap_mem ζ
  rw [hgen] at hT
  apply top_le_iff.mp
  intro x _hx
  exact hT (show x ∈ (⊤ : Subalgebra K E) from trivial)

private theorem finrank_eq_of_coprime_of_adjoin_eq_top
    (F L E : Type*) [Field F] [Field L] [Field E]
    [Algebra F L] [Algebra F E] [Algebra L E] [IsScalarTower F L E]
    [Algebra.IsAlgebraic F L] (A : IntermediateField F E)
    (hcop : (Module.finrank F A).Coprime (Module.finrank F L))
    (hgen : Algebra.adjoin L (A : Set E) = ⊤) :
    Module.finrank L E = Module.finrank F A := by
  have hdisjoint : A.LinearDisjoint L :=
    IntermediateField.LinearDisjoint.of_finrank_coprime hcop
  have hdim := congrArg Cardinal.toNat
    hdisjoint.adjoin_rank_eq_rank_left_of_isAlgebraic_right
  change Module.finrank L (IntermediateField.adjoin L (A : Set E)) =
    Module.finrank F A at hdim
  have hgen' : IntermediateField.adjoin L (A : Set E) = ⊤ :=
    IntermediateField.adjoin_eq_top_of_algebra L (A : Set E) hgen
  rw [hgen', IntermediateField.finrank_top'] at hdim
  exact hdim

/-- Adjoining the same prime-order roots of unity to a prime-degree extension
preserves its degree. Generation and coprimality are supplied by the actual
cyclotomic extensions. -/
theorem cyclotomic_compositum_finrank_eq_prime
    (F K L E : Type*) [Field F] [Field K] [Field L] [Field E]
    [Algebra F K] [Algebra F L] [Algebra F E] [Algebra K E] [Algebra L E]
    [IsScalarTower F K E] [IsScalarTower F L E]
    (p : ℕ) [Fact p.Prime]
    [IsCyclotomicExtension {p} F L] [IsCyclotomicExtension {p} K E]
    (hdegree : Module.finrank F K = p) : Module.finrank L E = p := by
  have : FiniteDimensional F L := IsCyclotomicExtension.finiteDimensional {p} F L
  have : IsGalois F L := IsCyclotomicExtension.isGalois {p} F L
  let f : K →ₐ[F] E := IsScalarTower.toAlgHom F K E
  let A : IntermediateField F E := f.fieldRange
  have hA : Module.finrank F A = p :=
    f.equivFieldRange.toLinearEquiv.finrank_eq.symm.trans hdegree
  have hcop : (Module.finrank F A).Coprime (Module.finrank F L) := by
    rw [hA]
    have hcard := prime_coprime_cyclotomicGalois_natCard F L p
    rw [IsGalois.card_aut_eq_finrank F L] at hcard
    exact hcard
  have hgen : Algebra.adjoin L (A : Set E) = ⊤ := by
    change Algebra.adjoin L (Set.range (algebraMap K E)) = ⊤
    exact cyclotomic_compositum_adjoin_range_eq_top F K L E p
  exact (finrank_eq_of_coprime_of_adjoin_eq_top F L E A hcop hgen).trans hA

end ValuationTheory.DiscreteValuationField
