import SawinTotallyRealTowers.QuadraticSquareDescent
import SawinTotallyRealTowers.SquareRootAdjoin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Even
import Mathlib.Data.Set.Image
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Empty
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
# Degree and square classes of multiquadratic extensions

A finite family of independent square classes gives an actual extension
of degree two to the power of the family size. Degree and square-class
classification are proved simultaneously: classification in the previous
layer guarantees that the next square root gives a quadratic extension.
The reverse square-class implication constructs the product of the roots.
-/

open scoped BigOperators
universe u v w
namespace ClassFieldTower.Sawin

private theorem isSquare_adjoin_of_product
    (F : Type u) (Ω : Type v) [Field F] [Field Ω] [Algebra F Ω]
    {ι : Type w} [DecidableEq ι] (d : ι → F) (α : ι → Ω)
    (s t : Finset ι) (ht : t ⊆ s)
    (hRoot : ∀ i ∈ s, α i ^ 2 = algebraMap F Ω (d i))
    (b q : F) (hClass : b = (∏ i ∈ t, d i) * q ^ 2) :
    IsSquare (algebraMap F (IntermediateField.adjoin F (α '' (s : Set ι))) b) := by
  let K : IntermediateField F Ω := IntermediateField.adjoin F (α '' (s : Set ι))
  let β : t → K := fun i ↦ ⟨α i, IntermediateField.subset_adjoin F _ ⟨i, ht i.property, rfl⟩⟩
  apply (isSquare_iff_exists_sq _).mpr
  refine ⟨(∏ i : t, β i) * algebraMap F K q, ?_⟩
  apply (algebraMap K Ω).injective
  rw [← IsScalarTower.algebraMap_apply F K Ω, map_pow, map_mul,
    ← IsScalarTower.algebraMap_apply F K Ω, mul_pow, map_prod]
  have hProduct : (∏ i : t, algebraMap K Ω (β i)) ^ 2 = algebraMap F Ω (∏ i ∈ t, d i) := by
    rw [← Finset.prod_pow]
    calc
      (∏ i : t, algebraMap K Ω (β i) ^ 2) = ∏ i : t, algebraMap F Ω (d i) := by
        apply Finset.prod_congr rfl
        intro i _
        exact hRoot i (ht i.property)
      _ = ∏ i ∈ t, algebraMap F Ω (d i) := Finset.prod_coe_sort t (fun i ↦ algebraMap F Ω (d i))
      _ = algebraMap F Ω (∏ i ∈ t, d i) := (map_prod (algebraMap F Ω) d t).symm
  rw [hProduct, hClass, map_mul, map_pow]

/-- Independent square classes generate a multiquadratic extension of the
expected degree, and precisely their subproduct classes become squares. -/
theorem finrank_and_squareClasses_adjoin_independent_squareRoots
    (F : Type u) (Ω : Type v) [Field F] [Field Ω] [Algebra F Ω]
    {ι : Type w} [DecidableEq ι] (d : ι → F) (α : ι → Ω)
    (hTwo : (2 : F) ≠ 0) (s : Finset ι)
    (hRoot : ∀ i ∈ s, α i ^ 2 = algebraMap F Ω (d i))
    (hIndependent : ∀ t : Finset ι, t ⊆ s → t.Nonempty → ¬ IsSquare (∏ i ∈ t, d i)) :
    Module.finrank F (IntermediateField.adjoin F (α '' (s : Set ι))) = 2 ^ s.card ∧
      ∀ b : F,
        IsSquare (algebraMap F (IntermediateField.adjoin F (α '' (s : Set ι))) b) ↔
          ∃ t : Finset ι, t ⊆ s ∧ ∃ q : F, b = (∏ i ∈ t, d i) * q ^ 2 := by
  induction s using Finset.induction_on with
  | empty =>
      have hEmpty : IntermediateField.adjoin F
          (α '' ((∅ : Finset ι) : Set ι)) = ⊥ := by
        rw [Finset.coe_empty, Set.image_empty, IntermediateField.adjoin_empty]
      rw [hEmpty, Finset.card_empty, pow_zero]
      refine ⟨IntermediateField.finrank_bot, ?_⟩
      intro b
      constructor
      · intro hb
        have hBase : IsSquare b := by
          have h := hb.map (IntermediateField.botEquiv F Ω)
          rw [AlgEquiv.commutes, Algebra.algebraMap_self, RingHom.id_apply] at h
          exact h
        obtain ⟨q, hq⟩ := hBase.exists_sq
        exact ⟨∅, Finset.Subset.refl ∅, q, by simpa only [Finset.prod_empty, one_mul] using hq⟩
      · rintro ⟨t, ht, q, hq⟩
        have ht0 : t = ∅ := Finset.subset_empty.mp ht
        subst t
        apply (isSquare_iff_exists_sq _).mpr
        refine ⟨algebraMap F (⊥ : IntermediateField F Ω) q, ?_⟩
        simpa only [Finset.prod_empty, one_mul, map_pow] using
          congrArg (algebraMap F (⊥ : IntermediateField F Ω)) hq
  | @insert i s hi ih =>
      have hRootS : ∀ j ∈ s, α j ^ 2 = algebraMap F Ω (d j) :=
        fun j hj ↦ hRoot j (Finset.mem_insert_of_mem hj)
      have hIndependentS : ∀ t : Finset ι, t ⊆ s → t.Nonempty →
          ¬ IsSquare (∏ j ∈ t, d j) :=
        fun t ht ↦ hIndependent t (ht.trans (Finset.subset_insert i s))
      obtain ⟨hRankS, hClassesS⟩ := ih hRootS hIndependentS
      let K : IntermediateField F Ω := IntermediateField.adjoin F (α '' (s : Set ι))
      have hNonSquare : ¬ IsSquare (algebraMap F K (d i)) := by
        intro hSquare
        obtain ⟨t, ht, q, hClass⟩ := (hClassesS (d i)).mp hSquare
        have hit : i ∉ t := fun h ↦ hi (ht h)
        apply hIndependent (insert i t) (Finset.insert_subset_insert i ht)
          (Finset.insert_nonempty i t)
        apply (isSquare_iff_exists_sq _).mpr
        refine ⟨(∏ j ∈ t, d j) * q, ?_⟩
        rw [Finset.prod_insert hit, hClass]
        ring
      have hRootK : α i ^ 2 = algebraMap K Ω (algebraMap F K (d i)) := by
        rw [← IsScalarTower.algebraMap_apply F K Ω]
        exact hRoot i (Finset.mem_insert_self i s)
      let L : IntermediateField K Ω := IntermediateField.adjoin K {α i}
      let : Algebra.IsQuadraticExtension K L :=
        isQuadraticExtension_adjoin_squareRoot K Ω (algebraMap F K (d i)) (α i) hRootK hNonSquare
      have hAdjoin : L.restrictScalars F =
          IntermediateField.adjoin F (α '' ((insert i s : Finset ι) : Set ι)) := by
        change (IntermediateField.adjoin (IntermediateField.adjoin F (α '' (s : Set ι)))
          {α i}).restrictScalars F = _
        rw [IntermediateField.adjoin_adjoin_left, Finset.coe_insert, Set.image_insert_eq,
          Set.union_singleton]
      rw [← hAdjoin]
      change Module.finrank F L = 2 ^ (insert i s).card ∧ _
      refine ⟨?_, ?_⟩
      · rw [← Module.finrank_mul_finrank F K L,
          show Module.finrank F K = 2 ^ s.card from hRankS,
          Algebra.IsQuadraticExtension.finrank_eq_two K L,
          Finset.card_insert_of_notMem hi, pow_succ]
      · intro b
        change IsSquare (algebraMap F L b) ↔ _
        constructor
        · intro hb
          have hTwoK : (2 : K) ≠ 0 := by
            intro h
            apply hTwo
            apply (algebraMap F K).injective
            simpa only [map_ofNat, map_zero] using h
          have hb' : IsSquare (algebraMap K L (algebraMap F K b)) := by
            rw [← IsScalarTower.algebraMap_apply F K L]
            exact hb
          rcases (isSquare_algebraMap_iff_of_quadraticGenerator K L hTwoK
            (algebraMap F K (d i)) (algebraMap F K b)
            (IntermediateField.AdjoinSimple.gen K (α i))
            (adjoinSquareRoot_gen_sq K Ω (algebraMap F K (d i)) (α i) hRootK)
            (adjoinSquareRoot_gen_adjoin K Ω (α i))).mp hb'
              with hBase | ⟨q, hq⟩
          · obtain ⟨t, ht, r, hr⟩ := (hClassesS b).mp hBase
            exact ⟨t, ht.trans (Finset.subset_insert i s), r, hr⟩
          · have hdi : d i ≠ 0 := by
              intro h
              apply hNonSquare
              rw [h, map_zero]
              exact ⟨0, (mul_zero 0).symm⟩
            have hdiK : algebraMap F K (d i) ≠ 0 := fun h ↦
              hdi ((algebraMap F K).injective (h.trans (map_zero (algebraMap F K)).symm))
            have hDiv : IsSquare (algebraMap F K (b / d i)) := by
              apply (isSquare_iff_exists_sq _).mpr
              refine ⟨q, ?_⟩
              rw [map_div₀, hq]
              exact mul_div_cancel_left₀ (q ^ 2) hdiK
            obtain ⟨t, ht, r, hr⟩ := (hClassesS (b / d i)).mp hDiv
            have hit : i ∉ t := fun h ↦ hi (ht h)
            refine ⟨insert i t, Finset.insert_subset_insert i ht, r, ?_⟩
            rw [Finset.prod_insert hit]
            calc
              b = d i * (b / d i) := by field_simp
              _ = d i * ((∏ j ∈ t, d j) * r ^ 2) := congrArg (d i * ·) hr
              _ = d i * (∏ j ∈ t, d j) * r ^ 2 := (mul_assoc _ _ _).symm
        · rintro ⟨t, ht, q, hClass⟩
          have hSquare := isSquare_adjoin_of_product F Ω d α (insert i s) t ht hRoot b q hClass
          rw [← hAdjoin] at hSquare
          exact hSquare

end ClassFieldTower.Sawin
