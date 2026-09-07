import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Ring.Commute

set_option autoImplicit false

/-!
# Square-class products inside intermediate fields

An intermediate field containing square roots of finitely many radicands
also contains a square root of their product, up to a square in the base
field. The proof constructs that root as an actual product and compares
the two roots by their signs.
-/

universe u v w

namespace ClassFieldTower.Sawin

open scoped BigOperators

/-- A finite product of known square roots realizes a product of square
classes inside the same intermediate field. -/
theorem squareRoot_mem_of_squareClass_product
    {F : Type u} {E : Type v} {ι : Type w}
    [Field F] [Field E] [Algebra F E]
    (K : IntermediateField F E) (s : Finset ι)
    (d : ι → F) (β : ι → E) (a q : F) (α : E)
    (hα : α ^ 2 = algebraMap F E a)
    (hβ : ∀ i ∈ s, β i ^ 2 = algebraMap F E (d i))
    (hMem : ∀ i ∈ s, β i ∈ K)
    (hClass : a = (∏ i ∈ s, d i) * q ^ 2) : α ∈ K := by
  have hProduct : (∏ i ∈ s, β i) ^ 2 = algebraMap F E (∏ i ∈ s, d i) := by
    rw [← Finset.prod_pow]
    calc
      (∏ i ∈ s, β i ^ 2) = ∏ i ∈ s, algebraMap F E (d i) :=
        Finset.prod_congr rfl hβ
      _ = algebraMap F E (∏ i ∈ s, d i) := (map_prod (algebraMap F E) d s).symm
  have hSquare : α ^ 2 = ((∏ i ∈ s, β i) * algebraMap F E q) ^ 2 := by
    rw [mul_pow, hProduct, ← map_pow, ← map_mul, ← hClass]
    exact hα
  have hProductMem : (∏ i ∈ s, β i) * algebraMap F E q ∈ K :=
    K.mul_mem (K.prod_mem hMem) (K.algebraMap_mem q)
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hSquare with hEq | hNeg
  · rw [hEq]
    exact hProductMem
  · rw [hNeg]
    exact K.neg_mem hProductMem

end ClassFieldTower.Sawin
