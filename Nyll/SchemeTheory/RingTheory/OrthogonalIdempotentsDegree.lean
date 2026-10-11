/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Algebra.Pi
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Idempotents

/-!
# A full-degree orthogonal family splits a finite algebra

Nonzero orthogonal idempotents are linearly independent. If their number is
at least the dimension of the algebra, the explicit sum of scalar multiples
is a bijective algebra map from a product of copies of the base field.
No separability or reducedness hypothesis is required.
-/

noncomputable section

namespace SchemeTheory

universe u v w

/-- A complete orthogonal family of nonzero idempotents whose cardinality
is at least the algebra's degree gives an actual split algebra isomorphism. -/
def splitAlgEquivOfCompleteOrthogonalIdempotents
    {K : Type u} {A : Type v} {ι : Type w}
    [Field K] [CommRing A] [Algebra K A] [FiniteDimensional K A] [Fintype ι]
    (e : ι → A) (he : CompleteOrthogonalIdempotents e)
    (hne : ∀ i, e i ≠ 0) (hdegree : Module.finrank K A ≤ Fintype.card ι) :
    A ≃ₐ[K] (ι → K) := by
  classical
  have hcoord (c : ι → K) (j : ι) :
      (∑ i, c i • e i) * e j = c j • e j := by
    rw [Finset.sum_mul]
    simp only [smul_mul_assoc, he.mul_eq, smul_ite, smul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  let g : (ι → K) →ₐ[K] A :=
    { toFun := fun c => ∑ i, c i • e i
      map_zero' := by
        simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero]
      map_one' := by
        simpa only [Pi.one_apply, one_smul] using he.complete
      map_add' := by
        intro c d
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_mul' := by
        intro c d
        change (∑ i, (c i * d i) • e i) = (∑ i, c i • e i) * ∑ i, d i • e i
        rw [Finset.mul_sum]
        symm
        apply Finset.sum_congr rfl
        intro i _
        rw [mul_smul_comm, hcoord, smul_smul, mul_comm]
      commutes' := by
        intro k
        change (∑ i, k • e i) = algebraMap K A k
        rw [← Finset.smul_sum, he.complete, Algebra.smul_def, mul_one] }
  have hinjective : Function.Injective g := by
    intro c d h
    funext i
    have hcoordEq := congrArg (fun z : A => z * e i) h
    change (∑ j, c j • e j) * e i = (∑ j, d j • e j) * e i at hcoordEq
    rw [hcoord, hcoord] at hcoordEq
    have hzero : (c i - d i) • e i = 0 := by
      rw [sub_smul, hcoordEq, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_right (hne i))
  have hdimension : Module.finrank K (ι → K) = Module.finrank K A := by
    apply le_antisymm
    · exact LinearMap.finrank_le_finrank_of_injective (f := g.toLinearMap) hinjective
    · simpa only [Module.finrank_pi] using hdegree
  have hsurjective : Function.Surjective g :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := g.toLinearMap) hdimension).mp hinjective
  exact (AlgEquiv.ofBijective g ⟨hinjective, hsurjective⟩).symm

end SchemeTheory
