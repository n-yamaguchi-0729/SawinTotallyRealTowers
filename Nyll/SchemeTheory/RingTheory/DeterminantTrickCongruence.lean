/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
/-!
# A determinant trick with prescribed reduction

A diagonal action on a finite generating family modulo an ideal gives a monic
annihilating polynomial whose reduction is the product of the diagonal linear factors.
The generating family need not be a basis.
-/

@[expose] public section

open Polynomial

universe u v w

namespace LinearMap

/-- A finite spanning family on which an endomorphism is diagonal modulo an ideal
gives an annihilating polynomial with the corresponding prescribed reduction. -/
theorem exists_monic_aeval_eq_zero_map_eq_prod_of_residual_diagonal
    {R : Type u} {M : Type v} {ι : Type w}
    [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι]
    (I : Ideal R) (f : Module.End R M) (v : ι → M)
    (hv : Submodule.span R (Set.range v) = ⊤) (d : ι → R)
    (hres : ∀ j, f (v j) - d j • v j ∈ I • (⊤ : Submodule R M)) :
    ∃ p : R[X], p.Monic ∧ aeval f p = 0 ∧
      p.map (Ideal.Quotient.mk I) =
        ∏ j, (X - C (Ideal.Quotient.mk I (d j))) := by
  classical
  have hmem (j : ι) : f (v j) - d j • v j ∈
      LinearMap.range (Ideal.finsuppTotal ι M I v) := by
    rw [Ideal.range_finsuppTotal, hv]
    exact hres j
  choose c hc using hmem
  have hsum (j : ι) : ∑ i, (c j i : R) • v i = f (v j) - d j • v j := by
    simpa only [Ideal.finsuppTotal_apply_eq_of_fintype] using hc j
  let A : Matrix ι ι R :=
    Matrix.diagonal d + Matrix.of (fun i j => (c j i : R))
  have hA : A.Represents v f := by
    rw [Matrix.represents_iff']
    intro j
    change (∑ i, ((if i = j then d i else 0) + (c j i : R)) • v i) = f (v j)
    simp only [add_smul, Finset.sum_add_distrib, ite_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [hsum j, add_sub_cancel]
  let A' : Matrix.isRepresentation R v := ⟨A, f, hA⟩
  have hEnd : Matrix.isRepresentation.toEnd R v hv A' = f :=
    Matrix.isRepresentation.eq_toEnd_of_represents R v hv A' hA
  have hchar : aeval f A.charpoly = 0 := by
    rw [← hEnd, Polynomial.aeval_algHom_apply,
      ← map_zero (Matrix.isRepresentation.toEnd R v hv)]
    congr 1
    ext1
    rw [Polynomial.aeval_subalgebra_coe, Matrix.aeval_self_charpoly, Subalgebra.coe_zero]
  have hAmap : A.map (Ideal.Quotient.mk I) =
      Matrix.diagonal (fun i => Ideal.Quotient.mk I (d i)) := by
    ext i j
    change Ideal.Quotient.mk I (Matrix.diagonal d i j + (c j i : R)) = _
    rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr (c j i).property, add_zero]
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  refine ⟨A.charpoly, A.charpoly_monic, hchar, ?_⟩
  rw [← Matrix.charpoly_map, hAmap, Matrix.charpoly_diagonal]

end LinearMap
