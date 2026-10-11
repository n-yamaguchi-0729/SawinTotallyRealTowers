/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Tensor elements over finite intermediate fields

Only finitely many coefficients from the algebraic extension occur in a
tensor element. Adjoining those coefficients gives a finite intermediate
field over which the element is already defined.
-/

namespace ValuationTheory.Completion

open scoped TensorProduct BigOperators

/-- Every tensor element over an algebraic field extension lifts from a
finite intermediate field, along its actual inclusion into the extension. -/
theorem exists_finiteSubfield_tensor_lift
    {K A L : Type*} [Field K] [CommRing A] [Field L]
    [Algebra K A] [Algebra K L] [Algebra.IsAlgebraic K L]
    (z : A ⊗[K] L) :
    ∃ F : IntermediateField K L, FiniteDimensional K F ∧
      ∃ w : A ⊗[K] F,
        Algebra.TensorProduct.map (R := K) (S := A) (AlgHom.id A A) F.val w = z := by
  classical
  obtain ⟨s, hz⟩ := TensorProduct.exists_finset z
  let t : Finset L := s.image Prod.snd
  let F : IntermediateField K L := IntermediateField.adjoin K (t : Set L)
  have hfinite : FiniteDimensional K F :=
    IntermediateField.finiteDimensional_adjoin
      (fun l _ => Algebra.IsIntegral.isIntegral l)
  have hmem (p : s) : p.val.2 ∈ F :=
    IntermediateField.subset_adjoin K (t : Set L)
      (Finset.mem_image.mpr ⟨p.val, p.property, rfl⟩)
  refine ⟨F, hfinite, ∑ p : s, p.val.1 ⊗ₜ[K] (⟨p.val.2, hmem p⟩ : F), ?_⟩
  rw [map_sum]
  simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  change (∑ p : s, p.val.1 ⊗ₜ[K] p.val.2) = z
  exact (Finset.sum_coe_sort s (fun p : A × L => p.1 ⊗ₜ[K] p.2)).trans hz.symm

end ValuationTheory.Completion
