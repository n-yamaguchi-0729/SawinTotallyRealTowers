/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Dense tensor images over a complete field

The tensor image of a finite extension is finite-dimensional over the
complete base field, hence closed. If it contains a dense copy of the
extension field, this image is the entire target ring.
-/

namespace ValuationTheory.Completion

open scoped TensorProduct

variable {K L A B : Type*} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [NontriviallyNormedField A] [CompleteSpace A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [T2Space B]
  [Algebra K A] [Algebra K B] [Algebra A B] [IsScalarTower K A B]
  [ContinuousSMul A B]

/-- A dense map from a finite extension induces a surjective tensor map
over a complete nontrivially normed field. The target needs no norm. -/
theorem tensorProduct_lift_surjective_of_denseRange
    (g : L →ₐ[K] B) (hg : DenseRange g) :
    Function.Surjective
      (Algebra.TensorProduct.lift (Algebra.ofId A B) g
        (fun (a : A) (l : L) => Commute.all (algebraMap A B a) (g l))) := by
  let f : A ⊗[K] L →ₐ[A] B :=
    Algebra.TensorProduct.lift (Algebra.ofId A B) g
      (fun (a : A) (l : L) => Commute.all (algebraMap A B a) (g l))
  have hclosed : IsClosed (f.toLinearMap.range : Set B) :=
    Submodule.closed_of_finiteDimensional (𝕜 := A) f.toLinearMap.range
  have hrange : Set.range g ⊆ (f.toLinearMap.range : Set B) := by
    rintro _ ⟨l, rfl⟩
    refine ⟨1 ⊗ₜ[K] l, ?_⟩
    change f (1 ⊗ₜ[K] l) = g l
    exact (Algebra.TensorProduct.lift_tmul (Algebra.ofId A B) g
      (fun (a : A) (l : L) => Commute.all (algebraMap A B a) (g l)) 1 l).trans
      (by rw [map_one, one_mul])
  change Function.Surjective f
  intro b
  exact closure_minimal hrange hclosed (hg b)

end ValuationTheory.Completion
