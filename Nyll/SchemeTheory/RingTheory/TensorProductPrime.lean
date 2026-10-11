/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Compatible prime ideals lift to a tensor product

Two prime ideals of algebras over the same ring lift simultaneously to the
tensor product when their contractions agree. The point is constructed in
the scheme fiber product and transported through its affine tensor-product
isomorphism, with both projections verified.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace PrimeSpectrum

universe u

/-- Compatible prime ideals lift to a prime of the tensor product, with both
contractions prescribed. No dominance or flatness assumption is required. -/
theorem exists_tensorProduct_of_comap_eq
    (R B C : Type u) [CommRing R] [CommRing B] [CommRing C]
    [Algebra R B] [Algebra R C]
    (p : PrimeSpectrum B) (q : PrimeSpectrum C)
    (h : comap (algebraMap R B) p = comap (algebraMap R C) q) :
    ∃ r : PrimeSpectrum (B ⊗[R] C),
      comap (algebraMap B (B ⊗[R] C)) r = p ∧
        comap (Algebra.TensorProduct.includeRight (R := R) (A := B)).toRingHom r = q := by
  let f : Spec (.of B) ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R B))
  let g : Spec (.of C) ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R C))
  obtain ⟨z, hzB, hzC⟩ :=
    Scheme.Pullback.exists_preimage_pullback (f := f) (g := g) p q h
  refine ⟨(pullbackSpecIso R B C).hom z, ?_, ?_⟩
  · exact (congrArg (fun k : pullback f g ⟶ Spec (.of B) ↦ k z)
      (pullbackSpecIso_hom_fst' R B C)).trans hzB
  · exact (congrArg (fun k : pullback f g ⟶ Spec (.of C) ↦ k z)
      (pullbackSpecIso_hom_snd R B C)).trans hzC

end PrimeSpectrum
