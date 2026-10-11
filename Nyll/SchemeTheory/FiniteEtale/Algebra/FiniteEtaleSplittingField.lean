/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# A finite separable splitting field for a finite étale algebra

A maximal quotient of the actual finite faithfully flat splitting algebra
is a finite separable field extension and still splits the original algebra.
The construction also applies to the zero algebra.
-/

noncomputable section

open scoped TensorProduct

namespace Algebra.IsFiniteSplit

universe u

/-- A finite étale algebra over a field splits over a finite separable
field extension. No nontriviality assumption on the algebra is needed. -/
theorem exists_finite_separable_splittingField
    (K B : Type u) [Field K] [CommRing B] [Algebra K B]
    [Module.Finite K B] [Algebra.Etale K B] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L)
      (_ : Module.Finite K L) (_ : Algebra.IsSeparable K L),
      Algebra.IsFiniteSplit L (L ⊗[K] B) := by
  obtain ⟨T, hRingT, hAlgT, hFaithfulT, hFiniteT, hEtaleT, hSplitT⟩ :=
    exists_tensorProduct_of_etale (R := K) (S := B)
      (Module.rankAtStalk_eq_finrank_of_free (R := K) (M := B))
  have : Nontrivial T := (Algebra.TensorProduct.lid K T).symm.toEquiv.nontrivial
  obtain ⟨p, hp⟩ := Ideal.exists_maximal T
  let L := T ⧸ p
  let : Field L := Ideal.Quotient.field p
  have hFiniteL : Module.Finite K L :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K p).toLinearMap
      Ideal.Quotient.mk_surjective
  have hSeparableL : Algebra.IsSeparable K L :=
    Algebra.FormallyUnramified.isSeparable K L
  refine ⟨L, inferInstance, inferInstance, hFiniteL, hSeparableL, ?_⟩
  exact Algebra.IsFiniteSplit.of_algEquiv
    (Algebra.TensorProduct.cancelBaseChange K T L L B)

end Algebra.IsFiniteSplit
