/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Descent
import Mathlib.RingTheory.Nilpotent.GeometricallyReduced

/-!
# Finite geometrically reduced algebras over fields

The geometric-fibre algebra in the proper-family argument is finite étale:
after extending the field to an algebraic closure it is a finite product of
fields, and étaleness descends along the field extension.
-/

noncomputable section

open scoped TensorProduct

namespace Algebra

universe u

/-- A finite reduced algebra over a perfect field is étale. -/
theorem etale_of_finite_of_isReduced_of_perfectField
    (K A : Type u) [Field K] [PerfectField K] [CommRing A] [Algebra K A]
    [Module.Finite K A] [IsReduced A] : Etale K A := by
  classical
  have : IsArtinianRing A := IsArtinianRing.of_finite K A
  let : ∀ I : MaximalSpectrum A, Field (A ⧸ I.asIdeal) :=
    fun I => Ideal.Quotient.field I.asIdeal
  exact (Etale.iff_exists_algEquiv_prod K A).mpr
    ⟨MaximalSpectrum A, inferInstance, fun I => A ⧸ I.asIdeal, inferInstance,
      inferInstance, (IsArtinianRing.equivPi A).restrictScalars K,
      fun I => ⟨inferInstance, inferInstance⟩⟩

/-- Reducedness after algebraic closure is sufficient for a finite algebra
over a field to be étale. -/
theorem etale_of_finite_of_isReduced_algebraicClosure_tensorProduct
    (K A : Type u) [Field K] [CommRing A] [Algebra K A]
    [Module.Finite K A] [IsReduced (AlgebraicClosure K ⊗[K] A)] : Etale K A := by
  have : Etale (AlgebraicClosure K) (AlgebraicClosure K ⊗[K] A) :=
    etale_of_finite_of_isReduced_of_perfectField
      (AlgebraicClosure K) (AlgebraicClosure K ⊗[K] A)
  exact Etale.of_etale_tensorProduct_of_faithfullyFlat (AlgebraicClosure K)

end Algebra
