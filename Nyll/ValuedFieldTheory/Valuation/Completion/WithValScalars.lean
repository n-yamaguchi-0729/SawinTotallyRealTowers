/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Topology.Algebra.Valued.WithVal

/-!
# Ground-field scalars on a valued completion

Scalar multiplication on `WithVal v` is multiplication by the image of the
scalar. Its uniform continuity supplies the existing completion algebra over
the original field, without choosing a topology on that field.
-/

namespace WithVal

variable {K Γ : Type*} [Ring K] [LinearOrderedCommGroupWithZero Γ]

/-- The canonical ground-field action on `WithVal v` is uniformly continuous
in its second argument. -/
instance uniformContinuousConstSMul (v : Valuation K Γ) :
    UniformContinuousConstSMul K (WithVal v) where
  uniformContinuous_const_smul k := by
    change UniformContinuous (fun x : WithVal v => toVal v k * x)
    exact uniformContinuous_mul_left' _

/-- Scalars from a specified algebra act uniformly continuously on its
valued model. This theorem does not register another global scalar instance. -/
theorem uniformContinuousConstSMul_algebra {R : Type*} [CommSemiring R]
    [Algebra R K] (v : Valuation K Γ) :
    UniformContinuousConstSMul R (WithVal v) where
  uniformContinuous_const_smul r := by
    have heq : (fun x : WithVal v => r • x) =
        (fun x => WithVal.toVal v (algebraMap R K r) * x) := by
      funext x
      apply WithVal.ofVal_injective v
      exact Algebra.smul_def r x.ofVal
    rw [heq]
    exact uniformContinuous_mul_left' _

/-- The canonical map from the original ring to its valuation completion
has dense range, without choosing a topology on the original ring. -/
theorem denseRange_algebraMap_completion {R : Type*} [CommRing R] (v : Valuation R Γ) :
    DenseRange (algebraMap R v.Completion) := by
  have hrange : Set.range (algebraMap R v.Completion) =
      Set.range ((↑) : WithVal v → v.Completion) := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨WithVal.toVal v k, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨WithVal.equiv v k, rfl⟩
  intro x
  rw [hrange]
  exact UniformSpace.Completion.denseRange_coe x

end WithVal
