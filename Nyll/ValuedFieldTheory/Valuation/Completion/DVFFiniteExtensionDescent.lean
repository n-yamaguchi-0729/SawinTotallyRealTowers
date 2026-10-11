/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.Completion.DVFFiniteSeparableGenerator
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Descending finite separable extensions of a valuation completion

A generator separable over the original field gives a finite separable
intermediate field. Its scalar extension maps onto the given extension of
the completion, and the equality of degrees makes this actual map injective.
-/

noncomputable section


namespace ValuationTheory.DiscreteValuationField.DVF

open IntermediateField
open scoped TensorProduct

variable {K : Type*} [Field K] (base : DVF K)

/-- The tensor map obtained from the two given embeddings into `E`. -/
def completionIntermediateFieldTensorHom
    {E : Type*} [Field E] [Algebra base.valuation.Completion E]
    [Algebra K E] [IsScalarTower K base.valuation.Completion E]
    (F : IntermediateField K E) :
    base.valuation.Completion ⊗[K] F →ₐ[base.valuation.Completion] E :=
  Algebra.TensorProduct.lift (Algebra.ofId base.valuation.Completion E) F.val
    (fun a x => Commute.all (algebraMap base.valuation.Completion E a) (x : E))

/-- The tensor map multiplies the canonical images of the two factors. -/
@[simp] theorem completionIntermediateFieldTensorHom_tmul
    {E : Type*} [Field E] [Algebra base.valuation.Completion E]
    [Algebra K E] [IsScalarTower K base.valuation.Completion E]
    (F : IntermediateField K E) (a : base.valuation.Completion) (x : F) :
    completionIntermediateFieldTensorHom base F (a ⊗ₜ[K] x) =
      algebraMap base.valuation.Completion E a * (x : E) :=
  Algebra.TensorProduct.lift_tmul (Algebra.ofId base.valuation.Completion E) F.val
    (fun b y => Commute.all (algebraMap base.valuation.Completion E b) (y : E)) a x

/-- Every finite separable extension of the actual valuation completion is
the scalar extension of a finite separable intermediate field over `K`. -/
theorem exists_finiteSeparable_completion_descent
    (E : Type*) [Field E] [Algebra base.valuation.Completion E]
    [Algebra K E] [IsScalarTower K base.valuation.Completion E]
    [FiniteDimensional base.valuation.Completion E]
    [Algebra.IsSeparable base.valuation.Completion E] :
    ∃ F : IntermediateField K E, FiniteDimensional K F ∧ Algebra.IsSeparable K F ∧
      Function.Bijective (completionIntermediateFieldTensorHom base F) := by
  obtain ⟨γ, hγsep, hγgen, hγdegree⟩ := base.exists_completion_extension_generator E
  let F : IntermediateField K E := K⟮γ⟯
  have hfinite : FiniteDimensional K F :=
    IntermediateField.adjoin.finiteDimensional hγsep.isIntegral
  have hsep : Algebra.IsSeparable K F := by
    apply (IntermediateField.isSeparable_adjoin_iff_isSeparable K E).mpr
    intro x hx
    exact (Set.mem_singleton_iff.mp hx).symm ▸ hγsep
  let φ : base.valuation.Completion ⊗[K] F →ₐ[base.valuation.Completion] E :=
    completionIntermediateFieldTensorHom base F
  have honto : Function.Surjective φ := by
    have hγrange : γ ∈ φ.range := by
      refine ⟨1 ⊗ₜ[K] (⟨γ, IntermediateField.mem_adjoin_simple_self K γ⟩ : F), ?_⟩
      change completionIntermediateFieldTensorHom base F
        (1 ⊗ₜ[K] (⟨γ, IntermediateField.mem_adjoin_simple_self K γ⟩ : F)) = γ
      rw [completionIntermediateFieldTensorHom_tmul, map_one, one_mul]
    apply φ.range_eq_top.mp
    apply top_unique
    rw [← hγgen]
    apply Algebra.adjoin_le
    intro x hx
    exact (Set.mem_singleton_iff.mp hx).symm ▸ hγrange
  have hdim : Module.finrank base.valuation.Completion
      (base.valuation.Completion ⊗[K] F) = Module.finrank base.valuation.Completion E := by
    rw [Module.finrank_baseChange]
    exact (IntermediateField.adjoin.finrank hγsep.isIntegral).trans hγdegree
  have hinj : Function.Injective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
      (f := φ.toLinearMap)).mpr honto
  exact ⟨F, hfinite, hsep, hinj, honto⟩

end ValuationTheory.DiscreteValuationField.DVF
