/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.Completion.DVFEmbedding
import Nyll.ValuedFieldTheory.Valuation.Completion.DenseTensorProduct
import Nyll.ValuedFieldTheory.Valuation.Completion.HenselianTensorField
import Nyll.ValuedFieldTheory.Valuation.Completion.WithValScalars
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.NormedModel
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Topology.Algebra.MulAction

/-!
# The tensor map for an extension of discrete valuations

The map of completions supplies the scalar algebra. Multiplication then
gives the actual tensor map to the completion of the extension field.

Class-valued statements specify this algebra's scalar action explicitly,
avoiding a search through the completion's general scalar-action instance.
The module-local algebra is the same data, used to elaborate the proofs.
-/

noncomputable section

namespace ValuationTheory.DiscreteValuationField.DVF

open scoped TensorProduct

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  (base : DVF K) (target : DVF L)
  [hExtension : base.valuation.HasExtension target.valuation]

/-- The scalar algebra given by the actual map of valuation completions. -/
@[instance_reducible] def completionAlgebra :
    Algebra base.valuation.Completion target.valuation.Completion :=
  (completionMap base target).toAlgebra

local instance : UniformContinuousConstSMul K (WithVal target.valuation) :=
  WithVal.uniformContinuousConstSMul_algebra target.valuation

local instance : Algebra base.valuation.Completion target.valuation.Completion :=
  completionAlgebra base target

/-- The completion scalar map commutes with the original ground-field map. -/
theorem completion_isScalarTower :
    @IsScalarTower K base.valuation.Completion target.valuation.Completion
      _ (completionAlgebra base target).toSMul _ := by
  refine ⟨?_⟩
  intro k a b
  change completionMap base target (k • a) * b = k • (completionMap base target a * b)
  rw [Algebra.smul_def, map_mul, Algebra.smul_def, mul_assoc]
  exact congrArg (fun c => c * (completionMap base target a * b))
    (completionMap_coe_base base target k)

/-- Scalar multiplication by the ground-field completion is continuous. -/
theorem completion_continuousSMul :
    @ContinuousSMul base.valuation.Completion target.valuation.Completion
      (completionAlgebra base target).toSMul _ _ := by
  refine ⟨?_⟩
  change Continuous (fun p : base.valuation.Completion × target.valuation.Completion =>
    completionMap base target p.1 * p.2)
  exact (UniformSpace.Completion.continuous_map.comp continuous_fst).mul continuous_snd

/-- The embedding of the extension field into its completion, over the original base. -/
def toCompletionAlgHom : L →ₐ[K] target.valuation.Completion where
  __ := algebraMap L target.valuation.Completion
  commutes' _ := rfl

private def completionMapAlgHom :
    base.valuation.Completion →ₐ[K] target.valuation.Completion where
  __ := completionMap base target
  commutes' k := completionMap_coe_base base target k

/-- Multiplication defines the canonical tensor map into the extension completion. -/
def completionTensorHom :
    @AlgHom base.valuation.Completion (base.valuation.Completion ⊗[K] L)
      target.valuation.Completion _ _ _ _ (completionAlgebra base target) where
  __ := (Algebra.TensorProduct.lift (R := K) (S := K)
    (completionMapAlgHom base target) (toCompletionAlgHom (K := K) target)
    (fun a l => Commute.all (completionMap base target a)
      (toCompletionAlgHom (K := K) target l))).toRingHom
  commutes' a := by
    change Algebra.TensorProduct.lift (R := K) (S := K)
      (completionMapAlgHom base target) (toCompletionAlgHom (K := K) target)
      (fun b l => Commute.all (completionMap base target b)
        (toCompletionAlgHom (K := K) target l)) (a ⊗ₜ[K] 1) = completionMap base target a
    exact (Algebra.TensorProduct.lift_tmul (R := K) (S := K)
      (completionMapAlgHom base target) (toCompletionAlgHom (K := K) target)
      (fun b l => Commute.all (completionMap base target b)
        (toCompletionAlgHom (K := K) target l)) a 1).trans
      (by rw [map_one, mul_one]; rfl)

/-- The tensor map sends a pure tensor to the product of the two canonical images. -/
@[simp] theorem completionTensorHom_tmul (a : base.valuation.Completion) (l : L) :
    completionTensorHom base target (a ⊗ₜ[K] l) =
      completionMap base target a * (l : target.valuation.Completion) := by
  exact Algebra.TensorProduct.lift_tmul (R := K) (S := K)
    (completionMapAlgHom base target) (toCompletionAlgHom (K := K) target)
    (fun b m => Commute.all (completionMap base target b)
      (toCompletionAlgHom (K := K) target m)) a l

/-- The canonical tensor map is onto for every finite extension of discrete
valuations. Only the ground-field completion is normed in the proof. -/
theorem completionTensorHom_surjective [FiniteDimensional K L] :
    Function.Surjective (completionTensorHom base target) := by
  have : @IsScalarTower K base.valuation.Completion target.valuation.Completion
      _ (completionAlgebra base target).toSMul _ :=
    completion_isScalarTower base target
  have : (Valued.v : _root_.Valuation (WithVal base.valuation)
      base.ValueGroup).IsRankOneDiscrete :=
    Valuation.isRankOneDiscrete_comap_ringEquiv base.valuation (WithVal.equiv base.valuation)
  let : (Valued.v : _root_.Valuation (WithVal base.valuation) base.ValueGroup).RankOne :=
    _root_.Valuation.IsRankOneDiscrete.rankOne
      (Valued.v : _root_.Valuation (WithVal base.valuation) base.ValueGroup)
      (e := 2) (by norm_num)
  let : NontriviallyNormedField (WithVal base.valuation) :=
    Valued.toNontriviallyNormedField (WithVal base.valuation) base.ValueGroup
  let : NontriviallyNormedField base.valuation.Completion :=
    { (inferInstance : NormedField base.valuation.Completion) with
      non_trivial := by
        obtain ⟨k, hk⟩ := NormedField.exists_one_lt_norm (WithVal base.valuation)
        exact ⟨(k : base.valuation.Completion),
          (UniformSpace.Completion.norm_coe k).symm ▸ hk⟩ }
  have : @ContinuousSMul base.valuation.Completion target.valuation.Completion
      (completionAlgebra base target).toSMul _ _ :=
    completion_continuousSMul base target
  have hdense : DenseRange (toCompletionAlgHom (K := K) target) := by
    change DenseRange (algebraMap L target.valuation.Completion)
    exact WithVal.denseRange_algebraMap_completion target.valuation
  have honto := Completion.tensorProduct_lift_surjective_of_denseRange
    (A := base.valuation.Completion) (toCompletionAlgHom (K := K) target) hdense
  have heq : completionTensorHom base target =
      Algebra.TensorProduct.lift (R := K) (S := base.valuation.Completion)
        (Algebra.ofId base.valuation.Completion target.valuation.Completion)
        (toCompletionAlgHom (K := K) target)
        (fun a l => Commute.all (completionMap base target a)
          (toCompletionAlgHom (K := K) target l)) := by
    apply Algebra.TensorProduct.ext'
    intro a l
    exact completionTensorHom_tmul base target a l
  exact heq.symm ▸ honto

/-- Every finite extension of discrete valuations gives a finite extension
of their actual completions. -/
theorem completion_finiteDimensional [FiniteDimensional K L] :
    @FiniteDimensional base.valuation.Completion target.valuation.Completion _ _
      (completionAlgebra base target).toModule := by
  exact Module.Finite.of_surjective (completionTensorHom base target).toLinearMap
    (completionTensorHom_surjective base target)

/-- For a finite separable extension of a Henselian DVF, the canonical tensor
map is injective because its actual source is a field. -/
theorem completionTensorHom_injective [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [HenselianRing base.valuationSubring base.maximalIdeal] :
    Function.Injective (completionTensorHom base target) := by
  let hbase : HenselianDVF K := { toDVF := base }
  let : Field (base.valuation.Completion ⊗[K] L) :=
    (hbase.completionTensor_isField L).toField
  exact (completionTensorHom base target).injective

/-- Completing a finite separable extension of a Henselian DVF is scalar
extension along the actual map of ground-field completions. -/
def completionTensorEquiv [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [HenselianRing base.valuationSubring base.maximalIdeal] :
    @AlgEquiv base.valuation.Completion (base.valuation.Completion ⊗[K] L)
      target.valuation.Completion _ _ _ _ (completionAlgebra base target) :=
  AlgEquiv.ofBijective (completionTensorHom base target)
    ⟨completionTensorHom_injective base target, completionTensorHom_surjective base target⟩

/-- The completion equivalence retains the prescribed embeddings of both fields. -/
@[simp] theorem completionTensorEquiv_tmul [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [HenselianRing base.valuationSubring base.maximalIdeal]
    (a : base.valuation.Completion) (l : L) :
    completionTensorEquiv base target (a ⊗ₜ[K] l) =
      completionMap base target a * (l : target.valuation.Completion) :=
  completionTensorHom_tmul base target a l

/-- A finite separable extension of a Henselian DVF has the same degree
after completing both valued fields. -/
theorem finrank_completion [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [HenselianRing base.valuationSubring base.maximalIdeal] :
    @Module.finrank base.valuation.Completion target.valuation.Completion _ _
      (completionAlgebra base target).toModule =
      Module.finrank K L := by
  rw [← (completionTensorEquiv base target).toLinearEquiv.finrank_eq]
  exact Module.finrank_baseChange

end ValuationTheory.DiscreteValuationField.DVF
