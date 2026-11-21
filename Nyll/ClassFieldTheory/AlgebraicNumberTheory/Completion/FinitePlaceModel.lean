/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Topology.Algebra.Group.Units
public import Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.Completion
public import Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.Theory.AbsoluteValues

/-!
# A canonical finite-place completion model

The absolute-value and adic completions are compared using the unique extension
of the dense field embedding. Ring, algebra, topological, units, and tensor
interfaces all use this same map, with independent universes for the two fields.
-/

@[expose] public section

open scoped NumberField TensorProduct NNReal
open NumberField IsDedekindDomain

noncomputable section

universe u v

variable {K : Type u} [Field K] [NumberField K]
    {L : Type v} [Field L] [Algebra K L]

/-- The canonical dense embedding used to compare the absolute-value
completion at `v` with the concrete adic completion. -/
noncomputable def finitePlaceCompletionBaseMap
    (v : HeightOneSpectrum (𝓞 K)) :
    WithAbs (NumberField.HeightOneSpectrum.adicAbv K v) →+*
      v.adicCompletion K :=
  (FinitePlace.embedding v).comp
    (WithAbs.equiv
      (NumberField.HeightOneSpectrum.adicAbv K v)).toRingHom

/-- The dense comparison agrees with the canonical finite-place embedding. -/
@[simp]
theorem finitePlaceCompletionBaseMap_apply
    (v : HeightOneSpectrum (𝓞 K))
    (x : WithAbs
      (NumberField.HeightOneSpectrum.adicAbv K v)) :
    finitePlaceCompletionBaseMap v x =
      FinitePlace.embedding v
        (WithAbs.equiv
          (NumberField.HeightOneSpectrum.adicAbv K v) x) :=
  rfl

/-- The dense comparison preserves the absolute-value norm. -/
theorem finitePlaceCompletionBaseMap_norm
    (v : HeightOneSpectrum (𝓞 K))
    (x : WithAbs
      (NumberField.HeightOneSpectrum.adicAbv K v)) :
    ‖finitePlaceCompletionBaseMap v x‖ = ‖x‖ := by
  rw [finitePlaceCompletionBaseMap_apply,
    FinitePlace.norm_embedding]
  rfl

/-- The base embedding is an isometry. -/
theorem finitePlaceCompletionBaseMap_isometry
    (v : HeightOneSpectrum (𝓞 K)) :
    Isometry (finitePlaceCompletionBaseMap v) :=
  AddMonoidHomClass.isometry_of_norm _
    (finitePlaceCompletionBaseMap_norm v)

/-- Extension of the base embedding to the absolute-value completion. -/
noncomputable def finitePlaceCompletionRingHom
    (v : HeightOneSpectrum (𝓞 K)) :
    (NumberField.HeightOneSpectrum.adicAbv K v).Completion →+*
      v.adicCompletion K :=
  (UniformSpace.Completion.extensionHom
    (finitePlaceCompletionBaseMap v)
    (finitePlaceCompletionBaseMap_isometry v).continuous).comp
      AbsoluteValue.Completion.toCompletion

/-- Extension to the completion preserves the value on every dense generator. -/
@[simp]
theorem finitePlaceCompletionRingHom_coe
    (v : HeightOneSpectrum (𝓞 K))
    (x : WithAbs
      (NumberField.HeightOneSpectrum.adicAbv K v)) :
    finitePlaceCompletionRingHom v
        (x :
          (NumberField.HeightOneSpectrum.adicAbv K v).Completion) =
      finitePlaceCompletionBaseMap v x := by
  rw [finitePlaceCompletionRingHom, RingHom.comp_apply,
    AbsoluteValue.Completion.toCompletion_coe, UniformSpace.Completion.extensionHom_coe]

/-- Extending the dense comparison preserves its isometry. -/
theorem finitePlaceCompletionRingHom_isometry
    (v : HeightOneSpectrum (𝓞 K)) :
    Isometry (finitePlaceCompletionRingHom v) :=
  (finitePlaceCompletionBaseMap_isometry v).completion_extension.comp
    (AbsoluteValue.Completion.isometry_toCompletion (NumberField.HeightOneSpectrum.adicAbv K v))

/-- The completed comparison map is onto the concrete adic
completion. -/
theorem finitePlaceCompletionRingHom_surjective
    (v : HeightOneSpectrum (𝓞 K)) :
    Function.Surjective (finitePlaceCompletionRingHom v) := by
  let f := finitePlaceCompletionRingHom v
  have hrangeClosed : IsClosed (Set.range f) :=
    (finitePlaceCompletionRingHom_isometry v).isClosedEmbedding.isClosed_range
  have hdense :
      DenseRange (algebraMap K (v.adicCompletion K)) :=
    v.denseRange_algebraMap K
  have hrange :
      Set.range (algebraMap K (v.adicCompletion K)) ⊆
        Set.range f := by
    rintro _ ⟨x, rfl⟩
    let x' : WithAbs
        (NumberField.HeightOneSpectrum.adicAbv K v) :=
      (WithAbs.equiv
        (NumberField.HeightOneSpectrum.adicAbv K v)).symm x
    refine
      ⟨(x' :
          (NumberField.HeightOneSpectrum.adicAbv K v).Completion),
        ?_⟩
    rw [finitePlaceCompletionRingHom_coe]
    rfl
  intro x
  have hx :
      x ∈ closure
        (Set.range (algebraMap K (v.adicCompletion K))) := by
    rw [hdense.closure_range]
    trivial
  exact closure_minimal hrange hrangeClosed hx

/-- The two concrete models of `K_v` are canonically isomorphic. -/
noncomputable def finitePlaceCompletionRingEquiv
    (v : HeightOneSpectrum (𝓞 K)) :
    (NumberField.HeightOneSpectrum.adicAbv K v).Completion ≃+*
      v.adicCompletion K :=
  RingEquiv.ofBijective (finitePlaceCompletionRingHom v)
    ⟨(finitePlaceCompletionRingHom_isometry v).injective,
      finitePlaceCompletionRingHom_surjective v⟩

/-- The preceding ring equivalence, with its native topologies. -/
noncomputable def finitePlaceCompletionContinuousMulEquiv
    (v : HeightOneSpectrum (𝓞 K)) :
    (NumberField.HeightOneSpectrum.adicAbv K v).Completion ≃ₜ*
      v.adicCompletion K where
  __ := (finitePlaceCompletionRingEquiv v).toMulEquiv
  continuous_toFun :=
    (finitePlaceCompletionRingHom_isometry v).continuous
  continuous_invFun :=
    ((finitePlaceCompletionRingHom_isometry v).right_inv
      (finitePlaceCompletionRingEquiv v).right_inv).continuous

/-- The induced topological multiplicative equivalence on unit
groups. -/
noncomputable def finitePlaceCompletionUnitsContinuousMulEquiv
    (v : HeightOneSpectrum (𝓞 K)) :
    (NumberField.HeightOneSpectrum.adicAbv K v).Completionˣ ≃ₜ*
      (v.adicCompletion K)ˣ :=
  Units.mapContinuousMulEquiv
    (finitePlaceCompletionContinuousMulEquiv v)

/-- The canonical completion comparison as a `K`-algebra
equivalence. -/
noncomputable def finitePlaceCompletionAlgEquiv
    (v : HeightOneSpectrum (𝓞 K)) :
    (NumberField.HeightOneSpectrum.adicAbv K v).Completion ≃ₐ[K]
      v.adicCompletion K where
  __ := finitePlaceCompletionRingEquiv v
  commutes' x := by
    change finitePlaceCompletionRingHom v
      (algebraMap K (NumberField.HeightOneSpectrum.adicAbv K v).Completion x) =
        algebraMap K (v.adicCompletion K) x
    rw [AbsoluteValue.Completion.algebraMap_def, finitePlaceCompletionRingHom_coe,
      WithAbs.algebraMap_right_apply, Algebra.algebraMap_self_apply]
    rfl

/-- Base change of the first tensor factor gives the concrete tensor
algebra at `v`. -/
noncomputable def finitePlaceLocalTensorAlgEquiv
    (v : HeightOneSpectrum (𝓞 K)) :
    (NumberField.HeightOneSpectrum.adicAbv K v).Completion ⊗[K] L ≃ₐ[K]
      v.adicCompletion K ⊗[K] L :=
  Algebra.TensorProduct.congr
    (finitePlaceCompletionAlgEquiv v)
    (AlgEquiv.refl : L ≃ₐ[K] L)

/-- The tensor comparison acts on each factor of a pure tensor. -/
@[simp]
theorem finitePlaceLocalTensorAlgEquiv_tmul
    (v : HeightOneSpectrum (𝓞 K))
    (a : (NumberField.HeightOneSpectrum.adicAbv K v).Completion) (b : L) :
    finitePlaceLocalTensorAlgEquiv (L := L) v (a ⊗ₜ[K] b) =
      finitePlaceCompletionAlgEquiv v a ⊗ₜ[K] b :=
  rfl

/-- The induced equivalence on tensor-algebra unit groups. -/
noncomputable def finitePlaceLocalTensorUnitsEquiv
    (v : HeightOneSpectrum (𝓞 K)) :
    ((NumberField.HeightOneSpectrum.adicAbv K v).Completion ⊗[K] L)ˣ ≃*
      (v.adicCompletion K ⊗[K] L)ˣ :=
  Units.mapEquiv
    (finitePlaceLocalTensorAlgEquiv
      (K := K) (L := L) v).toMulEquiv

/-- Passing to units does not change the underlying tensor comparison. -/
@[simp]
theorem finitePlaceLocalTensorUnitsEquiv_coe
    (v : HeightOneSpectrum (𝓞 K))
    (z : ((NumberField.HeightOneSpectrum.adicAbv K v).Completion ⊗[K] L)ˣ) :
    (finitePlaceLocalTensorUnitsEquiv (L := L) v z : v.adicCompletion K ⊗[K] L) =
      finitePlaceLocalTensorAlgEquiv (L := L) v z :=
  rfl

/-- Membership in the concrete finite-place valuation ring implies the
usual norm bound. -/
theorem norm_le_one_of_mem_adicCompletionIntegers
    (w : HeightOneSpectrum (𝓞 K))
    {x : w.adicCompletion K}
    (hx : x ∈ w.adicCompletionIntegers K) :
    ‖x‖ ≤ 1 := by
  rw [FinitePlace.norm_def]
  exact_mod_cast
    (WithZeroMulInt.toNNReal_le_one_iff
      (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal w)).2 hx

/-- The concrete adic completion integers are exactly the elements of
norm at most one. -/
theorem mem_adicCompletionIntegers_of_norm_le_one
    (w : HeightOneSpectrum (𝓞 K))
    {x : w.adicCompletion K}
    (hx : ‖x‖ ≤ 1) :
    x ∈ w.adicCompletionIntegers K := by
  rw [FinitePlace.norm_def] at hx
  exact_mod_cast
    (WithZeroMulInt.toNNReal_le_one_iff
      (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal w)).1 hx

/-- The inverse of the universe-polymorphic completion comparison is
also an isometry. -/
theorem finitePlaceCompletionAlgEquiv_symm_norm
    (w : HeightOneSpectrum (𝓞 K))
    (x : w.adicCompletion K) :
    ‖(finitePlaceCompletionAlgEquiv w).symm x‖ =
      ‖x‖ := by
  let y :=
    (finitePlaceCompletionAlgEquiv w).symm x
  have h :=
    (finitePlaceCompletionRingHom_isometry w).norm_map_of_map_zero
      (map_zero
        (finitePlaceCompletionRingHom w)) y
  have hy :
      finitePlaceCompletionRingHom w y = x := by
    change
      finitePlaceCompletionAlgEquiv w y = x
    exact
      (finitePlaceCompletionAlgEquiv w).apply_symm_apply x
  rw [hy] at h
  exact h.symm

namespace RayClass

/-- Every finite-place absolute value is nontrivial. -/
theorem adicAbv_isNontrivial
    (v : HeightOneSpectrum (𝓞 K)) :
    (NumberField.HeightOneSpectrum.adicAbv K v).IsNontrivial := by
  obtain ⟨x, hxv, hx0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  refine ⟨algebraMap (𝓞 K) K x, ?_, ?_⟩
  · exact (FaithfulSMul.algebraMap_eq_zero_iff (𝓞 K) K).not.mpr hx0
  · apply ne_of_lt
    rw [← FinitePlace.norm_embedding]
    exact (FinitePlace.norm_lt_one_iff_mem (K := K) v x).2 hxv

end RayClass
