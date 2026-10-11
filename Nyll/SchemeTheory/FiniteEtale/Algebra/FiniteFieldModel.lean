/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.FiniteEtale.Algebra.IntegralFiniteModel
import Nyll.ValuedFieldTheory.Valuation.Completion.FiniteSubfieldTensor
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Algebra.Tower
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Finite étale models after extending the constant field

A finite étale algebra over `R ⊗[k] L`, for an algebraic extension `L/k`,
descends to `R ⊗[k] F` for an actual finite intermediate field `F`.
We reuse the integral finite-model construction and ValuedFieldTheory's
finite-coefficient tensor lifting. The remaining step embeds the whole
finitely generated model base into one finite constant extension and extends
scalars along that embedding.
-/

noncomputable section

open scoped TensorProduct

universe u

namespace Algebra.FiniteEtale

private theorem tensor_field_range_mono
    {k L R : Type u} [Field k] [Field L] [CommRing R]
    [Algebra k L] [Algebra k R]
    {F E : IntermediateField k L} (h : F ≤ E) :
    (Algebra.TensorProduct.map (R := k) (S := R) (AlgHom.id R R) F.val).range ≤
      (Algebra.TensorProduct.map (R := k) (S := R) (AlgHom.id R R) E.val).range := by
  let i : F →ₐ[k] E := IntermediateField.inclusion h
  have hi :
      (Algebra.TensorProduct.map (R := k) (S := R) (AlgHom.id R R) E.val).comp
          (Algebra.TensorProduct.map (R := k) (S := R) (AlgHom.id R R) i) =
        Algebra.TensorProduct.map (R := k) (S := R) (AlgHom.id R R) F.val := by
    ext f
    rfl
  intro z hz
  obtain ⟨w, rfl⟩ := hz
  refine ⟨Algebra.TensorProduct.map (R := k) (S := R) (AlgHom.id R R) i w, ?_⟩
  exact DFunLike.congr_fun hi w

private theorem exists_finiteIntermediateField_range
    {k L R : Type u} [Field k] [Field L] [CommRing R]
    [Algebra k L] [Algebra k R] [Algebra.IsAlgebraic k L]
    (T : Subalgebra R (R ⊗[k] L)) (hT : T.FG) :
    ∃ F : IntermediateField k L, FiniteDimensional k F ∧
      T ≤ (Algebra.TensorProduct.map (R := k) (S := R) (AlgHom.id R R) F.val).range := by
  classical
  obtain ⟨g, hg⟩ := hT
  choose F hF w hw using fun z : g ↦
    ValuationTheory.Completion.exists_finiteSubfield_tensor_lift z.val
  let (z : g) : FiniteDimensional k (F z) := hF z
  let E : IntermediateField k L := ⨆ z : g, F z
  refine ⟨E, inferInstance, ?_⟩
  rw [← hg]
  apply Algebra.adjoin_le
  intro z hz
  let zg : g := ⟨z, hz⟩
  apply tensor_field_range_mono (le_iSup F zg)
  exact ⟨w zg, hw zg⟩

/-- Enlarge an actual finite model base through an injective algebra map. -/
private theorem exists_model_over_range
    {R S B : Type u} [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B]
    (m : B →ₐ[R] S) (hm : Function.Injective m)
    (T : Subalgebra R S) (hT : T ≤ m.range)
    (A₀ : CommAlgCat.FiniteEtale.{u} T) :
    letI : Algebra B S := m.toRingHom.toAlgebra
    ∃ A₁ : CommAlgCat.FiniteEtale.{u} B,
      Nonempty (S ⊗[T] A₀ ≃ₐ[S] S ⊗[B] A₁) := by
  let : Algebra B S := m.toRingHom.toAlgebra
  let em : B ≃ₐ[R] m.range := AlgEquiv.ofInjective m hm
  let f : T →ₐ[R] B :=
    em.symm.toAlgHom.comp (T.val.codRestrict m.range (fun x ↦ hT x.property))
  have hmf : m.comp f = T.val := by
    ext x
    exact congrArg Subtype.val (em.apply_symm_apply ⟨x.val, hT x.property⟩)
  let : Algebra T B := f.toRingHom.toAlgebra
  let : IsScalarTower T B S :=
    IsScalarTower.of_algebraMap_eq' (congrArg AlgHom.toRingHom hmf).symm
  let A₁ : Type u := B ⊗[T] A₀
  refine ⟨CommAlgCat.FiniteEtale.of B A₁, ?_⟩
  exact ⟨(Algebra.TensorProduct.cancelBaseChange T B S S A₀).symm⟩

/-- Every finite étale algebra over an affine constant extension is obtained
from a finite étale algebra over an actual finite intermediate field.
The scalar extension in the conclusion uses the literal tensor map of the
intermediate-field inclusion. No model or descent witness is assumed. -/
theorem exists_finiteIntermediateField_model
    (k L R : Type u) [Field k] [Field L] [CommRing R]
    [Algebra k L] [Algebra k R] [Algebra.IsAlgebraic k L]
    (A : CommAlgCat.FiniteEtale.{u} (R ⊗[k] L)) :
    ∃ F : IntermediateField k L, FiniteDimensional k F ∧
      letI : Algebra (R ⊗[k] F) (R ⊗[k] L) :=
        (Algebra.TensorProduct.map (R := k) (S := R) (AlgHom.id R R) F.val).toRingHom.toAlgebra
      ∃ A₀ : CommAlgCat.FiniteEtale.{u} (R ⊗[k] F),
        Nonempty (A ≃ₐ[R ⊗[k] L] (R ⊗[k] L) ⊗[R ⊗[k] F] A₀) := by
  obtain ⟨T, A₀, hring, halgebra, hTfinite, hfinite, hetale, ⟨eA⟩⟩ :=
    exists_finite_subalgebra_model R (R ⊗[k] L) A
  let : CommRing A₀ := hring
  let : Algebra T A₀ := halgebra
  let : Module.Finite T A₀ := hfinite
  let : Algebra.Etale T A₀ := hetale
  let : Module.Finite R T := hTfinite
  have hT : T.FG := (Subalgebra.fg_iff_finiteType T).mpr inferInstance
  obtain ⟨F, hF, hTF⟩ := exists_finiteIntermediateField_range T hT
  refine ⟨F, hF, ?_⟩
  let m : (R ⊗[k] F) →ₐ[R] (R ⊗[k] L) :=
    Algebra.TensorProduct.map (AlgHom.id R R) F.val
  let : Algebra (R ⊗[k] F) (R ⊗[k] L) := m.toRingHom.toAlgebra
  have hm : Function.Injective m :=
    TensorProduct.map_injective_of_flat_flat
      (AlgHom.id k R).toLinearMap F.val.toLinearMap
      (Function.injective_id) Subtype.val_injective
  obtain ⟨A₁, ⟨e₁⟩⟩ := by
    with_reducible_and_instances
      exact exists_model_over_range (R := R) (S := R ⊗[k] L) (B := R ⊗[k] F)
        m hm T hTF (CommAlgCat.FiniteEtale.of T A₀)
  exact ⟨A₁, ⟨eA.trans e₁⟩⟩

end Algebra.FiniteEtale

end
