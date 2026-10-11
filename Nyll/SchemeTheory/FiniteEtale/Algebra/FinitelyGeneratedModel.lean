/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.FiniteEtale.Algebra.FiniteCoefficientModel
public import Mathlib.Algebra.Algebra.Subalgebra.Tower
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.Smooth.NoetherianDescent
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Finite étale models over finitely generated coefficient subalgebras

An actual étale model is supplied by Mathlib's Noetherian descent theorem.
Its coefficient ring is enlarged by the monic equations needed for module
finiteness. Both properties therefore hold on the same model, with the
original algebra recovered by the canonical tensor-product associativity
equivalence. The ambient base ring is completely arbitrary.

This supplies the affine coefficient model used in Stacks Project, tag 0BTV.
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Algebra.FiniteEtale

/-- A finite étale algebra over any scalar extension has a finite étale
model over an actual finitely generated coefficient subalgebra. -/
theorem exists_fg_subalgebra_model
    (R : Type u) (A : Type v) (B : Type w)
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Module.Finite A B] [Algebra.Etale A B] :
    ∃ (A₁ : Subalgebra R A) (B₁ : Type v) (_ : CommRing B₁) (_ : Algebra A₁ B₁),
      A₁.FG ∧ Module.Finite A₁ B₁ ∧ Algebra.Etale A₁ B₁ ∧
        Nonempty (B ≃ₐ[A] A ⊗[A₁] B₁) := by
  obtain ⟨A₀, B₀, hring, halgebra, hfg, hetale, ⟨e⟩⟩ :=
    Algebra.Etale.exists_subalgebra_fg R A B
  let : CommRing B₀ := hring
  let : Algebra A₀ B₀ := halgebra
  have : Algebra.Etale A₀ B₀ := hetale
  have : Module.Finite A (A ⊗[A₀] B₀) := Module.Finite.equiv e.toLinearEquiv
  obtain ⟨T, hT, hfinite⟩ := exists_fg_subalgebra_finite_tensorProduct A₀ A B₀
  have : Algebra.FiniteType R A₀ := (Subalgebra.fg_iff_finiteType A₀).mp hfg
  have : Algebra.FiniteType A₀ T := (Subalgebra.fg_iff_finiteType T).mp hT
  have : Algebra.FiniteType R T := Algebra.FiniteType.trans
    (R := R) (S := A₀) (A := T) inferInstance inferInstance
  let A₁ : Subalgebra R A := T.restrictScalars R
  let B₁ : Type v := T ⊗[A₀] B₀
  let hA₁ : Algebra A₁ B₁ := (inferInstance : Algebra T B₁)
  refine ⟨A₁, B₁, inferInstance, hA₁,
    (Subalgebra.fg_iff_finiteType A₁).mpr (inferInstance : Algebra.FiniteType R T),
    hfinite, (inferInstance : Algebra.Etale T B₁), ?_⟩
  exact ⟨e.trans (Algebra.TensorProduct.cancelBaseChange A₀ T A A B₀).symm⟩

end Algebra.FiniteEtale
