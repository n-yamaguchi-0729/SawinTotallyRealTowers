/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.Smooth.NoetherianDescent
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Finite étale models over finite integral subalgebras

An étale algebra has a model over a finitely generated subalgebra of its base.
When the base is integral and the original algebra is finite, the model is
finite too: flatness embeds it into the scalar extension, where integrality
follows by transitivity. No Noetherian hypothesis on the original base is used.
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Algebra.FiniteEtale

/-- A finite étale algebra over an integral extension descends to a finite
étale algebra over an actual finite subalgebra of that extension. -/
theorem exists_finite_subalgebra_model
    (R : Type v) (S : Type u) (A : Type w)
    [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra.IsIntegral R S] [Algebra S A]
    [Module.Finite S A] [Algebra.Etale S A] :
    ∃ (S₀ : Subalgebra R S) (A₀ : Type u) (_ : CommRing A₀) (_ : Algebra S₀ A₀),
      Module.Finite R S₀ ∧ Module.Finite S₀ A₀ ∧ Algebra.Etale S₀ A₀ ∧
        Nonempty (A ≃ₐ[S] S ⊗[S₀] A₀) := by
  obtain ⟨S₀, A₀, hring, halgebra, hfg, hetale, ⟨e⟩⟩ :=
    Algebra.Etale.exists_subalgebra_fg R S A
  let : CommRing A₀ := hring
  let : Algebra S₀ A₀ := halgebra
  let : Algebra.Etale S₀ A₀ := hetale
  let : Algebra.FiniteType R S₀ := (Subalgebra.fg_iff_finiteType S₀).mp hfg
  let : Algebra.IsIntegral R S₀ :=
    Algebra.IsIntegral.of_injective S₀.val Subtype.val_injective
  let : Algebra.IsIntegral S₀ S := Algebra.IsIntegral.tower_top R
  let : Module.Finite S (S ⊗[S₀] A₀) := Module.Finite.equiv e.toLinearEquiv
  let : Algebra.IsIntegral S₀ (S ⊗[S₀] A₀) := Algebra.IsIntegral.trans S
  have hinj : Function.Injective
      (Algebra.TensorProduct.includeRight : A₀ →ₐ[S₀] S ⊗[S₀] A₀) :=
    Algebra.TensorProduct.includeRight_injective Subtype.val_injective
  let : Algebra.IsIntegral S₀ A₀ :=
    Algebra.IsIntegral.of_injective (R := S₀) (A := A₀) (B := S ⊗[S₀] A₀)
      (Algebra.TensorProduct.includeRight : A₀ →ₐ[S₀] S ⊗[S₀] A₀) hinj
  exact ⟨S₀, A₀, hring, halgebra, Algebra.IsIntegral.finite,
    Algebra.IsIntegral.finite, hetale, ⟨e⟩⟩

end Algebra.FiniteEtale
