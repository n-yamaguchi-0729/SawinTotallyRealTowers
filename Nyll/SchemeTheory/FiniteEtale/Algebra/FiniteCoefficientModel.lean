/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.Polynomial.Subring
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Finite coefficient models of flat algebras

Finitely many monic equations over an arbitrary scalar extension use only
finitely many coefficients. Flatness ensures that those equations already
hold after adjoining their coefficients. In particular, this construction
requires neither an integral scalar extension nor injective transition maps.

This is the coefficient-enlargement step in the finite étale object descent
of Stacks Project, tags 0BTV and 01ZO. The monic polynomial restriction uses
Mathlib's `Polynomial.toSubring` API.
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Algebra.FiniteEtale

/-- If a flat finite-type algebra becomes module-finite after an arbitrary
scalar extension, it is already module-finite after extending scalars to
one finitely generated subalgebra of that extension. -/
theorem exists_fg_subalgebra_finite_tensorProduct
    (R : Type u) (A : Type v) (B : Type w)
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Module.Flat R B]
    [Algebra.FiniteType R B] [Module.Finite A (A ⊗[R] B)] :
    ∃ (T : Subalgebra R A), T.FG ∧ Module.Finite T (T ⊗[R] B) := by
  classical
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out (R := R) (A := B))
  have hi (b : s) : IsIntegral A ((1 : A) ⊗ₜ[R] (b : B)) :=
    _root_.IsIntegral.of_finite A _
  choose p hp hz using hi
  let c : Set A := ⋃ b : s, ((p b).coeffs : Set A)
  let T : Subalgebra R A := Algebra.adjoin R c
  have hc : c.Finite := Set.finite_iUnion fun b : s ↦ (p b).coeffs.finite_toSet
  have hfg : T.FG := Subalgebra.fg_def.mpr ⟨c, hc, rfl⟩
  have hcoeff (b : s) : ((p b).coeffs : Set A) ⊆ T := by
    intro a ha
    apply Algebra.subset_adjoin
    exact Set.mem_iUnion.mpr ⟨b, ha⟩
  have hint (b : s) : IsIntegral T ((1 : A) ⊗ₜ[R] (b : B)) := by
    let q : Polynomial T := (p b).toSubring T.toSubring (hcoeff b)
    refine ⟨q, ((p b).monic_toSubring T.toSubring (hcoeff b)).mpr (hp b), ?_⟩
    rw [IsScalarTower.algebraMap_eq T A (A ⊗[R] B), ← Polynomial.eval₂_map]
    change Polynomial.eval₂ (algebraMap A (A ⊗[R] B))
      ((1 : A) ⊗ₜ[R] (b : B))
      (((p b).toSubring T.toSubring (hcoeff b)).map T.toSubring.subtype) = 0
    rw [Polynomial.map_toSubring]
    exact hz b
  let f : T ⊗[R] B →ₐ[T] A ⊗[R] B :=
    Algebra.TensorProduct.map (Algebra.ofId T A) (AlgHom.id R B)
  have hflinear : f.toLinearMap.restrictScalars R = T.val.toLinearMap.rTensor B := by
    apply _root_.TensorProduct.ext'
    intro a b
    rfl
  have hf : Function.Injective f := by
    change Function.Injective (f.toLinearMap.restrictScalars R)
    rw [hflinear]
    exact Module.Flat.rTensor_preserves_injective_linearMap T.val.toLinearMap
      Subtype.val_injective
  have hiT : ∀ x ∈ ((fun b : B ↦ (1 : T) ⊗ₜ[R] b) '' (s : Set B)),
      IsIntegral T x := by
    rintro x ⟨b, hb, rfl⟩
    apply (isIntegral_algHom_iff f hf).mp
    change IsIntegral T ((algebraMap T A 1) ⊗ₜ[R] b)
    rw [map_one]
    exact hint ⟨b, hb⟩
  have hg : Algebra.adjoin T ((fun b : B ↦ (1 : T) ⊗ₜ[R] b) '' (s : Set B)) = ⊤ :=
    Algebra.TensorProduct.adjoin_one_tmul_image_eq_top (s : Set B) hs
  refine ⟨T, hfg, ⟨?_⟩⟩
  have hfinite := fg_adjoin_of_finite (R := T)
    (s.finite_toSet.image (fun b : B ↦ (1 : T) ⊗ₜ[R] b)) hiT
  rw [hg, Algebra.top_toSubmodule] at hfinite
  exact hfinite

end Algebra.FiniteEtale
