/-
Copyright (c) 2024 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning

The characteristic-polynomial argument is adapted from
Mathlib/RingTheory/Invariant/Basic.lean, lines 413–446, at
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/RingTheory/Invariant/Basic.lean#L413-L446

Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
The RingHom-only decomposition is by
Naganori Yamaguchi (assisted by OpenAI Codex).
https://github.com/n-yamaguchi-0729
-/

import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.RingTheory.Invariant.Basic

/-!
# Finite invariant ring images

A ring automorphism of a domain preserves the image of a finite invariant ring
extension whenever it fixes the composite coefficient map. Only native ring
homomorphisms are used on the target. In particular, the argument does not add
an algebra structure on the target domain.

The polynomial evaluation and root extraction are separate proofs so that the
coefficient-algebra scope does not also instantiate the polynomial constant map.
-/

open scoped BigOperators

namespace EtaleFundamentalGroups.Inertia

/-- Transport a root of a polynomial lifted along `a` through an endomorphism
fixing the composite coefficient map. -/
private theorem eval₂_eq_zero_of_lift_and_fixed_coefficients
    {A C T : Type*} [CommRing A] [CommRing C] [CommRing T]
    (a : A →+* C) (f : C →+* T) (σ : T →+* T)
    (hσ : σ.comp (f.comp a) = f.comp a)
    (p : Polynomial A) (q : Polynomial C) (hp : p.map a = q)
    (x : C) (hx : q.eval x = 0) :
    q.eval₂ f (σ.toFun (f.toFun x)) = 0 := by
  rw [RingHom.toFun_eq_coe σ, RingHom.toFun_eq_coe f]
  calc
    q.eval₂ f (σ (f x)) = p.eval₂ (f.comp a) (σ (f x)) := by
      rw [← hp, Polynomial.eval₂_map]
    _ = p.eval₂ (σ.comp (f.comp a)) (σ (f x)) := by
      rw [hσ]
    _ = σ (p.eval₂ (f.comp a) (f x)) :=
      (Polynomial.hom_eval₂ p (f.comp a) σ (f x)).symm
    _ = σ ((p.map a).eval₂ f (f x)) := by
      rw [Polynomial.eval₂_map]
    _ = σ (q.eval₂ f (f x)) := by rw [hp]
    _ = σ (f (q.eval x)) :=
      congrArg σ (Polynomial.eval₂_at_apply (p := q) f x)
    _ = σ (f 0) := congrArg (fun z : C => σ (f z)) hx
    _ = σ 0 := congrArg σ (map_zero f)
    _ = 0 := map_zero σ

/-- A zero of the mapped orbit polynomial is one of the mapped orbit elements. -/
private theorem exists_smul_of_eval₂_charpoly_eq_zero
    {C T H : Type*} [CommRing C] [CommRing T] [IsDomain T]
    [Group H] [Fintype H] [MulSemiringAction H C]
    (f : C →+* T) (x : C) (y : T)
    (hy : (MulSemiringAction.charpoly H x).eval₂ f y = 0) :
    ∃ h : H, y = f.toFun (h • x) := by
  have hprod : (∏ h : H, (y - f (h • x))) = 0 := by
    simpa only [MulSemiringAction.charpoly_eq, Polynomial.eval₂_finsetProd,
      Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C] using hy
  obtain ⟨h, _, hh⟩ := Finset.prod_eq_zero_iff.mp hprod
  refine ⟨h, ?_⟩
  rw [RingHom.toFun_eq_coe f]
  exact sub_eq_zero.mp hh

/-- An automorphism fixing the image of the coefficient ring sends each image
element into the image of its finite orbit. -/
theorem exists_smul_ringHom_apply_of_invariant
    {A C T H : Type*} [CommRing A] [CommRing C] [CommRing T] [IsDomain T]
    [Algebra A C] [Group H] [Finite H] [MulSemiringAction H C]
    [Algebra.IsInvariant A C H]
    (f : C →+* T) (φ : T ≃+* T)
    (hφ : φ.toRingHom.comp (f.comp (algebraMap A C)) =
      f.comp (algebraMap A C))
    (x : C) :
    ∃ h : H, φ.toRingHom.toFun (f.toFun x) = f.toFun (h • x) := by
  cases nonempty_fintype H
  obtain ⟨p, hp⟩ := (Polynomial.mem_lifts (MulSemiringAction.charpoly H x)).mp
    (Algebra.IsInvariant.charpoly_mem_lifts A C H x)
  apply exists_smul_of_eval₂_charpoly_eq_zero f x
  exact eval₂_eq_zero_of_lift_and_fixed_coefficients
    (algebraMap A C) f φ.toRingHom hφ p (MulSemiringAction.charpoly H x) hp x
    (MulSemiringAction.eval_charpoly H x)

end EtaleFundamentalGroups.Inertia
