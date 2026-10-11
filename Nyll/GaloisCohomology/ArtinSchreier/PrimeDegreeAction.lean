/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.ArtinSchreier.FiniteRestrictionKernel
import Nyll.GaloisCohomology.FieldTheory.ContinuousAdditiveHilbert90
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-! # Nontrivial action on Artin–Schreier classes in residue-prime degree -/

namespace ArtinSchreierTheory

universe u v
variable (p : ℕ) [Fact p.Prime]
variable {K : Type u} {L : Type v} [Field K] [Field L]
  [CharP K p] [CharP L p] [Algebra K L] [IsGalois K L]

/-- A degree-p Galois extension cannot fix all Artin–Schreier classes
when the base field has infinitely many such classes. -/
theorem exists_moved_class_of_degree_eq_char
    [Infinite (K ⧸ ((frobenius K p).toAddMonoidHom - AddMonoidHom.id K).range)]
    (hdegree : Module.finrank K L = p) :
    ∃ τ : Gal(L/K), τ ≠ 1 ∧ ∃ x : L, ∀ y : L, y ^ p - y ≠ τ x - x := by
  classical
  have : FiniteDimensional K L :=
    FiniteDimensional.of_finrank_pos (hdegree.symm ▸ (Fact.out : p.Prime).pos)
  have hcard : Nat.card Gal(L/K) = p :=
    (IsGalois.card_aut_eq_finrank K L).trans hdegree
  let e : Gal(L/K) ≃* Multiplicative (ZMod p) :=
    mulEquivOfPrimeCardEq hcard
      (by rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card])
  let τ : Gal(L/K) := e.symm (Multiplicative.ofAdd (1 : ZMod p))
  have hτ : τ ≠ 1 := by
    intro h
    have ht : e τ = Multiplicative.ofAdd (1 : ZMod p) := e.apply_symm_apply _
    rw [h, map_one] at ht
    exact (one_ne_zero : (1 : ZMod p) ≠ 0) (congrArg Multiplicative.toAdd ht).symm
  by_contra hnone
  have hwp (x : L) : ∃ y : L, y ^ p - y = τ x - x := by
    by_contra h
    apply hnone
    refine ⟨τ, hτ, x, ?_⟩
    intro y hy
    exact h ⟨y, hy⟩
  have hbase (a : K) : ∃ y : L, y ^ p - y = algebraMap K L a := by
    let c : Gal(L/K) → L :=
      fun σ => (ZMod.castHom (dvd_refl p) L) (e σ).toAdd * algebraMap K L a
    have hc : ∀ σ υ : Gal(L/K), c (σ * υ) = σ (c υ) + c σ := by
      intro σ υ
      have hfixed : σ (c υ) = c υ := by
        dsimp only [c]
        rw [map_mul, σ.commutes]
        simp only [ZMod.castHom_apply, ZMod.cast_eq_val, map_natCast]
      rw [hfixed]
      change (ZMod.castHom (dvd_refl p) L) (e (σ * υ)).toAdd * algebraMap K L a =
        (ZMod.castHom (dvd_refl p) L) (e υ).toAdd * algebraMap K L a +
          (ZMod.castHom (dvd_refl p) L) (e σ).toAdd * algebraMap K L a
      rw [map_mul]
      change (ZMod.castHom (dvd_refl p) L) ((e σ).toAdd + (e υ).toAdd) *
        algebraMap K L a = _
      rw [map_add, add_mul, add_comm]
    obtain ⟨β, hβ⟩ := GaloisCohomology.additiveHilbert90_finite c hc
    obtain ⟨y, hy⟩ := hwp β
    refine ⟨y, hy.trans ((hβ τ).trans ?_)⟩
    change (ZMod.castHom (dvd_refl p) L) (e (e.symm _)).toAdd * algebraMap K L a =
      algebraMap K L a
    rw [e.apply_symm_apply]
    change (ZMod.castHom (dvd_refl p) L) 1 * algebraMap K L a = _
    rw [map_one, one_mul]
  have hzero (q : K ⧸
      ((frobenius K p).toAddMonoidHom - AddMonoidHom.id K).range) :
      classMap p (algebraMap K L) q = 0 := by
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective
      ((frobenius K p).toAddMonoidHom - AddMonoidHom.id K).range q
    change (algebraMap K L a : L ⧸
      ((frobenius L p).toAddMonoidHom - AddMonoidHom.id L).range) = 0
    apply (QuotientAddGroup.eq_zero_iff _).mpr
    exact hbase a
  have : Finite (classMap p (algebraMap K L)).ker := finite_classMap_kernel p
  have : Finite (K ⧸
      ((frobenius K p).toAddMonoidHom - AddMonoidHom.id K).range) :=
    Finite.of_injective
      (fun q => (⟨q, hzero q⟩ : (classMap p (algebraMap K L)).ker))
      (fun _ _ h => congrArg Subtype.val h)
  exact not_finite (K ⧸
    ((frobenius K p).toAddMonoidHom - AddMonoidHom.id K).range)

end ArtinSchreierTheory
