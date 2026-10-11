/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FiniteGroups.StandardClasses
import Mathlib.GroupTheory.PGroup
import Mathlib.Data.Nat.PrimeFin

/-!
# Singleton Sigma classes are finite p-groups

The finite class equality identifies the actual residual cores and maximal
quotients used by the singleton-Sigma and pro-p formulations.
-/

namespace ProCGroups.FiniteGroupClass

universe u

/-- A finite group has no prime divisors outside `{p}` exactly when it is a
finite p-group. -/
theorem sigmaGroup_singleton_iff_pGroup (p : ℕ) [Fact p.Prime]
    (G : Type u) [Group G] : sigmaGroup {p} G ↔ pGroup p G := by
  constructor
  · intro hG
    have : Finite G := hG.1
    refine ⟨hG.1, (isPGroup_iff_primeFactors_card_subset
      (Fact.out : p.Prime).ne_zero).mpr ?_⟩
    intro q hq
    have hqprime : q.Prime := (Nat.mem_primeFactors.mp hq).1
    have hqdvd : q ∣ Nat.card G := (Nat.mem_primeFactors.mp hq).2.1
    have hqp : q = p := by
      by_contra hne
      exact hG.2 q hqprime (fun hmem => hne (Set.mem_singleton_iff.mp hmem)) hqdvd
    rw [hqp]
    exact Nat.mem_primeFactors.mpr
      ⟨Fact.out, dvd_refl p, (Fact.out : p.Prime).ne_zero⟩
  · intro hG
    have : Finite G := hG.1
    obtain ⟨n, hn⟩ := hG.2.exists_card_eq
    refine ⟨hG.1, ?_⟩
    rw [hn]
    exact IsSigmaNumber.prime_pow_of_mem (Set.mem_singleton p) (Fact.out : p.Prime)

/-- Equality of the bundled finite classes also identifies their actual
maximal residual quotient constructions, without a comparison hypothesis. -/
theorem sigmaGroup_singleton_eq_pGroup (p : ℕ) [Fact p.Prime] :
    sigmaGroup.{u} {p} = pGroup.{u} p := by
  have hpred : (sigmaGroup.{u} {p}).pred = (pGroup.{u} p).pred := by
    funext G inst
    exact propext (sigmaGroup_singleton_iff_pGroup p G)
  have hext (C D : FiniteGroupClass.{u}) (h : C.pred = D.pred) : C = D := by
    cases C
    cases D
    cases h
    rfl
  exact hext _ _ hpred

end ProCGroups.FiniteGroupClass
