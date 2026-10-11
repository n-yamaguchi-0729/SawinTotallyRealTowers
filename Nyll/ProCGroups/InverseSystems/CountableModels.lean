/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Data.Set.Countable
import Mathlib.Topology.ClopenBox
import Mathlib.Topology.DiscreteQuotient
import Nyll.ProCGroups.InverseSystems.ProfiniteSpace

/-!
# Countable inverse-system models of profinite spaces

A second-countable profinite space is represented as an inverse limit of a sequence of finite
discrete spaces.  Conversely, the module characterizes second countability by the existence of
a finite-discrete inverse-system presentation over a countable linear order.
-/

open Set
open scoped Topology

namespace ProCGroups.InverseSystems

universe u w

/-- A second-countable profinite space is a sequential inverse limit of finite discrete spaces. -/
theorem exists_nat_inverseSystem_of_secondCountable (X : Type w) [TopologicalSpace X]
    [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    [SecondCountableTopology X] :
    ∃ S : InverseSystem.{0, w} (I := ℕ),
      (∀ n, Finite (S.X n)) ∧ (∀ n, DiscreteTopology (S.X n)) ∧
      Nonempty (X ≃ₜ S.inverseLimit) := by
  classical
  let : Countable (DiscreteQuotient X) := by
    have : Countable (TopologicalSpace.Clopens X) :=
      TopologicalSpace.Clopens.countable_iff_secondCountable.mpr
        (inferInstance : SecondCountableTopology X)
    exact (DiscreteQuotient.finsetClopens_inj X).countable
  let e : ℕ → DiscreteQuotient X :=
    Set.enumerateCountable (s := (Set.univ : Set (DiscreteQuotient X))) Set.countable_univ ⊤
  let q : ℕ → DiscreteQuotient X := fun n =>
    Nat.rec (motive := fun _ => DiscreteQuotient X) (e 0)
      (fun n qn => qn ⊓ e (n + 1)) n
  have hq_succ : ∀ n, q (n + 1) = q n ⊓ e (n + 1) := by
    intro n
    simp only [q]
  have hq_antitone : Antitone q := by
    refine antitone_nat_of_succ_le ?_
    intro n
    rw [hq_succ]
    exact inf_le_left
  have hq_le_enum : ∀ n, q n ≤ e n := by
    intro n
    induction n with
    | zero =>
        simp only [Nat.rec_zero, le_refl, q]
    | succ n ih =>
        rw [hq_succ]
        exact inf_le_right
  let σ : ℕ → OrderDual (DiscreteQuotient X) := fun n =>
    (show OrderDual (DiscreteQuotient X) from q n)
  have hσ : Monotone σ := by
    intro m n hmn
    change q n ≤ q m
    exact hq_antitone hmn
  have hdirNat : Directed (· ≤ ·) (id : ℕ → ℕ) := by
    intro a b
    exact ⟨max a b, le_max_left _ _, le_max_right _ _⟩
  have hrange : Set.range e = (Set.univ : Set (DiscreteQuotient X)) := by
    exact Set.range_enumerateCountable_of_mem
      (s := (Set.univ : Set (DiscreteQuotient X))) Set.countable_univ
      (default := (⊤ : DiscreteQuotient X)) (Set.mem_univ (⊤ : DiscreteQuotient X))
  have hcofinal : ∀ Q : OrderDual (DiscreteQuotient X), ∃ n : ℕ, Q ≤ σ n := by
    intro Q
    have hQ : (Q : DiscreteQuotient X) ∈ Set.range e := by
      rw [hrange]
      exact Set.mem_univ (Q : DiscreteQuotient X)
    rcases hQ with ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    change q n ≤ e n
    exact hq_le_enum n
  let S0 : InverseSystem (I := OrderDual (DiscreteQuotient X)) := discreteQuotientSystem X
  let S : InverseSystem (I := ℕ) := S0.reindex σ hσ
  refine ⟨S, ?_, ?_, ?_⟩
  · intro n
    have hfiniteQ (A : DiscreteQuotient X) : Finite ↥A := inferInstance
    exact hfiniteQ (q n)
  · intro n
    have hdiscreteQ (A : DiscreteQuotient X) : DiscreteTopology ↥A := inferInstance
    exact hdiscreteQ (q n)
  · refine ⟨(homeomorph_inverseLimit_discreteQuotientSystem X).trans ?_⟩
    exact S0.homeomorph_reindex_cofinal σ hσ hdirNat hcofinal

/--
A profinite space is second countable exactly when it admits a presentation as an inverse limit
of finite discrete spaces over a countable linear order.
-/
theorem secondCountable_iff_exists_countableLinearOrder_finiteDiscreteInverseSystem
    {X : Type w} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] :
    SecondCountableTopology X ↔
      ∃ (J : Type) (_ : LinearOrder J) (_ : Countable J),
        ∃ S : InverseSystem.{0, w} (I := J),
          (∀ j, Finite (S.X j)) ∧ (∀ j, DiscreteTopology (S.X j)) ∧
            Nonempty (X ≃ₜ S.inverseLimit) := by
  constructor
  · intro hsecond
    let : SecondCountableTopology X := hsecond
    rcases exists_nat_inverseSystem_of_secondCountable X with ⟨S, hfinite, hdisc, hhomeo⟩
    exact ⟨ℕ, inferInstance, inferInstance, S, hfinite, hdisc, hhomeo⟩
  · rintro ⟨J, _hJord, hJcount, S, hfinite, _hdisc, ⟨e⟩⟩
    let : Countable J := hJcount
    let : ∀ j, SecondCountableTopology (S.X j) := fun j => by
      have : Finite (S.X j) := hfinite j
      exact Finite.toSecondCountableTopology
    have : SecondCountableTopology S.inverseLimit :=
      TopologicalSpace.Subtype.secondCountableTopology {x : ∀ j, S.X j | S.Compatible x}
    exact e.secondCountableTopology

end ProCGroups.InverseSystems
