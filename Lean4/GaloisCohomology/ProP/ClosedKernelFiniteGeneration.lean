/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import GaloisCohomology.ProP.ClosedKernelH2FiniteFamily
import GaloisCohomology.ProP.TrivialZModP
import ProCGroups.Cohomology.RelativeNakayama
import ProCGroups.Presentations.Profinite
import ProCGroups.ProC.InverseLimits.Predicates
import ProCGroups.ProP.FrattiniPowers
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.Topology.Instances.ZMod

set_option autoImplicit false

/-!
# Finite normal generation from finite-dimensional H²

For a closed normal subgroup contained in the power--commutator subgroup of a pro-p group,
relative Nakayama constructs a new detecting invariant character whenever the chosen relators
do not normally generate.  Their triangular evaluation matrix forces independent H² classes.
Thus the H² dimension bounds an actual finite closed normal generating family.
-/

open scoped Topology

namespace ClassFieldTower.ProP

open ProCGroups ProCGroups.ProC ProCGroups.Presentations ClassFieldTower.Cohomology

noncomputable section

universe u v

private theorem linearIndependent_of_triangular_evaluation
    {k : Type v} [Field k] {X : Type u} {n : ℕ}
    (v : Fin n → X → k) (x : Fin n → X)
    (hdiag : ∀ i, v i (x i) ≠ 0)
    (htri : ∀ i j, j < i → v i (x j) = 0) : LinearIndependent k v := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a ha i
  have hzero : ∀ m : ℕ, ∀ hm : m < n, a ⟨m, hm⟩ = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro hm
      let j : Fin n := ⟨m, hm⟩
      have heval : ∑ l, a l * v l (x j) = 0 := by
        simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
          using congrFun ha (x j)
      have hother (l : Fin n) (hlj : l ≠ j) : a l * v l (x j) = 0 := by
        rcases lt_or_gt_of_ne hlj with hlt | hgt
        · have hlzero : a l = 0 := ih l.val hlt l.isLt
          rw [hlzero, zero_mul]
        · rw [htri l j hgt, mul_zero]
      rw [Finset.sum_eq_single j (fun l _ hlj ↦ hother l hlj)
        (fun hj ↦ (hj (Finset.mem_univ j)).elim)] at heval
      exact (mul_eq_zero.mp heval).resolve_right (hdiag j)
  exact hzero i.val i.isLt

/-- A closed normal subgroup in the Frattini subgroup is generated, as a closed normal
subgroup, by at most `dim H²(F/R, ZMod p)` actual relators. -/
theorem exists_closedNormal_generating_family_le_finrank_h2
    {p : ℕ} [Fact p.Prime]
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
    (hF : HasPGroupOpenNormalBasis p F)
    (R : ClosedSubgroup F) [R.Normal]
    (hR : (R : Subgroup F) ≤ closedPowerCommutator p F)
    [FiniteDimensional (ZMod p)
      (continuousCohomologyZModPLifted p (F ⧸ (R : Subgroup F)) 2)] :
    ∃ r ≤ Module.finrank (ZMod p)
        (continuousCohomologyZModPLifted p (F ⧸ (R : Subgroup F)) 2),
      ∃ ρ : Fin r → R,
        closedNormalClosure (Set.range (fun i ↦ (ρ i : F))) = (R : Subgroup F) := by
  classical
  let d : ℕ := Module.finrank (ZMod p)
    (continuousCohomologyZModPLifted p (F ⧸ (R : Subgroup F)) 2)
  by_contra hnone
  have hnot (n : ℕ) (hn : n ≤ d) (ρ : Fin n → R) :
      closedNormalClosure (Set.range (fun i ↦ (ρ i : F))) ≠ (R : Subgroup F) := by
    intro heq
    exact hnone ⟨n, hn, ρ, heq⟩
  have hbuild (n : ℕ) (hn : n ≤ d + 1) :
      ∃ ρ : Fin n → R, ∃ χ : Fin n → R →ₜ* Multiplicative (ZMod p),
        (∀ (i : Fin n) (f : F) (r : R), χ i (MulAut.conjNormal f r) = χ i r) ∧
        (∀ i : Fin n, χ i (ρ i) ≠ 1) ∧
        ∀ i j : Fin n, j < i → χ i (ρ j) = 1 := by
    induction n with
    | zero =>
      refine ⟨Fin.elim0, Fin.elim0, ?_, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
    | succ n ih =>
      obtain ⟨ρ, χ, hχinv, hdiag, htri⟩ := ih (Nat.le_trans (Nat.le_succ n) hn)
      let K : ClosedSubgroup F :=
        { toSubgroup := closedNormalClosure (Set.range (fun i ↦ (ρ i : F)))
          isClosed' := closedNormalClosure_isClosed (Set.range (fun i ↦ (ρ i : F))) }
      let : K.Normal :=
        inferInstanceAs (closedNormalClosure (Set.range (fun i ↦ (ρ i : F)))).Normal
      have hKR : K ≤ R := by
        apply closedNormalClosure_le_closed_normal R.isClosed'
        rintro r ⟨i, rfl⟩
        exact (ρ i).2
      have hKne : K ≠ R := by
        intro heq
        exact hnot n (Nat.le_of_succ_le_succ hn) ρ
          (congrArg (fun L : ClosedSubgroup F ↦ (L : Subgroup F)) heq)
      have hstrict : K < R := lt_of_le_of_ne hKR hKne
      obtain ⟨χnew, hnew, hkill, hnewInv⟩ := relativeNakayama_character hF K R hstrict
      obtain ⟨r, hr⟩ : ∃ r : R, χnew r ≠ 1 := by
        by_contra hall
        apply hnew
        apply ContinuousMonoidHom.ext
        intro r
        exact not_not.mp (fun hr ↦ hall ⟨r, hr⟩)
      refine ⟨Fin.snoc ρ r, Fin.snoc χ χnew, ?_, ?_, ?_⟩
      · intro i
        refine Fin.lastCases ?_ (fun j ↦ ?_) i
        · simpa only [Fin.snoc_last] using hnewInv
        · simpa only [Fin.snoc_castSucc] using hχinv j
      · intro i
        refine Fin.lastCases ?_ (fun j ↦ ?_) i
        · simpa only [Fin.snoc_last] using hr
        · simpa only [Fin.snoc_castSucc] using hdiag j
      · intro i
        refine Fin.lastCases ?_ (fun i ↦ ?_) i
        · intro j
          refine Fin.lastCases ?_ (fun j ↦ ?_) j
          · intro hlt
            exact (lt_irrefl (Fin.last n) hlt).elim
          · intro _hlt
            have hjK : (ρ j : F) ∈ K :=
              subset_closedNormalClosure (Set.range (fun i ↦ (ρ i : F))) ⟨j, rfl⟩
            simpa only [Fin.snoc_last, Fin.snoc_castSucc] using hkill ⟨(ρ j : F), hjK⟩
        · intro j
          refine Fin.lastCases ?_ (fun j ↦ ?_) j
          · intro hlt
            exact (Nat.not_lt_of_ge (Nat.le_of_lt i.isLt) hlt).elim
          · intro hlt
            simpa only [Fin.snoc_castSucc] using htri i j hlt
  obtain ⟨ρ, χ, hχinv, hdiag, htri⟩ := hbuild (d + 1) le_rfl
  have hχind : LinearIndependent (ZMod p) (fun i ↦ fun r : R ↦ (χ i r).toAdd) := by
    apply linearIndependent_of_triangular_evaluation (x := ρ)
    · intro i heq
      exact hdiag i (congrArg Multiplicative.ofAdd heq)
    · intro i j hji
      exact congrArg Multiplicative.toAdd (htri i j hji)
  have hbound := invariant_character_family_card_le_finrank_h2 hF R hR χ hχinv hχind
  have hbad : d + 1 ≤ d := by simpa only [Fintype.card_fin] using hbound
  exact Nat.not_succ_le_self d hbad

end

end ClassFieldTower.ProP
