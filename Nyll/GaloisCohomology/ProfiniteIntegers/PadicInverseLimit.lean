/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Topology.Instances.ZMod

/-! # Continuous p-adic functions from compatible finite reductions -/

namespace PadicInt

universe u

variable {p : ℕ} [Fact p.Prime]

/-- A compatible family of residues determines a p-adic integer. -/
theorem exists_of_compatible_residues
    (a : ∀ n : ℕ, ZMod (p ^ n))
    (ha : ∀ n, ZMod.castHom (pow_dvd_pow p (Nat.le_succ n))
      (ZMod (p ^ n)) (a (n + 1)) = a n) :
    ∃ z : PadicInt p, ∀ n, toZModPow n z = a n := by
  let f : ℕ → ℤ := fun n => (a n).val
  have hf (n : ℕ) : (p : ℤ) ^ n ∣ f (n + 1) - f n := by
    rw [← Nat.cast_pow, ← ZMod.intCast_eq_intCast_iff_dvd_sub]
    symm
    change (((a (n + 1)).val : ℤ) : ZMod (p ^ n)) = (((a n).val : ℤ) : ZMod (p ^ n))
    simp only [Int.cast_natCast]
    rw [ZMod.natCast_zmod_val]
    calc
      ((a (n + 1)).val : ZMod (p ^ n)) =
          ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))
            ((a (n + 1)).val : ZMod (p ^ (n + 1))) := (map_natCast _ _).symm
      _ = a n := by rw [ZMod.natCast_zmod_val, ha]
  refine ⟨PadicInt.ofIntSeq f (isCauSeq_padicNorm_of_pow_dvd_sub f p hf), ?_⟩
  intro n
  rw [toZModPow_ofIntSeq_of_pow_dvd_sub f p hf n]
  change (((a n).val : ℤ) : ZMod (p ^ n)) = a n
  rw [Int.cast_natCast, ZMod.natCast_zmod_val]

/-- Reduction modulo a p-power is continuous for the discrete target topology. -/
theorem continuous_toZModPow (n : ℕ) : Continuous (toZModPow n : PadicInt p → ZMod (p ^ n)) := by
  apply continuous_of_continuousAt_zero (toZModPow n).toAddMonoidHom
  rw [ContinuousAt, nhds_discrete (ZMod (p ^ n)), Filter.tendsto_pure, map_zero]
  change ∀ᶠ z in nhds (0 : PadicInt p), toZModPow n z = 0
  have hrad : (0 : ℝ) < (p : ℝ) ^ (-(n : ℤ)) :=
    zpow_pos (Nat.cast_pos.mpr (Fact.out : p.Prime).pos) _
  filter_upwards [Metric.ball_mem_nhds (0 : PadicInt p) hrad] with z hz
  rw [Metric.mem_ball, dist_zero_right] at hz
  rw [← RingHom.mem_ker, ker_toZModPow]
  exact (norm_le_pow_iff_mem_span_pow z n).mp hz.le

/-- Continuity of a p-adic function follows from continuity of all its finite reductions. -/
theorem continuous_of_continuous_toZModPow
    {X : Type u} [TopologicalSpace X] (f : X → PadicInt p)
    (hf : ∀ n, Continuous (fun x => toZModPow n (f x))) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, Metric.nhds_basis_closedBall.tendsto_right_iff]
  intro ε hε
  obtain ⟨n, hn⟩ := PadicInt.exists_pow_neg_lt p hε
  have hnb : {y | toZModPow n (f y) = toZModPow n (f x)} ∈ nhds x :=
    (isOpen_discrete ({toZModPow n (f x)} : Set (ZMod (p ^ n)))).preimage
      (hf n) |>.mem_nhds rfl
  apply Filter.mem_of_superset hnb
  intro y hy
  change f y ∈ Metric.closedBall (f x) ε
  rw [Metric.mem_closedBall, dist_eq_norm]
  apply le_trans _ hn.le
  rw [norm_le_pow_iff_mem_span_pow, ← ker_toZModPow n, RingHom.mem_ker, map_sub,
    sub_eq_zero]
  exact hy

/-- Compatible continuous finite functions have a continuous p-adic inverse limit. -/
theorem exists_continuous_of_compatible_residues
    {X : Type u} [TopologicalSpace X]
    (f : ∀ n : ℕ, X → ZMod (p ^ n))
    (hf : ∀ n, Continuous (f n))
    (hcompat : ∀ n x, ZMod.castHom (pow_dvd_pow p (Nat.le_succ n))
      (ZMod (p ^ n)) (f (n + 1) x) = f n x) :
    ∃ d : X → PadicInt p, Continuous d ∧ ∀ n x, toZModPow n (d x) = f n x := by
  choose d hd using fun x => exists_of_compatible_residues
    (fun n => f n x) (fun n => hcompat n x)
  refine ⟨d, continuous_of_continuous_toZModPow d ?_, fun n x => hd x n⟩
  intro n
  convert hf n using 1
  funext x
  exact hd x n

end PadicInt
