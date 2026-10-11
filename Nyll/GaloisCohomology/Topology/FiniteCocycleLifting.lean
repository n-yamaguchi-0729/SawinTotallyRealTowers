/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.ProfiniteIntegers.ZModPrimeKernel
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Instances.ZMod
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Successive lifting of finite crossed cocycles

An arbitrary finite-valued lift has a defect in the prime-order kernel.
Trivial action on that kernel makes the defect an ordinary two-cocycle;
a primitive supplied by H² vanishing corrects the lift.
-/

namespace GaloisCohomology

variable {p : ℕ} [Fact p.Prime]
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Vanishing of locally constant two-cocycles lifts crossed cocycles one prime-power level. -/
theorem exists_lift_crossed_cocycle_succ
    (hH2 : ∀ z : G → G → ZMod p,
      (∀ σ τ υ : G, z σ (τ * υ) + z τ υ = z (σ * τ) υ + z σ τ) →
      IsLocallyConstant (fun x : G × G => z x.1 x.2) →
      ∃ d : G → ZMod p, IsLocallyConstant d ∧
        ∀ σ τ : G, d τ - d (σ * τ) + d σ = z σ τ)
    (n : ℕ) (θ : G →ₜ* (ZMod (p ^ (n + 1)))ˣ)
    (hθ : ∀ g : G,
      ZMod.castHom (dvd_pow_self p (Nat.succ_ne_zero n)) (ZMod p)
        (θ g : ZMod (p ^ (n + 1))) = 1)
    (c : G → ZMod (p ^ n)) (hccont : Continuous c)
    (hc : ∀ σ τ : G, c (σ * τ) = c σ +
      ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))
        (θ σ : ZMod (p ^ (n + 1))) * c τ) :
    ∃ d : G → ZMod (p ^ (n + 1)), Continuous d ∧
      (∀ σ τ : G, d (σ * τ) = d σ + (θ σ : ZMod (p ^ (n + 1))) * d τ) ∧
      ∀ σ : G, ZMod.castHom (pow_dvd_pow p (Nat.le_succ n))
        (ZMod (p ^ n)) (d σ) = c σ := by
  classical
  have : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
  have : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  let r := ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))
  let e := ZMod.mulPowPrime p n
  have heinj : Function.Injective e := ZMod.mulPowPrime_injective (Fact.out : p.Prime).ne_zero n
  have hfixed (σ : G) (a : ZMod p) : (θ σ : ZMod (p ^ (n + 1))) * e a = e a := by
    rw [← ZMod.mulPowPrime_mul_castHom, hθ, one_mul]
  let f (σ : G) : ZMod (p ^ (n + 1)) := (c σ).val
  have hfcont : Continuous f :=
    (show Continuous (fun a : ZMod (p ^ n) => (a.val : ZMod (p ^ (n + 1)))) from
      continuous_of_discreteTopology).comp hccont
  have hred (σ : G) : r (f σ) = c σ := by
    change r ((c σ).val : ZMod (p ^ (n + 1))) = c σ
    rw [map_natCast, ZMod.natCast_zmod_val]
  let δ (σ τ : G) : ZMod (p ^ (n + 1)) :=
    (θ σ : ZMod (p ^ (n + 1))) * f τ - f (σ * τ) + f σ
  have hδcont : Continuous (fun x : G × G => δ x.1 x.2) :=
    (((Units.continuous_val.comp θ.continuous).comp continuous_fst).mul
      (hfcont.comp continuous_snd)).sub (hfcont.comp continuous_mul) |>.add
        (hfcont.comp continuous_fst)
  have hδzero (σ τ : G) : r (δ σ τ) = 0 := by
    change r ((θ σ : ZMod (p ^ (n + 1))) * f τ - f (σ * τ) + f σ) = 0
    rw [map_add, map_sub, map_mul, hred, hred, hred, hc]
    ring
  let z (σ τ : G) : ZMod p :=
    (ZMod.exists_mulPowPrime_eq_of_castHom_eq_zero p n (δ σ τ) (hδzero σ τ)).choose
  have hzval (σ τ : G) : e (z σ τ) = δ σ τ :=
    (ZMod.exists_mulPowPrime_eq_of_castHom_eq_zero p n (δ σ τ) (hδzero σ τ)).choose_spec
  have hzcont : IsLocallyConstant (fun x : G × G => z x.1 x.2) := by
    apply (IsLocallyConstant.iff_exists_open _).mpr
    intro x
    obtain ⟨U, hU, hx, hconst⟩ :=
      ((IsLocallyConstant.iff_continuous _).mpr hδcont).exists_open x
    refine ⟨U, hU, hx, ?_⟩
    intro y hy
    apply heinj
    rw [hzval, hzval]
    exact hconst y hy
  have hzcocycle (σ τ υ : G) : z σ (τ * υ) + z τ υ = z (σ * τ) υ + z σ τ := by
    apply heinj
    rw [map_add, map_add, hzval, hzval, hzval, hzval]
    have hfix := hfixed σ (z τ υ)
    rw [hzval] at hfix
    have hmul : (θ (σ * τ) : ZMod (p ^ (n + 1))) =
        (θ σ : ZMod (p ^ (n + 1))) * (θ τ : ZMod (p ^ (n + 1))) := by
      rw [map_mul, Units.val_mul]
    dsimp only [δ] at hfix ⊢
    rw [hmul]
    simp only [mul_assoc]
    linear_combination -hfix
  obtain ⟨b, hbcont, hb⟩ := hH2 z hzcocycle hzcont
  let d (σ : G) := f σ - e (b σ)
  have hdcont : Continuous d := hfcont.sub (continuous_of_discreteTopology.comp hbcont.continuous)
  refine ⟨d, hdcont, ?_, ?_⟩
  · intro σ τ
    have hb' := congrArg e (hb σ τ)
    rw [map_add, map_sub, hzval] at hb'
    have hfix := hfixed σ (b τ)
    dsimp only [d, δ] at hb' ⊢
    linear_combination hb' + hfix
  · intro σ
    change r (f σ - e (b σ)) = c σ
    rw [map_sub, hred, ZMod.castHom_mulPowPrime, sub_zero]

end GaloisCohomology
