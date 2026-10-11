/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Data.ZMod.Units
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Henselian

/-!
# Prime-to-p torsion is determined by reduction modulo p

Two units modulo a positive power of `p` annihilated by the same exponent
coprime to `p` are equal if their reductions modulo `p` agree. The proof
uses uniqueness of a simple polynomial root in a local ring.
-/

namespace LocalFieldTheory.DiscreteValuationField

/-- Reduction modulo `p` distinguishes the prime-to-`p` roots of unity
modulo any positive power of `p`. -/
theorem primePower_units_eq_of_pow_eq_one_of_reduction_eq
    (p : ℕ) [Fact p.Prime] (s n : ℕ) (hn : n.Coprime p)
    (u v : (ZMod (p ^ (s + 1)))ˣ) (hu : u ^ n = 1) (hv : v ^ n = 1)
    (hred : ZMod.unitsMap (dvd_pow_self p (Nat.succ_ne_zero s)) u =
      ZMod.unitsMap (dvd_pow_self p (Nat.succ_ne_zero s)) v) : u = v := by
  have hp : p.Prime := Fact.out
  have : Fact (1 < p ^ (s + 1)) := ⟨one_lt_pow₀ hp.one_lt (Nat.succ_ne_zero s)⟩
  have : IsLocalRing (ZMod (p ^ (s + 1))) :=
    IsLocalRing.of_surjective' (PadicInt.toZModPow (s + 1))
      (ZMod.ringHom_surjective (PadicInt.toZModPow (s + 1)))
  let f : Polynomial (ZMod (p ^ (s + 1))) := Polynomial.X ^ n - 1
  have huroot : f.eval (u : ZMod (p ^ (s + 1))) = 0 := by
    have h := congrArg (fun z : (ZMod (p ^ (s + 1)))ˣ => (z : ZMod (p ^ (s + 1)))) hu
    simpa only [f, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_one, Units.val_pow_eq_pow_val, Units.val_one, sub_eq_zero] using h
  have hvroot : f.eval (v : ZMod (p ^ (s + 1))) = 0 := by
    have h := congrArg (fun z : (ZMod (p ^ (s + 1)))ˣ => (z : ZMod (p ^ (s + 1)))) hv
    simpa only [f, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_one, Units.val_pow_eq_pow_val, Units.val_one, sub_eq_zero] using h
  let r : ZMod (p ^ (s + 1)) →+* ZMod p :=
    ZMod.castHom (dvd_pow_self p (Nat.succ_ne_zero s)) (ZMod p)
  have hreduction : r (u : ZMod (p ^ (s + 1))) = r (v : ZMod (p ^ (s + 1))) := by
    exact congrArg (fun z : (ZMod p)ˣ => (z : ZMod p)) hred
  have hsub : ¬ IsUnit ((u : ZMod (p ^ (s + 1))) - (v : ZMod (p ^ (s + 1)))) := by
    intro hunit
    have h := hunit.map r
    rw [r.map_sub, hreduction, sub_self] at h
    exact not_isUnit_zero h
  have hnunit : IsUnit (n : ZMod (p ^ (s + 1))) :=
    (ZMod.isUnit_iff_coprime n (p ^ (s + 1))).mpr (hn.pow_right (s + 1))
  have hderiv : IsUnit (f.derivative.eval (u : ZMod (p ^ (s + 1)))) := by
    simpa only [f, Polynomial.derivative_sub, Polynomial.derivative_X_pow,
      Polynomial.derivative_one, sub_zero, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X] using hnunit.mul (u.isUnit.pow (n - 1))
  exact Units.ext (IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub huroot hvroot hsub hderiv)

end LocalFieldTheory.DiscreteValuationField
