/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Tactic.Ring

/-!
# Normalization of a raw character transition

The canonical finite tame character is the raw uniformizer character raised
 to `e / n`. The raw tower exponent is the relative ramification index. The
following arithmetic converts that exponent into the ratio of the actual
finite tame orders. Coprimality with the upper normalization factor also
supplies divisibility of the tame orders without inertia surjectivity.
-/

namespace RamificationTheory.HilbertRamification

/-- A prime-to-wild divisor of a lower ramification index divides the upper
tame order. In the actual tower the coprimality comes from residue
invertibility and the upper normalization factor being a characteristic power. -/
theorem tameOrder_dvd_of_ramificationIdx_dvd
    {nE nF eE eF : ℕ} (hnE : nE ∣ eE) (hnF : nF ∣ eF)
    (he : eE ∣ eF) (hcoprime : Nat.Coprime nE (eF / nF)) : nE ∣ nF := by
  apply hcoprime.dvd_of_dvd_mul_right
  rw [Nat.mul_comm nF (eF / nF), Nat.div_mul_cancel hnF]
  exact hnE.trans he

private theorem normalizationExponents_tower
    {nE nF eE eF r : ℕ} (hnEpos : 0 < nE)
    (hnE : nE ∣ eE) (hnF : nF ∣ eF) (hn : nE ∣ nF)
    (he : eF = r * eE) :
    r * (eE / nE) = (eF / nF) * (nF / nE) := by
  apply Nat.eq_of_mul_eq_mul_left hnEpos
  calc
    nE * (r * (eE / nE)) = r * ((eE / nE) * nE) := by ring
    _ = r * eE := by rw [Nat.div_mul_cancel hnE]
    _ = eF := he.symm
    _ = ((eF / nF) * (nF / nE)) * nE := by
      rw [Nat.mul_assoc, Nat.div_mul_cancel hn, Nat.div_mul_cancel hnF]
    _ = nE * ((eF / nF) * (nF / nE)) :=
      Nat.mul_comm ((eF / nF) * (nF / nE)) nE

universe u v

/-- A raw character relation at the relative ramification index becomes the
canonical relation at the ratio of the actual tame orders after normalizing
both characters by their own `e / n`. The coefficient map is retained
literally; no new carrier or comparison map is introduced. -/
theorem normalizedCharacter_tower
    {M : Type u} {N : Type v} [Monoid M] [Monoid N]
    (i : M →* N) (x : M) (y : N)
    {nE nF eE eF r : ℕ} (hnEpos : 0 < nE)
    (hnE : nE ∣ eE) (hnF : nF ∣ eF) (hn : nE ∣ nF)
    (he : eF = r * eE) (hraw : i.toFun x = y ^ r) :
    i.toFun (x ^ (eE / nE)) = (y ^ (eF / nF)) ^ (nF / nE) := by
  calc
    _ = i.toFun x ^ (eE / nE) := map_pow i x (eE / nE)
    _ = (y ^ r) ^ (eE / nE) := congrArg (fun z : N => z ^ (eE / nE)) hraw
    _ = _ := by
      rw [← pow_mul, ← pow_mul, normalizationExponents_tower hnEpos hnE hnF hn he]

end RamificationTheory.HilbertRamification
