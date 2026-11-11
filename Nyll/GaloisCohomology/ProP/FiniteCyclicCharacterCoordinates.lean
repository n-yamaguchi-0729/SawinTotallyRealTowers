/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.ProP.FiniteCyclicCarryCocycle
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Normalized coordinates for a finite cyclic character image

An injective character into `ZMod n` determines a positive index `k`.
The index power of `1` belongs to its image and supplies an actual
generator. Its standard coordinates scale by exactly `k`, including
when the character has smaller order than `n` or has trivial image.
-/

@[expose] public section

noncomputable section

namespace ClassFieldTower.Cohomology

/-- The positive index and normalized generator of the actual character
image supply the scaled coordinates needed by cyclic carry descent. -/
theorem exists_generator_scaled_character
    {G : Type*} [Group G] [Fintype G] {n : ℕ} [NeZero n]
    (χ : G →* Multiplicative (ZMod n)) (hχ : Function.Injective χ) :
    ∃ k : ℕ, 0 < k ∧ n = k * Nat.card G ∧
      ∃ (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g),
        χ g = Multiplicative.ofAdd (k : ZMod n) ∧
        ∀ x : G, (Multiplicative.toAdd (χ x)).val =
          k * (finiteCyclicGeneratorCoordinate g hg x).val := by
  classical
  let k := χ.range.index
  have hk : 0 < k := Nat.pos_of_ne_zero χ.range.index_ne_zero_of_finite
  have hcardRange : Nat.card χ.range = Nat.card G :=
    (Nat.card_congr (MonoidHom.ofInjective hχ).toEquiv).symm
  have hcard : n = k * Nat.card G := by
    calc
      n = Nat.card (Multiplicative (ZMod n)) := by
        rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
      _ = k * Nat.card χ.range := χ.range.index_mul_card.symm
      _ = k * Nat.card G := by rw [hcardRange]
  obtain ⟨g, hgpow⟩ := χ.range.pow_index_mem (Multiplicative.ofAdd (1 : ZMod n))
  have hgχ : χ g = Multiplicative.ofAdd (k : ZMod n) := by
    calc
      χ g = Multiplicative.ofAdd (1 : ZMod n) ^ k := hgpow
      _ = Multiplicative.ofAdd (k : ZMod n) := by
        rw [← ofAdd_nsmul, nsmul_eq_mul, mul_one]
  have horder : orderOf g = Nat.card G := by
    rw [← orderOf_injective χ hχ g, hgχ]
    change addOrderOf (k : ZMod n) = Nat.card G
    rw [ZMod.addOrderOf_coe k (NeZero.ne n),
      Nat.gcd_eq_right (show k ∣ n from ⟨Nat.card G, hcard⟩), hcard,
      Nat.mul_div_cancel_left _ hk]
  have htop : Subgroup.zpowers g = ⊤ :=
    Subgroup.eq_top_of_card_eq (Subgroup.zpowers g) (by rw [Nat.card_zpowers, horder])
  have hg : ∀ x : G, x ∈ Subgroup.zpowers g := fun x => by
    rw [htop]
    exact Subgroup.mem_top x
  refine ⟨k, hk, hcard, g, hg, hgχ, fun x => ?_⟩
  have heq : Multiplicative.toAdd (χ x) =
      ((k * (finiteCyclicGeneratorCoordinate g hg x).val : ℕ) : ZMod n) := by
    calc
      Multiplicative.toAdd (χ x) =
          Multiplicative.toAdd (χ (g ^ (finiteCyclicGeneratorCoordinate g hg x).val)) :=
        congrArg (fun y => Multiplicative.toAdd (χ y))
          (finiteCyclicGenerator_zpow_coordinate g hg x).symm
      _ = (finiteCyclicGeneratorCoordinate g hg x).val • (k : ZMod n) := by
        rw [map_pow, hgχ, toAdd_pow, toAdd_ofAdd]
      _ = ((k * (finiteCyclicGeneratorCoordinate g hg x).val : ℕ) : ZMod n) := by
        rw [nsmul_eq_mul, Nat.cast_mul, mul_comm]
  have : NeZero (Nat.card G) := ⟨Nat.card_pos.ne'⟩
  have hlt : k * (finiteCyclicGeneratorCoordinate g hg x).val < n := by
    rw [hcard]
    exact Nat.mul_lt_mul_of_pos_left (ZMod.val_lt _) hk
  rw [heq, ZMod.val_natCast_of_lt hlt]

end ClassFieldTower.Cohomology
