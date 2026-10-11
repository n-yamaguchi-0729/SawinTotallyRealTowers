/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.ProfiniteIntegers.PadicInverseLimit
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Data.Nat.Totient

/-!
# Continuous principal-unit powers

Euler's theorem gives compatible finite powers of `(p + 1) ^ (p - 1)`.
Their inverse limit is a continuous character of the additive p-adic integers,
with infinite image and trivial reduction modulo p.
-/

namespace PadicInt
variable (p : ℕ) [Fact p.Prime]

private def principalUnitResidue (n : ℕ) : (ZMod (p ^ n))ˣ :=
  (ZMod.unitOfCoprime (p + 1)
    ((Nat.coprime_self_add_left.mpr (Nat.coprime_one_left p)).pow_right n)) ^ (p - 1)

private theorem principalUnitResidue_pow (n : ℕ) :
    principalUnitResidue p n ^ (p ^ n) = 1 := by
  cases n with
  | zero =>
    have : Subsingleton (ZMod (p ^ 0)) := by rw [pow_zero]; infer_instance
    exact Subsingleton.elim _ _
  | succ n =>
    have : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
    let u : (ZMod (p ^ (n + 1)))ˣ := ZMod.unitOfCoprime (p + 1)
      ((Nat.coprime_self_add_left.mpr (Nat.coprime_one_left p)).pow_right (n + 1))
    have hu : u ^ (p ^ n * (p - 1)) = 1 := by
      simpa only [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
        Nat.totient_prime_pow_succ (Fact.out : p.Prime)] using (pow_card_eq_one' (x := u))
    change (u ^ (p - 1)) ^ (p ^ (n + 1)) = 1
    calc
      (u ^ (p - 1)) ^ (p ^ (n + 1)) = u ^ ((p ^ n * (p - 1)) * p) := by
        rw [← pow_mul]
        apply congrArg (fun m : ℕ => u ^ m)
        rw [pow_succ]
        ac_rfl
      _ = 1 := by rw [pow_mul, hu, one_pow]

private def principalUnitPowerResidue (n : ℕ) :
    ZMod (p ^ n) →+ Additive (ZMod (p ^ n))ˣ :=
  ZMod.lift (p ^ n)
    ⟨{ toFun := fun a : ℤ => Additive.ofMul (principalUnitResidue p n ^ a)
       map_zero' := by change principalUnitResidue p n ^ (0 : ℤ) = 1; exact zpow_zero _
       map_add' := by
         intro a b
         change principalUnitResidue p n ^ (a + b) =
           principalUnitResidue p n ^ a * principalUnitResidue p n ^ b
         exact zpow_add _ _ _ }, by
      change principalUnitResidue p n ^ (p ^ n : ℕ) = 1
      exact principalUnitResidue_pow p n⟩

private theorem principalUnitPowerResidue_intCast (n : ℕ) (a : ℤ) :
    (principalUnitPowerResidue p n (a : ZMod (p ^ n))).toMul =
      principalUnitResidue p n ^ a :=
  congrArg Additive.toMul (ZMod.lift_coe (p ^ n) _ a)

private theorem principalUnitPowerResidue_compatible (n : ℕ)
    (a : ZMod (p ^ (n + 1))) :
    Units.map (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))).toMonoidHom
      (principalUnitPowerResidue p (n + 1) a).toMul =
    (principalUnitPowerResidue p n
      (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) a)).toMul := by
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective a
  rw [principalUnitPowerResidue_intCast, map_intCast,
    principalUnitPowerResidue_intCast, map_zpow]
  congr 1
  apply Units.ext
  change (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)))
      (((p + 1 : ℕ) : ZMod (p ^ (n + 1))) ^ (p - 1)) =
    ((p + 1 : ℕ) : ZMod (p ^ n)) ^ (p - 1)
  rw [map_pow, map_natCast]

/-- The powers of `(p + 1) ^ (p - 1)` extend continuously to p-adic exponents. -/
theorem exists_continuous_principal_unit_powers :
    ∃ φ : Multiplicative (PadicInt p) →ₜ* (PadicInt p)ˣ,
      ((φ (Multiplicative.ofAdd 1) : (PadicInt p)ˣ) : PadicInt p) =
        ((p + 1 : ℕ) : PadicInt p) ^ (p - 1) ∧
      ∀ x, toZModPow 1 (φ x : PadicInt p) = 1 := by
  classical
  let f (n : ℕ) (x : PadicInt p) : ZMod (p ^ n) :=
    (principalUnitPowerResidue p n (toZModPow n x)).toMul
  have hf (n : ℕ) : Continuous (f n) :=
    (continuous_of_discreteTopology (f := fun a : ZMod (p ^ n) =>
      ((principalUnitPowerResidue p n a).toMul : ZMod (p ^ n)))).comp
        (continuous_toZModPow n)
  have hc (n : ℕ) (x : PadicInt p) :
      ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) (f (n + 1) x) =
        f n x := by
    have h := congrArg Units.val
      (principalUnitPowerResidue_compatible p n (toZModPow (n + 1) x))
    change ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))
      (f (n + 1) x) =
      ((principalUnitPowerResidue p n
        (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))
          (toZModPow (n + 1) x))).toMul : ZMod (p ^ n)) at h
    rw [← RingHom.comp_apply, zmod_cast_comp_toZModPow n (n + 1) (Nat.le_succ n)] at h
    exact h
  obtain ⟨d, hdcont, hd⟩ := exists_continuous_of_compatible_residues f hf hc
  have hd0 : d 0 = 1 := by
    apply ext_of_toZModPow.mp
    intro n
    rw [hd, map_one]
    change ((principalUnitPowerResidue p n (toZModPow n 0)).toMul :
      ZMod (p ^ n)) = 1
    rw [map_zero, map_zero]
    rfl
  have hadd (x y : PadicInt p) : d (x + y) = d x * d y := by
    apply ext_of_toZModPow.mp
    intro n
    rw [map_mul, hd, hd, hd]
    change ((principalUnitPowerResidue p n (toZModPow n (x + y))).toMul :
        ZMod (p ^ n)) =
      ((principalUnitPowerResidue p n (toZModPow n x)).toMul : ZMod (p ^ n)) *
        ((principalUnitPowerResidue p n (toZModPow n y)).toMul : ZMod (p ^ n))
    rw [map_add, map_add]
    rfl
  let dHom : Multiplicative (PadicInt p) →* PadicInt p :=
    { toFun := fun x => d x.toAdd
      map_one' := hd0
      map_mul' := fun x y => hadd x.toAdd y.toAdd }
  let φ : Multiplicative (PadicInt p) →ₜ* (PadicInt p)ˣ :=
    ⟨dHom.toHomUnits,
      Units.continuous_iff.mpr ⟨hdcont, hdcont.comp continuous_inv⟩⟩
  refine ⟨φ, ?_, ?_⟩
  · change d 1 = ((p + 1 : ℕ) : PadicInt p) ^ (p - 1)
    apply ext_of_toZModPow.mp
    intro n
    rw [hd, map_pow, map_natCast]
    change ((principalUnitPowerResidue p n (toZModPow n 1)).toMul :
      ZMod (p ^ n)) = ((p + 1 : ℕ) : ZMod (p ^ n)) ^ (p - 1)
    rw [map_one]
    have h := principalUnitPowerResidue_intCast p n 1
    simp only [Int.cast_one, zpow_one] at h
    rw [h]
    rfl
  · intro x
    change toZModPow 1 (d x.toAdd) = 1
    rw [hd]
    change ((principalUnitPowerResidue p 1 (toZModPow 1 x.toAdd)).toMul :
      ZMod (p ^ 1)) = 1
    obtain ⟨a, ha⟩ := ZMod.intCast_surjective (toZModPow 1 x.toAdd)
    rw [← ha, principalUnitPowerResidue_intCast]
    have hu : principalUnitResidue p 1 = 1 := by
      apply Units.ext
      change ((p + 1 : ℕ) : ZMod (p ^ 1)) ^ (p - 1) = 1
      have hp : ((p : ℕ) : ZMod (p ^ 1)) = 0 := by
        rw [ZMod.natCast_eq_zero_iff, pow_one]
      rw [Nat.cast_add, Nat.cast_one, hp, zero_add, one_pow]
    rw [hu, one_zpow]
    rfl

/-- The additive p-adic integers admit a continuous infinite principal-unit character. -/
theorem exists_infinite_principal_unit_character :
    ∃ φ : Multiplicative (PadicInt p) →ₜ* (PadicInt p)ˣ,
      Set.Infinite (Set.range φ) ∧ ∀ x, toZModPow 1 (φ x : PadicInt p) = 1 := by
  obtain ⟨φ, hφ, hmod⟩ := exists_continuous_principal_unit_powers p
  refine ⟨φ, ?_, hmod⟩
  let B : ℕ := (p + 1) ^ (p - 1)
  have hB : 1 < B := one_lt_pow₀ (by have := (Fact.out : p.Prime).pos; omega)
    (Nat.ne_of_gt (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt))
  let g : Multiplicative (PadicInt p) := Multiplicative.ofAdd 1
  have hg : (φ g : PadicInt p) = (B : PadicInt p) := by
    rw [Nat.cast_pow]
    exact hφ
  have hinj : Function.Injective (fun n : ℕ => φ g ^ n) := by
    intro a b h
    have hval := congrArg (fun u : (PadicInt p)ˣ => (u : PadicInt p)) h
    simp only [Units.val_pow_eq_pow_val, hg, ← Nat.cast_pow] at hval
    exact pow_right_injective₀ (lt_trans Nat.zero_lt_one hB) (ne_of_gt hB)
      (Nat.cast_injective hval)
  apply (Set.infinite_range_of_injective hinj).mono
  rintro y ⟨n, rfl⟩
  exact ⟨g ^ n, map_pow φ g n⟩

end PadicInt
