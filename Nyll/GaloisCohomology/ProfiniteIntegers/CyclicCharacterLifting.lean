/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.ProfiniteIntegers.ZModCircle
import Nyll.ProCGroups.Cohomology.DivisibleCharacterExtension
import Nyll.ProCGroups.Topologies.ContinuousMulEquiv

/-! # Lifting cyclic characters along injective power maps -/

namespace ProCGroups.Abelian

universe u

/-- If the `m`th-power map on a profinite abelian group is injective, every
continuous character modulo `N` lifts to a character modulo `N*m`. -/
theorem exists_cyclic_character_lift_of_power_injective
    {A : Type u} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    [CompactSpace A] [T2Space A] [TotallyDisconnectedSpace A]
    (N m : ℕ) [NeZero N] [NeZero m]
    (hm : Function.Injective (fun a : A => a ^ m))
    (χ : A →ₜ* Multiplicative (ZMod N)) :
    ∃ ψ : A →ₜ* Multiplicative (ZMod (N * m)), ∀ a : A,
      ZMod.castHom (dvd_mul_right N m) (ZMod N) (ψ a).toAdd = (χ a).toAdd := by
  let pow : A →ₜ* A := ⟨powMonoidHom m, continuous_id.pow m⟩
  let P : Subgroup A := pow.toMonoidHom.range
  have hP : IsClosed (P : Set A) := ContinuousMonoidHom.isClosed_range pow
  let powRange : A →* P := pow.toMonoidHom.rangeRestrict
  have hbij : Function.Bijective powRange :=
    ⟨fun x y h => hm (congrArg Subtype.val h), by
      intro x
      obtain ⟨a, ha⟩ := x.2
      exact ⟨a, Subtype.ext ha⟩⟩
  let e : A ≃ₜ* P := ContinuousMulEquiv.ofBijectiveCompactToT2 powRange
    (pow.continuous.subtype_mk _) hbij
  let χP : P →ₜ* Multiplicative (ZMod N) :=
    { toMonoidHom := χ.toMonoidHom.comp e.symm.toMulEquiv.toMonoidHom
      continuous_toFun := χ.continuous.comp e.symm.continuous_toFun }
  let : DivisibleBy (Additive (Multiplicative UnitAddCircle)) ℤ := by
    change DivisibleBy UnitAddCircle ℤ
    infer_instance
  obtain ⟨η, hη⟩ := ProCGroups.exists_continuous_character_extension_divisible
    P hP χP (ZMod.toAddCircle (N := N)).toMultiplicative
  have hpow (a : A) : m • (η a).toAdd = ZMod.toAddCircle (χ a).toAdd := by
    have hh := hη (e a)
    change η (a ^ m) = Multiplicative.ofAdd (ZMod.toAddCircle (χ (e.symm (e a))).toAdd) at hh
    rw [e.symm_apply_apply, map_pow] at hh
    exact congrArg Multiplicative.toAdd hh
  have hexp (a : A) : (N * m) • (η a).toAdd = 0 := by
    rw [mul_smul, hpow, ← map_nsmul]
    have hz : N • (χ a).toAdd = 0 := by
      rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    rw [hz, map_zero]
  obtain ⟨ψ, hψ⟩ := ZMod.exists_continuous_zmod_character (N * m) η hexp
  refine ⟨ψ, ?_⟩
  intro a
  apply ZMod.toAddCircle_injective N
  rw [ZMod.toAddCircle_castHom_mul, hψ, hpow]

end ProCGroups.Abelian
