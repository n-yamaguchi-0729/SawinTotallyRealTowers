/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.CharacterMap
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.FiniteOrderValuation
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.FiniteRamificationPrimary

/-!
# Conjugation of inertia characters

Relate the residue-unit inertia character to decomposition and residue
actions. Finite inertia characters are injective in residue characteristic
zero.
-/

namespace RamificationTheory.HilbertRamification.ValuationSubring

variable (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]

/-- A finite-order decomposition automorphism does not change the argument of
an inertia character, because it preserves the value of every field element. -/
theorem valueTrivialInertiaResidueUnitHom_decomposition_arg
    (A : _root_.ValuationSubring L) (τ : valueTrivialInertiaGroup K A)
    (g : decompositionGroup K A) (hg : IsOfFinOrder g) (x : Lˣ) :
    valueTrivialInertiaResidueUnitHom K A τ
      (Units.mapEquiv (g : Gal(L/K)).toMulEquiv x) =
      valueTrivialInertiaResidueUnitHom K A τ x := by
  let q : Lˣ := automorphismUnitQuotient K A g x
  have hq : q ∈ A.unitGroup := by
    rw [A.mem_unitGroup_iff]
    simp only [q, automorphismUnitQuotient, Units.val_div_eq_div_val]
    change A.valuation ((g : Gal(L/K)) (x : L) / (x : L)) = 1
    rw [map_div₀, valuation_decomposition_apply_eq_of_isOfFinOrder K A g hg]
    exact div_self (A.valuation.ne_zero_iff.mpr x.ne_zero)
  have heq : Units.mapEquiv (g : Gal(L/K)).toMulEquiv x = q * x := by
    dsimp only [q, automorphismUnitQuotient]
    exact (div_mul_cancel _ _).symm
  rw [heq, map_mul,
    MonoidHom.mem_ker.mp (unitGroup_le_valueTrivialInertiaResidueUnitHom_ker K A τ hq), one_mul]

/-- The actual residue-unit character intertwines conjugation with residue action. -/
theorem valueTrivialInertiaResidueUnitHom_conj
    (A : _root_.ValuationSubring L) [Finite (inertiaGroup K A)]
    (g : decompositionGroup K A) (τ : inertiaGroup K A) (x : Lˣ) :
    let htop := valueTrivialInertiaGroup_eq_top_of_finite K A
    let s : valueTrivialInertiaGroup K A := ⟨τ, htop.symm ▸ Subgroup.mem_top τ⟩
    let t : valueTrivialInertiaGroup K A :=
      ⟨MulAut.conjNormal g τ, htop.symm ▸ Subgroup.mem_top _⟩
    (valueTrivialInertiaResidueUnitHom K A t x : IsLocalRing.ResidueField A) =
      residueAction K A g
        (valueTrivialInertiaResidueUnitHom K A s
          (Units.mapEquiv (g : Gal(L/K)).symm.toMulEquiv x) : IsLocalRing.ResidueField A) := by
  dsimp only
  rw [valueTrivialInertiaResidueUnitHom_apply, valueTrivialInertiaResidueUnitHom_apply,
    _root_.ValuationSubring.coe_unitGroupToResidueFieldUnits_apply,
    _root_.ValuationSubring.coe_unitGroupToResidueFieldUnits_apply]
  change IsLocalRing.residue A _ = IsLocalRing.residue A (g • _)
  apply congrArg (IsLocalRing.residue A)
  apply Subtype.ext
  change _ = (g : Gal(L/K)) (_ : L)
  simp only [_root_.ValuationSubring.coe_unitGroupMulEquiv_apply,
    valueTrivialAutomorphismUnit_coe, automorphismUnitQuotient, Units.val_div_eq_div_val]
  change ((g : Gal(L/K)) (((τ : decompositionGroup K A) : Gal(L/K))
      ((g : Gal(L/K)).symm (x : L))) / (x : L)) =
    (g : Gal(L/K))
      ((((τ : decompositionGroup K A) : Gal(L/K)) ((g : Gal(L/K)).symm (x : L))) /
        ((g : Gal(L/K)).symm (x : L)))
  rw [map_div₀, AlgEquiv.apply_symm_apply]

/-- In residue characteristic zero the finite inertia character is injective. -/
theorem valueTrivialInertiaCharacterHom_injective_of_residueCharZero
    (A : _root_.ValuationSubring L) [Finite (inertiaGroup K A)]
    [CharZero (IsLocalRing.ResidueField A)] :
    Function.Injective (valueTrivialInertiaCharacterHom K A) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm ?_ bot_le
  intro s hs
  have hram := (valueTrivialInertiaCharacterHom_mem_ker_iff K A s).mp hs
  rw [ramificationGroup_eq_bot_of_residueCharZero K A] at hram
  exact Subtype.ext hram

end RamificationTheory.HilbertRamification.ValuationSubring
