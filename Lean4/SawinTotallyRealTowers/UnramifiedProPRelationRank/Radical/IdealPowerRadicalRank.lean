/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.IdealPowerRadicalModule

set_option autoImplicit false
/-!
# The rank of the ideal-power radical

This file converts the cardinality formula for the empty-support ideal-power
radical into the dimension formula used in Shafarevich's relation-rank bound.
-/

open scoped NumberField

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.Martinet
open KummerTheory

variable (F : Type*) [Field F] [NumberField F]
variable (p : ℕ) [Fact p.Prime]

/-- The cardinality of the elementary `p`-class quotient is `p` to its
canonical `ZMod p`-dimension. -/
theorem card_pClassGroup_eq_pow_pClassRank :
    Nat.card (PClassGroup F p) = p ^ pClassRank F p := by
  let moduleInstance : Module (ZMod p) (Additive (PClassGroup F p)) :=
    AddCommGroup.zmodModule (fun x => by
      change (Additive.toMul x) ^ p = 1
      exact pClassGroup_pow_eq_one F p (Additive.toMul x))
  let _ : Module (ZMod p) (Additive (PClassGroup F p)) := moduleInstance
  let finiteInstance : Module.Finite (ZMod p) (Additive (PClassGroup F p)) :=
    Module.Finite.of_finite
      (R := ZMod p) (M := Additive (PClassGroup F p))
  have hcard :
      Nat.card (Additive (PClassGroup F p)) =
        Nat.card (ZMod p) ^
          Module.finrank (ZMod p) (Additive (PClassGroup F p)) :=
    @Module.natCard_eq_pow_finrank
      (ZMod p) (Additive (PClassGroup F p)) inferInstance inferInstance
        moduleInstance finiteInstance
  have hrank :
      Module.finrank (ZMod p) (Additive (PClassGroup F p)) =
        pClassRank F p := by
    rfl
  exact (Nat.card_congr
    (Additive.ofMul : PClassGroup F p ≃ Additive (PClassGroup F p))).trans
      (by simpa only [Nat.card_zmod, hrank] using hcard)

/-- The exact dimension of the empty-support ideal-power radical. -/
theorem finrank_idealPowerRadicalModP :
    Module.finrank (ZMod p) (idealPowerRadicalModP F p) =
      pClassRank F p +
        (NumberField.InfinitePlace.nrRealPlaces F +
          NumberField.InfinitePlace.nrComplexPlaces F - 1 +
            (if (primitiveRoots p F).Nonempty then 1 else 0)) := by
  apply Nat.pow_right_injective (Fact.out : p.Prime).two_le
  calc
    p ^ Module.finrank (ZMod p) (idealPowerRadicalModP F p) =
        p ^ (NumberField.InfinitePlace.nrRealPlaces F +
            NumberField.InfinitePlace.nrComplexPlaces F - 1 +
              (if (primitiveRoots p F).Nonempty then 1 else 0)) *
          Nat.card (PClassGroup F p) :=
      pow_finrank_idealPowerRadicalModP F p
    _ = p ^ (NumberField.InfinitePlace.nrRealPlaces F +
            NumberField.InfinitePlace.nrComplexPlaces F - 1 +
              (if (primitiveRoots p F).Nonempty then 1 else 0)) *
          p ^ pClassRank F p := by
      rw [card_pClassGroup_eq_pow_pClassRank F p]
    _ = p ^ (pClassRank F p +
          (NumberField.InfinitePlace.nrRealPlaces F +
            NumberField.InfinitePlace.nrComplexPlaces F - 1 +
              (if (primitiveRoots p F).Nonempty then 1 else 0))) := by
      rw [← pow_add, Nat.add_comm]

/-- The radical rank formula with the root-of-unity correction written in
the form used by the external Shafarevich statement. -/
theorem finrank_idealPowerRadicalModP_eq_pClassRank_add_infinitePlaces :
    (open Classical in
      Module.finrank (ZMod p) (idealPowerRadicalModP F p) =
        pClassRank F p +
          (NumberField.InfinitePlace.nrRealPlaces F +
            NumberField.InfinitePlace.nrComplexPlaces F - 1) +
          (if ∃ ζ : F, IsPrimitiveRoot ζ p then 1 else 0)) := by
  classical
  have hroots :
      (primitiveRoots p F).Nonempty ↔ ∃ ζ : F, IsPrimitiveRoot ζ p := by
    constructor
    · rintro ⟨ζ, hζ⟩
      exact ⟨ζ, (mem_primitiveRoots (Fact.out : p.Prime).pos).mp hζ⟩
    · rintro ⟨ζ, hζ⟩
      exact ⟨ζ, (mem_primitiveRoots (Fact.out : p.Prime).pos).mpr hζ⟩
  rw [finrank_idealPowerRadicalModP F p]
  simp only [hroots]
  rw [Nat.add_assoc]

/-- Passing to the linear dual does not change the radical dimension. -/
theorem finrank_idealPowerRadicalModPDual :
    (open Classical in
      Module.finrank (ZMod p)
          (Module.Dual (ZMod p) (idealPowerRadicalModP F p)) =
        pClassRank F p +
          (NumberField.InfinitePlace.nrRealPlaces F +
            NumberField.InfinitePlace.nrComplexPlaces F - 1) +
          (if ∃ ζ : F, IsPrimitiveRoot ζ p then 1 else 0)) := by
  classical
  let _ : FiniteDimensional (ZMod p) (idealPowerRadicalModP F p) :=
    idealPowerRadicalModP_finiteDimensional F p
  rw [Subspace.dual_finrank_eq,
    finrank_idealPowerRadicalModP_eq_pClassRank_add_infinitePlaces F p]

end ClassFieldTower.Martinet.Shafarevich
