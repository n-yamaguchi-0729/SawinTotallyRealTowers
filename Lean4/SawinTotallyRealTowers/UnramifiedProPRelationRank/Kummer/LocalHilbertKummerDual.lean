/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.AbsoluteKummerH1Linear
import ClassFieldTheory.LocalClassFieldTheory.Kummer.LocalHilbertPairingNondegeneracy
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.ZMod

set_option autoImplicit false
/-! # The local Hilbert pairing as a linear dual embedding -/

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open KummerTheory LocalClassFieldTheory LocalClassFieldTheory.Kummer

variable (L : Type) [Field L] [CharZero L]
variable [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
variable (n : ℕ+) [Fact ((n : ℕ).Prime)]

local instance localHilbertDualCanonicalZModAddCommGroup : AddCommGroup (ZMod (n : ℕ)) :=
  (ZMod.instField (n : ℕ)).toDivisionRing.toAddCommGroup

/-- A primitive root identifies the `n`-th roots of unity with additive `ZMod n`. -/
noncomputable def localNthRootsEquivMultiplicativeZMod
    (hmu : (primitiveRoots (n : ℕ) L).Nonempty) :
    nthRootsSubgroup L (n : ℕ) ≃* Multiplicative (ZMod (n : ℕ)) := by
  letI : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let ζ : L := hmu.choose
  let hζ : IsPrimitiveRoot ζ (n : ℕ) :=
    (mem_primitiveRoots n.pos).mp hmu.choose_spec
  let hζunit := hζ.isUnit_unit' n.ne_zero
  exact
    (nthRootsSubgroupEquivRootsOfUnity L (n : ℕ)).trans
      ((MulEquiv.subgroupCongr hζunit.zpowers_eq.symm).trans
        hζunit.zmodEquivZPowers.symm.toMultiplicativeRight)

/-- The local Hilbert pairing with its roots-of-unity values written in `ZMod n`. -/
noncomputable def localHilbertPairingZMod
    (hmu : (primitiveRoots (n : ℕ) L).Nonempty) :
    (Lˣ ⧸ (powMonoidHom (n : ℕ) : Lˣ →* Lˣ).range) →*
      ((Lˣ ⧸ (powMonoidHom (n : ℕ) : Lˣ →* Lˣ).range) →*
        Multiplicative (ZMod (n : ℕ))) := by
  let hnL : ((n : ℕ) : L) ≠ 0 := Nat.cast_ne_zero.mpr n.ne_zero
  let e := localNthRootsEquivMultiplicativeZMod L n hmu
  let H := localHilbertPairing L n hnL hmu
  exact
  { toFun := fun a ↦ e.toMonoidHom.comp (H a)
    map_one' := by
      apply MonoidHom.ext
      intro b
      change e (H 1 b) = 1
      rw [H.map_one]
      exact e.map_one
    map_mul' := by
      intro a c
      apply MonoidHom.ext
      intro b
      change e (H (a * c) b) = e (H a b) * e (H c b)
      rw [H.map_mul]
      exact e.map_mul (H a b) (H c b) }

/-- The Hilbert character of one local power class, regarded as a linear functional. -/
noncomputable def localHilbertLinearFunctional
    (hmu : (primitiveRoots (n : ℕ) L).Nonempty)
    (a : absolutePowerClassModP L (n : ℕ)) :
    Module.Dual (ZMod (n : ℕ)) (absolutePowerClassModP L (n : ℕ)) := by
  letI : Module (ZMod (n : ℕ))
      (Additive
        (Lˣ ⧸ (powMonoidHom (n : ℕ) : Lˣ →* Lˣ).range)) :=
    additiveZModModuleOfPowEqOne (n : ℕ)
      (absolutePowerClassQuotient_pow_eq_one L (n : ℕ))
  exact
    (localHilbertPairingZMod L n hmu (Additive.toMul a)).toAdditiveLeft.toZModLinearMap
      (n : ℕ)

/-- The local Hilbert pairing, curried as a `ZMod n`-linear map into the dual. -/
noncomputable def localHilbertDualEmbedding
    (hmu : (primitiveRoots (n : ℕ) L).Nonempty) :
    absolutePowerClassModP L (n : ℕ) →ₗ[ZMod (n : ℕ)]
      Module.Dual (ZMod (n : ℕ)) (absolutePowerClassModP L (n : ℕ)) := by
  letI : Module (ZMod (n : ℕ))
      (Additive
        (Lˣ ⧸ (powMonoidHom (n : ℕ) : Lˣ →* Lˣ).range)) :=
    additiveZModModuleOfPowEqOne (n : ℕ)
      (absolutePowerClassQuotient_pow_eq_one L (n : ℕ))
  let f :
      Additive
          (Lˣ ⧸ (powMonoidHom (n : ℕ) : Lˣ →* Lˣ).range) →+
        Module.Dual (ZMod (n : ℕ)) (absolutePowerClassModP L (n : ℕ)) :=
  { toFun := localHilbertLinearFunctional L n hmu
    map_zero' := by
      apply LinearMap.ext
      intro b
      change (localHilbertPairingZMod L n hmu 1 (Additive.toMul b)).toAdd = 0
      rw [map_one]
      rfl
    map_add' := by
      intro a c
      apply LinearMap.ext
      intro b
      change
        (localHilbertPairingZMod L n hmu
          (Additive.toMul a * Additive.toMul c) (Additive.toMul b)).toAdd =
        (localHilbertPairingZMod L n hmu
          (Additive.toMul a) (Additive.toMul b)).toAdd +
        (localHilbertPairingZMod L n hmu
          (Additive.toMul c) (Additive.toMul b)).toAdd
      rw [map_mul]
      rfl }
  exact f.toZModLinearMap (n : ℕ)

@[simp]
theorem localHilbertDualEmbedding_apply
    (hmu : (primitiveRoots (n : ℕ) L).Nonempty)
    (a b : absolutePowerClassModP L (n : ℕ)) :
    localHilbertDualEmbedding L n hmu a b =
      (localHilbertPairingZMod L n hmu
        (Additive.toMul a) (Additive.toMul b)).toAdd :=
  rfl

/-- Nondegeneracy makes the dual-valued local Hilbert map injective. -/
theorem localHilbertDualEmbedding_injective
    (hmu : (primitiveRoots (n : ℕ) L).Nonempty) :
    Function.Injective (localHilbertDualEmbedding L n hmu) := by
  intro a c hac
  apply Additive.toMul.injective
  apply localHilbertPairing_injective_left L n
    (Nat.cast_ne_zero.mpr n.ne_zero) hmu
  apply MonoidHom.ext
  intro b
  apply (localNthRootsEquivMultiplicativeZMod L n hmu).injective
  apply Multiplicative.toAdd.injective
  exact LinearMap.congr_fun hac (Additive.ofMul b)

end ClassFieldTower.Martinet.Shafarevich
