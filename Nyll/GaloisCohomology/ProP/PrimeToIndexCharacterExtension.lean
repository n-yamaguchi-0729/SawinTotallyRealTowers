/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.ProP.FiniteIndexTransfer
import Nyll.GaloisCohomology.ProP.TransferRestriction
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Instances.ZMod
import Mathlib.Topology.Algebra.Ring.Basic

/-!
# Extending invariant characters across a coprime index

Transfer followed by multiplication by the inverse index extends a conjugation-invariant
character on an open normal subgroup. The modulus need not be prime.
-/

namespace ClassFieldTower.Cohomology

variable {G : Type*} [Group G]

/-- A cyclic character is determined by its restriction to a normal subgroup of
coprime index. This uniqueness statement does not require finite index. -/
theorem cyclicCharacterRestriction_injective_of_index_coprime
    (H : Subgroup G) [H.Normal] (n : ℕ) (hcop : H.index.Coprime n) :
    Function.Injective
      (fun φ : G →* Multiplicative (ZMod n) => φ.comp H.subtype) := by
  intro φ ψ hres
  apply MonoidHom.ext
  intro g
  have hpow : g ^ H.index ∈ H := by
    apply (QuotientGroup.eq_one_iff (g ^ H.index)).mp
    change (QuotientGroup.mk' H) (g ^ H.index) = 1
    rw [map_pow, Subgroup.index_eq_card]
    exact pow_card_eq_one'
  have heq := DFunLike.congr_fun hres (⟨g ^ H.index, hpow⟩ : H)
  change φ (g ^ H.index) = ψ (g ^ H.index) at heq
  rw [map_pow, map_pow] at heq
  have hunit : IsUnit (H.index : ZMod n) :=
    (ZMod.isUnit_iff_coprime H.index n).mpr hcop
  apply Multiplicative.toAdd.injective
  apply hunit.mul_left_cancel
  simpa only [toAdd_pow, nsmul_eq_mul] using
    congrArg (fun z : Multiplicative (ZMod n) => z.toAdd) heq

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- Transfer divided by the subgroup index, with values in the additive cyclic group. -/
noncomputable def primeToIndexCharacterExtension
    (H : OpenSubgroup G) [H.toSubgroup.FiniteIndex] (n : ℕ)
    (φ : H →ₜ* Multiplicative (ZMod n)) : G →ₜ* Multiplicative (ZMod n) where
  toFun g := Multiplicative.ofAdd
    ((H.toSubgroup.index : ZMod n)⁻¹ * (openSubgroupTransfer H φ g).toAdd)
  map_one' := by
    change (H.toSubgroup.index : ZMod n)⁻¹ * (openSubgroupTransfer H φ 1).toAdd = 0
    rw [map_one, toAdd_one, mul_zero]
  map_mul' := by
    intro x y
    change (H.toSubgroup.index : ZMod n)⁻¹ *
      (openSubgroupTransfer H φ (x * y)).toAdd = _
    rw [map_mul, toAdd_mul]
    exact mul_add _ _ _
  continuous_toFun := by
    change Continuous fun g =>
      (H.toSubgroup.index : ZMod n)⁻¹ * (openSubgroupTransfer H φ g).toAdd
    exact continuous_const.mul (openSubgroupTransfer H φ).continuous_toFun

/-- Coprimality and conjugation invariance make normalized transfer restrict to the
original character. -/
theorem primeToIndexCharacterExtension_subtype
    (H : OpenSubgroup G) [H.toSubgroup.Normal] [H.toSubgroup.FiniteIndex]
    (n : ℕ) (hindex : H.toSubgroup.index.Coprime n)
    (φ : H →ₜ* Multiplicative (ZMod n))
    (hinv : ∀ (g : G) (h : H), φ (MulAut.conjNormal g h) = φ h) (h : H) :
    primeToIndexCharacterExtension H n φ (h : G) = φ h := by
  apply Multiplicative.toAdd.injective
  change (H.toSubgroup.index : ZMod n)⁻¹ * (openSubgroupTransfer H φ (h : G)).toAdd =
    (φ h).toAdd
  have htransfer : openSubgroupTransfer H φ (h : G) = φ h ^ H.toSubgroup.index :=
    transfer_subtype_eq_pow_of_conjInvariant H.toSubgroup φ.toMonoidHom hinv h
  rw [htransfer, toAdd_pow, nsmul_eq_mul, ← mul_assoc,
    ZMod.inv_mul_of_unit _ ((ZMod.isUnit_iff_coprime _ _).mpr hindex), one_mul]

end ClassFieldTower.Cohomology
