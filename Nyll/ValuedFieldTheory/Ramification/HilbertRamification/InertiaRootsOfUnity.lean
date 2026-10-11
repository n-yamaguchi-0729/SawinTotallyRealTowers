/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.ValuationSubring
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.HenselianRootsOfUnity
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Order.GroupWithZero.Basic

/-!
# Roots of unity in the actual inertia field

In residue characteristic zero, inertia fixes every root of unity. Each root
is a valuation-ring unit. Its image under inertia has the same reduction, so
the injectivity of Henselian root reduction identifies the two roots. This
gives membership in the actual inertia fixed field without assuming any
comparison or surjectivity of residue-field maps.
-/

namespace RamificationTheory.HilbertRamification.ValuationSubring

open ValuationTheory.DiscreteValuationField

universe u v w

variable (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
  (F : HenselianDVF.{v, w} L) [CharZero F.residueField]

-- The actions on the valuation ring and residue field are the canonical
-- decomposition-subgroup actions. No new algebra, action, or topology is installed.
/-- Every actual inertia automorphism fixes every finite-order field element
when the upper Henselian DVF has residue characteristic zero. -/
theorem inertia_fixes_of_isOfFinOrder
    (σ : inertiaGroup K F.valuation.valuationSubring)
    (ζ : L) (hζ : IsOfFinOrder ζ) :
    ((σ : decompositionGroup K F.valuation.valuationSubring) : L ≃ₐ[K] L) ζ = ζ := by
  obtain ⟨n, hn, hζpow⟩ := hζ.exists_pow_eq_one
  have : NeZero n := ⟨hn.ne'⟩
  have : NeZero (n : F.residueField) := ⟨Nat.cast_ne_zero.mpr hn.ne'⟩
  have hvalpow : F.valuation ζ ^ n = 1 := by
    rw [← map_pow, hζpow, map_one]
  have hval : F.valuation ζ = 1 :=
    (pow_eq_one_iff_of_nonneg zero_le hn.ne').mp hvalpow
  let a : F.valuationSubring := ⟨ζ, hval.le⟩
  have hapow : a ^ n = 1 := Subtype.ext hζpow
  let ξ : rootsOfUnity n F.valuationSubring := rootsOfUnity.mkOfPowEq a hapow
  let e : F.valuationSubring ≃+* F.valuationSubring :=
    MulSemiringAction.toRingEquiv
      (decompositionGroup K F.valuation.valuationSubring) F.valuationSubring
      (σ : decompositionGroup K F.valuation.valuationSubring)
  have hres : HenselianDVF.rootsOfUnityReduction F n
        (restrictRootsOfUnity e.toRingHom n ξ) =
      HenselianDVF.rootsOfUnityReduction F n ξ := by
    apply rootsOfUnity.coe_injective
    change F.residueMap (e a) = F.residueMap a
    calc
      F.residueMap (e a) =
          (σ : decompositionGroup K F.valuation.valuationSubring) • F.residueMap a := by
        rw [← IsLocalRing.ResidueField.residue_smul]
        rfl
      _ = F.residueMap a := by
        have hσ : residueAction K F.valuation.valuationSubring
            (σ : decompositionGroup K F.valuation.valuationSubring) = 1 := σ.property
        exact DFunLike.congr_fun hσ (F.residueMap a)
  have heq : restrictRootsOfUnity e.toRingHom n ξ = ξ :=
    HenselianDVF.rootsOfUnityReduction_injective F n hres
  exact congrArg (fun x : rootsOfUnity n F.valuationSubring =>
    (((x : F.valuationSubringˣ) : F.valuationSubring) : L)) heq

/-- All roots of unity lie in the actual inertia fixed field in residue
characteristic zero. No finiteness or residue-field comparison is required. -/
theorem mem_inertiaField_of_isOfFinOrder (ζ : L) (hζ : IsOfFinOrder ζ) :
    ζ ∈ inertiaField K F.valuation.valuationSubring := by
  apply (mem_inertiaField_iff (K := K) F.valuation.valuationSubring ζ).mpr
  intro σ
  exact inertia_fixes_of_isOfFinOrder K F σ ζ hζ

end RamificationTheory.HilbertRamification.ValuationSubring
