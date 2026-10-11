/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Henselian
import Nyll.ValuedFieldTheory.Valuation.Henselian.RootsOfUnity
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.ValuationSubring
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.CharacterMap
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.FiniteOrderValuation
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.InertiaCharacterConjugation

/-!
# Finite inertia and roots of unity

Roots of unity in the base force trivial residue action on those roots.
For a finite extension with Henselian valuation ring and residue characteristic
zero, the corresponding finite-order inertia elements commute with decomposition.
-/

namespace RamificationTheory.HilbertRamification.ValuationSubring

open ValuationTheory.DiscreteValuationField

universe u v w

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

/-- If all roots of a fixed order split over the base, decomposition acts
trivially on the roots of that order in the Henselian residue field. -/
theorem residueAction_fixes_pow_eq_one_of_primitiveRoot_of_henselianRing
    (A : _root_.ValuationSubring L)
    [HenselianRing A (IsLocalRing.maximalIdeal A)] (n : ℕ)
    [NeZero (n : (IsLocalRing.ResidueField A))]
    (ζ : K) (hζ : IsPrimitiveRoot ζ n)
    (σ : decompositionGroup K A)
    (ξ : (IsLocalRing.ResidueField A)) (hξ : ξ ^ n = 1) :
    residueAction K A σ ξ = ξ := by
  have : NeZero n := .of_neZero_natCast (IsLocalRing.ResidueField A)
  let r : rootsOfUnity n (IsLocalRing.ResidueField A) := rootsOfUnity.mkOfPowEq ξ hξ
  obtain ⟨a, ha⟩ := _root_.ValuationSubring.rootsOfUnityReduction_surjective A n r
  have hares : (IsLocalRing.residue A) ((a : Aˣ) : A) = ξ :=
    congrArg
      (fun b : rootsOfUnity n (IsLocalRing.ResidueField A) =>
        ((b : ((IsLocalRing.ResidueField A))ˣ) : (IsLocalRing.ResidueField A))) ha
  have hapow : ((((a : Aˣ) : A) : L)) ^ n = 1 := by
    exact congrArg (fun b : A => (b : L))
      ((mem_rootsOfUnity' n (a : Aˣ)).mp a.property)
  obtain ⟨i, _hi, hai⟩ :=
    (hζ.map_of_injective (algebraMap K L).injective).eq_pow_of_pow_eq_one hapow
  have hfixed : (σ : Gal(L/K))
      (((a : Aˣ) : A) : L) =
      (((a : Aˣ) : A) : L) := by
    rw [← hai, map_pow, (σ : Gal(L/K)).commutes]
  rw [← hares]
  change (IsLocalRing.residue A) (σ • ((a : Aˣ) : A)) =
    (IsLocalRing.residue A) ((a : Aˣ) : A)
  apply congrArg (IsLocalRing.residue A)
  exact Subtype.ext hfixed

/-- In a finite valued extension, an inertia element of order dividing n commutes
with the entire decomposition group if a primitive n-th root belongs to the base. -/
theorem inertia_commutes_of_primitiveRoot_of_henselianRing [FiniteDimensional K L]
    (A : _root_.ValuationSubring L)
    [HenselianRing A (IsLocalRing.maximalIdeal A)] [CharZero (IsLocalRing.ResidueField A)]
    (n : ℕ) (hn : 0 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n)
    (τ : inertiaGroup K A) (hτ : τ ^ n = 1)
    (g : decompositionGroup K A) :
    Commute g (τ : decompositionGroup K A) := by
  have : NeZero (n : (IsLocalRing.ResidueField A)) := ⟨Nat.cast_ne_zero.mpr hn.ne'⟩
  have htop := valueTrivialInertiaGroup_eq_top_of_finite K A
  let s : valueTrivialInertiaGroup K A := ⟨τ, htop.symm ▸ Subgroup.mem_top τ⟩
  let t : valueTrivialInertiaGroup K A :=
    ⟨MulAut.conjNormal g τ, htop.symm ▸ Subgroup.mem_top _⟩
  have hsPow : s ^ n = 1 := Subtype.ext hτ
  have hresPow (x : Lˣ) :
      (valueTrivialInertiaResidueUnitHom K A s x : (IsLocalRing.ResidueField A)) ^ n = 1 := by
    have h := congrArg (fun f =>
      (f (QuotientGroup.mk' (baseUnitValueClassSubgroup K A)
        (QuotientGroup.mk' A.unitGroup x)) : (IsLocalRing.ResidueField A)))
      (congrArg (valueTrivialInertiaCharacterHom K A) hsPow)
    simpa only [map_pow, map_one, MonoidHom.pow_apply, MonoidHom.one_apply,
      valueTrivialInertiaCharacterHom_apply, valueModuloBaseToResidueUnits_mk_mk,
      Units.val_pow_eq_pow_val, Units.val_one] using h
  have hchar : valueTrivialInertiaCharacterHom K A t =
      valueTrivialInertiaCharacterHom K A s := by
    apply QuotientGroup.monoidHom_ext
    apply QuotientGroup.monoidHom_ext
    apply MonoidHom.ext
    intro x
    change valueTrivialInertiaResidueUnitHom K A t x =
      valueTrivialInertiaResidueUnitHom K A s x
    apply Units.ext
    rw [valueTrivialInertiaResidueUnitHom_conj K A g τ x]
    have harg := valueTrivialInertiaResidueUnitHom_decomposition_arg K A s g⁻¹
      (isOfFinOrder_of_finite g⁻¹) x
    change valueTrivialInertiaResidueUnitHom K A s
      (Units.mapEquiv (g : Gal(L/K)).symm.toMulEquiv x) =
        valueTrivialInertiaResidueUnitHom K A s x at harg
    rw [harg]
    exact residueAction_fixes_pow_eq_one_of_primitiveRoot_of_henselianRing A n ζ hζ g _ (hresPow x)
  have hts : t = s := valueTrivialInertiaCharacterHom_injective_of_residueCharZero K A hchar
  have hconj : g * (τ : decompositionGroup K A) * g⁻¹ =
      (τ : decompositionGroup K A) :=
    congrArg (fun a : valueTrivialInertiaGroup K A =>
      ((a : inertiaGroup K A) : decompositionGroup K A)) hts
  exact (mul_inv_eq_iff_eq_mul).mp hconj


/-- The Henselian DVF form of rootwise residue-action triviality. -/
theorem residueAction_fixes_pow_eq_one_of_primitiveRoot
    (F : HenselianDVF.{v, w} L) (n : ℕ) [NeZero (n : F.residueField)]
    (ζ : K) (hζ : IsPrimitiveRoot ζ n)
    (σ : decompositionGroup K F.valuation.valuationSubring)
    (ξ : F.residueField) (hξ : ξ ^ n = 1) :
    residueAction K F.valuation.valuationSubring σ ξ = ξ :=
  residueAction_fixes_pow_eq_one_of_primitiveRoot_of_henselianRing
    F.valuation.valuationSubring n ζ hζ σ ξ hξ

/-- The Henselian DVF form of finite inertia centrality. -/
theorem inertia_commutes_of_primitiveRoot [FiniteDimensional K L]
    (F : HenselianDVF.{v, w} L) [CharZero F.residueField]
    (n : ℕ) (hn : 0 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n)
    (τ : inertiaGroup K F.valuation.valuationSubring) (hτ : τ ^ n = 1)
    (g : decompositionGroup K F.valuation.valuationSubring) :
    Commute g (τ : decompositionGroup K F.valuation.valuationSubring) :=
  inertia_commutes_of_primitiveRoot_of_henselianRing
    F.valuation.valuationSubring n hn ζ hζ τ hτ g

end RamificationTheory.HilbertRamification.ValuationSubring
