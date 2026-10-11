/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.CharacterMap
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.ResidueField
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Nat.Factors
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Wild ramification groups

This file contains the orbit-sum argument controlling the wild
ramification group.  The same field calculation supplies both branches
needed by tame inertia: the ramification group is trivial in residue
characteristic zero, and it is a `p`-group in positive residue
characteristic `p`.
-/


noncomputable section


universe u v

namespace TameAbhyankar.SGA1.TameInertiaRamification

open RamificationTheory.HilbertRamification
open RamificationTheory.HilbertRamification.ValuationSubring

/-- The orbit sum of a nontrivial ramification automorphism of prime order
forces that prime to vanish in the residue field. -/
private theorem residue_natCast_eq_zero_of_ramification_prime_order
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (V : _root_.ValuationSubring L)
    (ell : ℕ) (sigma : ramificationGroup K V)
    (hsigmaOrder : orderOf sigma = ell) (hsigma : sigma ≠ 1) :
    (ell : IsLocalRing.ResidueField V) = 0 := by
  have hsigmaAut :
      (((sigma : inertiaGroup K V) : decompositionGroup K V) :
        L ≃ₐ[K] L) ≠ 1 := by
    intro h
    apply hsigma
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact h
  obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp hsigmaAut
  let g : L ≃ₐ[K] L :=
    ((sigma : inertiaGroup K V) : decompositionGroup K V)
  let y : L := g x - x
  have hy : y ≠ 0 := sub_ne_zero.mpr hx
  let yu : Lˣ := Units.mk0 y hy
  have hsigmaPow : sigma ^ ell = 1 := by
    rw [← hsigmaOrder]
    exact pow_orderOf_eq_one sigma
  have hgPow : g ^ ell = 1 := by
    have h := congrArg
      (fun tau : ramificationGroup K V ↦
        (((tau : inertiaGroup K V) : decompositionGroup K V) :
          L ≃ₐ[K] L)) hsigmaPow
    simpa [g] using h
  let quotient (i : ℕ) : Lˣ :=
    automorphismUnitQuotient K V
      (((sigma ^ i : ramificationGroup K V) : inertiaGroup K V) :
        decompositionGroup K V) yu
  have hprincipal (i : ℕ) : quotient i ∈ V.principalUnitGroup :=
    (mem_ramificationGroup_iff K V
      ((sigma ^ i : ramificationGroup K V) : inertiaGroup K V)).mp
        (sigma ^ i).property yu
  let quotientUnit (i : ℕ) : V.unitGroup :=
    ⟨quotient i, V.principal_units_le_units (hprincipal i)⟩
  let quotientV (i : ℕ) : V :=
    (V.unitGroupMulEquiv (quotientUnit i) : Vˣ)
  have hquotientV_coe (i : ℕ) :
      (quotientV i : L) = (quotient i : L) := by
    rfl
  have hresidue (i : ℕ) :
      IsLocalRing.residue V (quotientV i) = 1 := by
    have hker : quotientUnit i ∈ V.unitGroupToResidueFieldUnits.ker := by
      rw [V.ker_unitGroupToResidueFieldUnits]
      exact hprincipal i
    have hunit := MonoidHom.mem_ker.mp hker
    have hcoe := congrArg Units.val hunit
    change IsLocalRing.residue V
      (V.unitGroupMulEquiv (quotientUnit i) : V) = 1 at hcoe
    simpa only [quotientV] using hcoe
  have hsumField :
      ∑ i ∈ Finset.range ell, (quotient i : L) = 0 := by
    calc
      ∑ i ∈ Finset.range ell, (quotient i : L) =
          ∑ i ∈ Finset.range ell, (g ^ i) y / y := by
        apply Finset.sum_congr rfl
        intro i _hi
        simp only [quotient, automorphismUnitQuotient,
          Units.val_div_eq_div_val, Units.coe_mapEquiv, yu]
        rfl
      _ = (∑ i ∈ Finset.range ell, (g ^ i) y) / y := by
        rw [Finset.sum_div]
      _ = (∑ i ∈ Finset.range ell,
          ((g ^ (i + 1)) x - (g ^ i) x)) / y := by
        congr 1
        apply Finset.sum_congr rfl
        intro i _hi
        simp [y, map_sub, pow_succ, AlgEquiv.mul_apply]
      _ = ((g ^ ell) x - (g ^ 0) x) / y := by
        congr 1
        exact Finset.sum_range_sub (fun i ↦ (g ^ i) x) ell
      _ = 0 := by
        rw [hgPow]
        simp
  have hsumV : ∑ i ∈ Finset.range ell, quotientV i = 0 := by
    apply V.subtype_injective
    rw [map_sum, map_zero]
    change ∑ i ∈ Finset.range ell, (quotientV i : L) = 0
    simpa only [hquotientV_coe] using hsumField
  have hsumResidue := congrArg (IsLocalRing.residue V) hsumV
  simpa only [map_sum, map_zero, hresidue, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_one] using hsumResidue

/-- In residue characteristic zero the ramification group is trivial. -/
theorem ramificationGroup_eq_bot_of_residue_charZero
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (V : _root_.ValuationSubring L) [CharZero (IsLocalRing.ResidueField V)]
    [Finite (ramificationGroup K V)] :
    ramificationGroup K V = ⊥ := by
  apply (Subgroup.eq_bot_iff_card (ramificationGroup K V)).2
  by_contra hcard
  obtain ⟨ell, hell, helldvd⟩ := Nat.exists_prime_and_dvd hcard
  let : Fact ell.Prime := ⟨hell⟩
  obtain ⟨sigma, hsigmaOrder⟩ :=
    exists_prime_orderOf_dvd_card'
      (G := ramificationGroup K V) ell helldvd
  have hsigmaOne : sigma = 1 := by
    by_contra hsigma
    have hellZero : (ell : IsLocalRing.ResidueField V) = 0 :=
      residue_natCast_eq_zero_of_ramification_prime_order
        K V ell sigma hsigmaOrder hsigma
    exact (Nat.cast_ne_zero.mpr hell.ne_zero) hellZero
  have : ell = 1 := by
    rw [← hsigmaOrder, hsigmaOne, orderOf_one]
  exact hell.ne_one this

/-- A finite ramification group is a `p`-group when the residue field has
positive prime characteristic `p`. -/
theorem ramificationGroup_isPGroup_of_residue_charP
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (V : _root_.ValuationSubring L) (p : ℕ)
    [Fact p.Prime] [CharP (IsLocalRing.ResidueField V) p]
    [Finite (ramificationGroup K V)] :
    IsPGroup p (ramificationGroup K V) := by
  rw [IsPGroup.iff_orderOf]
  intro sigma
  refine ⟨(orderOf sigma).primeFactorsList.length, ?_⟩
  apply Nat.eq_prime_pow_of_unique_prime_dvd (orderOf_pos sigma).ne'
  intro ell hell hellDvd
  let tau : ramificationGroup K V := sigma ^ (orderOf sigma / ell)
  have htauOrder : orderOf tau = ell := by
    exact orderOf_pow_orderOf_div (orderOf_pos sigma).ne' hellDvd
  by_contra hne
  have htauOne : tau = 1 := by
    by_contra htau
    have hellZero : (ell : IsLocalRing.ResidueField V) = 0 :=
      residue_natCast_eq_zero_of_ramification_prime_order
        K V ell tau htauOrder htau
    have hpDvd : p ∣ ell :=
      (CharP.cast_eq_zero_iff (IsLocalRing.ResidueField V) p ell).mp
        hellZero
    have hpEq : p = ell := by
      rcases hell.eq_one_or_self_of_dvd p hpDvd with hpOne | hpEq
      · exact False.elim ((Fact.out : p.Prime).ne_one hpOne)
      · exact hpEq
    exact hne hpEq.symm
  have : ell = 1 := by
    rw [← htauOrder, htauOne, orderOf_one]
  exact hell.ne_one this

end TameAbhyankar.SGA1.TameInertiaRamification

end
