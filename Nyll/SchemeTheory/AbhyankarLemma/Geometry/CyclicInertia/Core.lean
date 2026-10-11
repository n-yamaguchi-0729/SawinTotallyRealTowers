/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.AbhyankarLemma.Geometry.CyclicInertia.RamificationGroup
import Mathlib.RingTheory.IntegralDomain

/-!
# Tame-inertia cyclicity core

The production inertia character embeds tame inertia into the residue
field after coprimality kills the wild ramification kernel.  This file
contains that character argument and the comparison with ideal inertia.
-/


noncomputable section


universe u v

namespace TameAbhyankar.SGA1.TameInertiaCyclicCore

open RamificationTheory.HilbertRamification
open RamificationTheory.HilbertRamification.ValuationSubring

private theorem character_evaluation_injective_of_isCyclic
    (X k : Type*) [Group X] [IsCyclic X] [Field k] :
    ∃ x : X, Function.Injective
      (((MonoidHom.eval : X →* (X →* kˣ) →* kˣ) x)) := by
  obtain ⟨x, hx⟩ := IsCyclic.exists_generator (α := X)
  refine ⟨x, ?_⟩
  intro chi psi heq
  apply MonoidHom.ext
  intro y
  obtain ⟨n, rfl⟩ := hx y
  change chi (x ^ n) = psi (x ^ n)
  rw [map_zpow, map_zpow]
  change chi x = psi x at heq
  exact congrArg (fun z : kˣ ↦ z ^ n) heq

/-- The production inertia character embeds tame inertia into the residue
field once `ringExpChar` coprimality kills its ramification kernel. -/
theorem inertiaGroup_isCyclic_of_card_coprime_ringExpChar
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (V : _root_.ValuationSubring L)
    [Finite (inertiaGroup K V)]
    (hvalue : valueTrivialInertiaGroup K V = ⊤)
    [IsCyclic
      ((Lˣ ⧸ V.unitGroup) ⧸ baseUnitValueClassSubgroup K V)]
    (hcop : Nat.Coprime (Nat.card (inertiaGroup K V))
      (ringExpChar (IsLocalRing.ResidueField V))) :
    IsCyclic (inertiaGroup K V) := by
  let k := IsLocalRing.ResidueField V
  let : Finite (ramificationGroup K V) :=
    Finite.of_injective (ramificationGroup K V).subtype
      Subtype.coe_injective
  have hramBot : ramificationGroup K V = ⊥ := by
    by_cases hchar : ringChar k = 0
    · let : CharZero k :=
        (CharP.ringChar_zero_iff_CharZero (R := k)).mp hchar
      exact
        TameInertiaRamification.ramificationGroup_eq_bot_of_residue_charZero
          K V
    · have hp : (ringChar k).Prime :=
        CharP.char_prime_of_ne_zero k hchar
      let : Fact (ringChar k).Prime := ⟨hp⟩
      have hramP : IsPGroup (ringChar k) (ramificationGroup K V) :=
        TameInertiaRamification.ramificationGroup_isPGroup_of_residue_charP
          K V (ringChar k)
      obtain ⟨n, hramCard⟩ := IsPGroup.iff_card.mp hramP
      have hramDvd : Nat.card (ramificationGroup K V) ∣
          Nat.card (inertiaGroup K V) :=
        Subgroup.card_subgroup_dvd_card (ramificationGroup K V)
      have hcop' : Nat.Coprime (Nat.card (inertiaGroup K V))
          (ringChar k) := by
        simpa [k, ringExpChar,
          Nat.max_eq_left hp.one_lt.le] using hcop
      have hramOne : Nat.card (ramificationGroup K V) = 1 :=
        Nat.eq_one_of_dvd_coprimes (hcop'.pow_right n) hramDvd
          (hramCard ▸ dvd_rfl)
      exact (Subgroup.eq_bot_iff_card (ramificationGroup K V)).2 hramOne
  let e : inertiaGroup K V ≃* valueTrivialInertiaGroup K V := {
    toFun sigma := ⟨sigma, by rw [hvalue]; trivial⟩
    invFun sigma := sigma
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl }
  let chi := (valueTrivialInertiaCharacterHom K V).comp e.toMonoidHom
  have hchiKerRam : chi.ker = ramificationGroup K V := by
    ext sigma
    change
      valueTrivialInertiaCharacterHom K V (e sigma) = 1 ↔
        sigma ∈ ramificationGroup K V
    rw [← MonoidHom.mem_ker,
      valueTrivialInertiaCharacterHom_mem_ker_iff]
    rfl
  have hchiKer : chi.ker = ⊥ := by
    rw [hchiKerRam, hramBot]
  have hchi : Function.Injective chi := chi.ker_eq_bot_iff.mp hchiKer
  obtain ⟨x, hx⟩ := character_evaluation_injective_of_isCyclic
    ((Lˣ ⧸ V.unitGroup) ⧸ baseUnitValueClassSubgroup K V)
    (IsLocalRing.ResidueField V)
  let ev :
      (((Lˣ ⧸ V.unitGroup) ⧸ baseUnitValueClassSubgroup K V) →*
        (IsLocalRing.ResidueField V)ˣ) →*
          (IsLocalRing.ResidueField V)ˣ :=
    (MonoidHom.eval :
      ((Lˣ ⧸ V.unitGroup) ⧸ baseUnitValueClassSubgroup K V) →*
        ((((Lˣ ⧸ V.unitGroup) ⧸ baseUnitValueClassSubgroup K V) →*
          (IsLocalRing.ResidueField V)ˣ) →*
            (IsLocalRing.ResidueField V)ˣ)) x
  let rho : inertiaGroup K V →* IsLocalRing.ResidueField V :=
    (Units.coeHom (IsLocalRing.ResidueField V)).comp (ev.comp chi)
  apply isCyclic_of_injective_ringHom rho
  exact Units.val_injective.comp (hx.comp hchi)

/-- Ideal inertia at the maximal ideal of a valuation subring agrees with
the kernel-of-residue-action inertia group. -/
theorem valuationSubring_maximalIdeal_inertia_eq
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (V : _root_.ValuationSubring L) :
    (IsLocalRing.maximalIdeal V).toAddSubgroup.inertia
        (decompositionGroup K V) = inertiaGroup K V := by
  ext sigma
  rw [← residueAction_ker (K := K) V, MonoidHom.mem_ker]
  constructor
  · intro hsigma
    apply RingEquiv.ext
    intro x
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    change sigma • (IsLocalRing.residue V a : IsLocalRing.ResidueField V) =
      IsLocalRing.residue V a
    rw [← IsLocalRing.ResidueField.residue_smul]
    rw [(open _root_.ValuationTheory.DiscreteValuationField.ResidueField in
      residue_eq_residue_iff_sub_mem_maximalIdeal)]
    exact hsigma a
  · intro hsigma a
    change sigma • a - a ∈ IsLocalRing.maximalIdeal V
    rw [← (open _root_.ValuationTheory.DiscreteValuationField.ResidueField in
      residue_eq_residue_iff_sub_mem_maximalIdeal)]
    have happ := congrArg
      (fun e : IsLocalRing.ResidueField V ≃+* IsLocalRing.ResidueField V ↦
        e (IsLocalRing.residue V a)) hsigma
    change sigma • (IsLocalRing.residue V a : IsLocalRing.ResidueField V) =
      IsLocalRing.residue V a at happ
    rwa [← IsLocalRing.ResidueField.residue_smul] at happ

end TameAbhyankar.SGA1.TameInertiaCyclicCore

end
