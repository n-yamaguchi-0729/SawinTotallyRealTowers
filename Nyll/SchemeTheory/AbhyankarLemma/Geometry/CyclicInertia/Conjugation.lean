/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.AbhyankarLemma.Geometry.CyclicInertia.Ideal
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.Conjugation

/-!
# Conjugation on tame inertia over a discrete valuation ring

This file records the finite-level equivariance of the residue-unit inertia
character under the decomposition group.  In residue characteristic zero the
character is faithful, so an element whose residue action inverts the
character values conjugates inertia to its inverse.
-/

noncomputable section


universe u v

namespace TameAbhyankar.SGA1

open RamificationTheory.HilbertRamification
open RamificationTheory.HilbertRamification.ValuationSubring

/-- The inclusion of DVR inertia into the value-trivial inertia group. -/
def inertiaToValueTrivialOfDVR
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (V : _root_.ValuationSubring L) [IsDiscreteValuationRing V] :
    inertiaGroup K V →* valueTrivialInertiaGroup K V where
  toFun sigma :=
    ⟨sigma, inertia_mem_valueTrivialInertiaGroup_of_dvr K V sigma⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The residue-unit character of inertia over a DVR. -/
def dvrInertiaCharacter
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (V : _root_.ValuationSubring L) [IsDiscreteValuationRing V] :
    inertiaGroup K V →*
      (((Lˣ ⧸ V.unitGroup) ⧸ baseUnitValueClassSubgroup K V) →*
        (IsLocalRing.ResidueField V)ˣ) :=
  (valueTrivialInertiaCharacterHom K V).comp
    (inertiaToValueTrivialOfDVR K V)

/-- Conjugation by a decomposition element, restricted to inertia. -/
def inertiaConjugate
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (V : _root_.ValuationSubring L) (g : decompositionGroup K V) :
    inertiaGroup K V →* inertiaGroup K V where
  toFun sigma :=
    ⟨g * (sigma : decompositionGroup K V) * g⁻¹, by
      exact (inertiaGroup_normal (K := K) V).conj_mem
        (sigma : decompositionGroup K V) sigma.property g⟩
  map_one' := by
    ext
    simp
  map_mul' sigma tau := by
    ext
    simp [mul_assoc]

/-- The finite-level inertia character is equivariant for conjugation: the
decomposition element acts on the residue-unit value, while its inverse acts
on the field-unit argument. -/
theorem dvrInertiaCharacter_conjugate_apply_mk_mk
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (V : _root_.ValuationSubring L) [IsDiscreteValuationRing V]
    (g : decompositionGroup K V) (sigma : inertiaGroup K V) (x : Lˣ) :
    dvrInertiaCharacter K V (inertiaConjugate K V g sigma)
        (QuotientGroup.mk' (baseUnitValueClassSubgroup K V)
          (QuotientGroup.mk' V.unitGroup x)) =
      Units.mapEquiv (residueAction K V g).toMulEquiv
        (dvrInertiaCharacter K V sigma
          (QuotientGroup.mk' (baseUnitValueClassSubgroup K V)
            (QuotientGroup.mk' V.unitGroup
              (Units.mapEquiv
                (((g⁻¹ : decompositionGroup K V) : L ≃ₐ[K] L).toMulEquiv) x)))) := by
  apply Units.ext
  change
    IsLocalRing.residue V
        (V.unitGroupMulEquiv
          (valueTrivialAutomorphismUnit K V
            (inertiaToValueTrivialOfDVR K V (inertiaConjugate K V g sigma)) x) : V) =
      g • (IsLocalRing.residue V
          (V.unitGroupMulEquiv
            (valueTrivialAutomorphismUnit K V
              (inertiaToValueTrivialOfDVR K V sigma)
              (Units.mapEquiv
                (((g⁻¹ : decompositionGroup K V) : L ≃ₐ[K] L).toMulEquiv) x)) : V))
  rw [← IsLocalRing.ResidueField.residue_smul]
  congr 1
  apply Subtype.ext
  have coe_smul (a : V) : ((g • a : V) : L) =
      (g : L ≃ₐ[K] L) (a : L) := rfl
  rw [coe_smul]
  simp [valueTrivialAutomorphismUnit,
    automorphismUnitQuotient, inertiaConjugate,
    inertiaToValueTrivialOfDVR, mul_assoc, div_eq_mul_inv]

/-- A decomposition automorphism does not change the relative value-class
argument of the DVR inertia character. -/
theorem dvrInertiaCharacter_mapEquiv_inv_argument
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (V : _root_.ValuationSubring L) [IsDiscreteValuationRing V]
    (g : decompositionGroup K V) (sigma : inertiaGroup K V) (x : Lˣ) :
    dvrInertiaCharacter K V sigma
        (QuotientGroup.mk' (baseUnitValueClassSubgroup K V)
          (QuotientGroup.mk' V.unitGroup
            (Units.mapEquiv
              (((g⁻¹ : decompositionGroup K V) : L ≃ₐ[K] L).toMulEquiv) x))) =
      dvrInertiaCharacter K V sigma
        (QuotientGroup.mk' (baseUnitValueClassSubgroup K V)
          (QuotientGroup.mk' V.unitGroup x)) := by
  apply congrArg (dvrInertiaCharacter K V sigma)
  apply congrArg (QuotientGroup.mk' (baseUnitValueClassSubgroup K V))
  apply QuotientGroup.eq_iff_div_mem.mpr
  simpa only [automorphismUnitQuotient] using
    (automorphismUnitQuotient_mem_unitGroup_of_dvr K V
      (g⁻¹ : decompositionGroup K V) x)

/-- Equivariance with the unchanged DVR value-class argument. -/
theorem dvrInertiaCharacter_conjugate_apply
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (V : _root_.ValuationSubring L) [IsDiscreteValuationRing V]
    (g : decompositionGroup K V) (sigma : inertiaGroup K V) (x : Lˣ) :
    dvrInertiaCharacter K V (inertiaConjugate K V g sigma)
        (QuotientGroup.mk' (baseUnitValueClassSubgroup K V)
          (QuotientGroup.mk' V.unitGroup x)) =
      Units.mapEquiv (residueAction K V g).toMulEquiv
        (dvrInertiaCharacter K V sigma
          (QuotientGroup.mk' (baseUnitValueClassSubgroup K V)
            (QuotientGroup.mk' V.unitGroup x))) := by
  rw [dvrInertiaCharacter_conjugate_apply_mk_mk,
    dvrInertiaCharacter_mapEquiv_inv_argument]

/-- In residue characteristic zero, the DVR inertia character is faithful. -/
theorem dvrInertiaCharacter_injective_of_residue_charZero
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (V : _root_.ValuationSubring L) [IsDiscreteValuationRing V]
    [CharZero (IsLocalRing.ResidueField V)]
    [Finite (inertiaGroup K V)] :
    Function.Injective (dvrInertiaCharacter K V) := by
  apply (MonoidHom.ker_eq_bot_iff (dvrInertiaCharacter K V)).mp
  have hram : ramificationGroup K V = ⊥ :=
    TameInertiaRamification.ramificationGroup_eq_bot_of_residue_charZero K V
  ext sigma
  change
    valueTrivialInertiaCharacterHom K V
        (inertiaToValueTrivialOfDVR K V sigma) = 1 ↔ sigma = 1
  rw [← MonoidHom.mem_ker,
    valueTrivialInertiaCharacterHom_mem_ker_iff, hram]
  rfl

/-- Every value of a finite DVR inertia character has finite multiplicative
order in the residue field. -/
theorem dvrInertiaCharacter_value_isOfFinOrder
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (V : _root_.ValuationSubring L) [IsDiscreteValuationRing V]
    [Finite (inertiaGroup K V)]
    (sigma : inertiaGroup K V)
    (q : (Lˣ ⧸ V.unitGroup) ⧸ baseUnitValueClassSubgroup K V) :
    IsOfFinOrder (dvrInertiaCharacter K V sigma q) := by
  let ev :
      ((((Lˣ ⧸ V.unitGroup) ⧸ baseUnitValueClassSubgroup K V) →*
          (IsLocalRing.ResidueField V)ˣ) →*
        (IsLocalRing.ResidueField V)ˣ) :=
    (MonoidHom.eval :
      ((Lˣ ⧸ V.unitGroup) ⧸ baseUnitValueClassSubgroup K V) →*
        ((((Lˣ ⧸ V.unitGroup) ⧸ baseUnitValueClassSubgroup K V) →*
          (IsLocalRing.ResidueField V)ˣ) →*
            (IsLocalRing.ResidueField V)ˣ)) q
  exact ev.isOfFinOrder
    ((dvrInertiaCharacter K V).isOfFinOrder
      (isOfFinOrder_of_finite sigma))

/-- If a decomposition element acts by inversion on all values of the DVR
inertia character, it conjugates every inertia element to its inverse. -/
theorem inertiaConjugate_eq_inv_of_character_inversion
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (V : _root_.ValuationSubring L) [IsDiscreteValuationRing V]
    [CharZero (IsLocalRing.ResidueField V)]
    [Finite (inertiaGroup K V)]
    (g : decompositionGroup K V)
    (hinv : ∀ sigma : inertiaGroup K V,
      dvrInertiaCharacter K V (inertiaConjugate K V g sigma) =
        (dvrInertiaCharacter K V sigma)⁻¹)
    (sigma : inertiaGroup K V) :
    inertiaConjugate K V g sigma = sigma⁻¹ := by
  apply dvrInertiaCharacter_injective_of_residue_charZero K V
  rw [hinv]
  rw [map_inv]

/-- A decomposition element that inverts every residue-unit value of the DVR
inertia character conjugates inertia elementwise to inversion. -/
theorem inertiaConjugate_eq_inv_of_residue_inversion
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (V : _root_.ValuationSubring L) [IsDiscreteValuationRing V]
    [CharZero (IsLocalRing.ResidueField V)]
    [Finite (inertiaGroup K V)]
    (g : decompositionGroup K V)
    (hinv : ∀ (sigma : inertiaGroup K V) (x : Lˣ),
      Units.mapEquiv (residueAction K V g).toMulEquiv
          (dvrInertiaCharacter K V sigma
            (QuotientGroup.mk' (baseUnitValueClassSubgroup K V)
              (QuotientGroup.mk' V.unitGroup x))) =
        (dvrInertiaCharacter K V sigma
          (QuotientGroup.mk' (baseUnitValueClassSubgroup K V)
            (QuotientGroup.mk' V.unitGroup x)))⁻¹)
    (sigma : inertiaGroup K V) :
    inertiaConjugate K V g sigma = sigma⁻¹ := by
  apply inertiaConjugate_eq_inv_of_character_inversion K V g
  intro tau
  apply QuotientGroup.monoidHom_ext
  apply QuotientGroup.monoidHom_ext
  apply MonoidHom.ext
  intro x
  change
    dvrInertiaCharacter K V (inertiaConjugate K V g tau)
        (QuotientGroup.mk' (baseUnitValueClassSubgroup K V)
          (QuotientGroup.mk' V.unitGroup x)) =
      (dvrInertiaCharacter K V tau
        (QuotientGroup.mk' (baseUnitValueClassSubgroup K V)
          (QuotientGroup.mk' V.unitGroup x)))⁻¹
  rw [dvrInertiaCharacter_conjugate_apply, hinv]

/-- It is enough that the residue action invert finite-order units: all
finite-level tame-inertia character values are such units. -/
theorem inertiaConjugate_eq_inv_of_torsion_residue_inversion
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (V : _root_.ValuationSubring L) [IsDiscreteValuationRing V]
    [CharZero (IsLocalRing.ResidueField V)]
    [Finite (inertiaGroup K V)]
    (g : decompositionGroup K V)
    (hinv : ∀ z : (IsLocalRing.ResidueField V)ˣ,
      IsOfFinOrder z →
        Units.mapEquiv (residueAction K V g).toMulEquiv z = z⁻¹)
    (sigma : inertiaGroup K V) :
    inertiaConjugate K V g sigma = sigma⁻¹ := by
  apply inertiaConjugate_eq_inv_of_residue_inversion K V g
  intro tau x
  apply hinv
  exact dvrInertiaCharacter_value_isOfFinOrder K V tau _

end TameAbhyankar.SGA1
