/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.HenselianRootsOfUnity
import Mathlib.GroupTheory.Torsion
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Data.Fintype.EquivFin

/-!
# Reduction of all torsion roots in residue characteristic zero

The map on all roots of unity is the restriction of the actual residue map
on valuation-ring units. It is independent of any chosen exponent. Hensel
uniqueness makes this map injective when the residue field has characteristic
zero, so finiteness of residue-field torsion implies finiteness of field torsion.
-/

noncomputable section

namespace ValuationTheory.DiscreteValuationField

universe u v

variable {K : Type u} [Field K]

namespace DVF

private theorem torsion_le_unitGroup (D : DVF.{u, v} K) :
    CommGroup.torsion Kˣ ≤ D.valuation.valuationSubring.unitGroup := by
  intro z hz
  obtain ⟨n, hn, hzn⟩ := hz.exists_pow_eq_one
  apply (_root_.Valuation.mem_unitGroup_iff (v := D.valuation) (x := z)).mpr
  have hpow : D.valuation (z : K) ^ n = 1 := by
    rw [← map_pow]
    have hzpow : (z : K) ^ n = 1 :=
      congrArg (fun x : Kˣ => (x : K)) hzn
    rw [hzpow, map_one]
  exact (pow_eq_one_iff_of_nonneg zero_le hn.ne').mp hpow

/-- A single reduction homomorphism on all torsion roots. Its underlying map
is the canonical residue map on the valuation-ring unit represented by a root. -/
def torsionReduction (D : DVF.{u, v} K) :
    CommGroup.torsion Kˣ →* CommGroup.torsion D.residueFieldˣ :=
  let f : CommGroup.torsion Kˣ →* D.residueFieldˣ :=
    D.valuation.valuationSubring.unitGroupToResidueFieldUnits.comp
      (Subgroup.inclusion (torsion_le_unitGroup D))
  f.codRestrict (CommGroup.torsion D.residueFieldˣ) (fun z =>
    f.isOfFinOrder
      ((CommGroup.torsion Kˣ).subtype_injective.isOfFinOrder_iff.mp z.property))

end DVF

namespace HenselianDVF

variable (F : HenselianDVF.{u, v} K)

/-- In residue characteristic zero the actual reduction map is injective on
all torsion roots simultaneously. -/
theorem torsionReduction_injective [CharZero F.residueField] :
    Function.Injective F.toDVF.torsionReduction := by
  apply F.toDVF.torsionReduction.ker_eq_bot_iff.mp
  apply bot_unique
  intro z hz
  change z = 1
  have hred : F.toDVF.torsionReduction z = 1 := hz
  obtain ⟨n, hn, hzn⟩ := z.property.exists_pow_eq_one
  have : NeZero (n : F.residueField) := ⟨Nat.cast_ne_zero.mpr hn.ne'⟩
  let i : CommGroup.torsion Kˣ →* F.valuation.valuationSubring.unitGroup :=
    Subgroup.inclusion (DVF.torsion_le_unitGroup F.toDVF)
  let g : CommGroup.torsion Kˣ →* F.valuationSubringˣ :=
    F.valuation.valuationSubring.unitGroupMulEquiv.toMonoidHom.comp i
  have hzpow : z ^ n = 1 := Subtype.ext hzn
  have hwpow : (g z) ^ n = 1 := by
    rw [← map_pow, hzpow, map_one]
  let ζ : rootsOfUnity n F.valuationSubring :=
    ⟨g z, (mem_rootsOfUnity n (g z)).mpr hwpow⟩
  have hζred : rootsOfUnityReduction F n ζ = rootsOfUnityReduction F n 1 := by
    rw [map_one]
    apply Subtype.ext
    exact congrArg (fun x : CommGroup.torsion F.residueFieldˣ =>
      (x : F.residueFieldˣ)) hred
  have hζ : ζ = 1 := rootsOfUnityReduction_injective F n hζred
  have hw : g z = 1 :=
    congrArg (fun x : rootsOfUnity n F.valuationSubring =>
      (x : F.valuationSubringˣ)) hζ
  apply Subtype.ext
  apply Units.ext
  exact congrArg (fun x : F.valuationSubringˣ =>
    ((x : F.valuationSubring) : K)) hw

/-- Finiteness of all residue-field roots of unity transfers to the base field
for a Henselian DVF of residue characteristic zero. -/
theorem finite_torsion_of_finite_residueTorsion [CharZero F.residueField]
    [Finite (CommGroup.torsion F.residueFieldˣ)] :
    Finite (CommGroup.torsion Kˣ) :=
  Finite.of_injective F.toDVF.torsionReduction (torsionReduction_injective F)

end HenselianDVF

end ValuationTheory.DiscreteValuationField
