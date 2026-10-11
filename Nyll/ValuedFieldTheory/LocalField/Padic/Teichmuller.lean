/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PadicField
import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.ResidueRoots
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Teichmüller representatives in the p-adic units

Hensel lifting in the concrete complete discrete valuation field `ℚ_[p]`
gives a multiplicative section of reduction to `(ZMod p)ˣ`. Its values are
`(p - 1)`-st roots of unity, including when `p = 2`.
-/

noncomputable section

namespace LocalFieldTheory.DiscreteValuationField.Examples.Qp

open CompleteDVF.higherPrincipalUnitGroup

variable (p : ℕ) [Fact p.Prime]

-- The only additional instance is the existing finiteness proof for Qp's residue field.
attribute [local instance] padicCompleteDVF_residueField_finite

private def teichmullerIntegerEquiv : ℤ_[p] ≃+* (padicCompleteDVF p).valuationSubring :=
  padicIntEquivValuationSubring p

private def teichmullerResidueEquiv : (padicCompleteDVF p).residueField ≃+* ZMod p :=
  (IsLocalRing.ResidueField.mapEquiv (teichmullerIntegerEquiv p)).symm.trans
    PadicInt.residueField

private theorem toZMod_valuationSubring_symm
    (x : (padicCompleteDVF p).valuationSubring) :
    PadicInt.toZMod ((teichmullerIntegerEquiv p).symm x) =
      teichmullerResidueEquiv p ((padicCompleteDVF p).residueMap x) := by
  rw [PadicInt.toZMod_eq_residueField_comp_residue]
  change PadicInt.residueField
      (IsLocalRing.residue ℤ_[p] ((teichmullerIntegerEquiv p).symm x)) =
    PadicInt.residueField
      (IsLocalRing.ResidueField.map
        ((teichmullerIntegerEquiv p).symm : (padicCompleteDVF p).valuationSubring →+* ℤ_[p])
        (IsLocalRing.residue (padicCompleteDVF p).valuationSubring x))
  exact congrArg PadicInt.residueField
    (IsLocalRing.ResidueField.map_residue
      ((teichmullerIntegerEquiv p).symm : (padicCompleteDVF p).valuationSubring →+* ℤ_[p])
      x).symm

private def teichmullerRoots :
    (ZMod p)ˣ →* residueRootsOfUnityGroup (padicCompleteDVF p) :=
  (residueRootsOfUnityEquivResidueFieldUnits (padicCompleteDVF p)).symm.toMonoidHom.comp
    (Units.map (teichmullerResidueEquiv p).symm.toMonoidHom)

/-- The multiplicative Teichmüller section from residue units to p-adic units. -/
def teichmullerUnits : (ZMod p)ˣ →* ℤ_[p]ˣ :=
  (Units.map (teichmullerIntegerEquiv p).symm.toMonoidHom).comp
    ((residueRootsOfUnityGroup (padicCompleteDVF p)).subtype.comp (teichmullerRoots p))

/-- Reducing a Teichmüller representative recovers the original residue unit. -/
@[simp] theorem toZMod_teichmullerUnits (u : (ZMod p)ˣ) :
    Units.map PadicInt.toZMod.toMonoidHom (teichmullerUnits p u) = u := by
  let r : residueRootsOfUnityGroup (padicCompleteDVF p) := teichmullerRoots p u
  have hr : residueUnitHom (padicCompleteDVF p)
      (r : (padicCompleteDVF p).valuationSubringˣ) =
      Units.map (teichmullerResidueEquiv p).symm.toMonoidHom u :=
    (residueRootsOfUnityEquivResidueFieldUnits (padicCompleteDVF p)).apply_symm_apply
      (Units.map (teichmullerResidueEquiv p).symm.toMonoidHom u)
  apply Units.ext
  change PadicInt.toZMod ((teichmullerIntegerEquiv p).symm
    ((r : (padicCompleteDVF p).valuationSubringˣ) :
      (padicCompleteDVF p).valuationSubring)) = (u : ZMod p)
  rw [toZMod_valuationSubring_symm]
  have h := congrArg
    (fun z : (padicCompleteDVF p).residueFieldˣ => teichmullerResidueEquiv p z.val) hr
  change teichmullerResidueEquiv p ((padicCompleteDVF p).residueMap
    ((r : (padicCompleteDVF p).valuationSubringˣ) :
      (padicCompleteDVF p).valuationSubring)) =
    teichmullerResidueEquiv p ((teichmullerResidueEquiv p).symm (u : ZMod p)) at h
  rw [RingEquiv.apply_symm_apply] at h
  exact h

/-- Every Teichmüller representative is a `(p - 1)`-st root of unity. -/
theorem teichmullerUnits_pow (u : (ZMod p)ˣ) :
    teichmullerUnits p u ^ (p - 1) = 1 := by
  let r : residueRootsOfUnityGroup (padicCompleteDVF p) := teichmullerRoots p u
  have hr : (r : (padicCompleteDVF p).valuationSubringˣ) ^
      (Nat.card (padicCompleteDVF p).residueField - 1) = 1 :=
    (mem_rootsOfUnity (Nat.card (padicCompleteDVF p).residueField - 1)
      (r : (padicCompleteDVF p).valuationSubringˣ)).mp r.property
  rw [padicCompleteDVF_residueField_card p] at hr
  change Units.map (teichmullerIntegerEquiv p).symm.toMonoidHom
    (r : (padicCompleteDVF p).valuationSubringˣ) ^ (p - 1) = 1
  rw [← map_pow, hr, map_one]

end LocalFieldTheory.DiscreteValuationField.Examples.Qp
