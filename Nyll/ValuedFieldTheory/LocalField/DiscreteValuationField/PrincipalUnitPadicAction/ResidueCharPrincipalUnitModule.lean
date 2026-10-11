/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnitPadicAction.ResidueCharProdiscreteModule
import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnitPadicAction.AdicProdiscreteComparison

/-!
# P-adic scalars on the actual principal-unit group

The adic inverse-limit equivalence transports the compatible coordinate
actions to `U^1`. No finite-residue-field assumption is used.
-/

namespace LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup

universe u v

variable {K : Type u} [Field K]

/-- The principal-unit group as a p-adic module over its residue prime. -/
@[instance_reducible] noncomputable def principalUnitPadicModuleOfResidueChar
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)
    (p : ℕ) [Fact p.Prime] [hres : CharP F.residueField p] :
    Module ℤ_[p] (Additive (higherPrincipalUnitGroup F 1)) := by
  let : Module ℤ_[p] (PrincipalUnitProdiscreteLimit F) :=
    PrincipalUnitProdiscreteLimit.padicModuleOfResidueChar F p
  exact AddEquiv.module ℤ_[p]
    ((AdicPrincipalUnits.addEquiv F).symm.trans
      (adicPrincipalUnitsAddEquivProdiscreteLimit F))

end LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
