/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.LocalField.Padic.ClosedAddSubgroup
import Nyll.ValuedFieldTheory.LocalField.Padic.CompactDenominator
import Nyll.ValuedFieldTheory.LocalField.Padic.Cyclotomic.All
import Nyll.ValuedFieldTheory.LocalField.Padic.CyclotomicTeichmullerCharacter
import Nyll.ValuedFieldTheory.LocalField.Padic.CyclotomicTeichmullerRestriction
import Nyll.ValuedFieldTheory.LocalField.Padic.NonarchimedeanLocalField
import Nyll.ValuedFieldTheory.LocalField.Padic.PrincipalUnits
import Nyll.ValuedFieldTheory.LocalField.Padic.PrimePowerTorsionReduction
import Nyll.ValuedFieldTheory.LocalField.Padic.ReductionCompatibility
import Nyll.ValuedFieldTheory.LocalField.Padic.ResidueInverseLimit
import Nyll.ValuedFieldTheory.LocalField.Padic.Teichmuller
import Nyll.ValuedFieldTheory.LocalField.Padic.TeichmullerReduction
import Nyll.ValuedFieldTheory.LocalField.Padic.UnitDecomposition
import Nyll.ValuedFieldTheory.LocalField.Padic.PrimitiveRootTeichmullerCharacter

/-!
# Padic local fields and their units

This aggregate exposes padic local-field structures, cyclotomic extensions, Teichmuller
characters and reduction, and principal-unit comparisons.
-/
