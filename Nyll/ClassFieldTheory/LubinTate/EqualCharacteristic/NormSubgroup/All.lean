/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFixedFieldEmbedding
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFixedFieldEquiv
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFixedFieldMembership
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFixedFieldSurjective
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFrobeniusFixed
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitLevelMapFixed
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnits
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitsNorm
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.LevelAlgebra
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.StandardSubgroupNorm
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.UniformizerNorm
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.UnitQuotientCard
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.UnitTransport

/-!
# Reusable Lubin--Tate norm calculations in equal characteristic

Public aggregate for higher-unit norms, containment of the standard subgroup
in the finite-level norm subgroup, and the corresponding finite quotient
calculation.  The exact norm-subgroup equality, which uses finite local
reciprocity, is exported by
`LocalClassFieldTheory.LubinTateApplication`.
-/
