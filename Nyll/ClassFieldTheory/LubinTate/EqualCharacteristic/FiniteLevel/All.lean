/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.AmbientDivisionTorsion
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.DivisionPolynomial
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.FiniteParameters
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.FreeRankOne
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelAbelian
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelAutomorphisms
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelField
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelFieldTower
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.NormUniformizer
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.PrimitiveAction
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.PrimitiveIrreducible
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.PrimitiveTorsion
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.UnitQuotientGalois

/-!
# Finite Lubin--Tate levels in equal characteristic

Public aggregate for division torsion, finite level fields, and their Galois
and norm structure.
-/
