/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.LubinTate.Padic.ChangedUniformizerCoefficient
import Nyll.ClassFieldTheory.LubinTate.Padic.ChangedUniformizerIntertwiner.All
import Nyll.ClassFieldTheory.LubinTate.Padic.CompletedChangedStandardCompositum
import Nyll.ClassFieldTheory.LubinTate.Padic.CompletedChangedStandardFixedField
import Nyll.ClassFieldTheory.LubinTate.Padic.CompletedChangedStandardFrobenius
import Nyll.ClassFieldTheory.LubinTate.Padic.CompletedChangedStandardResidue
import Nyll.ClassFieldTheory.LubinTate.Padic.CompletedChangedStandardUnramified
import Nyll.ClassFieldTheory.LubinTate.Padic.CompletedChangedUniformizerFixedField
import Nyll.ClassFieldTheory.LubinTate.Padic.CompletedChangedUniformizerPrimitive
import Nyll.ClassFieldTheory.LubinTate.Padic.CompletedChangedUniformizerThetaFixed
import Nyll.ClassFieldTheory.LubinTate.Padic.CompletedFrobeniusEvaluation
import Nyll.ClassFieldTheory.LubinTate.Padic.CompletedFrobeniusLift
import Nyll.ClassFieldTheory.LubinTate.Padic.CompletedLevel
import Nyll.ClassFieldTheory.LubinTate.Padic.CompletedPrimitiveAction
import Nyll.ClassFieldTheory.LubinTate.Padic.CompletedPrimitiveIrreducible
import Nyll.ClassFieldTheory.LubinTate.Padic.CompletedPrimitiveUniformizer
import Nyll.ClassFieldTheory.LubinTate.Padic.CompletedResidueFrobenius
import Nyll.ClassFieldTheory.LubinTate.Padic.CompletedStandardLevelTransport
import Nyll.ClassFieldTheory.LubinTate.Padic.CompletedUnramifiedField
import Nyll.ClassFieldTheory.LubinTate.Padic.CompletedUnramifiedFrobeniusFixed
import Nyll.ClassFieldTheory.LubinTate.Padic.MultiplicativeEvaluation.All
import Nyll.ClassFieldTheory.LubinTate.Padic.MultiplicativeIntertwiner
import Nyll.ClassFieldTheory.LubinTate.Padic.MultiplicativeSeries

/-!
# P-adic Lubin--Tate theory

Aggregate for the multiplicative Lubin--Tate series and its completed-level,
Frobenius, residue, fixed-field, and changed-uniformizer constructions.
-/
