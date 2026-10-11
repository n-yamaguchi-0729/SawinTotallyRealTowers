/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.LocalField.Unramified.BaseChange
import Nyll.ValuedFieldTheory.LocalField.Unramified.BaseChangeCore
import Nyll.ValuedFieldTheory.LocalField.Unramified.BasicInvariants
import Nyll.ValuedFieldTheory.LocalField.Unramified.Composition
import Nyll.ValuedFieldTheory.LocalField.Unramified.Definitions
import Nyll.ValuedFieldTheory.LocalField.Unramified.FiniteSupport
import Nyll.ValuedFieldTheory.LocalField.Unramified.HenselReduction
import Nyll.ValuedFieldTheory.LocalField.Unramified.HenselianAlgebraicExtension
import Nyll.ValuedFieldTheory.LocalField.Unramified.MaximalResidue
import Nyll.ValuedFieldTheory.LocalField.Unramified.MaximalSubextension
import Nyll.ValuedFieldTheory.LocalField.Unramified.RamificationIndexTower
import Nyll.ValuedFieldTheory.LocalField.Unramified.ResidueEmbedding
import Nyll.ValuedFieldTheory.LocalField.Unramified.ResidueLifting
import Nyll.ValuedFieldTheory.LocalField.Unramified.Separable

/-!
# Unramified extensions of valued fields

Finite and algebraic unramified extensions, their residue extensions, maximal
unramified subextensions, and base change.
-/
