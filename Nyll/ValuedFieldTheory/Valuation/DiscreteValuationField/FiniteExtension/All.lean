/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.ProlongationDiscrete
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Core
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.DVRLocalExtension
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Defectless
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Degree
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Henselian
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Localization
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.LocalizationLocalMap
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.LocalizationRing
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.PrimePowerRoots
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Uniqueness

/-!
# Finite extensions of discrete valuation fields

This aggregate exposes degree and defectlessness, henselianity, localizations, discrete
prolongations, prime-power roots, and uniqueness of extensions.
-/
