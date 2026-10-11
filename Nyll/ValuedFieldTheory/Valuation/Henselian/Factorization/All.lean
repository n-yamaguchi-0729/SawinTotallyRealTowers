/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.Henselian.Factorization.AdicLimits
import Nyll.ValuedFieldTheory.Valuation.Henselian.Factorization.Assembly
import Nyll.ValuedFieldTheory.Valuation.Henselian.Factorization.Basic
import Nyll.ValuedFieldTheory.Valuation.Henselian.Factorization.CoefficientMinimum
import Nyll.ValuedFieldTheory.Valuation.Henselian.Factorization.Complete
import Nyll.ValuedFieldTheory.Valuation.Henselian.Factorization.DegreeBounds
import Nyll.ValuedFieldTheory.Valuation.Henselian.Factorization.DivisionBounds
import Nyll.ValuedFieldTheory.Valuation.Henselian.Factorization.ErrorPowers
import Nyll.ValuedFieldTheory.Valuation.Henselian.Factorization.FiniteApproximation
import Nyll.ValuedFieldTheory.Valuation.Henselian.Factorization.InfiniteApproximation
import Nyll.ValuedFieldTheory.Valuation.Henselian.Factorization.Iteration
import Nyll.ValuedFieldTheory.Valuation.Henselian.Factorization.PrincipalLimits
import Nyll.ValuedFieldTheory.Valuation.Henselian.Factorization.Step
import Nyll.ValuedFieldTheory.Valuation.Henselian.Factorization.Truncation
import Nyll.ValuedFieldTheory.Valuation.Henselian.Factorization.WeakLimits

/-!
# Henselian polynomial factorization

The approximation, correction, and completeness results used to lift coprime
factorizations over valuation rings.
-/
