/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.FunctionFields.Functoriality
import Nyll.SchemeTheory.FunctionFields.GeometricIntegrality
import Nyll.SchemeTheory.FunctionFields.IntegerBase
import Nyll.SchemeTheory.FunctionFields.ArithmeticGeometricIntegrality
import Nyll.SchemeTheory.FunctionFields.PlainIntegerBase
import Nyll.SchemeTheory.FunctionFields.PrimeDivisors.All
import Nyll.SchemeTheory.FunctionFields.SeparableClosure.All
import Nyll.SchemeTheory.FunctionFields.StalkFactorization
import Nyll.SchemeTheory.FunctionFields.Valuations.All
import Nyll.SchemeTheory.FunctionFields.StalkFunctoriality

/-!
# Function fields and prime divisors

This facade collects functoriality for dominant morphisms, function-field
transcendence, valuation-theoretic prime divisors and their counting theorems,
together with ring covers of domains.
-/

/- Canonical aggregate for SchemeTheory.FunctionFields. -/
