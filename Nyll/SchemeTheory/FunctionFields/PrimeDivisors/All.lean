/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.FunctionFields.PrimeDivisors.Basic
import Nyll.SchemeTheory.FunctionFields.PrimeDivisors.Centered
import Nyll.SchemeTheory.FunctionFields.PrimeDivisors.CenteredTransport
import Nyll.SchemeTheory.FunctionFields.PrimeDivisors.Counting
import Nyll.SchemeTheory.FunctionFields.PrimeDivisors.Dedekind
import Nyll.SchemeTheory.FunctionFields.PrimeDivisors.DegreeOne
import Nyll.SchemeTheory.FunctionFields.PrimeDivisors.Infinity
import Nyll.SchemeTheory.FunctionFields.PrimeDivisors.InseparableCounting
import Nyll.SchemeTheory.FunctionFields.PrimeDivisors.IntegralClosure
import Nyll.SchemeTheory.FunctionFields.PrimeDivisors.PrimesOver
import Nyll.SchemeTheory.FunctionFields.PrimeDivisors.Transport

/-!
# Prime divisors of function fields

This aggregate exposes centered prime divisors, degree and counting comparisons,
integral-closure primes, divisors at infinity, and transport across function-field maps.
-/

/- Canonical aggregate for SchemeTheory.FunctionFields.PrimeDivisors. -/
