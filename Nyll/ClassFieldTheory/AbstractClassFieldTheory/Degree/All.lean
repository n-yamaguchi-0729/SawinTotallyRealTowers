/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields
import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius
import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField
import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusLift
import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.Indices
import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm
import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormConjugation
import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws
import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.PadicCyclicClosure
import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements
import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.ProfiniteIntegerFiniteQuotient
import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.Valuation
import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.ValuationLaws

/-!
# Degree and valuation data

Focused aggregate for abstract fields, normalized degrees, Frobenius, norms, prime elements, and
valuation laws used by class formations.
-/
