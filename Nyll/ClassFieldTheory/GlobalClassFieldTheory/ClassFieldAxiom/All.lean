/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.CyclicIdeleClassNormIndex
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.HasseNormPrinciple
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.MathlibNormInterface
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassFormation
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.All
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdelePowerLocalUnitNormContainment
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdelePowerLocalUnitSubgroup
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.KummerLocalNormContainment
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.SUnitKummerPrimeSelection.All
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.SUnitLocalPowerMap
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.SupportedIdelePowerLocalUnitQuotient

/-!
# The global class-field axiom and its arithmetic consequences

This aggregate exports the cyclic idele-class norm-index calculation, the
Hasse norm principle, and the rational idele-class formation.
-/
