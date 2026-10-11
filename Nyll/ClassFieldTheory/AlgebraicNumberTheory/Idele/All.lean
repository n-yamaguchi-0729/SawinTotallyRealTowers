/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.BaseChange
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Basic
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.All
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.All
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.All
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.FiniteMathlibTopologyComparison
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.FinitePrime
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.IdealMap
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.IdentityComponent
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.LocallyCompact
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Norm
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormApproximation.All
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormCore
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormOneCompact
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormTopology.All
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.PositiveArchimedeanSection
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Principal
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalCore
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalNorm
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalTopology
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Relative.All
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.RestrictedProductUnitsTopology
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.SPlaces
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.SinglePlace
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.SufficientlyLarge
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Topology

/-!
# Ideles and idele classes

Public aggregate for the idele group and the idele class group of a number
field.
-/
