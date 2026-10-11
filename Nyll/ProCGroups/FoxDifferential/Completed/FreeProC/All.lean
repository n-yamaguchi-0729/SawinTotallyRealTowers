/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.FreeProC.BifilteredCoefficientStageProjection
import Nyll.ProCGroups.FoxDifferential.Completed.FreeProC.BifilteredStageProjection
import Nyll.ProCGroups.FoxDifferential.Completed.FreeProC.BifilteredSystemStageProjection
import Nyll.ProCGroups.FoxDifferential.Completed.FreeProC.CofinalQuotientKernelBasis
import Nyll.ProCGroups.FoxDifferential.Completed.FreeProC.CoordinateStageProjection
import Nyll.ProCGroups.FoxDifferential.Completed.FreeProC.Coordinates
import Nyll.ProCGroups.FoxDifferential.Completed.FreeProC.Density
import Nyll.ProCGroups.FoxDifferential.Completed.FreeProC.FiniteQuotientStages
import Nyll.ProCGroups.FoxDifferential.Completed.FreeProC.FundamentalFormula
import Nyll.ProCGroups.FoxDifferential.Completed.FreeProC.NaturalTopology
import Nyll.ProCGroups.FoxDifferential.Completed.FreeProC.PrimePowerStageProjection
import Nyll.ProCGroups.FoxDifferential.Completed.FreeProC.ProCIntegerBifilteredStageProjection
import Nyll.ProCGroups.FoxDifferential.Completed.FreeProC.ProCIntegerBifilteredStageRightProjection
import Nyll.ProCGroups.FoxDifferential.Completed.FreeProC.ProCIntegerStageCoeffProjection
import Nyll.ProCGroups.FoxDifferential.Completed.FreeProC.QuotientKernelBasis
import Nyll.ProCGroups.FoxDifferential.Completed.FreeProC.RelationReflection
import Nyll.ProCGroups.FoxDifferential.Completed.FreeProC.RelationSubmoduleApproximation
import Nyll.ProCGroups.FoxDifferential.Completed.FreeProC.SemidirectKernelBasis
import Nyll.ProCGroups.FoxDifferential.Completed.FreeProC.SemidirectLift
import Nyll.ProCGroups.FoxDifferential.Completed.FreeProC.StageApproximation
import Nyll.ProCGroups.FoxDifferential.Completed.FreeProC.StageProjection
import Nyll.ProCGroups.FoxDifferential.Completed.FreeProC.Uniqueness.All

/-!
# Fox differential: completed — free pro-\(C\)

This aggregate re-exports the following parts of the Fox differential API:

- `Completed.FreeProC.BifilteredCoefficientStageProjection`
- `Completed.FreeProC.BifilteredStageProjection`
- `Completed.FreeProC.BifilteredSystemStageProjection`
- `Completed.FreeProC.CofinalQuotientKernelBasis`
- `Completed.FreeProC.CoordinateStageProjection`
- `Completed.FreeProC.Density`
- `Completed.FreeProC.FiniteQuotientStages`
- `Completed.FreeProC.PrimePowerStageProjection`
- `Completed.FreeProC.ProCIntegerBifilteredStageProjection`
- `Completed.FreeProC.ProCIntegerBifilteredStageRightProjection`
- `Completed.FreeProC.ProCIntegerStageCoeffProjection`
- `Completed.FreeProC.QuotientKernelBasis`
- `Completed.FreeProC.RelationSubmoduleApproximation`
- `Completed.FreeProC.SemidirectKernelBasis`
- `Completed.FreeProC.SemidirectLift`
- `Completed.FreeProC.StageApproximation`
- `Completed.FreeProC.StageProjection`
- `Completed.FreeProC.Uniqueness`
- `Completed.FreeProC.RelationReflection`
- `Completed.FreeProC.NaturalTopology`
- `Completed.FreeProC.Coordinates`
- `Completed.FreeProC.FundamentalFormula`
-/
