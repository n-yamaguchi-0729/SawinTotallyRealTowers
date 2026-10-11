/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FreeProC.Abelianization
import Nyll.ProCGroups.FreeProC.Basic
import Nyll.ProCGroups.FreeProC.CanonicalData
import Nyll.ProCGroups.FreeProC.Characterization.All
import Nyll.ProCGroups.FreeProC.Criteria.All
import Nyll.ProCGroups.FreeProC.FiniteBasis
import Nyll.ProCGroups.FreeProC.FiniteRankSourceData
import Nyll.ProCGroups.FreeProC.FinitelyGenerated
import Nyll.ProCGroups.FreeProC.SolvableQuotients
import Nyll.ProCGroups.FreeProC.Universe
import Nyll.ProCGroups.FreeProC.Construction

/-!
# Free pro-`C` groups

This aggregate module exposes the construction and universal property of free pro-`C` groups,
finite-basis and finite-generation results, canonical source data, characterizations, and
applications to abelian and solvable quotients.
-/
