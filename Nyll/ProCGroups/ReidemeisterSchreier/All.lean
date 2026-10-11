/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.ReidemeisterSchreier.Discrete.All
import Nyll.ProCGroups.ReidemeisterSchreier.FreeGroup.All
import Nyll.ProCGroups.ReidemeisterSchreier.Groupoid
import Nyll.ProCGroups.ReidemeisterSchreier.Profinite.All
import Nyll.ProCGroups.ReidemeisterSchreier.Quiver
import Nyll.ProCGroups.ReidemeisterSchreier.RightQuotient
import Nyll.ProCGroups.ReidemeisterSchreier.Schreier

/-!
# Reidemeister--Schreier theory

Discrete and profinite forms of the Reidemeister--Schreier theorem, together with free-group word
rewriting, presentation equivalence certificates, verified Tietze scripts, Schreier cocycles, and
open-subgroup rank formulas.

This is the public aggregate.  For a smaller dependency surface, import
`ProCGroups.ReidemeisterSchreier.Discrete`,
`ProCGroups.ReidemeisterSchreier.Profinite`, or a focused submodule.
-/
