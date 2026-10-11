/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.ProC.OpenNormalSubgroups.Basic
import Nyll.ProCGroups.ProC.OpenNormalSubgroups.BasisAtOne
import Nyll.ProCGroups.ProC.OpenNormalSubgroups.ClosedAndCosets
import Nyll.ProCGroups.ProC.OpenNormalSubgroups.ClosedCommutator
import Nyll.ProCGroups.ProC.OpenNormalSubgroups.CountableChains
import Nyll.ProCGroups.ProC.OpenNormalSubgroups.FilteredFamilies
import Nyll.ProCGroups.ProC.OpenNormalSubgroups.LimitPresentation
import Nyll.ProCGroups.ProC.OpenNormalSubgroups.ProCGroup
import Nyll.ProCGroups.ProC.OpenNormalSubgroups.Separation

/-!
# Open normal subgroups of pro-\(C\) groups

This aggregate collects the finite quotient, separation, basis, countable-chain, filtered-family,
closed-commutator, and inverse-limit APIs built from open normal subgroups.
-/
