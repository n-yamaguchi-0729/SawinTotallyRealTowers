/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.ReidemeisterSchreier.Profinite.OpenSubgroups.BasisFiniteRank
import Nyll.ProCGroups.ReidemeisterSchreier.Profinite.OpenSubgroups.BasisTheorems
import Nyll.ProCGroups.ReidemeisterSchreier.Profinite.OpenSubgroups.DenseFreeModel
import Nyll.ProCGroups.ReidemeisterSchreier.Profinite.OpenSubgroups.ExactRightSchreierGeneration
import Nyll.ProCGroups.ReidemeisterSchreier.Profinite.OpenSubgroups.FinitePermutationTargets
import Nyll.ProCGroups.ReidemeisterSchreier.Profinite.OpenSubgroups.MinimalPower
import Nyll.ProCGroups.ReidemeisterSchreier.Profinite.OpenSubgroups.RankBound
import Nyll.ProCGroups.ReidemeisterSchreier.Profinite.OpenSubgroups.RightQuotient
import Nyll.ProCGroups.ReidemeisterSchreier.Profinite.OpenSubgroups.SchreierTransversals

/-!
# Profinite open-subgroup Reidemeister--Schreier theory

This aggregate exports the concrete right-quotient and Schreier-cocycle
constructions, exact right-Schreier generation, finite permutation targets,
rank bounds, and finite-rank basis theorems for open subgroups of
free pro-\(C\) groups.

Basis conclusions use `EpimorphicallyFreeProCGroupOnConvergingSetData` directly.  There is no
parallel RS-specific carrier/model wrapper layer.
-/
