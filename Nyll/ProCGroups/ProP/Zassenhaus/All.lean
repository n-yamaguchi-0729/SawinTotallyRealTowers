/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.ProP.Zassenhaus.OpenNormal
import Nyll.ProCGroups.ProP.Zassenhaus.AugmentationFiltration
import Nyll.ProCGroups.ProP.Zassenhaus.Basic
import Nyll.ProCGroups.ProP.Zassenhaus.DegreeTwo
import Nyll.ProCGroups.ProP.Zassenhaus.Depth
import Nyll.ProCGroups.ProP.Zassenhaus.FiniteAugmentationSquare
import Nyll.ProCGroups.ProP.Zassenhaus.FiniteDegreeOne
import Nyll.ProCGroups.ProP.Zassenhaus.FiniteLinearization
import Nyll.ProCGroups.ProP.Zassenhaus.Functoriality
import Nyll.ProCGroups.ProP.Zassenhaus.GroupLike
import Nyll.ProCGroups.ProP.Zassenhaus.Laws

/-!
# Zassenhaus filtration

Reader-facing facade for the mod-`p` augmentation and Zassenhaus filtration.
-/


/-!
# Zassenhaus aggregate

Imports every maintained augmentation-filtration and Zassenhaus leaf.
-/
