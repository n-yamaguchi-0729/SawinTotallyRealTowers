/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Common.CrossedDifferential
import Nyll.ProCGroups.FoxDifferential.Common.CrossedDifferentialModule
import Nyll.ProCGroups.FoxDifferential.Common.FiniteFamilyLinearMap
import Nyll.ProCGroups.FoxDifferential.Common.FoxBoundary
import Nyll.ProCGroups.FoxDifferential.Common.FreeCrossedDifferential
import Nyll.ProCGroups.FoxDifferential.Common.Jacobian

/-!
# Common Fox-differential interface

This aggregate collects the algebraic interface shared by the discrete and completed theories:
bundled crossed homomorphisms, their universal differential modules, Fox boundary identities,
free-source differentials, finite-family linear maps, and Jacobian constructions.  It does not
choose a completion topology or a finite-stage coefficient system.
-/
