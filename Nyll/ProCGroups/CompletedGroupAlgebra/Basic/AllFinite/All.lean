/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.CompletedGroupAlgebra.Basic.AllFinite.Carrier
import Nyll.ProCGroups.CompletedGroupAlgebra.Basic.AllFinite.Index
import Nyll.ProCGroups.CompletedGroupAlgebra.Basic.AllFinite.Projections
import Nyll.ProCGroups.CompletedGroupAlgebra.Basic.AllFinite.Ring
import Nyll.ProCGroups.CompletedGroupAlgebra.Basic.AllFinite.Stage
import Nyll.ProCGroups.CompletedGroupAlgebra.Basic.AllFinite.Topology

/-!
# Completed Group Algebra / Basic / All Finite

This is the public aggregate for the all-finite completion \(\widehat{R[G]}\). It exports:

* finite-quotient indices, stages, and transition maps;
* the opaque named carrier and its explicit compatible-family equivalence;
* the generic inverse-limit ring, module, and coefficient-algebra structures;
* canonical bundled finite-stage projections and their linear, algebra, and continuous forms; and
* the inverse-limit topological-ring, compactness, Hausdorff, and disconnectedness results.

Downstream code should use `completedGroupAlgebraProjection`, `completedGroupAlgebra_ext`, and
`completedGroupAlgebraCompatibleFamilyEquiv`; the concrete compatible-family subtype is not a
second public carrier.
-/
