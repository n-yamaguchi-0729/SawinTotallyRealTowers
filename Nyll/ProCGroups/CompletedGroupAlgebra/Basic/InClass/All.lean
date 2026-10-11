/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.CompletedGroupAlgebra.Basic.InClass.Index
import Nyll.ProCGroups.CompletedGroupAlgebra.Basic.InClass.LimitAlgebra
import Nyll.ProCGroups.CompletedGroupAlgebra.Basic.InClass.Projection
import Nyll.ProCGroups.CompletedGroupAlgebra.Basic.InClass.Stage
import Nyll.ProCGroups.CompletedGroupAlgebra.Basic.InClass.System
import Nyll.ProCGroups.CompletedGroupAlgebra.Basic.InClass.Topology

/-!
# Completed Group Algebra / Basic / Within a Class

This is the public aggregate for the completion indexed by a finite-group class \(C\). It exports
the in-class quotient indices and stages, their inverse system, the opaque named carrier, its
coefficient algebra, canonical bundled projections, and the inherited inverse-limit topology.

The API deliberately mirrors the all-finite aggregate: use
`completedGroupAlgebraProjectionInClass`, `completedGroupAlgebraInClass_ext`, and
`completedGroupAlgebraInClassCompatibleFamilyEquiv` instead of constructing or projecting the
compatible-family subtype directly.
-/
