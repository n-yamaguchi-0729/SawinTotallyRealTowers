/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.CompletedGroupAlgebra.OpenFiniteQuotientTopology.OpenFiniteLimit.CanonicalMap
import Nyll.ProCGroups.CompletedGroupAlgebra.OpenFiniteQuotientTopology.OpenFiniteLimit.System
import Nyll.ProCGroups.CompletedGroupAlgebra.OpenFiniteQuotientTopology.OpenFiniteLimit.Topology

/-!
# Completed Group Algebra / Open Finite Quotient Topology / Open Finite Limit

This aggregate exports the two-parameter inverse limit
\(\varprojlim_{I,U}(R/I)[G/U]\), its opaque named carrier, canonical bundled quotient
projections, inherited topological-ring structure, and the dense canonical map from \(R[G]\).

The carrier's compatible-family realization is available only through
`completedGroupAlgebraOpenFiniteQuotientCompatibleFamilyEquiv`; ordinary consumers should use
`completedGroupAlgebraOpenFiniteQuotientLimitProjection` and
`completedGroupAlgebraOpenFiniteQuotientLimit_ext`.
-/
