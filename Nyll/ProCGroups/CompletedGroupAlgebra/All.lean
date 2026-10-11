/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.CompletedGroupAlgebra.AllFiniteAugmentation.All
import Nyll.ProCGroups.CompletedGroupAlgebra.AllFiniteFunctoriality.All
import Nyll.ProCGroups.CompletedGroupAlgebra.Augmentation.All
import Nyll.ProCGroups.CompletedGroupAlgebra.Basic.All
import Nyll.ProCGroups.CompletedGroupAlgebra.FunctorialityComposition
import Nyll.ProCGroups.CompletedGroupAlgebra.InClassFunctoriality.All
import Nyll.ProCGroups.CompletedGroupAlgebra.OpenFiniteQuotientTopology.All
import Nyll.ProCGroups.CompletedGroupAlgebra.ProfiniteModules.All
import Nyll.ProCGroups.CompletedGroupAlgebra.Separation
import Nyll.ProCGroups.CompletedGroupAlgebra.UniversalProperty.All

/-!
# Completed group algebras

Completed group algebras are constructed as inverse limits of finite-quotient group algebras.
The library develops their additive, ring, and topological structures together with projections,
augmentation maps and ideals, finite-stage functoriality, separation, and universal properties for
profinite modules.

The completed carriers are opaque; their compatible-family inverse limits are implementation
models exposed through canonical projections, extensionality, and representation equivalences.
`CanonicalCompletedGroupAlgebraModel` is the specification-level API: its inverse-limit universal
property determines comparison, continuity, density, and uniqueness rather than storing parallel
certificates.

This file is the public aggregate for every maintained `CompletedGroupAlgebra` component.
-/
