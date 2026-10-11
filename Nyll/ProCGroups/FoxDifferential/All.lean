/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Common.All
import Nyll.ProCGroups.FoxDifferential.Completed.All
import Nyll.ProCGroups.FoxDifferential.Discrete.All
import Nyll.ProCGroups.FoxDifferential.RightDerivative.All

/-!
# Fox differential calculus

Fox differentials and Fox coordinates for free groups, group rings, finite algebraic stages, and
profinite completions.  The library includes bundled crossed homomorphisms, universal differential
modules, Fox boundaries, Jacobians, completed derivatives, and right-derivative formulas.

The canonical APIs are the bundled `CrossedHom` and `ScalarCrossedHom` constructions and the
`foxAlgebraicStage*` finite stages.  The universal construction's final topology and the locally
installed free-pro-\(C\) coordinate topology are distinct; neither is called a completion without
a comparison theorem.

This Pro-C Groups aggregate layer may depend on the base `ProCGroups` modules and the
`ProCGroups.ReidemeisterSchreier` and `ProCGroups.CompletedGroupAlgebra` layers. It also owns
the reusable Fox-coordinate, Magnus, and relation-reflection lemmas used by the Crowell
exact-sequence assembly. Application-level exact sequences are imported by
`ProCGroups.CrowellExactSequence`.
-/
