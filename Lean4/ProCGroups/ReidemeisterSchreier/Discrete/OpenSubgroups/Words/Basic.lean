/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ProCGroups.ReidemeisterSchreier.FreeGroup.PrefixParent

set_option autoImplicit false

universe u

/-!
# Reidemeister Schreier / Discrete / Open Subgroups / Words / Basic

This module defines the initial reduced-word segments of a free-group element
and proves the membership and prefix-parent facts used by discrete Schreier
transversals.
-/

namespace ReidemeisterSchreier.Discrete.OpenSubgroups


/--
This list consists of the initial segments (prefixes) of the reduced word representing a
free-group element, as used in Reidemeister--Schreier rewriting.
-/
def freeGroupInitialSegments {X : Type u} [DecidableEq X] (t : FreeGroup X) :
    Set (FreeGroup X) := by
  exact
    {u | ∃ n ≤ (FreeGroup.toWord t).length, u = FreeGroup.mk (List.take n (FreeGroup.toWord t))}


end ReidemeisterSchreier.Discrete.OpenSubgroups
