/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.All
import Nyll.ClassFieldTheory.LubinTate.FiniteLevel.All
import Nyll.ClassFieldTheory.LubinTate.FormalModule.All
import Nyll.ClassFieldTheory.LubinTate.Padic.All

/-!
# Lubin--Tate theory

This is the public aggregate for Lubin--Tate theory.  It exports the formal
module foundations, the characteristic-independent standard finite-level
division fields and their lower/upper ramification formulas, and the explicit
equal-characteristic construction.  The
norm-subgroup calculation and transport used by local class field theory are
exported from `LocalClassFieldTheory.LubinTateApplication`, and the
field-facing existence theorem from
`LocalClassFieldTheory.Finite.Existence.EqualCharacteristic`.
The equal-characteristic construction is organized by its mathematical stages
below `LubinTate.EqualCharacteristic`.
-/
