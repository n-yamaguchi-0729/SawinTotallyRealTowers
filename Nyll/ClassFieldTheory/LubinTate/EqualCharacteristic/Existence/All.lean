/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.Existence.LaurentLocalField
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.Existence.LaurentModel
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.Existence.LaurentUniformizerNormalization

/-!
# Equal-characteristic Laurent model for Lubin--Tate theory

Public aggregate for the reusable Laurent-series model and its normalized
uniformizer.  Transport of the exact norm-subgroup calculation to an arbitrary
equal-characteristic local field uses finite local reciprocity and is exported
by `LocalClassFieldTheory.LubinTateApplication`.
-/
