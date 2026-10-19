/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Group.Equiv.TypeTags
/-!
# Additive recoding of multiplicative equivalences

Turns a multiplicative group equivalence into the corresponding equivalence
between the additive recodings of its source and target.
-/

namespace LocalFieldTheory

noncomputable section

universe u

/-- Transport a multiplicative equivalence to an additive equivalence. -/
def additiveEquivOfMulEquiv {A B : Type u} [Group A] [Group B] (e : A ≃* B) :
    Additive A ≃+ Additive B :=
  MulEquiv.toAdditive e

end
end LocalFieldTheory
