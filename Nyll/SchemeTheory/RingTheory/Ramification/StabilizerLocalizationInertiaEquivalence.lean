/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Ramification.StabilizerLocalizationAction
import Mathlib.Algebra.Group.Subgroup.Map

/-!
# Equivalence of local and ideal inertia

Constructs a multiplicative equivalence between inertia for the stabilizer action on a prime
localization and the original ideal inertia group.
-/

open scoped Pointwise

namespace SchemeTheory

universe u v

/-- The actual local inertia and original ideal inertia are the same
stabilizer elements, with only their canonical subgroup presentations changed. -/
def stabilizerLocalizationInertiaMulEquiv
    (B : Type u) [CommRing B] (G : Type v) [Group G] [MulSemiringAction G B]
    (Q : Ideal B) [Q.IsPrime] :
    (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).inertia (MulAction.stabilizer G Q) ≃*
      Q.inertia G where
  toFun σ := ⟨σ.val.val,
    (stabilizerLocalization_mem_inertia_iff B G Q σ.val).mp σ.property⟩
  invFun σ :=
    let d : MulAction.stabilizer G Q := ⟨σ.val, Q.inertia_le_stabilizer σ.property⟩
    ⟨d, (stabilizerLocalization_mem_inertia_iff B G Q d).mpr σ.property⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

end SchemeTheory
