/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.GaloisCohomology.FieldTheory.FinitelyGeneratedCharZero
import Nyll.GaloisCohomology.FieldTheory.FinitelyGeneratedPositiveChar

/-!
# Primary roots in finite extensions of finitely generated fields
-/

namespace FieldTheory

universe u v

/-- Over any finitely generated field, the primary roots of unity in every
finite extension form a finite group, in arbitrary characteristic. -/
theorem finite_primaryComponent_finiteExtension_of_fg
    (K : Type u) [Field K] (hfg : Field.FG K)
    (L : Type v) [Field L] [Algebra K L] [FiniteDimensional K L]
    (p : ℕ) [Fact p.Prime] : Finite (CommGroup.primaryComponent Lˣ p) := by
  by_cases hchar : ringChar K = 0
  · have : CharP K 0 := hchar ▸ (inferInstance : CharP K (ringChar K))
    have : CharZero K := CharP.charP_to_charZero K
    exact finite_primaryComponent_finiteExtension_of_fg_charZero K hfg L p
  · exact finite_primaryComponent_finiteExtension_of_fg_posChar K hfg hchar L p

end FieldTheory
