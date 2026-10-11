/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Localization
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FinitePrimePowerRoots
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Extensions
import Mathlib.Algebra.CharP.Algebra

/-!
# Finiteness of prime-power roots after finite extension

The localized integral closure supplies a discrete extension valuation.
Its residue characteristic is the base residue characteristic, so the
prime-power root bound applies to every finite extension of a mixed
characteristic discretely valued field.
-/

namespace ValuationTheory.DiscreteValuationField

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/-- Every finite field extension of a mixed-characteristic DVF has only
finitely many prime-power roots. No extension valuation is assumed. -/
theorem DVF.finite_primePowerRoots_of_finiteExtension [CharZero K] (base : DVF K)
    (p : ℕ) [Fact p.Prime] [CharP base.residueField p] :
    Set.Finite {ζ : L | ∃ n : ℕ, ζ ^ (p ^ n) = 1} := by
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  let target : DVF L := FiniteExtensionLocalization.dvf (L := L) base
  have : base.valuation.HasExtension target.valuation :=
    FiniteExtensionLocalization.dvf_hasExtension (L := L) base
  have : CharP target.residueField p :=
    (Algebra.charP_iff base.residueField target.residueField p).mp inferInstance
  exact target.finite_primePowerRoots p

end ValuationTheory.DiscreteValuationField
