/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.ComapResidueCharacteristic
import Mathlib.Algebra.CharP.Defs

/-!
# Residue characteristic under pullback of valuations

The residue-field characteristic of a valuation subring is preserved by pullback along a
field embedding. The proof compares natural-number casts with membership in the
nonunits.
-/

namespace ValuationSubring

universe u v

/-- The residue characteristic of the specified valuation subring is
preserved by pullback along any field embedding. -/
theorem charP_residueField_comap
    {K : Type u} {L : Type v} [Field K] [Field L]
    (A : ValuationSubring L) (f : K →+* L) (p : ℕ)
    [CharP (IsLocalRing.ResidueField A) p] :
    CharP (IsLocalRing.ResidueField (A.comap f)) p := by
  constructor
  intro n
  rw [← CharP.cast_eq_zero_iff (IsLocalRing.ResidueField A) p n]
  have hdown : (n : IsLocalRing.ResidueField (A.comap f)) = 0 ↔
      (n : K) ∈ (A.comap f).nonunits := by
    rw [← map_natCast (IsLocalRing.residue (A.comap f)) n,
      IsLocalRing.residue_eq_zero_iff]
    exact (A.comap f).coe_mem_nonunits_iff.symm
  have hup : (n : IsLocalRing.ResidueField A) = 0 ↔ (n : L) ∈ A.nonunits := by
    rw [← map_natCast (IsLocalRing.residue A) n, IsLocalRing.residue_eq_zero_iff]
    exact A.coe_mem_nonunits_iff.symm
  rw [hdown, hup]
  simpa only [map_natCast] using mem_nonunits_comap_iff A f (n : K)

end ValuationSubring
