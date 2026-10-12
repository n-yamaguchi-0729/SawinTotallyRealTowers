/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.RegularLocalDomain
import Mathlib.Data.ENat.Basic
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# One-dimensional regular local rings are DVRs

Regularity supplies the domain structure and identifies the dimension of
the cotangent space with Krull dimension. The one-dimensional local-domain
criterion then produces the discrete valuation ring structure. No domain
or normality hypothesis is added to regularity.
-/

namespace SchemeTheory

universe u

/-- A regular local ring of dimension one is a DVR, with its domain
structure derived from regularity and retained in the conclusion. -/
theorem isDiscreteValuationRing_of_isRegularLocalRing_dimension_one
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (hdim : ringKrullDim R = (1 : WithBot ℕ∞)) :
    let : IsDomain R := IsRegularLocalRing.isDomain R
    IsDiscreteValuationRing R := by
  intro hdomain
  apply IsLocalRing.finrank_CotangentSpace_eq_one_iff.mp
  have hcotangent :
      ((Module.finrank (IsLocalRing.ResidueField R)
        (IsLocalRing.CotangentSpace R) : ℕ∞) : WithBot ℕ∞) =
      ((1 : ℕ∞) : WithBot ℕ∞) :=
    ((IsRegularLocalRing.iff_finrank_cotangentSpace R).mp inferInstance).trans hdim
  exact ENat.natCast_inj.mp (WithBot.coe_eq_coe.mp hcotangent)

end SchemeTheory
