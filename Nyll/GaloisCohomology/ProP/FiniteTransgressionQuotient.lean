/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.ProP.FiniteTransgressionExact
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Quotient presentation of finite transgression

The exact kernel calculation for finite transgression identifies invariant characters modulo
ambient restrictions with the range of finite transgression.
-/

open CategoryTheory TopRep ContRepresentation

namespace ClassFieldTower.Cohomology

noncomputable section

universe u

variable {p : ℕ}
variable {P : Type u} [Group P]

/-- The first isomorphism theorem for finite transgression, with its kernel rewritten as the
range of ambient character restriction. -/
noncomputable def finiteTransgressionQuotientEquivRange
    (N : Subgroup P) [N.Normal] [Finite (P ⧸ N)] :
    (InvariantFiniteCharacter (p := p) N ⧸
        LinearMap.range (finiteCharacterRestrictionLinearMap (p := p) N)) ≃ₗ[ZMod p]
      LinearMap.range (finiteTransgressionLinearMap (p := p) N) :=
  (Submodule.quotEquivOfEq _ _
      (finiteCharacterRestriction_range_eq_transgression_ker (p := p) N)).trans
    (finiteTransgressionLinearMap (p := p) N).quotKerEquivRange

@[simp]
theorem finiteTransgressionQuotientEquivRange_apply_mk
    (N : Subgroup P) [N.Normal] [Finite (P ⧸ N)]
    (χ : InvariantFiniteCharacter (p := p) N) :
    finiteTransgressionQuotientEquivRange (p := p) N
        (Submodule.Quotient.mk χ) =
      ⟨finiteTransgressionLinearMap N χ,
        LinearMap.mem_range_self (finiteTransgressionLinearMap N) χ⟩ := by
  rfl

/-- The quotient by ambient restrictions and the finite-transgression range have equal
`ZMod p`-dimension. -/
theorem finrank_finiteTransgressionCharacterQuotient_eq_range
    (N : Subgroup P) [N.Normal] [Finite (P ⧸ N)] :
    Module.finrank (ZMod p)
        (InvariantFiniteCharacter (p := p) N ⧸
          LinearMap.range (finiteCharacterRestrictionLinearMap (p := p) N)) =
      Module.finrank (ZMod p)
        (LinearMap.range (finiteTransgressionLinearMap (p := p) N)) :=
  (finiteTransgressionQuotientEquivRange (p := p) N).finrank_eq

end

end ClassFieldTower.Cohomology
