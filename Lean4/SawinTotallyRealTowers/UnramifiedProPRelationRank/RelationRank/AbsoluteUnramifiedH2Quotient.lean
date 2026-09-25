/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import GaloisCohomology.ProP.PresentationQuotientEquiv
import SawinTotallyRealTowers.UnramifiedProPRelationRank.RelationRank.AbsoluteUnramifiedGaloisSequence

set_option autoImplicit false
/-!
# Degree-two cohomology of the absolute unramified quotient

The topological first-isomorphism equivalence for absolute restriction identifies degree-two
continuous cohomology of the maximal everywhere-unramified pro-`p` Galois group with that of the
corresponding quotient of the absolute Galois group.
-/

open scoped NumberField

noncomputable section

universe u

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.Cohomology
open ClassFieldTower.Martinet

variable (F : Type u) [Field F] [NumberField F]
variable (p : ℕ) [Fact p.Prime]

/-- Pullback along the absolute unramified quotient equivalence identifies the two degree-two
continuous cohomology spaces with trivial lifted `ZMod p` coefficients. -/
noncomputable def absoluteUnramifiedQuotientH2LinearEquiv :
    continuousCohomologyZModPLifted p
        (MaxEverywhereUnramifiedProPGaloisGroup F p) 2 ≃ₗ[ZMod p]
      continuousCohomologyZModPLifted p
        (Field.absoluteGaloisGroup F ⧸
          (absoluteUnramifiedKernel F p).toSubgroup) 2 :=
  continuousCohomologyZModPLiftedLinearEquiv
    (absoluteUnramifiedQuotientContinuousMulEquiv F p) 2

/-- The forward equivalence is the cohomological pullback along the quotient equivalence. -/
@[simp]
theorem absoluteUnramifiedQuotientH2LinearEquiv_apply
    (x : continuousCohomologyZModPLifted p
      (MaxEverywhereUnramifiedProPGaloisGroup F p) 2) :
    absoluteUnramifiedQuotientH2LinearEquiv F p x =
      (continuousCohomologyZModPMapLifted p
        (absoluteUnramifiedQuotientContinuousMulEquiv F p) 2).hom x :=
  rfl

/-- Pullback to the absolute unramified quotient detects the zero class. -/
@[simp]
theorem absoluteUnramifiedQuotientH2LinearEquiv_eq_zero_iff
    (x : continuousCohomologyZModPLifted p
      (MaxEverywhereUnramifiedProPGaloisGroup F p) 2) :
    absoluteUnramifiedQuotientH2LinearEquiv F p x = 0 ↔ x = 0 :=
  (absoluteUnramifiedQuotientH2LinearEquiv F p).map_eq_zero_iff

/-- Pullback to the absolute unramified quotient is injective. -/
theorem absoluteUnramifiedQuotientH2LinearEquiv_injective :
    Function.Injective (absoluteUnramifiedQuotientH2LinearEquiv F p) :=
  (absoluteUnramifiedQuotientH2LinearEquiv F p).injective

end ClassFieldTower.Martinet.Shafarevich
