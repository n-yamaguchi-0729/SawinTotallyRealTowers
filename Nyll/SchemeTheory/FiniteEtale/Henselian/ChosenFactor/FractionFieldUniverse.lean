/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Localization.FractionRing
import Nyll.SchemeTheory.FiniteEtale.Henselian.ChosenFactorUniverse

/-!
# Fraction fields of a strict-Henselian chosen factor

A finite etale factor with a unique closed prime over a strictly Henselian
base is canonically the base ring.  The induced equivalence of fraction
fields is therefore the existing scalar map from the fraction field of the
base to the fraction field of the factor.  This file records that construction
with all four carriers allowed to live in independent universes.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe uB uD uF uP

variable {B : Type uB} {D : Type uD}
variable {Froot : Type uF} {P : Type uP}
variable [CommRing B] [CommRing D]
variable [Field Froot] [Field P]
variable [Algebra B D]
variable [Algebra B Froot] [IsFractionRing B Froot]
variable [Algebra D P] [IsFractionRing D P]
variable [Algebra B P] [IsScalarTower B D P]
variable [Algebra Froot P] [IsScalarTower B Froot P]
variable [HenselianLocalRing B]
variable [Module.Finite B D] [Algebra.Etale B D]
variable [IsSepClosed (IsLocalRing.ResidueField B)]

/-- The fraction field of the uniquely chosen finite etale factor over a
strictly Henselian base is canonically the fraction field of the base.

The target `Froot`-algebra is the one already present on `P`; the two scalar
tower assumptions say precisely that its restrictions are the canonical maps
through `B` and through the chosen factor `D`. -/
noncomputable def strictHenselianChosenFactorFractionFieldAlgEquiv_universe
    (q : Ideal D) [q.IsPrime]
    [q.LiesOver (IsLocalRing.maximalIdeal B)]
    (hunique : ∀ Q : Ideal D, Q.IsPrime →
      Q.LiesOver (IsLocalRing.maximalIdeal B) → Q = q) :
    Froot ≃ₐ[Froot] P :=
  IsFractionRing.fieldEquivOfAlgEquiv Froot Froot P
    (strictHenselianChosenFactorAlgEquiv_universe q hunique)

@[simp]
theorem strictHenselianChosenFactorFractionFieldAlgEquiv_universe_apply
    (q : Ideal D) [q.IsPrime]
    [q.LiesOver (IsLocalRing.maximalIdeal B)]
    (hunique : ∀ Q : Ideal D, Q.IsPrime →
      Q.LiesOver (IsLocalRing.maximalIdeal B) → Q = q)
    (x : Froot) :
    strictHenselianChosenFactorFractionFieldAlgEquiv_universe q hunique x =
      algebraMap Froot P x :=
  (strictHenselianChosenFactorFractionFieldAlgEquiv_universe q hunique).commutes x

end EtaleFundamentalGroups

end
