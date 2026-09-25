/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FinitePlaceH2Localization
import Mathlib.LinearAlgebra.Pi

set_option autoImplicit false
/-!
# The family of finite-place degree-two localization maps

The restriction maps to all absolute decomposition subgroups are assembled into one linear map
with dependent function codomain.
-/

open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.Cohomology

variable (F : Type) [Field F] [NumberField F]
variable (p : ℕ)

/-- The product of degree-two continuous cohomology spaces of the finite-place absolute
decomposition subgroups. -/
abbrev FinitePlaceH2LocalizationTarget :=
  (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) →
    continuousCohomologyZModPLifted p
      (finitePlaceAbsoluteDecompositionGroup F v) 2

/-- Simultaneous restriction of an absolute degree-two class to every finite-place decomposition
subgroup. -/
noncomputable def finitePlaceH2LocalizationFamily :
    continuousCohomologyZModPLifted p (Field.absoluteGaloisGroup F) 2 →ₗ[ZMod p]
      FinitePlaceH2LocalizationTarget F p :=
  LinearMap.pi fun v ↦ finitePlaceH2Localization F p v

/-- Each component of the family map is the corresponding finite-place localization. -/
@[simp]
theorem finitePlaceH2LocalizationFamily_apply
    (x : continuousCohomologyZModPLifted p (Field.absoluteGaloisGroup F) 2)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    finitePlaceH2LocalizationFamily F p x v =
      finitePlaceH2Localization F p v x :=
  rfl

end ClassFieldTower.Martinet.Shafarevich
