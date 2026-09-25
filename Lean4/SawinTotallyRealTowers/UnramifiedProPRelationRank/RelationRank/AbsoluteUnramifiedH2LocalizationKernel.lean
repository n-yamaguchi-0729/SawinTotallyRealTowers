/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.RelationRank.FinitePlaceUnramifiedH2LocalizationVanishing

set_option autoImplicit false
/-!
# Absolute unramified degree two in the localization kernel

Inflation from the maximal everywhere-unramified pro-`p` quotient has zero
restriction at every finite place.  This file bundles that source theorem as
a linear map into the kernel of simultaneous localization.
-/

open NumberField IsDedekindDomain
open scoped NumberField

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.Cohomology
open ClassFieldTower.Martinet

variable (F : Type) [Field F] [NumberField F]
variable (p : ℕ) [Fact p.Prime]

/-- Inflation of an everywhere-unramified degree-two class, bundled in the
kernel of simultaneous finite-place localization. -/
noncomputable def absoluteUnramifiedH2InflationToLocalizationKernel :
    continuousCohomologyZModPLifted p
        (MaxEverywhereUnramifiedProPGaloisGroup F p) 2 →ₗ[ZMod p]
      LinearMap.ker (finitePlaceH2LocalizationFamily F p) :=
  (absoluteUnramifiedH2Inflation F p).codRestrict
    (LinearMap.ker (finitePlaceH2LocalizationFamily F p))
    (by
      intro x
      rw [LinearMap.mem_ker]
      change absoluteUnramifiedH2LocalizationFamily F p x = 0
      rw [absoluteUnramifiedH2LocalizationFamily_eq_zero]
      rfl)

@[simp]
theorem absoluteUnramifiedH2InflationToLocalizationKernel_apply
    (x : continuousCohomologyZModPLifted p
      (MaxEverywhereUnramifiedProPGaloisGroup F p) 2) :
    (absoluteUnramifiedH2InflationToLocalizationKernel F p x).1 =
      absoluteUnramifiedH2Inflation F p x :=
  rfl

/-- The entire absolute inflation range lies in the finite-place
localization kernel. -/
theorem absoluteUnramifiedH2Inflation_range_le_localization_ker :
    LinearMap.range (absoluteUnramifiedH2Inflation F p) ≤
      LinearMap.ker (finitePlaceH2LocalizationFamily F p) := by
  rintro y ⟨x, rfl⟩
  exact (absoluteUnramifiedH2InflationToLocalizationKernel F p x).2

end ClassFieldTower.Martinet.Shafarevich
