/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.RelationRank.AbsoluteUnramifiedGaloisSequence
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FinitePlaceH2LocalizationFamily

set_option autoImplicit false
/-!
# Localization of degree-two classes inflated from the unramified quotient

This file defines inflation from the maximal everywhere-unramified pro-`p` Galois group to the
absolute Galois group and records its finite-place localization as pullback along the composite
local decomposition map.  Proving that this composite vanishes in degree two requires the missing
local unramified-quotient cohomology comparison, so the file stops at the naturality endpoint.
-/

open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.Cohomology
open ClassFieldTower.Martinet

variable (F : Type) [Field F] [NumberField F]
variable (p : ℕ) [Fact p.Prime]

/-- Inflation in degree two along absolute restriction to the maximal everywhere-unramified
pro-`p` extension. -/
noncomputable def absoluteUnramifiedH2Inflation :
    continuousCohomologyZModPLifted p
        (MaxEverywhereUnramifiedProPGaloisGroup F p) 2 →ₗ[ZMod p]
      continuousCohomologyZModPLifted p (Field.absoluteGaloisGroup F) 2 :=
  (continuousCohomologyZModPMapLifted p
    (absoluteToMaxEverywhereUnramifiedProP F p) 2).hom.toLinearMap

@[simp]
theorem absoluteUnramifiedH2Inflation_apply
    (x : continuousCohomologyZModPLifted p
      (MaxEverywhereUnramifiedProPGaloisGroup F p) 2) :
    absoluteUnramifiedH2Inflation F p x =
      (continuousCohomologyZModPMapLifted p
        (absoluteToMaxEverywhereUnramifiedProP F p) 2).hom x :=
  rfl

/-- Simultaneous finite-place localization after inflation from the everywhere-unramified
quotient. -/
noncomputable def absoluteUnramifiedH2LocalizationFamily :
    continuousCohomologyZModPLifted p
        (MaxEverywhereUnramifiedProPGaloisGroup F p) 2 →ₗ[ZMod p]
      FinitePlaceH2LocalizationTarget F p :=
  (finitePlaceH2LocalizationFamily F p).comp
    (absoluteUnramifiedH2Inflation F p)

@[simp]
theorem absoluteUnramifiedH2LocalizationFamily_apply
    (x : continuousCohomologyZModPLifted p
      (MaxEverywhereUnramifiedProPGaloisGroup F p) 2)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    absoluteUnramifiedH2LocalizationFamily F p x v =
      finitePlaceH2Localization F p v (absoluteUnramifiedH2Inflation F p x) :=
  rfl

/-- Each localized inflated class is pullback along the composite from the local decomposition
group to the maximal everywhere-unramified pro-`p` Galois group. -/
theorem absoluteUnramifiedH2LocalizationFamily_component
    (x : continuousCohomologyZModPLifted p
      (MaxEverywhereUnramifiedProPGaloisGroup F p) 2)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    absoluteUnramifiedH2LocalizationFamily F p x v =
      (continuousCohomologyZModPMapLifted p
        ((absoluteToMaxEverywhereUnramifiedProP F p).comp
          (finitePlaceAbsoluteDecompositionInclusion F v)) 2).hom x := by
  change
    ((continuousCohomologyZModPMapLifted p
          (absoluteToMaxEverywhereUnramifiedProP F p) 2 ≫
        continuousCohomologyZModPMapLifted p
          (finitePlaceAbsoluteDecompositionInclusion F v) 2).hom) x = _
  rw [← continuousCohomologyZModPMapLifted_comp]

end ClassFieldTower.Martinet.Shafarevich
