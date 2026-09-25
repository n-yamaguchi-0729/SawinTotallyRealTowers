/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FinitePlaceUnramifiedH1

set_option autoImplicit false
/-!
# Ramified local character quotient

Continuous mod-`p` characters of the chosen decomposition group are quotiented by the
characters trivial on absolute inertia.
-/

open NumberField IsDedekindDomain
open scoped NumberField

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.ProP

variable (F : Type) [Field F] [NumberField F]
variable (p : ℕ)

local instance finitePlaceRamifiedCharacterH1Module
    {q : ℕ} {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] :
    Module (ZMod q) (ContinuousH1ZMod (p := q) (G := H)) :=
  continuousH1ZModModule

/-- The ramified local character quotient `H¹(D_v, F_p) / H¹_unr(D_v, F_p)` as a
`ZMod p`-module object. -/
abbrev FinitePlaceRamifiedCharacterQuotient
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    ModuleCat (ZMod p) :=
  ModuleCat.of (ZMod p)
    (ContinuousH1ZMod (p := p) (G := finitePlaceAbsoluteDecompositionGroup F v) ⧸
      finitePlaceUnramifiedH1 F p v)

/-- The canonical quotient map from local decomposition-group characters to their ramified
classes. -/
noncomputable def finitePlaceRamifiedCharacterQuotientMap
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    ContinuousH1ZMod (p := p) (G := finitePlaceAbsoluteDecompositionGroup F v) →ₗ[ZMod p]
      FinitePlaceRamifiedCharacterQuotient F p v :=
  (finitePlaceUnramifiedH1 F p v).mkQ

@[simp]
theorem finitePlaceRamifiedCharacterQuotientMap_apply
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F))
    (chi : ContinuousH1ZMod (p := p) (G := finitePlaceAbsoluteDecompositionGroup F v)) :
    finitePlaceRamifiedCharacterQuotientMap F p v chi =
      Submodule.Quotient.mk chi :=
  rfl

/-- The kernel of the canonical ramified-character quotient map is exactly unramified
continuous `H¹`. -/
theorem finitePlaceRamifiedCharacterQuotientMap_ker
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    LinearMap.ker (finitePlaceRamifiedCharacterQuotientMap F p v) =
      finitePlaceUnramifiedH1 F p v :=
  Submodule.ker_mkQ (finitePlaceUnramifiedH1 F p v)

/-- Every ramified local character class has a decomposition-group character representative. -/
theorem finitePlaceRamifiedCharacterQuotientMap_surjective
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    Function.Surjective (finitePlaceRamifiedCharacterQuotientMap F p v) :=
  Submodule.mkQ_surjective (finitePlaceUnramifiedH1 F p v)

end ClassFieldTower.Martinet.Shafarevich
