/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FinitePlaceUnramifiedH1
import Mathlib.LinearAlgebra.Pi

set_option autoImplicit false
/-!
# The family of finite-place unramified H¹ spaces

The unramified continuous degree-one subspaces at every finite place are assembled into a
dependent product module.  Coordinatewise subtype inclusion embeds it in the corresponding
product of local decomposition-group `H¹` spaces.
-/

open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.ProP

variable (F : Type) [Field F] [NumberField F]
variable (p : ℕ)

local instance finitePlaceUnramifiedH1FamilyModule
    {q : ℕ} {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] :
    Module (ZMod q) (ContinuousH1ZMod (p := q) (G := H)) :=
  continuousH1ZModModule

/-- The dependent product of the unramified `H¹` subspaces over all finite places. -/
abbrev FinitePlaceUnramifiedH1Family : ModuleCat (ZMod p) :=
  ModuleCat.of (ZMod p)
    ((v : HeightOneSpectrum (NumberField.RingOfIntegers F)) →
      finitePlaceUnramifiedH1 F p v)

/-- The dependent product of decomposition-group `H¹` spaces over all finite places. -/
abbrev FinitePlaceDecompositionH1Family : ModuleCat (ZMod p) :=
  ModuleCat.of (ZMod p)
    ((v : HeightOneSpectrum (NumberField.RingOfIntegers F)) →
      ContinuousH1ZMod
        (p := p) (G := finitePlaceAbsoluteDecompositionGroup F v))

/-- Coordinatewise subtype inclusion of every unramified local class into local `H¹`. -/
noncomputable def finitePlaceUnramifiedH1FamilyInclusion :
    FinitePlaceUnramifiedH1Family F p →ₗ[ZMod p]
      FinitePlaceDecompositionH1Family F p :=
  LinearMap.piMap fun v ↦ (finitePlaceUnramifiedH1 F p v).subtype

/-- A component of the family inclusion is the ordinary submodule subtype inclusion. -/
@[simp]
theorem finitePlaceUnramifiedH1FamilyInclusion_apply
    (x : FinitePlaceUnramifiedH1Family F p)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    finitePlaceUnramifiedH1FamilyInclusion F p x v = (x v).1 :=
  rfl

/-- Evaluation after family inclusion does not change an unramified character. -/
@[simp]
theorem finitePlaceUnramifiedH1FamilyInclusion_apply_apply
    (x : FinitePlaceUnramifiedH1Family F p)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F))
    (sigma : finitePlaceAbsoluteDecompositionGroup F v) :
    finitePlaceUnramifiedH1FamilyInclusion F p x v (Additive.ofMul sigma) =
      (x v).1 (Additive.ofMul sigma) :=
  rfl

/-- Coordinatewise inclusion of the unramified family is injective. -/
theorem finitePlaceUnramifiedH1FamilyInclusion_injective :
    Function.Injective (finitePlaceUnramifiedH1FamilyInclusion F p) := by
  intro x y hxy
  funext v
  apply Subtype.ext
  exact congrFun hxy v

end ClassFieldTower.Martinet.Shafarevich
