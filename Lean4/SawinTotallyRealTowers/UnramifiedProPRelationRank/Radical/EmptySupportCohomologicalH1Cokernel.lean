/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.FinitePlaceH1RamificationLocalization
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FinitePlaceRamifiedCharacterQuotient
import Mathlib.LinearAlgebra.Dual.Lemmas

set_option autoImplicit false
/-!
# Self-dual empty-support cohomological H¹ cokernel

Absolute continuous mod-`p` characters restrict at every finite place and then pass to the
quotient by unramified characters.  The empty-support object is the cokernel of the dual of this
global-to-local map, not the cokernel of the primal map.

This is the self-dual `F_p` model.  Over a general number field, the Tate-dual coefficient of
trivial `F_p` is `μ_p`, so identifying this object with the arithmetic `B_∅` additionally requires
the cyclotomic coefficient comparison and local Tate duality.  No such identification is asserted
in this file.
-/

open NumberField IsDedekindDomain
open scoped NumberField

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.ProP

variable (F : Type) [Field F] [NumberField F]
variable (p : ℕ) [Fact p.Prime]

local instance emptySupportCohomologicalH1ZModAddCommGroup : AddCommGroup (ZMod p) :=
  (ZMod.instField p).toDivisionRing.toAddCommGroup

local instance emptySupportCohomologicalH1Module
    {q : ℕ} {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] :
    Module (ZMod q) (ContinuousH1ZMod (p := q) (G := H)) :=
  continuousH1ZModModule

/-- Restriction at `v`, followed by passage to the ramified local character quotient. -/
noncomputable def finitePlaceAbsoluteH1RamifiedQuotient
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    absoluteContinuousZModCharacterModP F p →ₗ[ZMod p]
      FinitePlaceRamifiedCharacterQuotient F p v :=
  (finitePlaceRamifiedCharacterQuotientMap F p v).comp
    (finitePlaceAbsoluteH1DecompositionRestriction F p v)

@[simp]
theorem finitePlaceAbsoluteH1RamifiedQuotient_apply
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F))
    (chi : absoluteContinuousZModCharacterModP F p) :
    finitePlaceAbsoluteH1RamifiedQuotient F p v chi =
      Submodule.Quotient.mk
        (finitePlaceAbsoluteH1DecompositionRestriction F p v chi) :=
  rfl

/-- The dependent product of ramified local character quotients at all finite places. -/
abbrev FinitePlaceRamifiedCharacterLocalizationTarget :=
  (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) →
    FinitePlaceRamifiedCharacterQuotient F p v

/-- The primal global-to-local map into all ramified local character quotients. -/
noncomputable def finitePlaceAbsoluteH1RamifiedQuotientFamily :
    absoluteContinuousZModCharacterModP F p →ₗ[ZMod p]
      FinitePlaceRamifiedCharacterLocalizationTarget F p :=
  LinearMap.pi fun v ↦ finitePlaceAbsoluteH1RamifiedQuotient F p v

@[simp]
theorem finitePlaceAbsoluteH1RamifiedQuotientFamily_apply
    (chi : absoluteContinuousZModCharacterModP F p)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    finitePlaceAbsoluteH1RamifiedQuotientFamily F p chi v =
      finitePlaceAbsoluteH1RamifiedQuotient F p v chi :=
  rfl

/-- The dual local-to-global map whose cokernel is the cohomological empty-support object. -/
noncomputable def finitePlaceAbsoluteH1RamifiedQuotientFamilyDual :
    Module.Dual (ZMod p) (FinitePlaceRamifiedCharacterLocalizationTarget F p) →ₗ[ZMod p]
      Module.Dual (ZMod p) (absoluteContinuousZModCharacterModP F p) :=
  (finitePlaceAbsoluteH1RamifiedQuotientFamily F p).dualMap

@[simp]
theorem finitePlaceAbsoluteH1RamifiedQuotientFamilyDual_apply
    (phi : Module.Dual (ZMod p) (FinitePlaceRamifiedCharacterLocalizationTarget F p))
    (chi : absoluteContinuousZModCharacterModP F p) :
    finitePlaceAbsoluteH1RamifiedQuotientFamilyDual F p phi chi =
      phi (finitePlaceAbsoluteH1RamifiedQuotientFamily F p chi) :=
  rfl

/-- The self-dual cohomological empty-support `H¹` cokernel: the cokernel of the dual
local-to-global map on trivial mod-`p` characters. -/
abbrev EmptySupportCohomologicalH1Cokernel : ModuleCat (ZMod p) :=
  ModuleCat.of (ZMod p)
    (Module.Dual (ZMod p) (absoluteContinuousZModCharacterModP F p) ⧸
      LinearMap.range (finitePlaceAbsoluteH1RamifiedQuotientFamilyDual F p))

/-- The canonical projection onto the cohomological empty-support cokernel. -/
noncomputable def emptySupportCohomologicalH1CokernelMap :
    Module.Dual (ZMod p) (absoluteContinuousZModCharacterModP F p) →ₗ[ZMod p]
      EmptySupportCohomologicalH1Cokernel F p :=
  (LinearMap.range (finitePlaceAbsoluteH1RamifiedQuotientFamilyDual F p)).mkQ

@[simp]
theorem emptySupportCohomologicalH1CokernelMap_apply
    (phi : Module.Dual (ZMod p) (absoluteContinuousZModCharacterModP F p)) :
    emptySupportCohomologicalH1CokernelMap F p phi =
      Submodule.Quotient.mk phi :=
  rfl

/-- The kernel of the cokernel projection is the range of the dual local-to-global map. -/
theorem emptySupportCohomologicalH1CokernelMap_ker :
    LinearMap.ker (emptySupportCohomologicalH1CokernelMap F p) =
      LinearMap.range (finitePlaceAbsoluteH1RamifiedQuotientFamilyDual F p) :=
  Submodule.ker_mkQ _

/-- The canonical projection onto the cohomological empty-support cokernel is surjective. -/
theorem emptySupportCohomologicalH1CokernelMap_surjective :
    Function.Surjective (emptySupportCohomologicalH1CokernelMap F p) :=
  Submodule.mkQ_surjective _

end ClassFieldTower.Martinet.Shafarevich
