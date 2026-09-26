/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.EmptySupportCohomologicalH1Cokernel
import Mathlib.LinearAlgebra.Dual.Lemmas

set_option autoImplicit false
/-!
# The kernel-dual model of the self-dual cohomological cokernel

Dualizing the global-to-local ramified-character map and taking its cokernel is canonically
equivalent to the dual of the kernel of the original map.  Thus a subsequent self-dual
arithmetic comparison can be reduced to identifying the corresponding primal kernels.

As in `EmptySupportCohomologicalH1Cokernel`, this is an intermediate self-dual `F_p` model.  The
general arithmetic `B_∅` uses the Tate-dual coefficient `μ_p`; connecting the two models remains a
separate local Tate/Kummer comparison.
-/

open NumberField IsDedekindDomain
open scoped NumberField

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.ProP

private theorem dualRange_eq_ker_kernelDualRestriction
    {q : ℕ} [Fact q.Prime]
    {V W : Type*}
    [AddCommGroup V] [Module (ZMod q) V]
    [AddCommGroup W] [Module (ZMod q) W]
    (f : V →ₗ[ZMod q] W) :
    LinearMap.range f.dualMap =
      LinearMap.ker (LinearMap.ker f).subtype.dualMap := by
  rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker,
    LinearMap.ker_dualMap_eq_dualAnnihilator_range,
    Submodule.range_subtype]

variable (F : Type) [Field F] [NumberField F]
variable (p : ℕ) [Fact p.Prime]

local instance emptySupportCohomologicalKernelZModAddCommGroup : AddCommGroup (ZMod p) :=
  (ZMod.instField p).toDivisionRing.toAddCommGroup

local instance emptySupportCohomologicalKernelH1Module
    {q : ℕ} {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] :
    Module (ZMod q) (ContinuousH1ZMod (p := q) (G := H)) :=
  continuousH1ZModModule

local instance finitePlaceRamifiedCharacterQuotientAddCommGroup
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    AddCommGroup (FinitePlaceRamifiedCharacterQuotient F p v) :=
  (FinitePlaceRamifiedCharacterQuotient F p v).isAddCommGroup

local instance finitePlaceRamifiedCharacterQuotientModule
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    Module (ZMod p) (FinitePlaceRamifiedCharacterQuotient F p v) :=
  (FinitePlaceRamifiedCharacterQuotient F p v).isModule

/-- Global continuous characters whose restriction at every finite place is unramified. -/
abbrev EmptySupportCohomologicalH1Kernel : ModuleCat (ZMod p) :=
  ModuleCat.of (ZMod p)
    (LinearMap.ker (finitePlaceAbsoluteH1RamifiedQuotientFamily F p))

/-- Inclusion of the empty-support cohomological kernel into global absolute characters. -/
noncomputable def emptySupportCohomologicalH1KernelInclusion :
    EmptySupportCohomologicalH1Kernel F p →ₗ[ZMod p]
      absoluteContinuousZModCharacterModP F p :=
  (LinearMap.ker (finitePlaceAbsoluteH1RamifiedQuotientFamily F p)).subtype

@[simp]
theorem emptySupportCohomologicalH1KernelInclusion_apply
    (x : EmptySupportCohomologicalH1Kernel F p) :
    emptySupportCohomologicalH1KernelInclusion F p x = x.1 :=
  rfl

/-- Restriction of global-character functionals to the empty-support cohomological kernel. -/
noncomputable def emptySupportCohomologicalH1KernelDualRestriction :
    Module.Dual (ZMod p) (absoluteContinuousZModCharacterModP F p) →ₗ[ZMod p]
      Module.Dual (ZMod p) (EmptySupportCohomologicalH1Kernel F p) :=
  (emptySupportCohomologicalH1KernelInclusion F p).dualMap

/-- Every functional on the cohomological kernel extends to the full global-character space. -/
theorem emptySupportCohomologicalH1KernelDualRestriction_surjective :
    Function.Surjective (emptySupportCohomologicalH1KernelDualRestriction F p) :=
  LinearMap.dualMap_surjective_of_injective Subtype.val_injective

/-- The dual global-to-local range is exactly the kernel of restriction to the cohomological
kernel. -/
theorem finitePlaceAbsoluteH1RamifiedQuotientFamilyDual_range :
    LinearMap.range (finitePlaceAbsoluteH1RamifiedQuotientFamilyDual F p) =
      LinearMap.ker (emptySupportCohomologicalH1KernelDualRestriction F p) := by
  simpa only [finitePlaceAbsoluteH1RamifiedQuotientFamilyDual,
    emptySupportCohomologicalH1KernelDualRestriction,
    emptySupportCohomologicalH1KernelInclusion] using
    (dualRange_eq_ker_kernelDualRestriction
      (q := p)
      (V := absoluteContinuousZModCharacterModP F p)
      (W := FinitePlaceRamifiedCharacterLocalizationTarget F p)
      (finitePlaceAbsoluteH1RamifiedQuotientFamily F p))

/-- The cohomological empty-support cokernel is canonically the dual of the kernel of the
primal global-to-local ramified-character map. -/
noncomputable def emptySupportCohomologicalH1CokernelEquivKernelDual :
    EmptySupportCohomologicalH1Cokernel F p ≃ₗ[ZMod p]
      Module.Dual (ZMod p) (EmptySupportCohomologicalH1Kernel F p) :=
  (Submodule.quotEquivOfEq
      (LinearMap.range (finitePlaceAbsoluteH1RamifiedQuotientFamilyDual F p))
      (LinearMap.ker (emptySupportCohomologicalH1KernelDualRestriction F p))
      (finitePlaceAbsoluteH1RamifiedQuotientFamilyDual_range F p)).trans
    ((emptySupportCohomologicalH1KernelDualRestriction F p).quotKerEquivOfSurjective
      (emptySupportCohomologicalH1KernelDualRestriction_surjective F p))

@[simp]
theorem emptySupportCohomologicalH1CokernelEquivKernelDual_mk
    (phi : Module.Dual (ZMod p) (absoluteContinuousZModCharacterModP F p)) :
    emptySupportCohomologicalH1CokernelEquivKernelDual F p
        (Submodule.Quotient.mk phi) =
      emptySupportCohomologicalH1KernelDualRestriction F p phi := by
  simp [emptySupportCohomologicalH1CokernelEquivKernelDual]

end ClassFieldTower.Martinet.Shafarevich
