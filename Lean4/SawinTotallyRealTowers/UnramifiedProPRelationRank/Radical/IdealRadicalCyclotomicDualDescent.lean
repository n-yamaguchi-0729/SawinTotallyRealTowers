/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.IdealRadicalCyclotomicModule

set_option autoImplicit false
/-!
# Descent from the cyclotomic ideal-radical dual

The restricted ideal radical over the chosen cyclotomic base is a quotient of
the base-field ideal radical.  Its dual therefore embeds canonically into the
base-field radical dual.  This file applies that embedding functorially to an
entire space of linear maps with fixed source.

In particular, a linear map constructed first with cyclotomic target can be
descended without changing its kernel.  Thus injectivity at the cyclotomic
stage is exactly injectivity after descent to the target used in the final
Shafarevich bound.
-/

open scoped NumberField

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

universe u

variable (F : Type*) [Field F] [NumberField F]
variable (p : ℕ) [Fact p.Prime]
variable (M : Type u) [AddCommGroup M] [Module (ZMod p) M]

/-- Postcomposition with the canonical cyclotomic-dual injection, linear in
the input map.  This is the descent endpoint for maps whose source is fixed
and whose initial target is the restricted cyclotomic ideal-radical dual. -/
noncomputable def idealRadicalCyclotomicDualDescent :
    (M →ₗ[ZMod p]
        Module.Dual (ZMod p) (idealRadicalCyclotomicModP F p)) →ₗ[ZMod p]
      (M →ₗ[ZMod p]
        Module.Dual (ZMod p) (idealPowerRadicalModP F p)) :=
  LinearMap.compRight (ZMod p) (idealRadicalCyclotomicDualInjection F p)

@[simp]
theorem idealRadicalCyclotomicDualDescent_apply
    (f : M →ₗ[ZMod p]
      Module.Dual (ZMod p) (idealRadicalCyclotomicModP F p))
    (x : M) :
    idealRadicalCyclotomicDualDescent F p M f x =
      idealRadicalCyclotomicDualInjection F p (f x) :=
  rfl

/-- Descent is faithful on the whole space of maps with a fixed source. -/
theorem idealRadicalCyclotomicDualDescent_injective :
    Function.Injective (idealRadicalCyclotomicDualDescent F p M) := by
  intro f g hfg
  apply LinearMap.ext
  intro x
  apply idealRadicalCyclotomicDualInjection_injective F p
  exact DFunLike.congr_fun hfg x

/-- Postcomposition with cyclotomic descent does not change the kernel of the
input map. -/
theorem idealRadicalCyclotomicDualDescent_ker
    (f : M →ₗ[ZMod p]
      Module.Dual (ZMod p) (idealRadicalCyclotomicModP F p)) :
    LinearMap.ker (idealRadicalCyclotomicDualDescent F p M f) =
      LinearMap.ker f := by
  ext x
  simp only [LinearMap.mem_ker,
    idealRadicalCyclotomicDualDescent_apply]
  constructor
  · intro hx
    apply idealRadicalCyclotomicDualInjection_injective F p
    simpa using hx
  · intro hx
    simp [hx]

/-- A map into the cyclotomic radical dual is injective exactly when its
canonical descent to the base-field radical dual is injective. -/
theorem idealRadicalCyclotomicDualDescent_apply_injective_iff
    (f : M →ₗ[ZMod p]
      Module.Dual (ZMod p) (idealRadicalCyclotomicModP F p)) :
    Function.Injective (idealRadicalCyclotomicDualDescent F p M f) ↔
      Function.Injective f := by
  rw [← LinearMap.ker_eq_bot, ← LinearMap.ker_eq_bot,
    idealRadicalCyclotomicDualDescent_ker F p M f]

end ClassFieldTower.Martinet.Shafarevich
