/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.LinearMap

/-!
# Localization of the actual kernel map in a commutative square

The native localization theorem identifies the kernel of the universal
localized arrow with the localization of the original kernel. Here the
lower arrow is the one supplied by an actual commutative square. Its
universal property identifies it with that native arrow, so restriction of
the vertical map to the two kernels is itself a localization.

This is the module-level kernel supplier for the quasicoherent extension
construction in Stacks, Tag 01PE. It adds no kernel-comparison premise and
does not yet assert a sheaf-extension or relative approximation theorem.
-/

noncomputable section

universe u v₁ v₂ v₃ v₄

namespace LinearMap

private theorem mapsTo_ker_of_comp_eq
    {R : Type u} [CommRing R]
    {M : Type v₁} [AddCommGroup M] [Module R M]
    {M' : Type v₂} [AddCommGroup M'] [Module R M']
    {N : Type v₃} [AddCommGroup N] [Module R N]
    {N' : Type v₄} [AddCommGroup N'] [Module R N']
    (f : M →ₗ[R] M') (g : N →ₗ[R] N')
    (φ : M →ₗ[R] N) (ψ : M' →ₗ[R] N')
    (h : ψ.comp f = g.comp φ) :
    ∀ x ∈ φ.ker, f x ∈ ψ.ker := by
  change φ.ker ≤ ψ.ker.comap f
  rw [← LinearMap.ker_comp, h]
  exact LinearMap.ker_le_ker_comp φ g

/-- The restriction of the left vertical arrow to the kernels of the two
horizontal arrows of an actual commutative square. -/
def kernelRestriction
    {R : Type u} [CommRing R]
    {M : Type v₁} [AddCommGroup M] [Module R M]
    {M' : Type v₂} [AddCommGroup M'] [Module R M']
    {N : Type v₃} [AddCommGroup N] [Module R N]
    {N' : Type v₄} [AddCommGroup N'] [Module R N']
    (f : M →ₗ[R] M') (g : N →ₗ[R] N')
    (φ : M →ₗ[R] N) (ψ : M' →ₗ[R] N')
    (h : ψ.comp f = g.comp φ) : φ.ker →ₗ[R] ψ.ker :=
  f.restrict (mapsTo_ker_of_comp_eq f g φ ψ h)

private theorem isLocalizedModule_restrict_of_localized₀_eq
    {R : Type u} [CommRing R]
    {M : Type v₁} [AddCommGroup M] [Module R M]
    {M' : Type v₂} [AddCommGroup M'] [Module R M']
    (S : Submonoid R) (f : M →ₗ[R] M') [IsLocalizedModule S f]
    (K : Submodule R M) (L : Submodule R M')
    (hf : ∀ x ∈ K, f x ∈ L) (h : K.localized₀ S f = L) :
    IsLocalizedModule S (f.restrict hf) := by
  subst L
  exact inferInstanceAs (IsLocalizedModule S (K.toLocalized₀ S f))

private theorem localized₀_ker_eq_of_comp_eq
    {R : Type u} [CommRing R]
    {M : Type v₁} [AddCommGroup M] [Module R M]
    {M' : Type v₂} [AddCommGroup M'] [Module R M']
    {N : Type v₃} [AddCommGroup N] [Module R N]
    {N' : Type v₄} [AddCommGroup N'] [Module R N']
    (S : Submonoid R)
    (f : M →ₗ[R] M') [IsLocalizedModule S f]
    (g : N →ₗ[R] N') [IsLocalizedModule S g]
    (φ : M →ₗ[R] N) (ψ : M' →ₗ[R] N')
    (h : ψ.comp f = g.comp φ) :
    φ.ker.localized₀ S f = ψ.ker := by
  have hψ : ψ = IsLocalizedModule.map S f g φ := by
    apply IsLocalizedModule.linearMap_ext (S := S) (f := f) g
    exact h.trans (IsLocalizedModule.map_comp S f g φ).symm
  rw [hψ]
  exact (LinearMap.ker_localizedMap_eq_localized₀_ker S f g φ).symm

/-- If both vertical arrows of a commutative square are localizations, the
actual restriction map between the kernels is a localization too. -/
theorem isLocalizedModule_kernelRestriction
    {R : Type u} [CommRing R]
    {M : Type v₁} [AddCommGroup M] [Module R M]
    {M' : Type v₂} [AddCommGroup M'] [Module R M']
    {N : Type v₃} [AddCommGroup N] [Module R N]
    {N' : Type v₄} [AddCommGroup N'] [Module R N']
    (S : Submonoid R)
    (f : M →ₗ[R] M') [IsLocalizedModule S f]
    (g : N →ₗ[R] N') [IsLocalizedModule S g]
    (φ : M →ₗ[R] N) (ψ : M' →ₗ[R] N')
    (h : ψ.comp f = g.comp φ) :
    IsLocalizedModule S (kernelRestriction f g φ ψ h) := by
  exact isLocalizedModule_restrict_of_localized₀_eq S f φ.ker ψ.ker
    (mapsTo_ker_of_comp_eq f g φ ψ h)
    (localized₀_ker_eq_of_comp_eq S f g φ ψ h)

end LinearMap
