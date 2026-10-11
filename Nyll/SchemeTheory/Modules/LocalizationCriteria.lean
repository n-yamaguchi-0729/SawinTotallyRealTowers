/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Module.LocalizedModule.Away
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Group.Action.Basic

/-!
# Native module localization criteria

Constructs localization from the actual invertibility, fraction and kernel criteria.
-/

noncomputable section

universe u v

open CategoryTheory

namespace ModuleCat

/-- The native module localization constructor with its three actual criteria.
This keeps the endomorphism-ring unit conversion in its algebraic owner. -/
theorem isLocalizedModuleAway_of_criteria (R : CommRingCat.{u})
    (M N : ModuleCat.{v} R) (f : M ⟶ N) (r : R)
    (hunit : Function.Bijective (fun x : N => r • x))
    (hsurj : ∀ x : N, ∃ (n : ℕ) (y : M), f.hom y = r ^ n • x)
    (hker : ∀ y : M, f.hom y = 0 → ∃ n : ℕ, r ^ n • y = 0) :
    IsLocalizedModule.Away r f.hom := by
  apply IsLocalizedModule.Away.mk_of_addCommGroup
  · rw [Module.End.isUnit_iff]
    exact hunit
  · intro x
    obtain ⟨n, y, hy⟩ := hsurj x
    exact ⟨n, y, hy.symm⟩
  · exact hker

/-- A unit in the coefficient ring acts bijectively on the actual module
obtained by native restriction of scalars. No new action is installed. -/
theorem restrictScalars_smul_bijective_of_isUnit (R A : CommRingCat.{u})
    (σ : R →+* A) (N : ModuleCat.{v} A) (r : R) (hr : IsUnit (σ r)) :
    Function.Bijective (fun x : (ModuleCat.restrictScalars σ).obj N => r • x) := by
  have hfun : (fun x : (ModuleCat.restrictScalars σ).obj N => r • x) =
      (fun x : (ModuleCat.restrictScalars σ).obj N =>
        (show A from σ r) • (show N from x)) := by
    funext x
    exact ModuleCat.restrictScalars.smul_def σ r x
  rw [hfun]
  exact hr.smul_bijective (β := N)

end ModuleCat
