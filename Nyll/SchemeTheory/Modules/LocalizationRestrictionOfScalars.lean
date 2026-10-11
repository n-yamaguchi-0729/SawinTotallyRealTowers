/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Module.LocalizedModule.Basic

/-!
# Localization after restricting scalars

Preserves the actual localized-module property under the prescribed coefficient ring map.
-/

noncomputable section

universe u v

open CategoryTheory

namespace ModuleCat

theorem isLocalizedModuleAway_restrictScalars (R A : CommRingCat.{u}) (σ : R →+* A)
    (M N : ModuleCat.{v} A) (f : M ⟶ N) (r : R)
    [IsLocalizedModule (Submonoid.powers (σ r)) f.hom] :
    IsLocalizedModule (Submonoid.powers r) ((ModuleCat.restrictScalars σ).map f).hom := by
  let : Algebra R A := σ.toAlgebra
  have : IsScalarTower R A ((ModuleCat.restrictScalars σ).obj M) :=
    IsScalarTower.of_compHom R A M
  have : IsScalarTower R A ((ModuleCat.restrictScalars σ).obj N) :=
    IsScalarTower.of_compHom R A N
  let fA : ((ModuleCat.restrictScalars σ).obj M) →ₗ[A]
      ((ModuleCat.restrictScalars σ).obj N) := f.hom
  have : IsLocalizedModule (Submonoid.powers (algebraMap R A r)) fA :=
    inferInstanceAs (IsLocalizedModule (Submonoid.powers (σ r)) f.hom)
  exact IsLocalizedModule.restrictScalars_powers (R := R) (A := A) r fA

end ModuleCat
