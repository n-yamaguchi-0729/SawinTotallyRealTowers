/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.Grp.Basic

/-!
# Native section objects for pushforward comparison

Keeps section opens, rings and modules in their existing categorical objects.
-/

noncomputable section

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Hom

/-- The actual preimage open, computed before evaluating any module. -/
def sectionComparisonOpen {X Y : Scheme.{u}} (j : X ⟶ Y) (V : Y.Opens) : X.Opens :=
  j ⁻¹ᵁ V

/-- The existing commutative section-ring object on that open. -/
def sectionComparisonRing {X Y : Scheme.{u}} (j : X ⟶ Y) (V : Y.Opens) : CommRingCat.{u} :=
  Γ(X, j.sectionComparisonOpen V)

/-- The existing native section module; no module action is installed or reconstructed. -/
def sectionComparisonModule {X Y : Scheme.{u}} (j : X ⟶ Y)
    (M : X.Modules) (V : Y.Opens) : ModuleCat.{u} (j.sectionComparisonRing V) :=
  M.val.obj (op (j.sectionComparisonOpen V))

/-- The existing underlying abelian section-group object at the computed open. -/
def sectionComparisonGroup {X Y : Scheme.{u}} (j : X ⟶ Y)
    (M : X.Modules) (V : Y.Opens) : AddCommGrpCat.{u} :=
  M.presheaf.obj (op (j.sectionComparisonOpen V))

end AlgebraicGeometry.Scheme.Hom
