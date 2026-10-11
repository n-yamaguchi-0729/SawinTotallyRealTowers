/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Finite type of the sheaf associated to a finite module

Choose actual finite module generators, and use the native tilde
presentation with exactly this generating set. Its relation module is
allowed to be infinite. Restricting the finite family of generators to
the slice sites gives the native finite-type condition.
-/

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A finite module gives an actual sheaf of finite type under tilde.
No finite-presentation or Noetherian hypothesis is imposed. -/
theorem isFiniteType_tilde_of_finite {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
    [Module.Finite R M] : (tilde M).IsFiniteType := by
  obtain ⟨s, hsFinite, hs⟩ :=
    Submodule.fg_def.mp (Module.Finite.fg_top (R := R) (M := M))
  have : Finite s := hsFinite.to_subtype
  let K : Submodule R (s →₀ R) :=
    LinearMap.ker (Finsupp.linearCombination R ((↑) : s → M))
  let P : (tilde M).Presentation :=
    presentationTilde M s hs (K : Set (s →₀ R)) (Submodule.span_eq K)
  let q : (tilde M).LocalGeneratorsData := P.generators.localGeneratorsData
  have hq : q.IsFiniteType := by
    constructor
    intro U
    constructor
    exact inferInstanceAs (Finite s)
  refine { exists_localGeneratorsData := ?_ }
  exact ⟨q, hq⟩

end AlgebraicGeometry
