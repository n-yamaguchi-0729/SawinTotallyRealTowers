/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.FiniteEtale.BaseChange.PullbackIdentity
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.Topology.NoetherianSpace
import Mathlib.Order.Minimal

/-!
# Maximal open extensions of finite étale covers

The ascending chain condition on opens gives a maximal open over which a
given finite étale cover extends. This is maximal among extensions, without
assuming uniqueness of extensions or compatibility between unrelated ones.
-/

noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.FiniteEtale

universe u

attribute [local instance] finiteEtaleOverCategoryCoherence
  finiteEtaleHasPullbacksAlongCoherence finiteEtaleStableUnderBaseChangeAlongCoherence

/-- A finite étale cover of an open in a topologically Noetherian scheme
has an extension which cannot be extended to a strictly larger open. -/
theorem exists_maximal_open_extension
    {X : Scheme.{u}} [NoetherianSpace X]
    (U : X.Opens) (V : FiniteEtale U.toScheme) :
    ∃ (N : X.Opens) (hUN : U ≤ N) (W : FiniteEtale N.toScheme),
      Nonempty ((pullback (X.homOfLE hUN)).obj W ≅ V) ∧
      ∀ (M : X.Opens) (hNM : N ≤ M) (Z : FiniteEtale M.toScheme),
        Nonempty ((pullback (X.homOfLE hNM)).obj Z ≅ W) → M ≤ N := by
  let P (N : X.Opens) : Prop := ∃ (hUN : U ≤ N) (W : FiniteEtale N.toScheme),
    Nonempty ((pullback (X.homOfLE hUN)).obj W ≅ V)
  have hU : P U := by
    refine ⟨le_rfl, V, ⟨?_⟩⟩
    rw [Scheme.homOfLE_rfl]
    exact (pullbackIdIso U.toScheme).app V
  obtain ⟨N, hmax⟩ := exists_maximal_of_wellFoundedGT P ⟨U, hU⟩
  obtain ⟨hUN, W, ⟨e⟩⟩ := hmax.1
  refine ⟨N, hUN, W, ⟨e⟩, ?_⟩
  intro M hNM Z ⟨a⟩
  apply hmax.2 ?_ hNM
  refine ⟨hUN.trans hNM, Z, ⟨?_⟩⟩
  let c : pullback (X.homOfLE (hUN.trans hNM)) ≅
      pullback (X.homOfLE hNM) ⋙ pullback (X.homOfLE hUN) :=
    MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤)
      (X.homOfLE hUN) (X.homOfLE hNM) (X.homOfLE (hUN.trans hNM))
      (X.homOfLE_homOfLE hUN hNM).symm
  exact c.app Z ≪≫ (pullback (X.homOfLE hUN)).mapIso a ≪≫ e

end AlgebraicGeometry.FiniteEtale
