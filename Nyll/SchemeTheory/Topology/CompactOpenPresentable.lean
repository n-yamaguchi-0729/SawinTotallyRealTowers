/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.CategoryTheory.Presentable.Finite
import Nyll.SchemeTheory.Topology.CompactOpenGenerators
import Nyll.SchemeTheory.Topology.CompactOpenSections

/-!
# Finite presentability of compact-open generators

Maps from the actual sheafified one-generator free representable are
sections over the corresponding open. For a compact open, the naturality
of this correspondence transfers preservation of filtered colimits from
the sections functor to the represented Hom functor.

No subcanonicity instance is needed: the generator is defined by actual
sheafification. This is an input to the finite-presentation argument in
Stacks Project, tag 0CAI: https://stacks.math.columbia.edu/tag/0CAI.
The Lean proof is original.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace SchemeTheory

variable {X : TopCat.{u}} [PrespectralSpace X] [QuasiSeparatedSpace X]

/-- The sheafified free representable with one generator on a compact
open is a finitely presentable object of the topological sheaf category. -/
theorem isFinitelyPresentable_openGenerator
    (U : Opens X) (hU : IsCompact (U : Set X)) :
    IsFinitelyPresentable.{u} (openGenerator U) := by
  let Γ : CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u) ⥤ Type u :=
    (sheafSections (Opens.grothendieckTopology X) (Type u)).obj (op U)
  let e : coyoneda.obj (op (openGenerator U)) ≅ Γ :=
    NatIso.ofComponents
      (fun F => (openGeneratorHomEquiv (U := U) (F := F)).toIso)
      (by
        intro F G f
        ext α
        exact openGeneratorHomEquiv_comp α f)
  have hΓ : PreservesFilteredColimitsOfSize.{u, u} Γ :=
    TopCat.Sheaf.preservesFilteredColimits_sheafSections_of_isCompact U hU
  apply isFinitelyPresentable_iff_preservesFilteredColimitsOfSize.mpr
  refine ⟨fun I _ _ => ?_⟩
  exact preservesColimitsOfShape_of_natIso (J := I) e.symm

end SchemeTheory
