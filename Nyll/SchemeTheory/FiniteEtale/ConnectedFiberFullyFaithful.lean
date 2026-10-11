/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.FiniteEtale.ConnectedFiberSections
import Nyll.SchemeTheory.FiniteEtale.FullOfSectionDescent
import Nyll.SchemeTheory.FiniteEtale.DensePullback
import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Full faithfulness for universally open maps with connected geometric fibres

The actual descent of finite etale sections supplies fullness through the
finite etale internal Hom. Surjectivity of a geometrically connected map
supplies faithfulness. Neither source nor target is assumed connected.
-/

noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.FiniteEtale

universe u

/-- A universally open morphism with geometrically connected fibres induces
a fully faithful pullback functor on finite etale covers of an arbitrary base. -/
def pullbackFullyFaithful_of_universallyOpen_geometricallyConnected
    {X S : Scheme.{u}} (f : X ⟶ S) [UniversallyOpen f] [GeometricallyConnected f] :
    (FiniteEtale.pullback f).FullyFaithful := by
  have hFull : (FiniteEtale.pullback f).Full :=
    pullback_full_of_section_descent f (fun W a ha =>
      exists_section_descent_of_universallyOpen_geometricallyConnected f W.hom a ha)
  have hFaithful : (FiniteEtale.pullback f).Faithful :=
    pullback_faithful_of_isDominant f
  exact Functor.FullyFaithful.ofFullyFaithful (FiniteEtale.pullback f)

end AlgebraicGeometry.FiniteEtale
