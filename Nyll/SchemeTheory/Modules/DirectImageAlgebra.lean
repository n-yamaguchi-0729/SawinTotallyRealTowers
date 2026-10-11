/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.FiniteRelativeSpec
import Mathlib.AlgebraicGeometry.Modules.Presheaf
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Topology.Sheaves.Functors

/-!
# The actual direct-image algebra of a scheme morphism

The ring sheaf is the native pushforward of the structure sheaf and its
structure morphism is the original morphism's sheaf map. Its underlying
module is identified with the native direct image of the unit module,
using identity maps on the actual section modules and their restrictions.
-/

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.DirectImageAlgebra

variable {T X : Scheme.{u}} (g : T ⟶ X)

/-- The native direct image of the source's sheaf of commutative rings. -/
def sheaf : TopCat.Sheaf CommRingCat.{u} X :=
  (TopCat.Sheaf.pushforward CommRingCat.{u} g.base).obj T.sheaf

/-- The structure map is the original morphism's map on structure sheaves. -/
def structureMap : X.sheaf ⟶ sheaf g where
  hom := g.c

/-- The algebra's underlying module is the actual direct image of the
source unit module, including its original scalar and restriction maps. -/
def underlyingModuleIso :
    RelativeSpec.underlyingModule (structureMap g) ≅
      (Modules.pushforward g).obj (SheafOfModules.unit T.ringCatSheaf) := by
  apply (SheafOfModules.fullyFaithfulForget X.ringCatSheaf).preimageIso
  refine PresheafOfModules.isoMk (fun U => Iso.refl _) ?_
  intro U V i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

end AlgebraicGeometry.Scheme.DirectImageAlgebra
