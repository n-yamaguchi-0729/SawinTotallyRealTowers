/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality

/-!
# Homogeneous continuous cochains with arbitrary scalar coefficients

The coefficient functor uses Mathlib's actual homogeneous cochains and coefficient maps.
The carrier universe is the group universe, as required by its iterated continuous resolution;
the scalar ring has an independent universe. No action or cochain complex is reconstructed.
-/

@[expose] public section

noncomputable section

universe r u

open CategoryTheory

namespace TopRep

variable (R : Type r) [Ring R] [TopologicalSpace R]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Homogeneous continuous cochains, functorially in the actual coefficient representation. -/
def homogeneousContinuousCochainsFunctorOver :
    TopRep.{u} R G ⥤ CochainComplex (TopModuleCat.{u} R) ℕ where
  obj := homogeneousCochains
  map φ := ContinuousCohomology.cochainsMap (ContinuousMonoidHom.id G) φ
  map_id A := ContinuousCohomology.cochainsMap_id A
  map_comp φ ψ :=
    ContinuousCohomology.cochainsMap_comp (ContinuousMonoidHom.id G)
      (ContinuousMonoidHom.id G) φ ψ

end TopRep
