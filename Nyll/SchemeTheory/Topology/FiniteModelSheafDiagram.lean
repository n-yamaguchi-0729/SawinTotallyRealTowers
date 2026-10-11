/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Cones
import Nyll.SchemeTheory.Topology.CompactOpenFiniteModels
import Nyll.SchemeTheory.Topology.FiniteModelSheafTransitions

/-!
# The actual diagram of finite-model sheaf approximations

Finite families of compact opens form a filtered index category. Their
realized membership spaces and coordinate-forgetting maps give the
actual approximations `q⁻¹q_*F`, with transition maps adjoint to the finer
unit. The actual counits form a cocone with vertex `F`.

This is the finite-model diagram used in the proof of Stacks Project,
tag 09ZG: https://stacks.math.columbia.edu/tag/09ZG.
The Lean constructions and proofs are original.
-/

noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace

namespace SchemeTheory.CompactOpenFiniteModel

variable {X : TopCat.{u}}

/-- The actual inverse-image/direct-image approximations indexed by finite
families of compact opens, with their coherent refinement maps. -/
def sheafDiagram (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u)) :
    Finset (CompactOpens X) ⥤
      CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u) where
  obj S := sheafApproximation (quotient S) F
  map {S T} h := sheafApproximationTransition (quotient T) (refinement (leOfHom h)) F
  map_id S := by
    exact sheafApproximationTransition_id (quotient S) F
  map_comp {S T R} h k := by
    exact (sheafApproximationTransition_comp (quotient R)
      (refinement (leOfHom k)) (refinement (leOfHom h)) F).symm

/-- The actual adjunction counits form a cocone from the finite-model
diagram to the original sheaf. -/
def sheafCocone (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u)) :
    Cocone (sheafDiagram F) where
  pt := F
  ι :=
    { app := fun S =>
        (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (quotient S)).counit.app F
      naturality := fun S T h => by
        let eS : sheafApproximation (quotient S) F ⟶ F :=
          (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (quotient S)).counit.app F
        let eT : sheafApproximation (quotient T) F ⟶ F :=
          (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (quotient T)).counit.app F
        let t : sheafApproximation (quotient S) F ⟶ sheafApproximation (quotient T) F :=
          sheafApproximationTransition (quotient T) (refinement (leOfHom h)) F
        have he : t ≫ eT = eS := sheafApproximationTransition_counit (quotient T)
          (refinement (leOfHom h)) F
        change t ≫ eT = eS ≫ 𝟙 F
        exact he.trans (Category.comp_id eS).symm }

end SchemeTheory.CompactOpenFiniteModel
