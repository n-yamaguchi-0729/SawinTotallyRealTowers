/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.Topology.Sheaves.Skyscraper
import Nyll.SchemeTheory.Topology.FiniteModelStalkComparison
import Nyll.SchemeTheory.Topology.FiniteModelStalkColimit
import Nyll.SchemeTheory.Topology.FiniteModelSheafDiagram

/-!
# Every sheaf is the colimit of its actual finite-model approximations

For a prespectral space, the actual counits `q⁻¹q_*F → F` form a colimit
cocone. On each stalk the diagram is the explicitly constructed diagram
of principal-neighborhood sections. Its germ cocone is a colimit. Stalks
preserve colimits and jointly detect isomorphisms, so the original sheaf
cocone is a colimit as well.

This supplies the finite-model reduction used in the proof of Stacks
Project, tag 09ZG: https://stacks.math.columbia.edu/tag/09ZG.
The Lean constructions and proofs are original.
-/

noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace

namespace SchemeTheory.CompactOpenFiniteModel

variable {X : TopCat.{u}} [PrespectralSpace X]

/-- The actual counit cocone becomes a colimit after taking any stalk. -/
def sheafStalkCoconeIsColimit
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u)) (x : X) :
    IsColimit ((sheafToPresheaf (Opens.grothendieckTopology X) (Type u) ⋙
      TopCat.Presheaf.stalkFunctor (Type u) x).mapCocone (sheafCocone F)) := by
  let T : CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u) ⥤ Type u :=
    sheafToPresheaf (Opens.grothendieckTopology X) (Type u) ⋙
      TopCat.Presheaf.stalkFunctor (Type u) x
  let P : X.Presheaf (Type u) := F.obj
  let c : Cocone (sheafDiagram F ⋙ T) := T.mapCocone (sheafCocone F)
  let α : sectionDiagram F x ≅ sheafDiagram F ⋙ T := stalkDiagramIso F x
  let d : Cocone (sectionDiagram F x) := (Cocone.precompose α.hom).obj c
  let e : d ≅ sectionCocone F x := Cocone.ext (Iso.refl _) (fun S => by
    let a : (sectionDiagram F x).obj S ⟶
        TopCat.Presheaf.stalk ((sheafDiagram F).obj S).obj x := (stageStalkIso F x S).hom
    let b : TopCat.Presheaf.stalk ((sheafDiagram F).obj S).obj x ⟶ P.stalk x :=
      T.map ((sheafCocone F).ι.app S)
    let g : (sectionDiagram F x).obj S ⟶ P.stalk x := (sectionCocone F x).ι.app S
    have hab : a ≫ b = g := stageStalkIso_hom_counit F x S
    change (a ≫ b) ≫ 𝟙 (P.stalk x) = g
    exact (Category.comp_id (a ≫ b)).trans hab)
  exact (IsColimit.precomposeHomEquiv α c)
    ((sectionCoconeIsColimit F x).ofIsoColimit e.symm)

/-- A sheaf on a prespectral space is the actual filtered colimit of
the inverse images of its direct images on finite compact-open models. -/
def sheafCoconeIsColimit
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u)) :
    IsColimit (sheafCocone F) := by
  classical
  let T (x : X) :
      CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u) ⥤ Type u :=
    sheafToPresheaf (Opens.grothendieckTopology X) (Type u) ⋙
      TopCat.Presheaf.stalkFunctor (Type u) x
  have hT : ∀ x : X, PreservesColimitsOfSize.{u, u} (T x) := fun x =>
    (stalkSkyscraperSheafAdjunction (C := Type u) x).leftAdjoint_preservesColimits
  have hReflects : JointlyReflectIsomorphisms T := by
    constructor
    intro A B f hf
    have hstalk : ∀ x : X,
        IsIso ((TopCat.Presheaf.stalkFunctor (Type u) x).map f.hom) := fun x => hf x
    exact TopCat.Presheaf.isIso_of_stalkFunctor_map_iso f
  exact hReflects.jointlyReflectsColimit (fun x => sheafStalkCoconeIsColimit F x)

end SchemeTheory.CompactOpenFiniteModel
