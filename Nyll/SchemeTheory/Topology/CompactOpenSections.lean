/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.Topology.Sheaves.Limits
import Nyll.SchemeTheory.Topology.FiniteCoverFilteredColimit

/-!
# Compact-open sections preserve filtered colimits

The colimit of topological sheaves is the sheafification of their
presheaf colimit. Over a compact open in a prespectral, quasi-separated
space, the sheafification unit is bijective. Comparing the evaluated
presheaf colimit cocone with the evaluated sheafified cocone therefore
proves that the actual sheaf sections functor preserves filtered colimits.

Reference: https://stacks.math.columbia.edu/tag/009F.
The Lean proof is original.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace TopCat.Sheaf

variable {X : TopCat.{u}} [PrespectralSpace X] [QuasiSeparatedSpace X]

/-- Sections over a compact open preserve the colimit of any small
filtered diagram of sheaves on the actual topological site. -/
theorem preservesColimit_sheafSections_of_isCompact
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (U : Opens X) (hU : IsCompact (U : Set X))
    (F : I ⥤ CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u)) :
    PreservesColimit F
      ((sheafSections (Opens.grothendieckTopology X) (Type u)).obj (op U)) := by
  let J : GrothendieckTopology (Opens X) := Opens.grothendieckTopology X
  let P : I ⥤ (Opens X)ᵒᵖ ⥤ Type u := F ⋙ sheafToPresheaf J (Type u)
  let E : Cocone P := colimit.cocone P
  let S : Cocone F := CategoryTheory.Sheaf.sheafifyCocone E
  let Ev : ((Opens X)ᵒᵖ ⥤ Type u) ⥤ Type u :=
    (evaluation (Opens X)ᵒᵖ (Type u)).obj (op U)
  let Γ : CategoryTheory.Sheaf J (Type u) ⥤ Type u :=
    (sheafSections J (Type u)).obj (op U)
  let η : E.pt.obj (op U) ⟶ (CategoryTheory.sheafify J E.pt).obj (op U) :=
    (CategoryTheory.toSheafify J E.pt).app (op U)
  have hη : IsIso η := (isIso_iff_bijective η).mpr
    (TopCat.Presheaf.filteredColimit_toSheafify_app_bijective P
      (fun i => (F.obj i).property) U hU)
  let eη : E.pt.obj (op U) ≅ (CategoryTheory.sheafify J E.pt).obj (op U) :=
    asIso η
  have hE : IsColimit E := colimit.isColimit P
  have hS : IsColimit S := CategoryTheory.Sheaf.isColimitSheafifyCocone E hE
  have e : Ev.mapCocone E ≅ Γ.mapCocone S := by
    refine Cocone.ext eη ?_
    intro i
    change (E.ι.app i).app (op U) ≫
        (CategoryTheory.toSheafify J E.pt).app (op U) =
      ((CategoryTheory.Sheaf.sheafifyCocone E).ι.app i).hom.app (op U)
    rw [CategoryTheory.Sheaf.sheafifyCocone_ι_app_val, NatTrans.comp_app]
  exact preservesColimit_of_preserves_colimit_cocone hS
    ((isColimitOfPreserves Ev hE).ofIsoColimit e)

/-- The sections functor of a compact open preserves filtered colimits
on a prespectral, quasi-separated topological space. -/
theorem preservesFilteredColimits_sheafSections_of_isCompact
    (U : Opens X) (hU : IsCompact (U : Set X)) :
    PreservesFilteredColimitsOfSize.{u, u}
      ((sheafSections (Opens.grothendieckTopology X) (Type u)).obj (op U)) where
  preserves_filtered_colimits I _ _ :=
    ⟨fun {F} => preservesColimit_sheafSections_of_isCompact (I := I) U hU F⟩

end TopCat.Sheaf
