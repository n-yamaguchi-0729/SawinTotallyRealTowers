/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.EpiMono
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Topology.Sheaves.Limits
import Mathlib.Topology.Sheaves.Skyscraper
import Mathlib.Topology.Sheaves.Stalks

/-!
# The actual stalk-skyscraper embedding

The units of the stalk-skyscraper adjunction give a monomorphism from a
sheaf into the product of its stalk skyscrapers. The proof uses the
adjunction triangle to split every stalk map, then the conservativity of
stalks for monomorphisms.

For a finite topological space this is a finite product indexed explicitly
by `Fin n`. This is the finite-space embedding step of Stacks Project,
tag 0CAL: https://stacks.math.columbia.edu/tag/0CAL.
The finite-space reduction and the closed-constant comparison are separate
requirements; neither is assumed or asserted here.
-/

noncomputable section

universe u

open CategoryTheory Limits TopCat

namespace SchemeTheory

variable {X : TopCat.{u}}

/-- The skyscraper at a point, with its actual stalk as value. -/
abbrev stalkSkyscraper (F : X.Sheaf (Type u)) (x : X) : X.Sheaf (Type u) := by
  classical
  exact skyscraperSheaf x (F.presheaf.stalk x)

/-- The actual product of the adjunction units. -/
def toStalkSkyscrapers (F : X.Sheaf (Type u)) :
    F ⟶ ∏ᶜ (stalkSkyscraper F) := by
  classical
  exact Pi.lift (fun x : X => (stalkSkyscraperSheafAdjunction (C := Type u) x).unit.app F)

/-- Every stalk map of the product unit is split by a product projection
followed by the counit, so the original sheaf map is a monomorphism. -/
theorem mono_toStalkSkyscrapers (F : X.Sheaf (Type u)) :
    Mono (toStalkSkyscrapers F) := by
  classical
  have hmono (x : X) :
      Mono ((TopCat.Presheaf.stalkFunctor (Type u) x).map (toStalkSkyscrapers F).hom) := by
    let L : X.Sheaf (Type u) ⥤ Type u :=
      TopCat.Sheaf.forget (Type u) X ⋙ TopCat.Presheaf.stalkFunctor (Type u) x
    let adj := stalkSkyscraperSheafAdjunction (C := Type u) x
    let η : ∀ y : X, F ⟶ stalkSkyscraper F y :=
      fun y => (stalkSkyscraperSheafAdjunction (C := Type u) y).unit.app F
    have hπ : toStalkSkyscrapers F ≫ Pi.π (stalkSkyscraper F) x = η x :=
      Pi.lift_comp_π η x
    let r : L.obj (stalkSkyscraper F x) ⟶ L.obj F := adj.counit.app (L.obj F)
    have hsplit : L.map (toStalkSkyscrapers F) ≫
        (L.map (Pi.π (stalkSkyscraper F) x) ≫ r) = 𝟙 (L.obj F) := by
      rw [← Category.assoc, ← L.map_comp]
      rw [hπ]
      exact adj.left_triangle_components F
    change Mono (L.map (toStalkSkyscrapers F))
    have : IsSplitMono (L.map (toStalkSkyscrapers F)) :=
      ⟨⟨{ retraction := L.map (Pi.π (stalkSkyscraper F) x) ≫ r, id := hsplit }⟩⟩
    infer_instance
  exact (TopCat.Presheaf.mono_iff_stalk_mono (toStalkSkyscrapers F)).mpr hmono

/-- On an actual finite topological space the stalk embedding has finitely
many factors; the points are enumerated rather than supplied as missing
covering data. -/
theorem exists_finite_skyscraper_embedding [Finite X] (F : X.Sheaf (Type u)) :
    ∃ (n : ℕ) (p : Fin n → X) (m : F ⟶ ∏ᶜ (fun i => stalkSkyscraper F (p i))),
      Mono m := by
  classical
  let : Fintype X := Fintype.ofFinite X
  let e : X ≃ Fin (Fintype.card X) := Fintype.equivFin X
  have : Mono (toStalkSkyscrapers F) := mono_toStalkSkyscrapers F
  refine ⟨Fintype.card X, e.symm,
    toStalkSkyscrapers F ≫ (Pi.reindex e.symm (stalkSkyscraper F)).inv, ?_⟩
  infer_instance

end SchemeTheory
