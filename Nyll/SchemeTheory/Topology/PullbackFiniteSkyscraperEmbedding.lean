/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Topology.FiniteSkyscraperEmbedding
import Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.Limits
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# Pullback of the finite stalk-skyscraper embedding

Mapping the components of the actual stalk-skyscraper embedding gives
a morphism from the inverse image of a sheaf to the product of the
inverse images of its stalk skyscrapers. For a finite target space,
this is a monomorphism: inverse image preserves monomorphisms and the
finite product, whose comparison is Mathlib's `PreservesProduct.iso`.

The Lean proofs are original.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace SchemeTheory

variable {X Y : TopCat.{u}}

/-- The product of the inverse images of the actual skyscraper-unit maps. -/
def pullbackToStalkSkyscrapers (q : X ⟶ Y)
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) (Type u)) :
    (TopCat.Sheaf.pullback (Type u) q).obj G ⟶
      ∏ᶜ (fun y : Y => (TopCat.Sheaf.pullback (Type u) q).obj (stalkSkyscraper G y)) := by
  let JX : GrothendieckTopology (Opens X) := Opens.grothendieckTopology X
  let JY : GrothendieckTopology (Opens Y) := Opens.grothendieckTopology Y
  let L : CategoryTheory.Sheaf JY (Type u) ⥤ CategoryTheory.Sheaf JX (Type u) :=
    (Opens.map q).sheafPullback (Type u) JY JX
  let S : Y → CategoryTheory.Sheaf JY (Type u) := stalkSkyscraper G
  let m : G ⟶ ∏ᶜ S := toStalkSkyscrapers G
  exact Pi.lift (fun y : Y => L.map (m ≫ Pi.π S y))

/-- Pulling back the finite stalk-skyscraper embedding gives a
monomorphism into the product of the pulled-back skyscrapers. -/
theorem mono_pullbackToStalkSkyscrapers (q : X ⟶ Y) [Finite Y]
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) (Type u)) :
    Mono (pullbackToStalkSkyscrapers q G) := by
  let JX : GrothendieckTopology (Opens X) := Opens.grothendieckTopology X
  let JY : GrothendieckTopology (Opens Y) := Opens.grothendieckTopology Y
  let L : CategoryTheory.Sheaf JY (Type u) ⥤ CategoryTheory.Sheaf JX (Type u) :=
    (Opens.map q).sheafPullback (Type u) JY JX
  let S : Y → CategoryTheory.Sheaf JY (Type u) := stalkSkyscraper G
  let m : G ⟶ ∏ᶜ S := toStalkSkyscrapers G
  let n : L.obj G ⟶ ∏ᶜ (fun y : Y => L.obj (S y)) := pullbackToStalkSkyscrapers q G
  have hm : Mono m := mono_toStalkSkyscrapers G
  have hReflects : ReflectsLimits (CategoryTheory.forget (Type u)) :=
    reflectsLimits_of_reflectsIsomorphisms
  have hLan : PreservesFiniteLimits
      ((Opens.map q).op.lan : ((Opens Y)ᵒᵖ ⥤ Type u) ⥤ (Opens X)ᵒᵖ ⥤ Type u) :=
    lan_preservesFiniteLimits_of_flat (E := Type u) (Opens.map q)
  have hL : PreservesFiniteLimits L :=
    Functor.sheafPullbackConstruction.preservesFiniteLimits (Opens.map q) (Type u) JY JX
  let e : L.obj (∏ᶜ S) ≅ ∏ᶜ (fun y : Y => L.obj (S y)) := PreservesProduct.iso L S
  have heπ (y : Y) : e.hom ≫ Pi.π (fun z : Y => L.obj (S z)) y = L.map (Pi.π S y) :=
    piComparison_comp_π L S y
  have hn : n = L.map m ≫ e.hom := by
    apply Pi.hom_ext
    intro y
    change Pi.lift (fun z : Y => L.map (m ≫ Pi.π S z)) ≫
        Pi.π (fun z : Y => L.obj (S z)) y =
      (L.map m ≫ e.hom) ≫ Pi.π (fun z : Y => L.obj (S z)) y
    rw [Pi.lift_comp_π, Category.assoc, heπ, L.map_comp]
  have hmL : Mono (L.map m) := preserves_mono_of_preservesLimit L m
  have hmono : Mono (L.map m ≫ e.hom) := inferInstance
  change Mono n
  exact hn.symm ▸ hmono

end SchemeTheory
